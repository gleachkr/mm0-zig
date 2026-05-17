const std = @import("std");
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const Metadata = @import("../metadata.zig");
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("../../parse_recovery.zig").MM0Stmt;
const ProofScript = @import("../../proof_script.zig");
const Span = ProofScript.Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerEmit = @import("../emit.zig");
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerVars = @import("../vars.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CompilerLints = @import("../lints.zig");
const Common = @import("common.zig");

const FreshDecl = Metadata.FreshDecl;
const FreshenDecl = Metadata.FreshenDecl;
const ViewDecl = Metadata.ViewDecl;
const SortVarRegistry = CompilerVars.SortVarRegistry;
const Output = Common.Output;
const ProofItemStream = Common.ProofItemStream;
const DiagnosticSource = CompilerDiag.DiagnosticSource;
const drainAnchoredLocalProofItems = Common.drainAnchoredLocalProofItems;
const fillPublicDefBody = Common.fillPublicDefBody;
const processAssertion = Common.processAssertion;
const setExtraProofItemDiagnostic = Common.setExtraProofItemDiagnostic;
const validateDefinitionBody = Common.validateDefinitionBody;

pub fn run(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    emit: ?*Output,
) !void {
    var parser = MM0Parser.init(self.source, allocator);
    var rule_catalog = RuleCatalog.build(allocator, self.source) catch
        RuleCatalog.Catalog.init(allocator);
    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    var fresh_bindings = std.AutoHashMap(u32, []const FreshDecl).init(
        allocator,
    );
    var freshen_bindings = std.AutoHashMap(u32, []const FreshenDecl).init(
        allocator,
    );
    var views = std.AutoHashMap(u32, ViewDecl).init(allocator);
    var sort_vars = SortVarRegistry.init(allocator);
    var proof_stream = if (self.proof_source) |proof|
        ProofItemStream.init(allocator, proof)
    else
        null;
    var last_stmt: ?MM0Stmt = null;

    while (true) {
        parser.prepareNextPublicStatement() catch |err| {
            self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(
                &parser,
                err,
            ));
            return err;
        };
        try drainAnchoredLocalProofItems(
            self,
            allocator,
            &parser,
            &env,
            &registry,
            &rule_catalog,
            &fresh_bindings,
            &freshen_bindings,
            &views,
            &sort_vars,
            &proof_stream,
            emit,
        );

        const stmt = parser.next() catch |err| {
            self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(
                &parser,
                err,
            ));
            return err;
        } orelse break;
        last_stmt = stmt;
        CompilerVars.validateSortVarCollisions(&parser, &sort_vars) catch |err| {
            self.setIfMissing(
                CompilerDiag.mm0StatementDiagnostic(&parser, stmt, err),
            );
            return err;
        };
        switch (stmt) {
            .sort => |sort_stmt| {
                const sort_stmt_copy = sort_stmt;
                if (emit) |out| {
                    try out.sort_names.append(allocator, sort_stmt.name);
                    try out.sorts.append(allocator, sort_stmt.modifiers);
                    try out.statements.append(allocator, .{
                        .cmd = .Sort,
                        .body = &.{},
                    });
                }
                env.addStmt(stmt) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .sort = sort_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
                Metadata.processSortMetadata(
                    &parser,
                    sort_stmt,
                    parser.last_annotations,
                    &sort_vars,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .sort = sort_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
            },
            .term => |term_stmt| {
                var filled_term_stmt = term_stmt;
                var filled_body_span: ?Span = null;
                if (term_stmt.is_def and term_stmt.body == null) {
                    const filled = try fillPublicDefBody(
                        self,
                        allocator,
                        &parser,
                        &proof_stream,
                        term_stmt,
                    );
                    filled_term_stmt = filled.stmt;
                    filled_body_span = filled.body_span;
                }

                const term_stmt_copy = filled_term_stmt;
                const term_diag_source: DiagnosticSource = if (filled_body_span != null)
                    .proof
                else
                    .mm0;
                const term_diag_span = filled_body_span;
                validateDefinitionBody(
                    self,
                    allocator,
                    &parser,
                    &env,
                    filled_term_stmt,
                    term_diag_source,
                    term_diag_span,
                ) catch |err| {
                    return err;
                };
                if (emit) |out| {
                    const term_record = CompilerEmit.compileTermRecord(
                        allocator,
                        &parser,
                        filled_term_stmt,
                    ) catch |err| {
                        self.setIfMissing(
                            CompilerDiag.mm0StatementDiagnostic(
                                &parser,
                                MM0Stmt{ .term = term_stmt_copy },
                                err,
                            ),
                        );
                        return err;
                    };
                    try out.terms.append(allocator, term_record);
                    const body = if (filled_term_stmt.is_def)
                        CompilerEmit.buildDefProofBody(
                            allocator,
                            &parser,
                            filled_term_stmt,
                        ) catch |err| {
                            self.setIfMissing(
                                CompilerDiag.mm0StatementDiagnostic(
                                    &parser,
                                    MM0Stmt{ .term = term_stmt_copy },
                                    err,
                                ),
                            );
                            return err;
                        }
                    else
                        &.{};
                    try out.statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = body,
                    });
                }
                env.addStmt(.{ .term = filled_term_stmt }) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
                if (filled_term_stmt.is_def) {
                    const term_id = env.term_names.get(
                        filled_term_stmt.name,
                    ) orelse {
                        return error.UnknownTerm;
                    };
                    try CompilerLints.lintUnusedDefinitionParameters(
                        self,
                        allocator,
                        &env.terms.items[term_id],
                        CompilerDiag.mathSpanToSpan(
                            filled_term_stmt.name_span,
                        ),
                        .mm0,
                    );
                }
                Metadata.processTermMetadata(
                    &env,
                    &registry,
                    filled_term_stmt,
                    parser.last_annotations,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
            },
            .assertion => |assertion| {
                processAssertion(
                    self,
                    allocator,
                    &parser,
                    &env,
                    &registry,
                    &rule_catalog,
                    &fresh_bindings,
                    &freshen_bindings,
                    &views,
                    &sort_vars,
                    &proof_stream,
                    assertion,
                    emit,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .assertion = assertion },
                            err,
                        ),
                    );
                    return err;
                };
            },
        }
    }

    CompilerVars.validateSortVarCollisions(&parser, &sort_vars) catch |err| {
        if (last_stmt) |stmt| {
            self.setIfMissing(
                CompilerDiag.mm0StatementDiagnostic(&parser, stmt, err),
            );
        }
        return err;
    };

    if (proof_stream) |*proofs| {
        const item = proofs.next() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proofs.parser,
                null,
                err,
            ));
            return err;
        } orelse return;
        return setExtraProofItemDiagnostic(self, item);
    }
}
