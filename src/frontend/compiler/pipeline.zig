const std = @import("std");
const GlobalEnv = @import("../env.zig").GlobalEnv;
const TheoremContext = @import("../expr.zig").TheoremContext;
const MmbWriter = @import("../mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const Metadata = @import("./metadata.zig");
const Sort = @import("../../trusted/sorts.zig").Sort;
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const MM0Stmt = @import("../../trusted/parse.zig").MM0Stmt;
const ProofScriptParser = @import("../proof_script.zig").Parser;
const TheoremBlock = @import("../proof_script.zig").TheoremBlock;
const Span = @import("../proof_script.zig").Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const CompilerEmit = @import("./emit.zig");
const Check = @import("./check.zig");
const RuleCatalog = @import("./rule_catalog.zig");
const CompilerVars = @import("./vars.zig");
const CompilerDiag = @import("./diag.zig");
const DiagnosticSource = CompilerDiag.DiagnosticSource;

const ViewDecl = Metadata.ViewDecl;
const FreshDecl = Metadata.FreshDecl;
const FreshenDecl = Metadata.FreshenDecl;
const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const Output = struct {
    sort_names: std.ArrayListUnmanaged([]const u8) = .{},
    sorts: std.ArrayListUnmanaged(Sort) = .{},
    terms: std.ArrayListUnmanaged(TermRecord) = .{},
    theorems: std.ArrayListUnmanaged(TheoremRecord) = .{},
    statements: std.ArrayListUnmanaged(Statement) = .{},
};

pub fn run(
    self: anytype,
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
    var proof_parser = if (self.proof_source) |proof|
        ProofScriptParser.init(allocator, proof)
    else
        null;
    var last_stmt: ?MM0Stmt = null;

    while (true) {
        const stmt = parser.next() catch |err| {
            self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(
                &parser,
                err,
            ));
            return err;
        } orelse break;
        last_stmt = stmt;
        CompilerVars.validateSortVarCollisions(&parser, &sort_vars) catch |err| {
            CompilerDiag.setIfMissing(
                self,
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
                    CompilerDiag.setIfMissing(
                        self,
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
                    CompilerDiag.setIfMissing(
                        self,
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
                const term_stmt_copy = term_stmt;
                if (emit) |out| {
                    const term_record = CompilerEmit.compileTermRecord(
                        allocator,
                        &parser,
                        term_stmt,
                    ) catch |err| {
                        CompilerDiag.setIfMissing(
                            self,
                            CompilerDiag.mm0StatementDiagnostic(
                                &parser,
                                MM0Stmt{ .term = term_stmt_copy },
                                err,
                            ),
                        );
                        return err;
                    };
                    try out.terms.append(allocator, term_record);
                    const body = if (term_stmt.is_def)
                        CompilerEmit.buildDefProofBody(
                            allocator,
                            &parser,
                            term_stmt,
                        ) catch |err| {
                            CompilerDiag.setIfMissing(
                                self,
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
                env.addStmt(stmt) catch |err| {
                    CompilerDiag.setIfMissing(
                        self,
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
                Metadata.processTermMetadata(
                    &env,
                    &registry,
                    term_stmt,
                    parser.last_annotations,
                ) catch |err| {
                    CompilerDiag.setIfMissing(
                        self,
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
                    &proof_parser,
                    assertion,
                    emit,
                ) catch |err| {
                    CompilerDiag.setIfMissing(
                        self,
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
            CompilerDiag.setIfMissing(
                self,
                CompilerDiag.mm0StatementDiagnostic(&parser, stmt, err),
            );
        }
        return err;
    };

    if (proof_parser) |*proofs| {
        const block = proofs.nextBlock() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                proofs,
                null,
                err,
            ));
            return err;
        } orelse return;
        self.setDiagnostic(CompilerDiag.extraProofBlockDiagnostic(
            block.name,
            block.name_span,
        ));
        return error.ExtraProofBlock;
    }
}

fn processAssertion(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *SortVarRegistry,
    proof_parser: *?ProofScriptParser,
    assertion: AssertionStmt,
    emit: ?*Output,
) !void {
    if (assertion.kind != .theorem) {
        return try processNonTheoremAssertion(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            assertion,
            emit,
        );
    }

    if (proof_parser.*) |*proofs| {
        var theorem = TheoremContext.init(allocator);
        defer theorem.deinit();

        try theorem.seedAssertion(assertion);
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
        const block = try nextTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            proofs,
            assertion.name,
            CompilerDiag.mathSpanToSpan(assertion.name_span),
            emit,
        );
        const checked = Check.checkTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            assertion,
            block,
            &theorem,
            theorem_concl,
        ) catch |err| {
            CompilerDiag.setIfMissing(
                self,
                CompilerDiag.theoremDiagnostic(
                    assertion.name,
                    block.name_span,
                    .proof,
                    err,
                ),
            );
            return err;
        };
        if (emit) |out| {
            const unify = try CompilerEmit.buildAssertionUnifyStream(
                allocator,
                &theorem,
                theorem_concl,
            );
            const args = try CompilerEmit.buildArgArray(parser, assertion.args);
            const hyp_names = try CompilerEmit.buildHypNames(
                allocator,
                assertion.hyps.len,
            );
            const body = CompilerEmit.buildTheoremProofBody(
                allocator,
                &theorem,
                env,
                checked,
            ) catch |err| {
                CompilerDiag.setIfMissing(
                    self,
                    CompilerDiag.theoremDiagnostic(
                        assertion.name,
                        block.name_span,
                        .proof,
                        err,
                    ),
                );
                return err;
            };
            try out.theorems.append(allocator, .{
                .args = args,
                .unify = unify,
                .name = assertion.name,
                .var_names = try CompilerEmit.buildTheoremVarNames(
                    allocator,
                    assertion.arg_names,
                    theorem.theorem_dummies.items.len,
                ),
                .hyp_names = hyp_names,
            });
            try out.statements.append(allocator, .{
                .cmd = .Thm,
                .body = body,
            });
        }
    }

    try addAssertionToEnv(
        self,
        env,
        assertion,
        assertion.name,
        CompilerDiag.mathSpanToSpan(assertion.name_span),
        .mm0,
    );
    try Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        parser.last_annotations,
    );
}

fn processNonTheoremAssertion(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    _: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    emit: ?*Output,
) !void {
    if (emit) |out| {
        var theorem = TheoremContext.init(allocator);
        defer theorem.deinit();
        try theorem.seedAssertion(assertion);
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
        const unify = try CompilerEmit.buildAssertionUnifyStream(
            allocator,
            &theorem,
            theorem_concl,
        );
        const args = try CompilerEmit.buildArgArray(parser, assertion.args);
        const hyp_names = try CompilerEmit.buildHypNames(
            allocator,
            assertion.hyps.len,
        );
        const body = try CompilerEmit.buildAxiomProofBody(
            allocator,
            &theorem,
            theorem_concl,
        );
        try out.theorems.append(allocator, .{
            .args = args,
            .unify = unify,
            .name = assertion.name,
            .var_names = try CompilerEmit.buildTheoremVarNames(
                allocator,
                assertion.arg_names,
                theorem.theorem_dummies.items.len,
            ),
            .hyp_names = hyp_names,
        });
        try out.statements.append(allocator, .{
            .cmd = .Axiom,
            .body = body,
        });
    }

    try addAssertionToEnv(
        self,
        env,
        assertion,
        assertion.name,
        CompilerDiag.mathSpanToSpan(assertion.name_span),
        .mm0,
    );
    try Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        parser.last_annotations,
    );
}

fn nextTheoremBlock(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proofs: *ProofScriptParser,
    theorem_name: []const u8,
    theorem_name_span: Span,
    emit: ?*Output,
) !TheoremBlock {
    while (true) {
        const block = proofs.nextBlock() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                proofs,
                theorem_name,
                err,
            ));
            return err;
        } orelse {
            self.setDiagnostic(CompilerDiag.missingProofBlockDiagnostic(
                theorem_name,
                theorem_name_span,
            ));
            return error.MissingProofBlock;
        };
        if (block.kind == .lemma) {
            try processLocalProofBlock(
                self,
                allocator,
                parser,
                env,
                registry,
                rule_catalog,
                fresh_bindings,
                freshen_bindings,
                views,
                sort_vars,
                block,
                emit,
            );
            continue;
        }
        if (!std.mem.eql(u8, block.name, theorem_name)) {
            self.setDiagnostic(CompilerDiag.theoremNameMismatchDiagnostic(
                theorem_name,
                block.name,
                block.name_span,
            ));
            return error.TheoremNameMismatch;
        }
        return block;
    }
}

fn parseLemmaAssertion(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    block: TheoremBlock,
) !AssertionStmt {
    const src = try std.fmt.allocPrint(
        allocator,
        "theorem {s}{s};",
        .{ block.name, block.header_tail },
    );
    return parser.parseAssertionText(src, .theorem, true) catch |err| {
        self.setDiagnostic(CompilerDiag.proofBlockDiagnostic(
            block.name,
            block.header_span,
            err,
        ));
        return err;
    };
}

fn processLocalProofBlock(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    block: TheoremBlock,
    emit: ?*Output,
) !void {
    const assertion = try parseLemmaAssertion(self, allocator, parser, block);

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(assertion);
    const theorem_concl = try theorem.internParsedExpr(assertion.concl);

    const checked = Check.checkTheoremBlock(
        self,
        allocator,
        parser,
        env,
        registry,
        rule_catalog,
        fresh_bindings,
        freshen_bindings,
        views,
        sort_vars,
        assertion,
        block,
        &theorem,
        theorem_concl,
    ) catch |err| {
        CompilerDiag.setIfMissing(
            self,
            CompilerDiag.theoremDiagnostic(
                assertion.name,
                block.header_span,
                .proof,
                err,
            ),
        );
        return err;
    };

    if (emit) |out| {
        const unify = try CompilerEmit.buildAssertionUnifyStream(
            allocator,
            &theorem,
            theorem_concl,
        );
        const args = try CompilerEmit.buildArgArray(parser, assertion.args);
        const hyp_names = try CompilerEmit.buildHypNames(
            allocator,
            assertion.hyps.len,
        );
        const body = CompilerEmit.buildTheoremProofBody(
            allocator,
            &theorem,
            env,
            checked,
        ) catch |err| {
            CompilerDiag.setIfMissing(
                self,
                CompilerDiag.theoremDiagnostic(
                    assertion.name,
                    block.header_span,
                    .proof,
                    err,
                ),
            );
            return err;
        };
        try out.theorems.append(allocator, .{
            .args = args,
            .unify = unify,
            .name = assertion.name,
            .var_names = try CompilerEmit.buildTheoremVarNames(
                allocator,
                assertion.arg_names,
                theorem.theorem_dummies.items.len,
            ),
            .hyp_names = hyp_names,
        });
        try out.statements.append(allocator, .{
            .cmd = .LocalThm,
            .body = body,
        });
    }

    try addAssertionToEnv(
        self,
        env,
        assertion,
        block.name,
        block.name_span,
        .proof,
    );
}

fn addAssertionToEnv(
    self: anytype,
    env: *GlobalEnv,
    assertion: AssertionStmt,
    diag_name: []const u8,
    span: ?Span,
    source: DiagnosticSource,
) !void {
    env.addStmt(.{ .assertion = assertion }) catch |err| {
        if (err == error.DuplicateRuleName) {
            self.setDiagnostic(CompilerDiag.duplicateRuleNameDiagnostic(
                diag_name,
                span,
                source,
            ));
        }
        return err;
    };
}
