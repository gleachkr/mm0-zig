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
const ProofScriptParser = @import("../proof_script.zig").Parser;
const TheoremBlock = @import("../proof_script.zig").TheoremBlock;
const Span = @import("../proof_script.zig").Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const CompilerEmit = @import("./emit.zig");
const Check = @import("./check.zig");
const CompilerVars = @import("./vars.zig");

const ViewDecl = Metadata.ViewDecl;
const FreshDecl = Metadata.FreshDecl;
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
    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    var fresh_bindings = std.AutoHashMap(u32, []const FreshDecl).init(
        allocator,
    );
    var views = std.AutoHashMap(u32, ViewDecl).init(allocator);
    var sort_vars = SortVarRegistry.init(allocator);
    var proof_parser = if (self.proof_source) |proof|
        ProofScriptParser.init(allocator, proof)
    else
        null;

    while (try parser.next()) |stmt| {
        try CompilerVars.validateSortVarCollisions(&parser, &sort_vars);
        switch (stmt) {
            .sort => |sort_stmt| {
                if (emit) |out| {
                    try out.sort_names.append(allocator, sort_stmt.name);
                    try out.sorts.append(allocator, sort_stmt.modifiers);
                    try out.statements.append(allocator, .{
                        .cmd = .Sort,
                        .body = &.{},
                    });
                }
                try env.addStmt(stmt);
                try Metadata.processSortMetadata(
                    &parser,
                    sort_stmt,
                    parser.last_annotations,
                    &sort_vars,
                );
            },
            .term => |term_stmt| {
                if (emit) |out| {
                    const term_record = try CompilerEmit.compileTermRecord(
                        allocator,
                        &parser,
                        term_stmt,
                    );
                    try out.terms.append(allocator, term_record);
                    try out.statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = if (term_stmt.is_def)
                            try CompilerEmit.buildDefProofBody(
                                allocator,
                                &parser,
                                term_stmt,
                            )
                        else
                            &.{},
                    });
                }
                try env.addStmt(stmt);
                try Metadata.processTermMetadata(
                    &env,
                    &registry,
                    term_stmt,
                    parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                try processAssertion(
                    self,
                    allocator,
                    &parser,
                    &env,
                    &registry,
                    &fresh_bindings,
                    &views,
                    &sort_vars,
                    &proof_parser,
                    assertion,
                    emit,
                );
            },
        }
    }

    try CompilerVars.validateSortVarCollisions(&parser, &sort_vars);

    if (proof_parser) |*proofs| {
        if (try proofs.nextBlock()) |block| {
            self.setDiagnostic(.{
                .kind = .extra_proof_block,
                .err = error.ExtraProofBlock,
                .block_name = block.name,
                .span = block.name_span,
            });
            return error.ExtraProofBlock;
        }
    }
}

fn processAssertion(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
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
            fresh_bindings,
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
            fresh_bindings,
            views,
            sort_vars,
            proofs,
            assertion.name,
            emit,
        );
        const checked = Check.checkTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            fresh_bindings,
            views,
            sort_vars,
            assertion,
            block,
            &theorem,
            theorem_concl,
        ) catch |err| {
            setTheoremDiagnosticIfMissing(
                self,
                assertion.name,
                block.name_span,
                err,
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
                setTheoremDiagnosticIfMissing(
                    self,
                    assertion.name,
                    block.name_span,
                    err,
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
        null,
    );
    try Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
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
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
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
        null,
    );
    try Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
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
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proofs: *ProofScriptParser,
    theorem_name: []const u8,
    emit: ?*Output,
) !TheoremBlock {
    while (true) {
        const block = try proofs.nextBlock() orelse {
            self.setDiagnostic(.{
                .kind = .missing_proof_block,
                .err = error.MissingProofBlock,
                .theorem_name = theorem_name,
            });
            return error.MissingProofBlock;
        };
        if (block.kind == .lemma) {
            try processLocalProofBlock(
                self,
                allocator,
                parser,
                env,
                registry,
                fresh_bindings,
                views,
                sort_vars,
                block,
                emit,
            );
            continue;
        }
        if (!std.mem.eql(u8, block.name, theorem_name)) {
            self.setDiagnostic(.{
                .kind = .theorem_name_mismatch,
                .err = error.TheoremNameMismatch,
                .theorem_name = theorem_name,
                .block_name = block.name,
                .expected_name = theorem_name,
                .span = block.name_span,
            });
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
        self.setDiagnostic(.{
            .kind = .generic,
            .err = err,
            .theorem_name = block.name,
            .block_name = block.name,
            .span = block.header_span,
        });
        return err;
    };
}

fn processLocalProofBlock(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
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
        fresh_bindings,
        views,
        sort_vars,
        assertion,
        block,
        &theorem,
        theorem_concl,
    ) catch |err| {
        setTheoremDiagnosticIfMissing(
            self,
            assertion.name,
            block.header_span,
            err,
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
            setTheoremDiagnosticIfMissing(
                self,
                assertion.name,
                block.header_span,
                err,
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
    );
}

fn addAssertionToEnv(
    self: anytype,
    env: *GlobalEnv,
    assertion: AssertionStmt,
    diag_name: []const u8,
    span: ?Span,
) !void {
    env.addStmt(.{ .assertion = assertion }) catch |err| {
        if (err == error.DuplicateRuleName) {
            self.setDiagnostic(.{
                .kind = .duplicate_rule_name,
                .err = err,
                .name = diag_name,
                .span = span,
            });
        }
        return err;
    };
}

fn setTheoremDiagnosticIfMissing(
    self: anytype,
    theorem_name: []const u8,
    span: Span,
    err: anyerror,
) void {
    if (self.last_diagnostic != null) return;
    self.setDiagnostic(.{
        .kind = .generic,
        .err = err,
        .theorem_name = theorem_name,
        .span = span,
    });
}
