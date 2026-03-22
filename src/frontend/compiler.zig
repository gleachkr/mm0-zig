const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const Expr = @import("../trusted/expressions.zig").Expr;
const MmbWriter = @import("./mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const CompilerDiag = @import("./compiler_diag.zig");
const CompilerDummies = @import("./compiler_dummies.zig");
const CompilerViews = @import("./compiler_views.zig");
const TermAnnotations = @import("./term_annotations.zig");
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const TermStmt = @import("../trusted/parse.zig").TermStmt;
const ProofScriptParser = @import("./proof_script.zig").Parser;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
pub const DebugConfig = @import("./debug.zig").DebugConfig;

// Sub-modules
const Emit = @import("./compiler_emit.zig");
const Check = @import("./compiler_check.zig");
const Inference = @import("./compiler_inference.zig");
const Normalize = @import("./compiler_normalize.zig");

pub const ViewDecl = CompilerViews.ViewDecl;
pub const DummyDecl = CompilerDummies.DummyDecl;
pub const Diagnostic = CompilerDiag.Diagnostic;

pub const CheckedRef = union(enum) {
    hyp: usize,
    line: usize,
};

pub const CheckedLine = struct {
    expr: ExprId,
    data: union(enum) {
        rule: RuleLine,
        transport: TransportLine,
    },

    pub const RuleLine = struct {
        rule_id: u32,
        bindings: []const ExprId,
        refs: []const CheckedRef,
    };

    pub const TransportLine = struct {
        source: CheckedRef,
        source_expr: ExprId,
    };
};

pub fn appendRuleLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{
        .expr = expr,
        .data = .{ .rule = .{
            .rule_id = rule_id,
            .bindings = bindings,
            .refs = refs,
        } },
    });
    return idx;
}

pub fn appendTransportLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
    source_expr: ExprId,
    source: CheckedRef,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{
        .expr = expr,
        .data = .{ .transport = .{
            .source = source,
            .source_expr = source_expr,
        } },
    });
    return idx;
}

pub const Compiler = struct {
    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    last_diagnostic: ?Diagnostic,
    debug: DebugConfig,

    pub fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = null,
            .last_diagnostic = null,
            .debug = DebugConfig.none,
        };
    }

    pub fn initWithProof(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: []const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = proof_source,
            .last_diagnostic = null,
            .debug = DebugConfig.none,
        };
    }

    pub fn check(self: *Compiler) !void {
        self.last_diagnostic = null;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(self.source, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
        var dummies = std.AutoHashMap(u32, []const DummyDecl).init(
            arena.allocator(),
        );
        var views = std.AutoHashMap(u32, ViewDecl).init(arena.allocator());
        var proof_parser = if (self.proof_source) |proof|
            ProofScriptParser.init(arena.allocator(), proof)
        else
            null;

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .assertion => |assertion| {
                    if (assertion.kind != .theorem) {
                        try env.addStmt(stmt);
                        try processAssertionMetadata(
                            arena.allocator(),
                            &parser,
                            &env,
                            &registry,
                            &dummies,
                            &views,
                            assertion,
                            parser.last_annotations,
                        );
                        continue;
                    }

                    var theorem = TheoremContext.init(arena.allocator());
                    defer theorem.deinit();

                    try theorem.seedAssertion(assertion);
                    const theorem_concl = try theorem.internParsedExpr(
                        assertion.concl,
                    );

                    if (proof_parser) |*proofs| {
                        const block = try proofs.nextBlock() orelse {
                            self.setDiagnostic(.{
                                .kind = .missing_proof_block,
                                .err = error.MissingProofBlock,
                                .theorem_name = assertion.name,
                            });
                            return error.MissingProofBlock;
                        };
                        if (!std.mem.eql(u8, block.name, assertion.name)) {
                            self.setDiagnostic(.{
                                .kind = .theorem_name_mismatch,
                                .err = error.TheoremNameMismatch,
                                .theorem_name = assertion.name,
                                .block_name = block.name,
                                .expected_name = assertion.name,
                                .span = block.name_span,
                            });
                            return error.TheoremNameMismatch;
                        }
                        _ = try Check.checkTheoremBlock(
                            self,
                            arena.allocator(),
                            &parser,
                            &env,
                            &registry,
                            &dummies,
                            &views,
                            assertion,
                            block,
                            &theorem,
                            theorem_concl,
                        );
                    }

                    try env.addStmt(stmt);
                    try processAssertionMetadata(
                        arena.allocator(),
                        &parser,
                        &env,
                        &registry,
                        &dummies,
                        &views,
                        assertion,
                        parser.last_annotations,
                    );
                },
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try processTermMetadata(
                        &env,
                        &registry,
                        term_stmt,
                        parser.last_annotations,
                    );
                },
                else => try env.addStmt(stmt),
            }
        }

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

    pub fn compileMmb(
        self: *Compiler,
        out_allocator: std.mem.Allocator,
    ) ![]u8 {
        self.last_diagnostic = null;

        const proof_source = self.proof_source orelse return error.MissingProofFile;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();

        var parser = MM0Parser.init(self.source, allocator);
        var proof_parser = ProofScriptParser.init(allocator, proof_source);
        var env = GlobalEnv.init(allocator);
        var registry = RewriteRegistry.init(allocator);
        var dummies = std.AutoHashMap(u32, []const DummyDecl).init(
            allocator,
        );
        var views = std.AutoHashMap(u32, ViewDecl).init(allocator);

        var sort_names = std.ArrayListUnmanaged([]const u8){};
        var sorts = std.ArrayListUnmanaged(@import("../trusted/sorts.zig").Sort){};
        var terms = std.ArrayListUnmanaged(TermRecord){};
        var theorems = std.ArrayListUnmanaged(TheoremRecord){};
        var statements = std.ArrayListUnmanaged(Statement){};

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .sort => |sort_stmt| {
                    try sort_names.append(allocator, sort_stmt.name);
                    try sorts.append(allocator, sort_stmt.modifiers);
                    try statements.append(allocator, .{
                        .cmd = .Sort,
                        .body = &.{},
                    });
                    try env.addStmt(stmt);
                },
                .term => |term_stmt| {
                    const term_record = try Emit.compileTermRecord(
                        allocator,
                        &parser,
                        term_stmt,
                    );
                    try terms.append(allocator, term_record);
                    try statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = if (term_stmt.is_def)
                            try Emit.buildDefProofBody(allocator, &parser, term_stmt)
                        else
                            &.{},
                    });
                    try env.addStmt(stmt);
                    try processTermMetadata(
                        &env,
                        &registry,
                        term_stmt,
                        parser.last_annotations,
                    );
                },
                .assertion => |assertion| {
                    var theorem = TheoremContext.init(allocator);
                    defer theorem.deinit();
                    try theorem.seedAssertion(assertion);
                    const theorem_concl = try theorem.internParsedExpr(
                        assertion.concl,
                    );
                    const unify = try Emit.buildAssertionUnifyStream(
                        allocator,
                        &theorem,
                        theorem_concl,
                    );
                    const args = try Emit.buildArgArray(&parser, assertion.args);
                    const hyp_names = try Emit.buildHypNames(
                        allocator,
                        assertion.hyps.len,
                    );

                    switch (assertion.kind) {
                        .axiom => {
                            const body = try Emit.buildAxiomProofBody(
                                allocator,
                                &theorem,
                                theorem_concl,
                            );
                            try theorems.append(allocator, .{
                                .args = args,
                                .unify = unify,
                                .name = assertion.name,
                                .var_names = try Emit.buildTheoremVarNames(
                                    allocator,
                                    assertion.arg_names,
                                    theorem.theorem_dummies.items.len,
                                ),
                                .hyp_names = hyp_names,
                            });
                            try statements.append(allocator, .{
                                .cmd = .Axiom,
                                .body = body,
                            });
                            try env.addStmt(stmt);
                            try processAssertionMetadata(
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &dummies,
                                &views,
                                assertion,
                                parser.last_annotations,
                            );
                        },
                        .theorem => {
                            const block = try proof_parser.nextBlock() orelse {
                                self.setDiagnostic(.{
                                    .kind = .missing_proof_block,
                                    .err = error.MissingProofBlock,
                                    .theorem_name = assertion.name,
                                });
                                return error.MissingProofBlock;
                            };
                            if (!std.mem.eql(u8, block.name, assertion.name)) {
                                self.setDiagnostic(.{
                                    .kind = .theorem_name_mismatch,
                                    .err = error.TheoremNameMismatch,
                                    .theorem_name = assertion.name,
                                    .block_name = block.name,
                                    .expected_name = assertion.name,
                                    .span = block.name_span,
                                });
                                return error.TheoremNameMismatch;
                            }
                            const checked = try Check.checkTheoremBlock(
                                self,
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &dummies,
                                &views,
                                assertion,
                                block,
                                &theorem,
                                theorem_concl,
                            );
                            const body = try Emit.buildTheoremProofBody(
                                allocator,
                                &theorem,
                                &env,
                                checked,
                            );
                            try theorems.append(allocator, .{
                                .args = args,
                                .unify = unify,
                                .name = assertion.name,
                                .var_names = try Emit.buildTheoremVarNames(
                                    allocator,
                                    assertion.arg_names,
                                    theorem.theorem_dummies.items.len,
                                ),
                                .hyp_names = hyp_names,
                            });
                            try statements.append(allocator, .{
                                .cmd = .Thm,
                                .body = body,
                            });
                            try env.addStmt(stmt);
                            try processAssertionMetadata(
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &dummies,
                                &views,
                                assertion,
                                parser.last_annotations,
                            );
                        },
                    }
                },
            }
        }

        if (try proof_parser.nextBlock()) |block| {
            self.setDiagnostic(.{
                .kind = .extra_proof_block,
                .err = error.ExtraProofBlock,
                .block_name = block.name,
                .span = block.name_span,
            });
            return error.ExtraProofBlock;
        }

        return try MmbWriter.buildFile(
            out_allocator,
            sort_names.items,
            sorts.items,
            terms.items,
            theorems.items,
            statements.items,
        );
    }

    pub fn writeMmb(self: *Compiler) !void {
        const bytes = try self.compileMmb(self.allocator);
        self.allocator.free(bytes);
    }

    pub fn writeMm0(self: *Compiler) !void {
        try self.check();
        return error.Unimplemented;
    }

    pub fn reportError(self: *const Compiler, err: anyerror) void {
        if (self.last_diagnostic) |diag| {
            if (diag.err == err) {
                std.debug.print(
                    "error: {s}\n",
                    .{diagnosticSummary(diag)},
                );
                if (diag.theorem_name) |name| {
                    std.debug.print("  theorem: {s}\n", .{name});
                }
                if (diag.block_name) |name| {
                    std.debug.print("  proof block: {s}\n", .{name});
                }
                if (diag.line_label) |label| {
                    std.debug.print("  line: {s}\n", .{label});
                }
                if (diag.rule_name) |rule| {
                    std.debug.print("  rule: {s}\n", .{rule});
                }
                if (diag.name) |name| {
                    std.debug.print("  name: {s}\n", .{name});
                }
                if (diag.expected_name) |name| {
                    std.debug.print("  expected: {s}\n", .{name});
                }
                self.reportDiagnosticLocation(diag);
                return;
            }
        }
        std.debug.print("error: {s}\n", .{@errorName(err)});
    }

    fn reportDiagnosticLocation(
        self: *const Compiler,
        diag: Diagnostic,
    ) void {
        const span = diag.span orelse return;
        const src = self.proof_source orelse return;
        const info = lineCol(src, span.start);
        const line = src[info.line_start..info.line_end];

        std.debug.print(
            "  --> proof:{d}:{d}\n",
            .{ info.line, info.column },
        );
        std.debug.print("  | {s}\n", .{line});
        std.debug.print("  | ", .{});

        const caret_start = span.start - info.line_start;
        const caret_end = if (span.end > span.start)
            @min(span.end, info.line_end)
        else
            @min(span.start + 1, info.line_end);
        const caret_len = @max(caret_end - span.start, 1);

        for (0..caret_start) |_| {
            std.debug.print(" ", .{});
        }
        for (0..caret_len) |_| {
            std.debug.print("^", .{});
        }
        std.debug.print("\n", .{});
    }

    pub fn setDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.last_diagnostic = diag;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;

const LineCol = struct {
    line: usize,
    column: usize,
    line_start: usize,
    line_end: usize,
};

fn lineCol(src: []const u8, pos_raw: usize) LineCol {
    const pos = @min(pos_raw, src.len);
    var line: usize = 1;
    var column: usize = 1;
    var line_start: usize = 0;
    var i: usize = 0;

    while (i < pos) : (i += 1) {
        if (src[i] == '\n') {
            line += 1;
            column = 1;
            line_start = i + 1;
        } else {
            column += 1;
        }
    }

    var line_end = line_start;
    while (line_end < src.len and src[line_end] != '\n') : (line_end += 1) {}

    return .{
        .line = line,
        .column = column,
        .line_start = line_start,
        .line_end = line_end,
    };
}

fn processTermMetadata(
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    term_stmt: TermStmt,
    annotations: []const []const u8,
) !void {
    try TermAnnotations.processTermAnnotations(
        env,
        term_stmt,
        annotations,
    );
    try registry.processAnnotations(env, term_stmt.name, annotations);
}

fn processAssertionMetadata(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    dummies: *std.AutoHashMap(u32, []const DummyDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    annotations: []const []const u8,
) !void {
    try registry.processAnnotations(env, assertion.name, annotations);
    try CompilerDummies.processDummyAnnotations(
        allocator,
        parser,
        env,
        assertion,
        annotations,
        dummies,
    );
    try CompilerViews.processViewAnnotations(
        allocator,
        parser,
        env,
        assertion,
        annotations,
        views,
    );
}
