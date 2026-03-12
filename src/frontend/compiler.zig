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
const CompilerViews = @import("./compiler_views.zig");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const TermStmt = @import("../trusted/parse.zig").TermStmt;
const ProofCmd = @import("../trusted/proof.zig").ProofCmd;
const UnifyCmd = @import("../trusted/proof.zig").UnifyCmd;
const UnifyReplay = @import("../trusted/unify_replay.zig");
const ProofLine = @import("./proof_script.zig").ProofLine;
const Span = @import("./proof_script.zig").Span;
const TheoremBlock = @import("./proof_script.zig").TheoremBlock;
const ProofScriptParser = @import("./proof_script.zig").Parser;
const Arg = @import("../trusted/args.zig").Arg;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const Normalizer = @import("./normalizer.zig").Normalizer;
const InferenceSolver = @import("./inference_solver.zig").Solver;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;

const NameExprMap = std.StringHashMap(*const Expr);
const LabelIndexMap = std.StringHashMap(usize);
const ExprSlotMap = std.AutoHashMapUnmanaged(ExprId, u32);

pub const ViewDecl = CompilerViews.ViewDecl;
pub const Diagnostic = CompilerDiag.Diagnostic;

pub const CheckedRef = union(enum) {
    hyp: usize,
    line: usize,
};

pub const CheckedLine = struct {
    expr: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
};

const ExprInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

const LineCol = struct {
    line: usize,
    column: usize,
    line_start: usize,
    line_end: usize,
};

pub const Compiler = struct {
    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    last_diagnostic: ?Diagnostic,

    pub fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = null,
            .last_diagnostic = null,
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
        };
    }

    pub fn check(self: *Compiler) !void {
        self.last_diagnostic = null;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(self.source, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
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
                        try registry.processAnnotations(&env, assertion.name, parser.last_annotations);
                        try CompilerViews.processViewAnnotations(
                            arena.allocator(),
                            &parser,
                            &env,
                            assertion,
                            parser.last_annotations,
                            &views,
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
                        _ = try checkTheoremBlock(
                            self,
                            arena.allocator(),
                            &parser,
                            &env,
                            &registry,
                            &views,
                            assertion,
                            block,
                            &theorem,
                            theorem_concl,
                        );
                    }

                    try env.addStmt(stmt);
                    try registry.processAnnotations(&env, assertion.name, parser.last_annotations);
                    try CompilerViews.processViewAnnotations(
                        arena.allocator(),
                        &parser,
                        &env,
                        assertion,
                        parser.last_annotations,
                        &views,
                    );
                },
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(&env, term_stmt.name, parser.last_annotations);
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
                },
                .term => |term_stmt| {
                    const term_record = try compileTermRecord(
                        allocator,
                        &parser,
                        term_stmt,
                    );
                    try terms.append(allocator, term_record);
                    try statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = if (term_stmt.is_def)
                            try buildDefProofBody(allocator, term_stmt)
                        else
                            &.{},
                    });
                    try env.addStmt(stmt);
                    try registry.processAnnotations(&env, term_stmt.name, parser.last_annotations);
                },
                .assertion => |assertion| {
                    var theorem = TheoremContext.init(allocator);
                    defer theorem.deinit();
                    try theorem.seedAssertion(assertion);
                    const theorem_concl = try theorem.internParsedExpr(
                        assertion.concl,
                    );
                    const unify = try buildAssertionUnifyStream(
                        allocator,
                        &theorem,
                        theorem_concl,
                    );
                    const args = try buildArgArray(&parser, assertion.args);
                    const hyp_names = try buildHypNames(
                        allocator,
                        assertion.hyps.len,
                    );

                    switch (assertion.kind) {
                        .axiom => {
                            const body = try buildAxiomProofBody(
                                allocator,
                                &theorem,
                                theorem_concl,
                            );
                            try theorems.append(allocator, .{
                                .args = args,
                                .unify = unify,
                                .name = assertion.name,
                                .var_names = assertion.arg_names,
                                .hyp_names = hyp_names,
                            });
                            try statements.append(allocator, .{
                                .cmd = .Axiom,
                                .body = body,
                            });
                            try env.addStmt(stmt);
                            try registry.processAnnotations(&env, assertion.name, parser.last_annotations);
                            try CompilerViews.processViewAnnotations(
                                allocator,
                                &parser,
                                &env,
                                assertion,
                                parser.last_annotations,
                                &views,
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
                            const checked = try checkTheoremBlock(
                                self,
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &views,
                                assertion,
                                block,
                                &theorem,
                                theorem_concl,
                            );
                            const body = try buildTheoremProofBody(
                                allocator,
                                &theorem,
                                checked,
                            );
                            try theorems.append(allocator, .{
                                .args = args,
                                .unify = unify,
                                .name = assertion.name,
                                .var_names = assertion.arg_names,
                                .hyp_names = hyp_names,
                            });
                            try statements.append(allocator, .{
                                .cmd = .Thm,
                                .body = body,
                            });
                            try env.addStmt(stmt);
                            try CompilerViews.processViewAnnotations(
                                allocator,
                                &parser,
                                &env,
                                assertion,
                                parser.last_annotations,
                                &views,
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

    fn setDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.last_diagnostic = diag;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;

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

fn compileTermRecord(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    stmt: TermStmt,
) !TermRecord {
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(stmt);

    const unify = if (stmt.body) |body| blk: {
        const expr_id = try theorem.internParsedExpr(body);
        break :blk try buildTermUnifyStream(allocator, &theorem, expr_id);
    } else &.{};

    return .{
        .args = try buildArgArray(parser, stmt.args),
        .ret_sort = try lookupSortId(parser, stmt.ret_sort_name),
        .is_def = stmt.is_def,
        .unify = unify,
        .name = stmt.name,
        .var_names = stmt.arg_names,
    };
}

fn buildArgArray(
    parser: *MM0Parser,
    args: []const ArgInfo,
) ![]const Arg {
    const result = try parser.allocator.alloc(Arg, args.len);
    for (args, 0..) |arg, idx| {
        result[idx] = .{
            .deps = arg.deps,
            .reserved = 0,
            .sort = try lookupSortId(parser, arg.sort_name),
            .bound = arg.bound,
        };
    }
    return result;
}

fn lookupSortId(parser: *const MM0Parser, sort_name: []const u8) !u7 {
    const sort_id = parser.sort_names.get(sort_name) orelse return error.UnknownSort;
    return @intCast(sort_id);
}

fn buildDefProofBody(
    allocator: std.mem.Allocator,
    stmt: TermStmt,
) ![]const u8 {
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(stmt);
    const body = stmt.body orelse return error.ExpectedDefinitionBody;
    const expr_id = try theorem.internParsedExpr(body);

    var emitter = ExprProofEmitter.init(allocator, &theorem);
    defer emitter.deinit();
    try emitter.emitExpr(expr_id);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

fn buildAxiomProofBody(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    concl: ExprId,
) ![]const u8 {
    var emitter = ExprProofEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.emitExpr(concl);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

fn buildTermUnifyStream(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    body: ExprId,
) ![]const u8 {
    var emitter = UnifyEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.emitExpr(body);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

fn buildAssertionUnifyStream(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    concl: ExprId,
) ![]const u8 {
    var emitter = UnifyEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.emitExpr(concl);
    // `UHyp` pushes the next hypothesis target onto the unify stack before
    // replay continues. To make hypotheses replay in source order, the stream
    // therefore stores them in reverse.
    var hyp_idx = theorem.theorem_hyps.items.len;
    while (hyp_idx > 0) {
        hyp_idx -= 1;
        try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.UHyp, 0);
        try emitter.emitExpr(theorem.theorem_hyps.items[hyp_idx]);
    }
    try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

fn buildRuleUnifyStream(
    allocator: std.mem.Allocator,
    rule: *const RuleDecl,
) ![]const u8 {
    // For inference we rebuild the cited rule's unify stream from the same
    // binder-indexed templates that drive explicit instantiation. This keeps
    // one source of truth for theorem shape instead of maintaining a second,
    // compiler-only matcher by hand.
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(rule.args.len);

    var emitter = UnifyEmitter.init(allocator, &theorem);
    defer emitter.deinit();

    const binders = theorem.theorem_vars.items;
    const concl = try theorem.instantiateTemplate(rule.concl, binders);
    try emitter.emitExpr(concl);

    var hyp_idx = rule.hyps.len;
    while (hyp_idx > 0) {
        hyp_idx -= 1;
        try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.UHyp, 0);
        const hyp = try theorem.instantiateTemplate(rule.hyps[hyp_idx], binders);
        try emitter.emitExpr(hyp);
    }

    try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

fn buildTheoremProofBody(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    lines: []const CheckedLine,
) ![]const u8 {
    var emitter = try TheoremProofEmitter.init(allocator, theorem, lines);
    defer emitter.deinit();
    try emitter.emitHyps();
    try emitter.emitLine(lines.len - 1);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

const ExprProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    bytes: std.ArrayListUnmanaged(u8) = .{},
    expr_slots: ExprSlotMap = .empty,
    heap_len: u32,

    fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
    ) ExprProofEmitter {
        var emitter = ExprProofEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .heap_len = @intCast(theorem.theorem_vars.items.len),
        };
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            emitter.expr_slots.put(allocator, expr_id, @intCast(idx)) catch unreachable;
        }
        return emitter;
    }

    fn deinit(self: *ExprProofEmitter) void {
        self.bytes.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
    }

    fn emitExpr(self: *ExprProofEmitter, expr_id: ExprId) !void {
        if (self.expr_slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Ref, slot);
            return;
        }

        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => return error.UnboundExprVariable,
            .app => |app| {
                for (app.args) |arg| {
                    try self.emitExpr(arg);
                }
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.TermSave,
                    app.term_id,
                );
                const slot = self.heap_len;
                self.heap_len = try std.math.add(u32, self.heap_len, 1);
                try self.expr_slots.put(self.allocator, expr_id, slot);
            },
        }
    }
};

const UnifyEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    bytes: std.ArrayListUnmanaged(u8) = .{},
    slots: ExprSlotMap = .empty,
    heap_len: u32,

    fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
    ) UnifyEmitter {
        var emitter = UnifyEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .heap_len = @intCast(theorem.theorem_vars.items.len),
        };
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            emitter.slots.put(allocator, expr_id, @intCast(idx)) catch unreachable;
        }
        return emitter;
    }

    fn deinit(self: *UnifyEmitter) void {
        self.bytes.deinit(self.allocator);
        self.slots.deinit(self.allocator);
    }

    fn emitExpr(self: *UnifyEmitter, expr_id: ExprId) !void {
        if (self.slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, UnifyCmd.URef, slot);
            return;
        }

        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => return error.UnboundExprVariable,
            .app => |app| {
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    UnifyCmd.UTermSave,
                    app.term_id,
                );
                const slot = self.heap_len;
                self.heap_len = try std.math.add(u32, self.heap_len, 1);
                try self.slots.put(self.allocator, expr_id, slot);
                for (app.args) |arg| {
                    try self.emitExpr(arg);
                }
            },
        }
    }
};

const InferenceContext = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    // Heap prefix `0..rule.args.len` stores inferred theorem arguments.
    // These slots start as either an explicit binding or `null` if omitted.
    // Any entries appended later by `UTermSave` are concrete by construction.
    uheap: std.ArrayListUnmanaged(?ExprId) = .{},
    ustack: std.ArrayListUnmanaged(ExprId) = .{},
    hyps: []const ExprId,
    next_hyp: usize,

    fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        partial_bindings: []const ?ExprId,
        hyps: []const ExprId,
        line_expr: ExprId,
    ) !InferenceContext {
        var ctx = InferenceContext{
            .allocator = allocator,
            .theorem = theorem,
            .hyps = hyps,
            .next_hyp = hyps.len,
        };
        try ctx.uheap.appendSlice(allocator, partial_bindings);
        try ctx.ustack.append(allocator, line_expr);
        return ctx;
    }

    fn deinit(self: *InferenceContext) void {
        self.uheap.deinit(self.allocator);
        self.ustack.deinit(self.allocator);
    }

    pub fn uopRef(self: *InferenceContext, heap_id: u32) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        if (heap_id >= self.uheap.items.len) return error.UHeapOutOfBounds;
        if (self.uheap.items[heap_id]) |expected| {
            if (expr_id != expected) return error.UnifyMismatch;
        } else {
            // This is the one semantic difference from verifier-style unify:
            // the first encounter with an omitted binder solves it.
            self.uheap.items[heap_id] = expr_id;
        }
    }

    pub fn uopTerm(
        self: *InferenceContext,
        term_id: u32,
        save: bool,
    ) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |app| app,
            .variable => return error.ExpectedTermApp,
        };
        if (app.term_id != term_id) return error.TermMismatch;
        if (save) try self.uheap.append(self.allocator, expr_id);
        var i = app.args.len;
        while (i > 0) {
            i -= 1;
            try self.ustack.append(self.allocator, app.args[i]);
        }
    }

    pub fn uopDummy(self: *InferenceContext, _: u32) !void {
        _ = self;
        return error.UDummyNotAllowed;
    }

    pub fn uopHyp(self: *InferenceContext) !void {
        if (self.next_hyp == 0) return error.HypCountMismatch;
        // See `buildRuleUnifyStream`: hypotheses are replayed from the end so
        // that they are matched in source order overall.
        self.next_hyp -= 1;
        try self.ustack.append(self.allocator, self.hyps[self.next_hyp]);
    }
};

const TheoremProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    lines: []const CheckedLine,
    bytes: std.ArrayListUnmanaged(u8) = .{},
    expr_slots: ExprSlotMap = .empty,
    heap_len: u32,
    hyp_slots: []u32,
    line_slots: []u32,
    emitted: []bool,

    fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        lines: []const CheckedLine,
    ) !TheoremProofEmitter {
        var emitter = TheoremProofEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .lines = lines,
            .heap_len = @intCast(theorem.theorem_vars.items.len),
            .hyp_slots = try allocator.alloc(u32, theorem.theorem_hyps.items.len),
            .line_slots = try allocator.alloc(u32, lines.len),
            .emitted = try allocator.alloc(bool, lines.len),
        };
        @memset(emitter.emitted, false);
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            try emitter.expr_slots.put(allocator, expr_id, @intCast(idx));
        }
        return emitter;
    }

    fn deinit(self: *TheoremProofEmitter) void {
        self.bytes.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
        self.allocator.free(self.hyp_slots);
        self.allocator.free(self.line_slots);
        self.allocator.free(self.emitted);
    }

    fn emitHyps(self: *TheoremProofEmitter) !void {
        for (self.theorem.theorem_hyps.items, 0..) |hyp, idx| {
            try self.emitExpr(hyp);
            try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Hyp, 0);
            self.hyp_slots[idx] = self.heap_len;
            self.heap_len = try std.math.add(u32, self.heap_len, 1);
        }
    }

    fn emitLine(self: *TheoremProofEmitter, line_idx: usize) !void {
        if (self.emitted[line_idx]) {
            try MmbWriter.appendCmd(
                &self.bytes,
                self.allocator,
                ProofCmd.Ref,
                self.line_slots[line_idx],
            );
            return;
        }

        const line = self.lines[line_idx];
        for (line.refs) |ref| {
            switch (ref) {
                .hyp => |idx| try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Ref,
                    self.hyp_slots[idx],
                ),
                .line => |idx| try self.emitLine(idx),
            }
        }

        for (line.bindings) |binding| {
            try self.emitExpr(binding);
        }
        try self.emitExpr(line.expr);
        try MmbWriter.appendCmd(
            &self.bytes,
            self.allocator,
            ProofCmd.ThmSave,
            line.rule_id,
        );
        self.line_slots[line_idx] = self.heap_len;
        self.heap_len = try std.math.add(u32, self.heap_len, 1);
        self.emitted[line_idx] = true;
    }

    fn emitExpr(self: *TheoremProofEmitter, expr_id: ExprId) !void {
        if (self.expr_slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Ref, slot);
            return;
        }

        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => return error.UnboundExprVariable,
            .app => |app| {
                for (app.args) |arg| {
                    try self.emitExpr(arg);
                }
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.TermSave,
                    app.term_id,
                );
                const slot = self.heap_len;
                self.heap_len = try std.math.add(u32, self.heap_len, 1);
                try self.expr_slots.put(self.allocator, expr_id, slot);
            },
        }
    }
};

fn checkTheoremBlock(
    self: *Compiler,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    views: *const std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    block: TheoremBlock,
    theorem: *TheoremContext,
    theorem_concl: ExprId,
) ![]const CheckedLine {
    var theorem_vars = try buildTheoremVarMap(allocator, assertion);
    defer theorem_vars.deinit();

    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();

    var checked = std.ArrayListUnmanaged(CheckedLine){};
    var last_line: ?ExprId = null;
    var last_label: ?[]const u8 = null;
    var last_span: ?Span = null;

    for (block.lines) |line| {
        const line_expr = parseLineAssertion(
            parser,
            theorem,
            &theorem_vars,
            line,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .parse_assertion,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .span = line.assertion.span,
            });
            return err;
        };
        const rule_id = env.getRuleId(line.rule_name) orelse {
            self.setDiagnostic(.{
                .kind = .unknown_rule,
                .err = error.UnknownRule,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return error.UnknownRule;
        };
        const rule = &env.rules.items[rule_id];
        if (line.refs.len != rule.hyps.len) {
            self.setDiagnostic(.{
                .kind = .ref_count_mismatch,
                .err = error.RefCountMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return error.RefCountMismatch;
        }

        const refs = try allocator.alloc(CheckedRef, line.refs.len);
        const ref_exprs = try allocator.alloc(ExprId, line.refs.len);
        for (line.refs, 0..) |ref, idx| {
            ref_exprs[idx] = switch (ref) {
                .hyp => |hyp| blk: {
                    if (hyp.index == 0 or
                        hyp.index > theorem.theorem_hyps.items.len)
                    {
                        const hyp_name = try hypText(allocator, hyp.index);
                        self.setDiagnostic(.{
                            .kind = .unknown_hypothesis_ref,
                            .err = error.UnknownHypothesisRef,
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .name = hyp_name,
                            .span = hyp.span,
                        });
                        return error.UnknownHypothesisRef;
                    }
                    refs[idx] = .{ .hyp = hyp.index - 1 };
                    break :blk theorem.theorem_hyps.items[hyp.index - 1];
                },
                .line => |label| blk: {
                    const line_idx = labels.get(label.label) orelse {
                        self.setDiagnostic(.{
                            .kind = .unknown_label,
                            .err = error.UnknownLabel,
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .name = label.label,
                            .span = label.span,
                        });
                        return error.UnknownLabel;
                    };
                    refs[idx] = .{ .line = line_idx };
                    break :blk checked.items[line_idx].expr;
                },
            };
        }

        const partial_bindings = try parseBindings(
            self,
            allocator,
            parser,
            theorem,
            &theorem_vars,
            assertion.name,
            rule,
            line,
        );
        const maybe_view = views.get(rule_id);
        const had_omitted = hasOmittedBindings(partial_bindings);
        const use_advanced_inference = had_omitted and
            shouldUseAdvancedInference(rule_id, maybe_view, registry);

        if (maybe_view) |view| {
            if (!use_advanced_inference) {
                CompilerViews.applyViewBindings(
                    allocator,
                    theorem,
                    &view,
                    line_expr,
                    ref_exprs,
                    partial_bindings,
                ) catch |err| {
                    self.setDiagnostic(.{
                        .kind = .generic,
                        .err = err,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .rule_name = line.rule_name,
                        .span = line.span,
                    });
                    return err;
                };
            }
        }

        const bindings = if (had_omitted)
            try inferBindings(
                self,
                allocator,
                env,
                registry,
                theorem,
                assertion,
                rule,
                line,
                partial_bindings,
                ref_exprs,
                line_expr,
                maybe_view,
                use_advanced_inference,
            )
        else
            try requireConcreteBindings(
                allocator,
                partial_bindings,
            );
        if (!had_omitted) {
            try validateResolvedBindings(
                self,
                env,
                theorem,
                assertion,
                line,
                rule,
                bindings,
            );
        }

        const norm_spec = registry.getNormalizeSpec(rule_id);

        // Check hypotheses (with optional normalization)
        for (ref_exprs, line.refs, 0..) |actual, ref, idx| {
            const expected = try theorem.instantiateTemplate(
                rule.hyps[idx],
                bindings,
            );
            if (actual != expected) {
                if (norm_spec) |spec| {
                    if (isHypMarkedForNormalize(spec, idx)) {
                        if (try buildNormalizedConversion(
                            allocator,
                            theorem,
                            registry,
                            env,
                            &checked,
                            actual,
                            expected,
                        )) |conversion| {
                            var conversion_mut = conversion;
                            const actual_ref = refs[idx];
                            if (conversion_mut.conv_line_idx) |conv_line_idx| {
                                const transport_idx = try conversion_mut.normalizer.emitTransport(
                                    conversion_mut.relation,
                                    expected,
                                    actual,
                                    conv_line_idx,
                                    actual_ref,
                                );
                                refs[idx] = .{ .line = transport_idx };
                            }
                            continue;
                        }
                        return error.HypothesisMismatch;
                    }
                }
                const name = switch (ref) {
                    .hyp => |hyp| try hypText(allocator, hyp.index),
                    .line => |label| label.label,
                };
                const span = switch (ref) {
                    .hyp => |hyp| hyp.span,
                    .line => |label| label.span,
                };
                self.setDiagnostic(.{
                    .kind = .hypothesis_mismatch,
                    .err = error.HypothesisMismatch,
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = line.rule_name,
                    .name = name,
                    .span = span,
                });
                return error.HypothesisMismatch;
            }
        }

        const expected_line = try theorem.instantiateTemplate(
            rule.concl,
            bindings,
        );

        if (line_expr != expected_line) {
            if (norm_spec) |spec| {
                if (spec.concl) {
                    if (try buildNormalizedConversion(
                        allocator,
                        theorem,
                        registry,
                        env,
                        &checked,
                        expected_line,
                        line_expr,
                    )) |conversion| {
                        var conversion_mut = conversion;
                        const raw_idx = checked.items.len;
                        try checked.append(allocator, .{
                            .expr = expected_line,
                            .rule_id = rule_id,
                            .bindings = bindings,
                            .refs = refs,
                        });

                        const line_idx = if (conversion_mut.conv_line_idx) |conv_idx|
                            try conversion_mut.normalizer.emitTransport(
                                conversion_mut.relation,
                                line_expr,
                                expected_line,
                                conv_idx,
                                .{ .line = raw_idx },
                            )
                        else
                            raw_idx;

                        const gop = try labels.getOrPut(line.label);
                        if (gop.found_existing) {
                            self.setDiagnostic(.{
                                .kind = .duplicate_label,
                                .err = error.DuplicateLabel,
                                .theorem_name = assertion.name,
                                .line_label = line.label,
                                .name = line.label,
                                .span = line.span,
                            });
                            return error.DuplicateLabel;
                        }
                        gop.value_ptr.* = line_idx;
                        last_line = line_expr;
                        last_label = line.label;
                        last_span = line.assertion.span;
                        continue;
                    }
                }
            }

            self.setDiagnostic(.{
                .kind = .conclusion_mismatch,
                .err = error.ConclusionMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.assertion.span,
            });
            return error.ConclusionMismatch;
        }

        const gop = try labels.getOrPut(line.label);
        if (gop.found_existing) {
            self.setDiagnostic(.{
                .kind = .duplicate_label,
                .err = error.DuplicateLabel,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .name = line.label,
                .span = line.span,
            });
            return error.DuplicateLabel;
        }
        gop.value_ptr.* = checked.items.len;
        try checked.append(allocator, .{
            .expr = line_expr,
            .rule_id = rule_id,
            .bindings = bindings,
            .refs = refs,
        });
        last_line = line_expr;
        last_label = line.label;
        last_span = line.assertion.span;
    }

    const final_line = last_line orelse {
        self.setDiagnostic(.{
            .kind = .empty_proof_block,
            .err = error.EmptyProofBlock,
            .theorem_name = assertion.name,
            .block_name = block.name,
            .span = block.name_span,
        });
        return error.EmptyProofBlock;
    };
    if (final_line != theorem_concl) {
        self.setDiagnostic(.{
            .kind = .final_line_mismatch,
            .err = error.FinalLineMismatch,
            .theorem_name = assertion.name,
            .line_label = last_label,
            .span = last_span,
        });
        return error.FinalLineMismatch;
    }
    return try checked.toOwnedSlice(allocator);
}

fn buildTheoremVarMap(
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
) !NameExprMap {
    var vars = NameExprMap.init(allocator);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try vars.put(actual_name, expr);
        }
    }
    return vars;
}

fn parseLineAssertion(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    line: ProofLine,
) !ExprId {
    const expr = try parser.parseFormulaText(line.assertion.text, theorem_vars);
    return try theorem.internParsedExpr(expr);
}

fn parseBindings(
    self: *Compiler,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ProofLine,
) ![]?ExprId {
    for (rule.arg_names) |arg_name| {
        if (arg_name == null) {
            self.setDiagnostic(.{
                .kind = .generic,
                .err = error.UnnamedRuleBinder,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return error.UnnamedRuleBinder;
        }
    }

    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    for (line.arg_bindings) |binding| {
        const arg_index = findRuleArgIndex(rule, binding.name) orelse {
            self.setDiagnostic(.{
                .kind = .unknown_binder_name,
                .err = error.UnknownBinderName,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = binding.name,
                .span = binding.span,
            });
            return error.UnknownBinderName;
        };
        if (bindings[arg_index] != null) {
            self.setDiagnostic(.{
                .kind = .duplicate_binder_assignment,
                .err = error.DuplicateBinderAssignment,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = binding.name,
                .span = binding.span,
            });
            return error.DuplicateBinderAssignment;
        }

        const expr = parser.parseArgText(
            binding.formula.text,
            theorem_vars,
            rule.args[arg_index],
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .parse_binding,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = binding.name,
                .span = binding.formula.span,
            });
            return err;
        };
        bindings[arg_index] = try theorem.internParsedExpr(expr);
    }

    return bindings;
}

fn hasOmittedBindings(bindings: []const ?ExprId) bool {
    for (bindings) |binding| {
        if (binding == null) return true;
    }
    return false;
}

fn requireConcreteBindings(
    allocator: std.mem.Allocator,
    partial_bindings: []const ?ExprId,
) ![]const ExprId {
    const bindings = try allocator.alloc(ExprId, partial_bindings.len);
    for (partial_bindings, 0..) |binding, idx| {
        bindings[idx] = binding orelse return error.MissingBinderAssignment;
    }
    return bindings;
}

fn shouldUseAdvancedInference(
    rule_id: u32,
    maybe_view: ?ViewDecl,
    registry: *RewriteRegistry,
) bool {
    if (maybe_view != null) return true;
    return registry.getNormalizeSpec(rule_id) != null;
}

fn inferBindings(
    self: *Compiler,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ProofLine,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    maybe_view: ?ViewDecl,
    use_advanced_inference: bool,
) ![]const ExprId {
    if (use_advanced_inference) {
        var solver = InferenceSolver.init(
            allocator,
            env,
            theorem,
            registry,
            rule,
            if (maybe_view) |*view| view else null,
        );
        const bindings = solver.solve(
            partial_bindings,
            ref_exprs,
            line_expr,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .inference_failed,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return err;
        };
        try validateResolvedBindings(
            self,
            env,
            theorem,
            assertion,
            line,
            rule,
            bindings,
        );
        return bindings;
    }

    const unify = buildRuleUnifyStream(allocator, rule) catch |err| {
        self.setDiagnostic(.{
            .kind = .inference_failed,
            .err = err,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.span,
        });
        return err;
    };

    var inference = try InferenceContext.init(
        allocator,
        theorem,
        partial_bindings,
        ref_exprs,
        line_expr,
    );
    defer inference.deinit();

    UnifyReplay.run(unify, 0, &inference) catch |err| {
        self.setDiagnostic(.{
            .kind = .inference_failed,
            .err = err,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.span,
        });
        return err;
    };
    if (inference.ustack.items.len != 0) {
        self.setDiagnostic(.{
            .kind = .inference_failed,
            .err = error.UnifyStackNotEmpty,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.span,
        });
        return error.UnifyStackNotEmpty;
    }
    if (inference.next_hyp != 0) {
        self.setDiagnostic(.{
            .kind = .inference_failed,
            .err = error.HypCountMismatch,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.span,
        });
        return error.HypCountMismatch;
    }

    const bindings = try allocator.alloc(ExprId, rule.args.len);
    for (0..rule.args.len) |idx| {
        const binding = inference.uheap.items[idx] orelse {
            self.setDiagnostic(.{
                .kind = .missing_binder_assignment,
                .err = error.MissingBinderAssignment,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx].?,
                .span = line.span,
            });
            return error.MissingBinderAssignment;
        };
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .inference_failed,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx].?,
                .span = line.span,
            });
            return err;
        };
        bindings[idx] = binding;
    }
    return bindings;
}

fn validateResolvedBindings(
    self: *Compiler,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: ProofLine,
    rule: *const RuleDecl,
    bindings: []const ExprId,
) !void {
    for (bindings, 0..) |binding, idx| {
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx],
                .span = line.span,
            });
            return err;
        };
    }
}

// Inference only solves equalities. We still need the same sort, boundness,
// and dependency checks that explicit parser-side argument parsing performs.
fn validateBindingExpr(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expected: ArgInfo,
    expr_id: ExprId,
) !void {
    const info = try exprInfo(env, theorem, theorem_args, expr_id);
    if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
        return error.SortMismatch;
    }
    // Match verifier semantics: bound params require bound exprs,
    // but regular params accept any expression (including bound vars).
    if (expected.bound and !info.bound) return error.BoundnessMismatch;
    // Note: dep checking is deferred to the verifier which checks deps
    // relative to the theorem's own bound variables.
}

fn exprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expr_id: ExprId,
) !ExprInfo {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= theorem_args.len) return error.UnknownTheoremVariable;
                const arg = theorem_args[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                    .deps = arg.deps,
                };
            },
            .dummy_var => return error.UnexpectedDummyVar,
        },
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            var deps: u55 = 0;
            for (app.args) |arg_id| {
                deps |= (try exprInfo(env, theorem, theorem_args, arg_id)).deps;
            }
            break :blk .{
                .sort_name = env.terms.items[app.term_id].ret_sort_name,
                .bound = false,
                .deps = deps,
            };
        },
    };
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}

fn buildHypNames(
    allocator: std.mem.Allocator,
    count: usize,
) ![]const ?[]const u8 {
    const names = try allocator.alloc(?[]const u8, count);
    for (0..count) |idx| {
        names[idx] = try hypText(allocator, idx + 1);
    }
    return names;
}

fn hypText(
    allocator: std.mem.Allocator,
    index: usize,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "#{d}", .{index});
}

const NormalizedConversion = struct {
    relation: @import("./rewrite_registry.zig").ResolvedRelation,
    conv_line_idx: ?usize,
    normalizer: Normalizer,
};

fn buildNormalizedConversion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    actual: ExprId,
    expected: ExprId,
) !?NormalizedConversion {
    var normalizer = Normalizer.init(
        allocator,
        theorem,
        registry,
        env,
        checked,
    );
    const relation = normalizer.resolveRelationForExpr(actual) orelse return null;
    const norm_actual = try normalizer.normalize(actual);
    const norm_expected = try normalizer.normalize(expected);
    if (norm_actual.result_expr != norm_expected.result_expr) return null;

    const conv_line_idx = if (norm_actual.conv_line_idx) |actual_idx|
        if (norm_expected.conv_line_idx) |expected_idx|
            try normalizer.composeTransitivity(
                relation,
                actual,
                norm_actual.result_expr,
                expected,
                actual_idx,
                try normalizer.emitSymm(
                    relation,
                    expected,
                    norm_expected.result_expr,
                    expected_idx,
                ),
            )
        else
            actual_idx
    else if (norm_expected.conv_line_idx) |expected_idx|
        try normalizer.emitSymm(
            relation,
            expected,
            norm_expected.result_expr,
            expected_idx,
        )
    else
        null;

    return .{
        .relation = relation,
        .conv_line_idx = conv_line_idx,
        .normalizer = normalizer,
    };
}

fn isHypMarkedForNormalize(
    spec: @import("./rewrite_registry.zig").NormalizeSpec,
    hyp_idx: usize,
) bool {
    for (spec.hyp_indices) |marked| {
        if (marked == hyp_idx) return true;
    }
    return false;
}

fn getRuleConcSort(env: *const GlobalEnv, rule: *const RuleDecl) ?[]const u8 {
    return getTemplateSort(env, rule.concl);
}

fn getTemplateSort(env: *const GlobalEnv, template: TemplateExpr) ?[]const u8 {
    switch (template) {
        .app => |app| {
            if (app.term_id < env.terms.items.len) {
                return env.terms.items[app.term_id].ret_sort_name;
            }
            return null;
        },
        .binder => return null,
    }
}
