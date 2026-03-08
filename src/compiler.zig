const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const Expr = @import("./expressions.zig").Expr;
const MmbWriter = @import("./mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const ArgInfo = @import("./parse.zig").ArgInfo;
const AssertionStmt = @import("./parse.zig").AssertionStmt;
const MM0Parser = @import("./parse.zig").MM0Parser;
const TermStmt = @import("./parse.zig").TermStmt;
const ProofCmd = @import("./proof.zig").ProofCmd;
const StmtCmd = @import("./proof.zig").StmtCmd;
const UnifyCmd = @import("./proof.zig").UnifyCmd;
const ProofLine = @import("./proof_script.zig").ProofLine;
const Span = @import("./proof_script.zig").Span;
const TheoremBlock = @import("./proof_script.zig").TheoremBlock;
const ProofScriptParser = @import("./proof_script.zig").Parser;
const Arg = @import("./args.zig").Arg;

const NameExprMap = std.StringHashMap(*const Expr);
const LabelIndexMap = std.StringHashMap(usize);
const ExprSlotMap = std.AutoHashMapUnmanaged(ExprId, u32);

const CheckedRef = union(enum) {
    hyp: usize,
    line: usize,
};

const CheckedLine = struct {
    expr: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
};

const DiagnosticKind = enum {
    generic,
    missing_proof_block,
    extra_proof_block,
    theorem_name_mismatch,
    parse_assertion,
    parse_binding,
    unknown_rule,
    unknown_binder_name,
    duplicate_binder_assignment,
    missing_binder_assignment,
    ref_count_mismatch,
    unknown_hypothesis_ref,
    unknown_label,
    hypothesis_mismatch,
    conclusion_mismatch,
    duplicate_label,
    empty_proof_block,
    final_line_mismatch,
};

pub const Diagnostic = struct {
    kind: DiagnosticKind,
    err: anyerror,
    theorem_name: ?[]const u8 = null,
    block_name: ?[]const u8 = null,
    line_label: ?[]const u8 = null,
    rule_name: ?[]const u8 = null,
    name: ?[]const u8 = null,
    expected_name: ?[]const u8 = null,
    span: ?Span = null,
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
        var proof_parser = if (self.proof_source) |proof|
            ProofScriptParser.init(arena.allocator(), proof)
        else
            null;

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .assertion => |assertion| {
                    if (assertion.kind != .theorem) {
                        try env.addStmt(stmt);
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
                            assertion,
                            block,
                            &theorem,
                            theorem_concl,
                        );
                    }

                    try env.addStmt(stmt);
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

        var sort_names = std.ArrayListUnmanaged([]const u8){};
        var sorts = std.ArrayListUnmanaged(@import("./sorts.zig").Sort){};
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

fn diagnosticSummary(diag: Diagnostic) []const u8 {
    return switch (diag.kind) {
        .generic => @errorName(diag.err),
        .missing_proof_block => "missing proof block for theorem",
        .extra_proof_block => "extra proof block with no matching theorem",
        .theorem_name_mismatch => "proof block name does not match the theorem",
        .parse_assertion => "could not parse proof line assertion",
        .parse_binding => "could not parse binder assignment",
        .unknown_rule => "unknown rule in proof line",
        .unknown_binder_name => "unknown binder name in rule application",
        .duplicate_binder_assignment => "duplicate binder assignment in rule application",
        .missing_binder_assignment => "missing binder assignment in rule application",
        .ref_count_mismatch => "wrong number of references for rule application",
        .unknown_hypothesis_ref => "unknown theorem hypothesis reference",
        .unknown_label => "unknown proof line label",
        .hypothesis_mismatch => "rule reference does not match the expected hypothesis",
        .conclusion_mismatch => "proof line assertion does not match the rule conclusion",
        .duplicate_label => "duplicate proof line label",
        .empty_proof_block => "proof block is empty",
        .final_line_mismatch => "last proof line does not prove the theorem conclusion",
    };
}

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
    for (theorem.theorem_hyps.items) |hyp| {
        try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.UHyp, 0);
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
        var ref_idx = line.refs.len;
        while (ref_idx > 0) {
            ref_idx -= 1;
            switch (line.refs[ref_idx]) {
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
        const bindings = try parseBindings(
            self,
            allocator,
            parser,
            theorem,
            &theorem_vars,
            assertion.name,
            rule,
            line,
        );
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
        for (line.refs, 0..) |ref, idx| {
            const actual = switch (ref) {
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
            const expected = try theorem.instantiateTemplate(
                rule.hyps[idx],
                bindings,
            );
            if (actual != expected) {
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
) ![]const ExprId {
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

    const bindings = try allocator.alloc(ExprId, rule.args.len);
    const seen = try allocator.alloc(bool, rule.args.len);
    defer allocator.free(seen);
    @memset(seen, false);

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
        if (seen[arg_index]) {
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
        seen[arg_index] = true;
    }

    for (seen, 0..) |was_seen, idx| {
        if (!was_seen) {
            self.setDiagnostic(.{
                .kind = .missing_binder_assignment,
                .err = error.MissingBinderAssignment,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx].?,
                .span = line.span,
            });
            return error.MissingBinderAssignment;
        }
    }
    return bindings;
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
