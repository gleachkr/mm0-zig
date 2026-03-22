const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const MmbWriter = @import("./mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const DefOps = @import("./def_ops.zig");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const TermStmt = @import("../trusted/parse.zig").TermStmt;
const ProofCmd = @import("../trusted/proof.zig").ProofCmd;
const UnifyCmd = @import("../trusted/proof.zig").UnifyCmd;
const Arg = @import("../trusted/args.zig").Arg;
const CheckedLine = @import("./compiler.zig").CheckedLine;
const CheckedRef = @import("./compiler.zig").CheckedRef;

const ExprSlotMap = std.AutoHashMapUnmanaged(ExprId, u32);

pub const ExprProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    bytes: std.ArrayListUnmanaged(u8) = .{},
    expr_slots: ExprSlotMap = .empty,
    heap_len: u32,

    pub fn init(
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

    pub fn deinit(self: *ExprProofEmitter) void {
        self.bytes.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
    }

    pub fn emitExpr(self: *ExprProofEmitter, expr_id: ExprId) !void {
        if (self.expr_slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Ref, slot);
            return;
        }

        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => return error.UnboundExprVariable,
                .dummy_var => |dummy_id| {
                    if (dummy_id >= self.theorem.theorem_dummies.items.len) {
                        return error.UnknownDummyVar;
                    }
                    const info = self.theorem.theorem_dummies.items[dummy_id];
                    try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Dummy, info.sort_id);
                    const slot = self.heap_len;
                    self.heap_len = try std.math.add(u32, self.heap_len, 1);
                    try self.expr_slots.put(self.allocator, expr_id, slot);
                },
            },
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

pub const UnifyEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    bytes: std.ArrayListUnmanaged(u8) = .{},
    slots: ExprSlotMap = .empty,
    heap_len: u32,

    pub fn init(
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

    pub fn deinit(self: *UnifyEmitter) void {
        self.bytes.deinit(self.allocator);
        self.slots.deinit(self.allocator);
    }

    pub fn emitExpr(self: *UnifyEmitter, expr_id: ExprId) !void {
        if (self.slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, UnifyCmd.URef, slot);
            return;
        }

        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => return error.UnboundExprVariable,
                .dummy_var => |dummy_id| {
                    if (dummy_id >= self.theorem.theorem_dummies.items.len) {
                        return error.UnknownDummyVar;
                    }
                    const info = self.theorem.theorem_dummies.items[dummy_id];
                    try MmbWriter.appendCmd(&self.bytes, self.allocator, UnifyCmd.UDummy, info.sort_id);
                    const slot = self.heap_len;
                    self.heap_len = try std.math.add(u32, self.heap_len, 1);
                    try self.slots.put(self.allocator, expr_id, slot);
                },
            },
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

pub const TheoremProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    lines: []const CheckedLine,
    bytes: std.ArrayListUnmanaged(u8) = .{},
    expr_slots: ExprSlotMap = .empty,
    heap_len: u32,
    hyp_slots: []u32,
    line_slots: []u32,
    emitted: []bool,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        env: *const GlobalEnv,
        lines: []const CheckedLine,
    ) !TheoremProofEmitter {
        var emitter = TheoremProofEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
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

    pub fn deinit(self: *TheoremProofEmitter) void {
        self.bytes.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
        self.allocator.free(self.hyp_slots);
        self.allocator.free(self.line_slots);
        self.allocator.free(self.emitted);
    }

    pub fn emitHyps(self: *TheoremProofEmitter) !void {
        for (self.theorem.theorem_hyps.items, 0..) |hyp, idx| {
            try self.emitExpr(hyp);
            try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Hyp, 0);
            self.hyp_slots[idx] = self.heap_len;
            self.heap_len = try std.math.add(u32, self.heap_len, 1);
        }
    }

    pub fn emitLine(
        self: *TheoremProofEmitter,
        line_idx: usize,
    ) anyerror!void {
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
        switch (line.data) {
            .rule => |rule| {
                for (rule.refs) |ref| {
                    try self.emitRef(ref);
                }
                for (rule.bindings) |binding| {
                    try self.emitExpr(binding);
                }
                try self.emitExpr(line.expr);
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.ThmSave,
                    rule.rule_id,
                );
            },
            .transport => |transport| {
                try self.emitExpr(line.expr);
                try self.emitRef(transport.source);
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Conv,
                    0,
                );
                try self.emitConversion(line.expr, transport.source_expr);
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Save,
                    0,
                );
            },
        }
        self.line_slots[line_idx] = self.heap_len;
        self.heap_len = try std.math.add(u32, self.heap_len, 1);
        self.emitted[line_idx] = true;
    }

    fn emitRef(
        self: *TheoremProofEmitter,
        ref: CheckedRef,
    ) anyerror!void {
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

    fn emitConversion(
        self: *TheoremProofEmitter,
        target_expr: ExprId,
        source_expr: ExprId,
    ) !void {
        var def_ops = DefOps.Context.init(
            self.allocator,
            @constCast(self.theorem),
            self.env,
            .all_defs,
        );
        defer def_ops.deinit();
        const plan = try def_ops.planConversionByDefOpening(
            target_expr,
            source_expr,
        ) orelse return error.MissingConversionPlan;
        try self.emitConversionPlan(plan);
    }

    fn emitConversionPlan(
        self: *TheoremProofEmitter,
        plan: *const DefOps.ConversionPlan,
    ) !void {
        switch (plan.*) {
            .refl => try MmbWriter.appendCmd(
                &self.bytes,
                self.allocator,
                ProofCmd.Refl,
                0,
            ),
            .unfold_lhs => |step| {
                try self.emitExpr(step.witness);
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Unfold,
                    0,
                );
                try self.emitConversionPlan(step.next);
            },
            .unfold_rhs => |step| {
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Symm,
                    0,
                );
                try self.emitExpr(step.witness);
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Unfold,
                    0,
                );
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Symm,
                    0,
                );
                try self.emitConversionPlan(step.next);
            },
            .cong => |step| {
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    ProofCmd.Cong,
                    0,
                );
                for (step.children) |child| {
                    try self.emitConversionPlan(child);
                }
            },
        }
    }

    pub fn emitExpr(self: *TheoremProofEmitter, expr_id: ExprId) !void {
        if (self.expr_slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, ProofCmd.Ref, slot);
            return;
        }

        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => return error.UnboundExprVariable,
                .dummy_var => |dummy_id| {
                    if (dummy_id >= self.theorem.theorem_dummies.items.len) {
                        return error.UnknownDummyVar;
                    }
                    const info = self.theorem.theorem_dummies.items[dummy_id];
                    try MmbWriter.appendCmd(
                        &self.bytes,
                        self.allocator,
                        ProofCmd.Dummy,
                        info.sort_id,
                    );
                    const slot = self.heap_len;
                    self.heap_len = try std.math.add(u32, self.heap_len, 1);
                    try self.expr_slots.put(self.allocator, expr_id, slot);
                },
            },
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

pub fn compileTermRecord(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    stmt: TermStmt,
) !TermRecord {
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(parser, stmt);

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

pub fn buildArgArray(
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

pub fn lookupSortId(parser: *const MM0Parser, sort_name: []const u8) !u7 {
    const sort_id = parser.sort_names.get(sort_name) orelse return error.UnknownSort;
    return @intCast(sort_id);
}

pub fn buildDefProofBody(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    stmt: TermStmt,
) ![]const u8 {
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(parser, stmt);
    const body = stmt.body orelse return error.ExpectedDefinitionBody;
    const expr_id = try theorem.internParsedExpr(body);

    var emitter = ExprProofEmitter.init(allocator, &theorem);
    defer emitter.deinit();
    try emitter.emitExpr(expr_id);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

pub fn buildAxiomProofBody(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    concl: ExprId,
) ![]const u8 {
    var emitter = ExprProofEmitter.init(allocator, theorem);
    defer emitter.deinit();
    for (theorem.theorem_hyps.items) |hyp| {
        try emitter.emitExpr(hyp);
        try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.Hyp, 0);
        emitter.heap_len = try std.math.add(u32, emitter.heap_len, 1);
    }
    try emitter.emitExpr(concl);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

pub fn buildTermUnifyStream(
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

pub fn buildAssertionUnifyStream(
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

pub fn buildRuleUnifyStream(
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

pub fn buildTheoremProofBody(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    lines: []const CheckedLine,
) ![]const u8 {
    var emitter = try TheoremProofEmitter.init(allocator, theorem, env, lines);
    defer emitter.deinit();
    try emitter.emitHyps();
    try emitter.emitLine(lines.len - 1);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, ProofCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

pub fn buildHypNames(
    allocator: std.mem.Allocator,
    count: usize,
) ![]const ?[]const u8 {
    const names = try allocator.alloc(?[]const u8, count);
    for (0..count) |idx| {
        names[idx] = try hypText(allocator, idx + 1);
    }
    return names;
}

pub fn buildTheoremVarNames(
    allocator: std.mem.Allocator,
    arg_names: []const ?[]const u8,
    dummy_count: usize,
) ![]const ?[]const u8 {
    const names = try allocator.alloc(?[]const u8, arg_names.len + dummy_count);
    @memcpy(names[0..arg_names.len], arg_names);
    @memset(names[arg_names.len..], null);
    return names;
}

pub fn hypText(
    allocator: std.mem.Allocator,
    index: usize,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "#{d}", .{index});
}
