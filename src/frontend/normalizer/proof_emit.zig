const std = @import("std");
const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const DiagScratch = @import("../diag_scratch.zig");
const RewriteRule = @import("../rewrite_registry.zig").RewriteRule;
const MissingCongruenceReason = DiagScratch.MissingCongruenceReason;
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../rewrite_registry.zig").ResolvedStructuralCombiner;
const CheckedIr = @import("../compiler/checked_ir.zig");
const DebugTrace = @import("../debug.zig");
const ViewTrace = @import("../view_trace.zig");
const Support = @import("./support.zig");

const CheckedRef = CheckedIr.CheckedRef;
const appendRuleLine = CheckedIr.appendRuleLine;
const appendTransportLine = CheckedIr.appendTransportLine;

const Types = @import("./types.zig");
const NormalizeResult = Types.NormalizeResult;

pub fn emitTransparentRelationProof(
    self: anytype,
    relation: ResolvedRelation,
    source_expr: ExprId,
    target_expr: ExprId,
) anyerror!?usize {
    if (source_expr == target_expr) return null;
    const source_rel = try buildRelExpr(self, relation, source_expr, source_expr);
    const target_rel = try buildRelExpr(self, relation, source_expr, target_expr);
    const refl_idx = try emitRefl(self, relation, source_expr);
    return try appendTransportLine(
        self.lines,
        self.allocator,
        target_rel,
        source_rel,
        .{ .line = refl_idx },
    );
}

pub fn tryApplyRule(
    self: anytype,
    relation: ResolvedRelation,
    expr_id: ExprId,
    rule: RewriteRule,
) anyerror!?NormalizeResult {
    const bindings = try self.allocator.alloc(?ExprId, rule.num_binders);
    defer self.allocator.free(bindings);
    @memset(bindings, null);

    if (!self.theorem.matchTemplate(rule.lhs, expr_id, bindings)) {
        return null;
    }

    const concrete = try self.allocator.alloc(ExprId, rule.num_binders);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding orelse {
            self.allocator.free(concrete);
            return null;
        };
    }

    if (rule.rule_id >= self.env.rules.items.len) {
        self.allocator.free(concrete);
        return null;
    }
    const rule_decl = &self.env.rules.items[rule.rule_id];
    if (rule_decl.args.len != concrete.len) {
        self.allocator.free(concrete);
        return null;
    }
    validateRewriteBindings(
        self.env,
        self.theorem,
        rule_decl.args,
        concrete,
    ) catch {
        self.allocator.free(concrete);
        return null;
    };

    const rhs_expr = try self.theorem.instantiateTemplate(rule.rhs, concrete);
    const step_expr = try buildRelExpr(self, relation, expr_id, rhs_expr);

    const line_idx = try appendRuleLine(
        self.lines,
        self.allocator,
        step_expr,
        rule.rule_id,
        concrete,
        &.{},
    );
    traceExprPair(
        self,
        "applied rewrite",
        expr_id,
        rhs_expr,
    );

    return .{
        .result_expr = rhs_expr,
        .conv_line_idx = line_idx,
    };
}

fn setMissingCongruenceDetail(
    self: anytype,
    term_id: ?u32,
    reason: MissingCongruenceReason,
    sort_name: ?[]const u8,
    arg_index: ?usize,
) void {
    const scratch = self.diag_scratch orelse return;
    scratch.record(error.MissingCongruenceRule, .{
        .missing_congruence_rule = .{
            .reason = reason,
            .term_id = term_id,
            .sort_name = sort_name,
            .arg_index = arg_index,
        },
    });
}

fn failMissingCongruence(
    self: anytype,
    term_id: ?u32,
    reason: MissingCongruenceReason,
    sort_name: ?[]const u8,
    arg_index: ?usize,
) error{MissingCongruenceRule} {
    setMissingCongruenceDetail(self, term_id, reason, sort_name, arg_index);
    DebugTrace.traceNormalization(
        self.debug,
        "missing congruence detail recorded: reason={s}",
        .{@tagName(reason)},
    );
    return error.MissingCongruenceRule;
}

pub fn emitCongruenceLine(
    self: anytype,
    term_id: u32,
    old_args: []const ExprId,
    new_args: []const ExprId,
    child_proofs: []const ?usize,
) anyerror!?usize {
    var any_changed = false;
    for (old_args, new_args) |old_arg, new_arg| {
        any_changed = any_changed or old_arg != new_arg;
    }
    if (!any_changed) return null;

    const term_decl = if (term_id < self.env.terms.items.len)
        &self.env.terms.items[term_id]
    else
        return failMissingCongruence(
            self,
            null,
            .unknown_term,
            null,
            null,
        );
    const congr_rule = self.registry.getCongruenceRule(term_id) orelse {
        return failMissingCongruence(
            self,
            term_id,
            .missing_rule,
            term_decl.ret_sort_name,
            null,
        );
    };

    const bindings = try self.allocator.alloc(ExprId, congr_rule.num_binders);
    var binding_idx: usize = 0;
    var ref_count: usize = 0;
    for (term_decl.args) |arg| {
        if (!arg.bound) ref_count += 1;
    }

    const refs = try self.allocator.alloc(CheckedRef, ref_count);
    var ref_idx: usize = 0;
    for (old_args, new_args, term_decl.args, 0..) |
        old_arg,
        new_arg,
        arg_decl,
        idx,
    | {
        if (arg_decl.bound) {
            if (old_arg != new_arg) {
                return failMissingCongruence(
                    self,
                    term_id,
                    .changed_bound_arg,
                    arg_decl.sort_name,
                    idx,
                );
            }
            bindings[binding_idx] = old_arg;
            binding_idx += 1;
            continue;
        }

        bindings[binding_idx] = old_arg;
        bindings[binding_idx + 1] = new_arg;
        binding_idx += 2;

        if (child_proofs[idx]) |proof_idx| {
            refs[ref_idx] = .{ .line = proof_idx };
            ref_idx += 1;
            continue;
        }
        if (old_arg == new_arg) {
            const child_rel = self.registry.resolveRelation(
                self.env,
                arg_decl.sort_name,
            ) orelse return failMissingCongruence(
                self,
                term_id,
                .missing_child_relation,
                arg_decl.sort_name,
                idx,
            );
            refs[ref_idx] = .{ .line = try emitRefl(self, child_rel, old_arg) };
            ref_idx += 1;
            continue;
        }
        return failMissingCongruence(
            self,
            term_id,
            .missing_child_proof,
            arg_decl.sort_name,
            idx,
        );
    }

    if (binding_idx != bindings.len or ref_idx != refs.len) {
        return failMissingCongruence(
            self,
            term_id,
            .malformed_rule,
            term_decl.ret_sort_name,
            null,
        );
    }

    const old_expr = try self.theorem.interner.internApp(term_id, old_args);
    const new_expr = try self.theorem.interner.internApp(term_id, new_args);
    const parent_relation = Support.resolveRelationForExpr(self, old_expr) orelse {
        return failMissingCongruence(
            self,
            term_id,
            .missing_parent_relation,
            term_decl.ret_sort_name,
            null,
        );
    };
    const expr = try buildRelExpr(self, parent_relation, old_expr, new_expr);

    const line_idx = try appendRuleLine(
        self.lines,
        self.allocator,
        expr,
        congr_rule.rule_id,
        bindings,
        refs,
    );
    traceExprPair(self, "emitted congruence", old_expr, new_expr);
    return line_idx;
}

pub fn emitRefl(
    self: anytype,
    relation: ResolvedRelation,
    expr_id: ExprId,
) anyerror!usize {
    const refl_expr = try buildRelExpr(self, relation, expr_id, expr_id);
    const bindings = try self.allocator.alloc(ExprId, 1);
    bindings[0] = expr_id;

    return try appendRuleLine(
        self.lines,
        self.allocator,
        refl_expr,
        relation.refl_id,
        bindings,
        &.{},
    );
}

pub fn emitAssoc(
    self: anytype,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!usize {
    const lhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{
            try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ a, b },
            ),
            c,
        },
    );
    const rhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{
            a,
            try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ b, c },
            ),
        },
    );
    const expr = try buildRelExpr(self, relation, lhs, rhs);
    const bindings = try self.allocator.alloc(ExprId, 3);
    bindings[0] = a;
    bindings[1] = b;
    bindings[2] = c;

    return try appendRuleLine(
        self.lines,
        self.allocator,
        expr,
        acui.assoc_id,
        bindings,
        &.{},
    );
}

pub fn emitAssocSymm(
    self: anytype,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!usize {
    const assoc_idx = try emitAssoc(self, a, b, c, relation, acui);
    const lhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{
            try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ a, b },
            ),
            c,
        },
    );
    const rhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{
            a,
            try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ b, c },
            ),
        },
    );
    return try emitSymm(self, relation, lhs, rhs, assoc_idx);
}

pub fn emitComm(
    self: anytype,
    a: ExprId,
    b: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!usize {
    const lhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{ a, b },
    );
    const rhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{ b, a },
    );
    const expr = try buildRelExpr(self, relation, lhs, rhs);
    const bindings = try self.allocator.alloc(ExprId, 2);
    bindings[0] = a;
    bindings[1] = b;

    return try appendRuleLine(
        self.lines,
        self.allocator,
        expr,
        acui.comm_id orelse return error.MissingStructuralMetadata,
        bindings,
        &.{},
    );
}

pub fn emitIdem(
    self: anytype,
    a: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!usize {
    const lhs = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{ a, a },
    );
    const expr = try buildRelExpr(self, relation, lhs, a);
    const bindings = try self.allocator.alloc(ExprId, 1);
    bindings[0] = a;

    return try appendRuleLine(
        self.lines,
        self.allocator,
        expr,
        acui.idem_id orelse return error.MissingStructuralMetadata,
        bindings,
        &.{},
    );
}

pub fn emitLeftUnit(
    self: anytype,
    current_expr: ExprId,
    result_expr: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!usize {
    const bindings = try self.allocator.alloc(ExprId, 1);
    bindings[0] = result_expr;

    const theorem_expr = if (acui.left_unit_rule_reversed)
        try buildRelExpr(self, relation, result_expr, current_expr)
    else
        try buildRelExpr(self, relation, current_expr, result_expr);

    const unit_idx = try appendRuleLine(
        self.lines,
        self.allocator,
        theorem_expr,
        acui.left_unit_rule_id,
        bindings,
        &.{},
    );
    if (!acui.left_unit_rule_reversed) return unit_idx;
    return try emitSymm(self, relation, result_expr, current_expr, unit_idx);
}

pub fn emitRightUnit(
    self: anytype,
    item: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!usize {
    const unit_expr = try unitExpr(self, acui);
    const current_expr = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{ item, unit_expr },
    );
    const swapped = try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{ unit_expr, item },
    );
    const comm_idx = try emitComm(self, item, unit_expr, relation, acui);
    const unit_idx = try emitLeftUnit(self, swapped, item, relation, acui);
    return try composeTransitivityLine(
        self,
        relation,
        current_expr,
        swapped,
        item,
        comm_idx,
        unit_idx,
    );
}

pub fn composeTransitivity(
    self: anytype,
    relation: ResolvedRelation,
    original: ExprId,
    mid: ExprId,
    final: ExprId,
    first_proof: ?usize,
    second_proof: ?usize,
) anyerror!?usize {
    if (first_proof == null) return second_proof;
    if (second_proof == null) return first_proof;
    return try composeTransitivityLine(
        self,
        relation,
        original,
        mid,
        final,
        first_proof.?,
        second_proof.?,
    );
}

pub fn composeTransitivityLine(
    self: anytype,
    relation: ResolvedRelation,
    original: ExprId,
    mid: ExprId,
    final: ExprId,
    first_proof: usize,
    second_proof: usize,
) anyerror!usize {
    const trans_expr = try buildRelExpr(self, relation, original, final);
    const bindings = try self.allocator.alloc(ExprId, 3);
    bindings[0] = original;
    bindings[1] = mid;
    bindings[2] = final;

    const refs = try self.allocator.alloc(CheckedRef, 2);
    refs[0] = .{ .line = first_proof };
    refs[1] = .{ .line = second_proof };

    const line_idx = try appendRuleLine(
        self.lines,
        self.allocator,
        trans_expr,
        relation.trans_id,
        bindings,
        refs,
    );
    traceExprPair(self, "composed transitivity", original, final);
    return line_idx;
}

pub fn buildRelExpr(
    self: anytype,
    relation: ResolvedRelation,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!ExprId {
    return try self.theorem.interner.internApp(
        relation.rel_term_id,
        &[_]ExprId{ lhs, rhs },
    );
}

pub fn unitExpr(
    self: anytype,
    acui: ResolvedStructuralCombiner,
) anyerror!ExprId {
    return try self.theorem.interner.internApp(acui.unit_term_id, &.{});
}

pub fn emitTransport(
    self: anytype,
    relation: ResolvedRelation,
    target_expr: ExprId,
    source_expr: ExprId,
    conv_line_idx: usize,
    source_line: CheckedRef,
) anyerror!usize {
    const transport_id = relation.transport_id orelse {
        return error.MissingTransport;
    };
    const bindings = try self.allocator.alloc(ExprId, 2);
    bindings[0] = source_expr;
    bindings[1] = target_expr;

    const refs = try self.allocator.alloc(CheckedRef, 2);
    refs[0] = .{ .line = conv_line_idx };
    refs[1] = source_line;

    const line_idx = try appendRuleLine(
        self.lines,
        self.allocator,
        target_expr,
        transport_id,
        bindings,
        refs,
    );
    traceExprPair(self, "emitted transport", source_expr, target_expr);
    return line_idx;
}

pub fn emitSymm(
    self: anytype,
    relation: ResolvedRelation,
    a: ExprId,
    b: ExprId,
    proof_line_idx: usize,
) anyerror!usize {
    const symm_expr = try buildRelExpr(self, relation, b, a);
    const bindings = try self.allocator.alloc(ExprId, 2);
    bindings[0] = a;
    bindings[1] = b;

    const refs = try self.allocator.alloc(CheckedRef, 1);
    refs[0] = .{ .line = proof_line_idx };

    const line_idx = try appendRuleLine(
        self.lines,
        self.allocator,
        symm_expr,
        relation.symm_id,
        bindings,
        refs,
    );
    traceExprPair(self, "emitted symmetry", a, b);
    return line_idx;
}

fn traceExprPair(
    self: anytype,
    label: []const u8,
    lhs: ExprId,
    rhs: ExprId,
) void {
    if (!self.debug.normalization) return;

    const lhs_text = ViewTrace.formatExpr(
        self.allocator,
        self.theorem,
        self.env,
        lhs,
    ) catch return;
    defer self.allocator.free(lhs_text);
    const rhs_text = ViewTrace.formatExpr(
        self.allocator,
        self.theorem,
        self.env,
        rhs,
    ) catch return;
    defer self.allocator.free(rhs_text);

    DebugTrace.traceNormalization(
        self.debug,
        "{s}: {s} ⇒ {s}",
        .{ label, lhs_text, rhs_text },
    );
}

const ExprInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

pub fn validateRewriteBindings(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expected_args: []const ArgInfo,
    bindings: []const ExprId,
) !void {
    if (expected_args.len != bindings.len) return error.SortMismatch;

    var bound_deps: [56]u55 = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_len: usize = 0;
    for (expected_args, bindings) |expected, expr_id| {
        const info = try rewriteExprInfo(env, theorem, expr_id);
        if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
            return error.SortMismatch;
        }
        if (expected.bound) {
            if (!info.bound) return error.BoundnessMismatch;
            var k: usize = 0;
            while (k < prev_len) : (k += 1) {
                if (prev_deps[k] & info.deps != 0) return error.DepViolation;
            }
            bound_deps[bound_len] = info.deps;
            bound_len += 1;
        } else {
            for (0..bound_len) |k| {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0)
                    continue;
                if (bound_deps[k] & info.deps != 0) return error.DepViolation;
            }
        }
        prev_deps[prev_len] = info.deps;
        prev_len += 1;
    }
}

pub fn rewriteExprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !ExprInfo {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= theorem.arg_infos.len) {
                    return error.UnknownTheoremVariable;
                }
                const arg = theorem.arg_infos[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                    .deps = arg.deps,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                    .deps = dummy.deps,
                };
            },
        },
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            var deps: u55 = 0;
            for (app.args) |arg_id| {
                deps |= (try rewriteExprInfo(env, theorem, arg_id)).deps;
            }
            break :blk .{
                .sort_name = env.terms.items[app.term_id].ret_sort_name,
                .bound = false,
                .deps = deps,
            };
        },
    };
}

test "validateRewriteBindings rejects bound alias after regular arg" {
    const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
    const allocator = std.testing.allocator;
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term P (x: obj): wff;
        \\axiom sb_rule (t: obj) {x: obj} (p: wff x): $ P t $;
        \\theorem host {x y: obj}: $ P y $;
    ;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(mm0_src, arena.allocator());
    var env = GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    const rule = env.getRule("sb_rule") orelse return error.MissingAssertion;

    var theorem = TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    parser = MM0Parser.init(mm0_src, arena.allocator());
    var found_host = false;
    while (try parser.next()) |stmt| {
        switch (stmt) {
            .assertion => |assertion| {
                if (std.mem.eql(u8, assertion.name, "host")) {
                    try theorem.seedAssertion(assertion);
                    found_host = true;
                    break;
                }
            },
            else => {},
        }
    }
    if (!found_host) return error.MissingAssertion;

    const y_expr = try theorem.interner.internVar(.{ .theorem_var = 1 });
    const p_term = env.term_names.get("P") orelse return error.MissingTerm;
    const p_y = try theorem.interner.internApp(p_term, &.{y_expr});
    const bindings = [_]ExprId{ y_expr, y_expr, p_y };

    try std.testing.expectError(
        error.DepViolation,
        validateRewriteBindings(&env, &theorem, rule.args, &bindings),
    );
}
