const std = @import("std");

const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const NormalizedCompare = @import("../compiler/normalized_compare.zig");
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralIntervals = @import("./structural_intervals.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;

pub fn matchExprTransparent(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    const transparent = try matchTransparentOnly(
        self,
        template,
        actual,
        space,
        state,
    );
    if (transparent.len != 0) return transparent;

    return try matchNormalizedOnly(
        self,
        template,
        actual,
        space,
        state,
    );
}

fn matchTransparentOnly(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    var new_state = try BranchStateOps.cloneState(self, state);
    const bindings = BranchStateOps.getBindings(self, &new_state, space);
    const old_bindings = switch (space) {
        .rule => state.rule_bindings,
        .view => state.view_bindings.?,
    };

    var def_ops = DefOps.Context.init(
        self.allocator,
        self.theorem,
        self.env,
    );
    defer def_ops.deinit();
    if (!(def_ops.matchTemplateTransparent(
        template,
        actual,
        bindings,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return &.{},
        else => return err,
    })) {
        return &.{};
    }
    for (bindings, old_bindings, 0..) |binding, old_binding, idx| {
        const expr_id = binding orelse continue;
        if (old_binding != null) continue;
        if (!try StructuralIntervals.bindingSatisfiesStructural(
            self,
            &new_state,
            space,
            idx,
            expr_id,
        )) {
            return &.{};
        }
    }

    const out = try self.allocator.alloc(BranchState, 1);
    out[0] = new_state;
    return out;
}

fn matchNormalizedOnly(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    if (!self.canUseNormalizedStructuralItemMatch()) return &.{};
    const scratch = self.scratch orelse return &.{};

    const old_bindings = switch (space) {
        .rule => state.rule_bindings,
        .view => state.view_bindings.?,
    };
    const seeds = try exactBindingSeeds(self.allocator, old_bindings);
    defer self.allocator.free(seeds);

    var def_ops = DefOps.Context.initWithRegistry(
        self.allocator,
        self.theorem,
        self.env,
        self.registry,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(
        ruleArgsForSpace(self, space),
        seeds,
    );
    defer session.deinit();

    const mark = scratch.mark();
    const matched = NormalizedCompare.matchTemplate(
        self.allocator,
        self.env,
        self.registry,
        scratch,
        &session,
        template,
        actual,
    ) catch |err| {
        scratch.discard(mark);
        return switch (err) {
            error.DependencySlotExhausted => &.{},
            error.MissingRepresentative => &.{},
            error.UnresolvedDummyWitness => &.{},
            else => err,
        };
    };
    scratch.discard(mark);
    if (!matched) return &.{};

    const materialized = try session.materializeOptionalBindings();
    defer self.allocator.free(materialized);
    const represented = try session.representOptionalBindings(materialized);
    defer self.allocator.free(represented);

    return try copySessionBindingsToBranch(
        self,
        &session,
        represented,
        old_bindings,
        space,
        state,
    );
}

fn copySessionBindingsToBranch(
    self: anytype,
    session: *DefOps.RuleMatchSession,
    session_bindings: []const ?ExprId,
    old_bindings: []const ?ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    var new_state = try BranchStateOps.cloneState(self, state);
    const bindings = BranchStateOps.getBindings(self, &new_state, space);

    for (session_bindings, old_bindings, 0..) |
        maybe_expr,
        old_binding,
        idx,
    | {
        if (idx >= bindings.len) return &.{};
        const expr_id = maybe_expr orelse {
            if (old_binding == null and session.state.bindings[idx] != null) {
                return &.{};
            }
            continue;
        };
        if (old_binding) |existing| {
            if (!try SemanticCompare.bindingCompatible(
                self,
                existing,
                expr_id,
            )) {
                return &.{};
            }
            continue;
        }
        if (!try StructuralIntervals.bindingSatisfiesStructural(
            self,
            &new_state,
            space,
            idx,
            expr_id,
        )) {
            return &.{};
        }
        bindings[idx] = expr_id;
    }

    if (!try self.partialStructuralStateCompatible(&new_state, space)) {
        return &.{};
    }

    const out = try self.allocator.alloc(BranchState, 1);
    out[0] = new_state;
    return out;
}

fn exactBindingSeeds(
    allocator: std.mem.Allocator,
    bindings: []const ?ExprId,
) ![]DefOps.BindingSeed {
    const seeds = try allocator.alloc(DefOps.BindingSeed, bindings.len);
    for (bindings, 0..) |binding, idx| {
        seeds[idx] = if (binding) |expr_id|
            .{ .exact = expr_id }
        else
            .none;
    }
    return seeds;
}

fn ruleArgsForSpace(
    self: anytype,
    space: BinderSpace,
) []const ArgInfo {
    return switch (space) {
        .rule => self.rule.args,
        .view => self.view.?.arg_infos,
    };
}
