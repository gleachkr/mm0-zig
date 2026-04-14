const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralIntervals = @import("./structural_intervals.zig");
const StructuralItems = @import("./structural_items.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;
const StructuralInterval = types.StructuralInterval;
const StructuralJointObligation = types.StructuralJointObligation;
const StructuralProfile = types.StructuralProfile;
const StructuralRemainder = types.StructuralRemainder;

pub fn appendStructuralRemainderState(
    self: anytype,
    actual_items: []const ExprId,
    used: []const bool,
    remainders: []const StructuralRemainder,
    space: BinderSpace,
    state: BranchState,
    out: *std.ArrayListUnmanaged(BranchState),
    profile: StructuralProfile,
) anyerror!void {
    if (remainders.len == 0) {
        for (used) |is_used| {
            if (!is_used) return;
        }
        try out.append(
            self.allocator,
            try BranchStateOps.cloneState(self, state),
        );
        return;
    }

    const interval = try buildStructuralInterval(
        self,
        actual_items,
        used,
        profile,
    );
    if (remainders.len == 1) {
        try appendCombinedStructuralIntervalState(
            self,
            remainders[0].binder_idx,
            interval,
            space,
            state,
            out,
        );
        return;
    }

    try appendCombinedStructuralObligationState(
        self,
        remainders,
        interval,
        space,
        state,
        out,
    );
}

pub fn appendExactStructuralIntervalState(
    self: anytype,
    binder_idx: usize,
    items: []const ExprId,
    space: BinderSpace,
    state: BranchState,
    out: *std.ArrayListUnmanaged(BranchState),
    profile: StructuralProfile,
) anyerror!void {
    try appendCombinedStructuralIntervalState(
        self,
        binder_idx,
        try buildExactStructuralInterval(self, items, profile),
        space,
        state,
        out,
    );
}

pub fn appendCombinedStructuralObligationState(
    self: anytype,
    remainders: []const StructuralRemainder,
    interval: StructuralInterval,
    space: BinderSpace,
    state: BranchState,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    var final_state = try BranchStateOps.cloneState(self, state);
    const binder_idxs = try self.allocator.alloc(usize, remainders.len);
    for (remainders, 0..) |remainder, idx| {
        binder_idxs[idx] = remainder.binder_idx;
    }
    const obligation: StructuralJointObligation = .{
        .head_term_id = interval.head_term_id,
        .unit_term_id = interval.unit_term_id,
        .lower_expr = interval.lower_expr,
        .upper_expr = interval.upper_expr,
        .binder_idxs = binder_idxs,
    };
    if (!try StructuralIntervals.obligationCompatibleWithState(
        self,
        &final_state,
        space,
        obligation,
    )) {
        self.allocator.free(binder_idxs);
        return;
    }

    var obligations = BranchStateOps.getStructuralObligations(
        self,
        &final_state,
        space,
    );
    for (obligations, 0..) |existing, idx| {
        if (existing.head_term_id != obligation.head_term_id or
            existing.unit_term_id != obligation.unit_term_id or
            !std.mem.eql(
                usize,
                existing.binder_idxs,
                obligation.binder_idxs,
            ))
        {
            continue;
        }
        const combined =
            (try combineStructuralObligations(self, existing, obligation))
                orelse {
            self.allocator.free(binder_idxs);
            return;
        };
        if (!try StructuralIntervals.obligationCompatibleWithState(
            self,
            &final_state,
            space,
            combined,
        )) {
            self.allocator.free(binder_idxs);
            return;
        }
        obligations[idx].lower_expr = combined.lower_expr;
        obligations[idx].upper_expr = combined.upper_expr;
        self.allocator.free(binder_idxs);
        try out.append(self.allocator, final_state);
        return;
    }

    obligations = try self.allocator.realloc(obligations, obligations.len + 1);
    BranchStateOps.setStructuralObligations(
        self,
        &final_state,
        space,
        obligations,
    );
    obligations[obligations.len - 1] = obligation;
    try out.append(self.allocator, final_state);
}

pub fn appendCombinedStructuralIntervalState(
    self: anytype,
    binder_idx: usize,
    interval: StructuralInterval,
    space: BinderSpace,
    state: BranchState,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    var final_state = try BranchStateOps.cloneState(self, state);
    const intervals = BranchStateOps.getStructuralIntervals(
        self,
        &final_state,
        space,
    );
    const bindings = BranchStateOps.getBindings(self, &final_state, space);
    const combined = if (intervals[binder_idx]) |existing|
        (try combineStructuralIntervals(self, existing, interval)) orelse return
    else
        interval;

    if (bindings[binder_idx]) |existing| {
        if (!try StructuralIntervals.exprWithinInterval(
            self,
            existing,
            combined,
        )) return;
    }
    intervals[binder_idx] = combined;
    try out.append(self.allocator, final_state);
}

pub fn appendStructuralCandidateState(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    binder_idxs: []const usize,
    binder_exprs: []const ExprId,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    var next_state = try BranchStateOps.cloneState(self, state);
    for (binder_idxs, binder_exprs) |binder_idx, expr_id| {
        if (!try applyStructuralBindingCandidate(
            self,
            &next_state,
            space,
            binder_idx,
            expr_id,
        )) {
            return;
        }
    }
    if (!try self.partialStructuralStateCompatible(&next_state, space)) {
        return;
    }
    try appendUniqueStateForSpace(self, out, next_state, space);
}

pub fn appendUniqueStateForSpace(
    self: anytype,
    out: *std.ArrayListUnmanaged(BranchState),
    state: BranchState,
    space: BinderSpace,
) anyerror!void {
    const candidate_bindings = switch (space) {
        .rule => state.rule_bindings,
        .view => state.view_bindings orelse return,
    };
    for (out.items) |existing| {
        const existing_bindings = switch (space) {
            .rule => existing.rule_bindings,
            .view => existing.view_bindings orelse continue,
        };
        if (try SemanticCompare.sameBindingsCompatible(
            self,
            existing_bindings,
            candidate_bindings,
        )) {
            return;
        }
    }
    try out.append(self.allocator, state);
}

pub fn candidateBindingCompatible(
    self: anytype,
    state: *const BranchState,
    space: BinderSpace,
    binder_idx: usize,
    expr_id: ExprId,
) anyerror!bool {
    return try bindingCandidateCompatibleImpl(
        self,
        @constCast(state),
        space,
        binder_idx,
        expr_id,
    );
}

pub fn buildStructuralInterval(
    self: anytype,
    actual_items: []const ExprId,
    used: []const bool,
    profile: StructuralProfile,
) anyerror!StructuralInterval {
    var lower_items = std.ArrayListUnmanaged(ExprId){};
    defer lower_items.deinit(self.allocator);
    for (actual_items, used) |actual_item, is_used| {
        if (!is_used) try lower_items.append(self.allocator, actual_item);
    }

    const lower_expr = try StructuralItems.rebuildStructuralExpr(
        self,
        lower_items.items,
        profile.headTermId(),
        profile.unitTermId(),
    );
    const upper_expr = switch (profile.fragment) {
        .acui => try StructuralItems.rebuildStructuralExpr(
            self,
            actual_items,
            profile.headTermId(),
            profile.unitTermId(),
        ),
        .au, .acu, .aui => lower_expr,
    };
    return .{
        .head_term_id = profile.headTermId(),
        .unit_term_id = profile.unitTermId(),
        .lower_expr = lower_expr,
        .upper_expr = upper_expr,
    };
}

fn bindingCandidateCompatibleImpl(
    self: anytype,
    state: *BranchState,
    space: BinderSpace,
    binder_idx: usize,
    expr_id: ExprId,
) anyerror!bool {
    const bindings = BranchStateOps.getBindings(self, state, space);
    if (binder_idx >= bindings.len) return false;
    if (bindings[binder_idx]) |existing| {
        return try SemanticCompare.bindingCompatible(self, existing, expr_id);
    }
    return try StructuralIntervals.bindingSatisfiesStructural(
        self,
        state,
        space,
        binder_idx,
        expr_id,
    );
}

pub fn buildExactStructuralInterval(
    self: anytype,
    items: []const ExprId,
    profile: StructuralProfile,
) anyerror!StructuralInterval {
    const exact_expr = try StructuralItems.rebuildStructuralExpr(
        self,
        items,
        profile.headTermId(),
        profile.unitTermId(),
    );
    return .{
        .head_term_id = profile.headTermId(),
        .unit_term_id = profile.unitTermId(),
        .lower_expr = exact_expr,
        .upper_expr = exact_expr,
    };
}

pub fn combineStructuralObligations(
    self: anytype,
    lhs: StructuralJointObligation,
    rhs: StructuralJointObligation,
) anyerror!?StructuralJointObligation {
    if (lhs.head_term_id != rhs.head_term_id or
        lhs.unit_term_id != rhs.unit_term_id or
        !std.mem.eql(usize, lhs.binder_idxs, rhs.binder_idxs))
    {
        return error.UnifyMismatch;
    }
    const interval = (try combineStructuralIntervals(
        self,
        .{
            .head_term_id = lhs.head_term_id,
            .unit_term_id = lhs.unit_term_id,
            .lower_expr = lhs.lower_expr,
            .upper_expr = lhs.upper_expr,
        },
        .{
            .head_term_id = rhs.head_term_id,
            .unit_term_id = rhs.unit_term_id,
            .lower_expr = rhs.lower_expr,
            .upper_expr = rhs.upper_expr,
        },
    )) orelse return null;
    return .{
        .head_term_id = interval.head_term_id,
        .unit_term_id = interval.unit_term_id,
        .lower_expr = interval.lower_expr,
        .upper_expr = interval.upper_expr,
        .binder_idxs = lhs.binder_idxs,
    };
}

pub fn combineStructuralIntervals(
    self: anytype,
    lhs: StructuralInterval,
    rhs: StructuralInterval,
) anyerror!?StructuralInterval {
    if (lhs.head_term_id != rhs.head_term_id or
        lhs.unit_term_id != rhs.unit_term_id)
    {
        return error.UnifyMismatch;
    }
    const profile = StructuralItems.resolveStructuralProfile(
        self,
        lhs.head_term_id,
    ) orelse return error.UnifyMismatch;
    if (profile.unitTermId() != lhs.unit_term_id) {
        return error.UnifyMismatch;
    }

    return switch (profile.fragment) {
        .acui => blk: {
            const lower_expr = try StructuralIntervals.unionStructuralExprs(
                self,
                lhs.lower_expr,
                rhs.lower_expr,
                lhs.head_term_id,
                lhs.unit_term_id,
            );
            const upper_expr = try StructuralIntervals.intersectStructuralExprs(
                self,
                lhs.upper_expr,
                rhs.upper_expr,
                lhs.head_term_id,
                lhs.unit_term_id,
            );
            if (!try StructuralIntervals.structuralExprSubset(
                self,
                lower_expr,
                upper_expr,
                lhs.head_term_id,
                lhs.unit_term_id,
            )) {
                break :blk null;
            }
            break :blk .{
                .head_term_id = lhs.head_term_id,
                .unit_term_id = lhs.unit_term_id,
                .lower_expr = lower_expr,
                .upper_expr = upper_expr,
            };
        },
        .au, .acu, .aui => blk: {
            if (!try SemanticCompare.bindingCompatible(
                self,
                lhs.lower_expr,
                rhs.lower_expr,
            )) {
                break :blk null;
            }
            if (!try SemanticCompare.bindingCompatible(
                self,
                lhs.upper_expr,
                rhs.upper_expr,
            )) {
                break :blk null;
            }
            break :blk lhs;
        },
    };
}

fn applyStructuralBindingCandidate(
    self: anytype,
    state: *BranchState,
    space: BinderSpace,
    binder_idx: usize,
    expr_id: ExprId,
) anyerror!bool {
    const bindings = BranchStateOps.getBindings(self, state, space);
    if (!try bindingCandidateCompatibleImpl(
        self,
        state,
        space,
        binder_idx,
        expr_id,
    )) {
        return false;
    }
    if (bindings[binder_idx] == null) {
        bindings[binder_idx] = expr_id;
    }
    return true;
}
