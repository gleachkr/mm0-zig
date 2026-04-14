const ExprId = @import("../expr.zig").ExprId;
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;
const StructuralInterval = types.StructuralInterval;
const StructuralJointObligation = types.StructuralJointObligation;

pub fn initState(
    self: anytype,
    partial_bindings: []const ?ExprId,
) !BranchState {
    const rule_bindings = try self.allocator.dupe(?ExprId, partial_bindings);
    const rule_structural_intervals = try self.allocator.alloc(
        ?StructuralInterval,
        partial_bindings.len,
    );
    @memset(rule_structural_intervals, null);
    const view_bindings = if (self.view) |view| blk: {
        const result = try self.allocator.alloc(?ExprId, view.num_binders);
        @memset(result, null);
        for (view.binder_map, 0..) |mapping, idx| {
            const rule_idx = mapping orelse continue;
            result[idx] = partial_bindings[rule_idx];
        }
        break :blk result;
    } else null;
    const view_structural_intervals = if (self.view) |view| blk: {
        const result = try self.allocator.alloc(
            ?StructuralInterval,
            view.num_binders,
        );
        @memset(result, null);
        break :blk result;
    } else null;
    const rule_structural_obligations =
        try self.allocator.alloc(StructuralJointObligation, 0);
    const view_structural_obligations = if (self.view != null)
        try self.allocator.alloc(StructuralJointObligation, 0)
    else
        null;
    return .{
        .rule_bindings = rule_bindings,
        .view_bindings = view_bindings,
        .rule_structural_intervals = rule_structural_intervals,
        .view_structural_intervals = view_structural_intervals,
        .rule_structural_obligations = rule_structural_obligations,
        .view_structural_obligations = view_structural_obligations,
    };
}

pub fn getBindings(
    _: anytype,
    state: *BranchState,
    space: BinderSpace,
) []?ExprId {
    return switch (space) {
        .rule => state.rule_bindings,
        .view => state.view_bindings.?,
    };
}

pub fn getStructuralIntervals(
    _: anytype,
    state: *BranchState,
    space: BinderSpace,
) []?StructuralInterval {
    return switch (space) {
        .rule => state.rule_structural_intervals,
        .view => state.view_structural_intervals.?,
    };
}

pub fn getStructuralObligations(
    _: anytype,
    state: *BranchState,
    space: BinderSpace,
) []StructuralJointObligation {
    return switch (space) {
        .rule => state.rule_structural_obligations,
        .view => state.view_structural_obligations.?,
    };
}

pub fn setStructuralObligations(
    _: anytype,
    state: *BranchState,
    space: BinderSpace,
    obligations: []StructuralJointObligation,
) void {
    switch (space) {
        .rule => state.rule_structural_obligations = obligations,
        .view => state.view_structural_obligations = obligations,
    }
}

pub fn cloneState(
    self: anytype,
    state: BranchState,
) anyerror!BranchState {
    return .{
        .rule_bindings = try self.allocator.dupe(?ExprId, state.rule_bindings),
        .view_bindings = if (state.view_bindings) |bindings|
            try self.allocator.dupe(?ExprId, bindings)
        else
            null,
        .rule_structural_intervals = try self.allocator.dupe(
            ?StructuralInterval,
            state.rule_structural_intervals,
        ),
        .view_structural_intervals = if (state.view_structural_intervals) |i|
            try self.allocator.dupe(?StructuralInterval, i)
        else
            null,
        .rule_structural_obligations = try cloneStructuralObligations(
            self,
            state.rule_structural_obligations,
        ),
        .view_structural_obligations = if (state.view_structural_obligations) |obligations|
            try cloneStructuralObligations(self, obligations)
        else
            null,
    };
}

pub fn cloneStructuralObligations(
    self: anytype,
    obligations: []const StructuralJointObligation,
) anyerror![]StructuralJointObligation {
    const result = try self.allocator.alloc(
        StructuralJointObligation,
        obligations.len,
    );
    for (obligations, 0..) |obligation, idx| {
        result[idx] = .{
            .head_term_id = obligation.head_term_id,
            .unit_term_id = obligation.unit_term_id,
            .lower_expr = obligation.lower_expr,
            .upper_expr = obligation.upper_expr,
            .binder_idxs = try self.allocator.dupe(
                usize,
                obligation.binder_idxs,
            ),
        };
    }
    return result;
}
