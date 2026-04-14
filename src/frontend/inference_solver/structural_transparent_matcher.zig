const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const BranchStateOps = @import("./branch_state.zig");
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
