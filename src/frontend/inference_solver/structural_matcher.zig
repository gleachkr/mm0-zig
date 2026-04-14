const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralFragmentMatcher =
    @import("./structural_fragment_matcher.zig");
const StructuralIntervals = @import("./structural_intervals.zig");
const StructuralTransparentMatcher =
    @import("./structural_transparent_matcher.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;

pub fn matchExpr(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    if (try StructuralFragmentMatcher.matchStructural(
        @This(),
        self,
        template,
        actual,
        space,
        state,
    )) |states| {
        return states;
    }

    return switch (template) {
        .binder => |idx| blk: {
            var new_state = try BranchStateOps.cloneState(self, state);
            const bindings = BranchStateOps.getBindings(self, &new_state, space);
            if (idx >= bindings.len) break :blk &.{};
            if (bindings[idx]) |existing| {
                if (!try SemanticCompare.bindingCompatible(
                    self,
                    existing,
                    actual,
                )) {
                    break :blk &.{};
                }
            } else {
                if (!try StructuralIntervals.bindingSatisfiesStructural(
                    self,
                    &new_state,
                    space,
                    idx,
                    actual,
                )) {
                    break :blk &.{};
                }
                bindings[idx] = actual;
            }
            const out = try self.allocator.alloc(BranchState, 1);
            out[0] = new_state;
            break :blk out;
        },
        .app => |app| blk: {
            const node = self.theorem.interner.node(actual);
            const actual_app = switch (node.*) {
                .app => |value| value,
                .variable => {
                    break :blk try StructuralTransparentMatcher
                        .matchExprTransparent(
                        self,
                        template,
                        actual,
                        space,
                        state,
                    );
                },
            };
            if (actual_app.term_id != app.term_id or
                actual_app.args.len != app.args.len)
            {
                break :blk try StructuralTransparentMatcher
                    .matchExprTransparent(
                    self,
                    template,
                    actual,
                    space,
                    state,
                );
            }
            var states = std.ArrayListUnmanaged(BranchState){};
            try states.append(
                self.allocator,
                try BranchStateOps.cloneState(self, state),
            );
            for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
                var next = std.ArrayListUnmanaged(BranchState){};
                for (states.items) |current| {
                    const matches = try matchExpr(
                        self,
                        tmpl_arg,
                        actual_arg,
                        space,
                        current,
                    );
                    try next.appendSlice(self.allocator, matches);
                }
                if (next.items.len == 0) break :blk &.{};
                states = next;
            }
            break :blk try states.toOwnedSlice(self.allocator);
        },
    };
}
