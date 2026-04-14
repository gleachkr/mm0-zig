const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const BranchStateOps = @import("./branch_state.zig");
const StructuralIntervals = @import("./structural_intervals.zig");
const StructuralItems = @import("./structural_items.zig");
const StructuralStateUpdates =
    @import("./structural_state_updates.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;
const StructuralJointObligation = types.StructuralJointObligation;
const StructuralProfile = types.StructuralProfile;

pub fn solveStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
) anyerror![]BranchState {
    const profile = StructuralItems.resolveStructuralProfile(
        self,
        obligation.head_term_id,
    ) orelse return error.UnifyMismatch;
    if (profile.unitTermId() != obligation.unit_term_id) {
        return error.UnifyMismatch;
    }
    return switch (profile.fragment) {
        .au, .aui => try solveOrderedStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
        .acu => try solveAcuStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
        .acui => try solveAcuiStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
    };
}

fn solveOrderedStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var target_items = std.ArrayListUnmanaged(ExprId){};
    defer target_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.lower_expr,
        profile,
        &target_items,
    );

    const binder_exprs = try self.allocator.alloc(
        ExprId,
        obligation.binder_idxs.len,
    );
    defer self.allocator.free(binder_exprs);

    var out = std.ArrayListUnmanaged(BranchState){};
    try searchOrderedStructuralObligationAssignments(
        self,
        state,
        space,
        obligation,
        profile,
        target_items.items,
        binder_exprs,
        0,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

fn searchOrderedStructuralObligationAssignments(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    target_items: []const ExprId,
    binder_exprs: []ExprId,
    binder_pos: usize,
    item_start: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (binder_pos >= obligation.binder_idxs.len) {
        if (item_start != target_items.len) return;
        try StructuralStateUpdates.appendStructuralCandidateState(
            self,
            state,
            space,
            obligation.binder_idxs,
            binder_exprs,
            out,
        );
        return;
    }

    var item_end = item_start;
    while (item_end <= target_items.len) : (item_end += 1) {
        const expr_id = try StructuralItems.rebuildStructuralExpr(
            self,
            target_items[item_start..item_end],
            profile.headTermId(),
            profile.unitTermId(),
        );
        if (!try StructuralStateUpdates.candidateBindingCompatible(
            self,
            &state,
            space,
            obligation.binder_idxs[binder_pos],
            expr_id,
        )) {
            continue;
        }
        binder_exprs[binder_pos] = expr_id;
        try searchOrderedStructuralObligationAssignments(
            self,
            state,
            space,
            obligation,
            profile,
            target_items,
            binder_exprs,
            binder_pos + 1,
            item_end,
            out,
        );
    }
}

fn solveAcuStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var target_items = std.ArrayListUnmanaged(ExprId){};
    defer target_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.lower_expr,
        profile,
        &target_items,
    );

    const binder_item_lists = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_item_lists);

    var out = std.ArrayListUnmanaged(BranchState){};
    try searchAcuStructuralObligationAssignments(
        self,
        state,
        space,
        obligation,
        profile,
        target_items.items,
        binder_item_lists,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

fn searchAcuStructuralObligationAssignments(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    binder_target_items: []const ExprId,
    binder_item_lists: []std.ArrayListUnmanaged(ExprId),
    item_pos: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (item_pos >= binder_target_items.len) {
        const binder_exprs = try rebuildBindingExprs(
            self,
            binder_item_lists,
            profile,
        );
        defer self.allocator.free(binder_exprs);
        try StructuralStateUpdates.appendStructuralCandidateState(
            self,
            state,
            space,
            obligation.binder_idxs,
            binder_exprs,
            out,
        );
        return;
    }

    for (binder_item_lists) |*items| {
        try items.append(self.allocator, binder_target_items[item_pos]);
        try searchAcuStructuralObligationAssignments(
            self,
            state,
            space,
            obligation,
            profile,
            binder_target_items,
            binder_item_lists,
            item_pos + 1,
            out,
        );
        _ = items.pop();
    }
}

fn solveAcuiStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var lower_items = std.ArrayListUnmanaged(ExprId){};
    defer lower_items.deinit(self.allocator);
    var upper_items = std.ArrayListUnmanaged(ExprId){};
    defer upper_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.lower_expr,
        profile,
        &lower_items,
    );
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.upper_expr,
        profile,
        &upper_items,
    );

    const binder_lowers = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_lowers);
    const binder_uppers = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_uppers);
    const binder_items = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_items);

    for (
        binder_lowers,
        binder_uppers,
        binder_items,
        obligation.binder_idxs,
    ) |*lower, *upper, *items, binder_idx| {
        _ = items;
        try collectAcuiBinderBounds(
            self,
            &state,
            space,
            binder_idx,
            profile,
            upper_items.items,
            lower,
            upper,
        );
    }

    var out = std.ArrayListUnmanaged(BranchState){};
    try searchAcuiStructuralObligationAssignments(
        self,
        state,
        space,
        obligation,
        profile,
        lower_items.items,
        upper_items.items,
        binder_lowers,
        binder_uppers,
        binder_items,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

fn searchAcuiStructuralObligationAssignments(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    lower_items: []const ExprId,
    upper_items: []const ExprId,
    binder_lowers: []const std.ArrayListUnmanaged(ExprId),
    binder_uppers: []const std.ArrayListUnmanaged(ExprId),
    binder_items: []std.ArrayListUnmanaged(ExprId),
    item_pos: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (item_pos >= upper_items.len) {
        const binder_exprs = try rebuildBindingExprs(
            self,
            binder_items,
            profile,
        );
        defer self.allocator.free(binder_exprs);
        try StructuralStateUpdates.appendStructuralCandidateState(
            self,
            state,
            space,
            obligation.binder_idxs,
            binder_exprs,
            out,
        );
        return;
    }

    const item = upper_items[item_pos];
    const global_required =
        try StructuralIntervals.structuralItemsContainCompatible(
            self,
            lower_items,
            item,
        );
    var required_mask: usize = 0;
    var allowed_mask: usize = 0;
    for (binder_lowers, binder_uppers, 0..) |lower, upper, idx| {
        if (try StructuralIntervals.structuralItemsContainCompatible(
            self,
            upper.items,
            item,
        )) {
            allowed_mask |= (@as(usize, 1) << @intCast(idx));
        }
        if (try StructuralIntervals.structuralItemsContainCompatible(
            self,
            lower.items,
            item,
        )) {
            required_mask |= (@as(usize, 1) << @intCast(idx));
        }
    }
    if ((required_mask & ~allowed_mask) != 0) return;
    const optional_mask = allowed_mask & ~required_mask;
    var choice = optional_mask;
    while (true) {
        const subset = required_mask | choice;
        if (!global_required or subset != 0) {
            for (binder_items, 0..) |*items, idx| {
                if ((subset & (@as(usize, 1) << @intCast(idx))) != 0) {
                    try items.append(self.allocator, item);
                }
            }
            try searchAcuiStructuralObligationAssignments(
                self,
                state,
                space,
                obligation,
                profile,
                lower_items,
                upper_items,
                binder_lowers,
                binder_uppers,
                binder_items,
                item_pos + 1,
                out,
            );
            for (binder_items, 0..) |*items, idx| {
                if ((subset & (@as(usize, 1) << @intCast(idx))) != 0) {
                    _ = items.pop();
                }
            }
        }
        if (choice == 0) break;
        choice = (choice - 1) & optional_mask;
    }
}

fn collectAcuiBinderBounds(
    self: anytype,
    state: *const BranchState,
    space: BinderSpace,
    binder_idx: usize,
    profile: StructuralProfile,
    default_upper_items: []const ExprId,
    lower_out: *std.ArrayListUnmanaged(ExprId),
    upper_out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    const bindings = BranchStateOps.getBindings(self, @constCast(state), space);
    const intervals = BranchStateOps.getStructuralIntervals(
        self,
        @constCast(state),
        space,
    );
    if (binder_idx < bindings.len) {
        if (bindings[binder_idx]) |binding| {
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                binding,
                profile,
                lower_out,
            );
            try upper_out.appendSlice(self.allocator, lower_out.items);
            return;
        }
    }
    if (binder_idx < intervals.len) {
        if (intervals[binder_idx]) |interval| {
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                interval.lower_expr,
                profile,
                lower_out,
            );
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                interval.upper_expr,
                profile,
                upper_out,
            );
            return;
        }
    }
    try upper_out.appendSlice(self.allocator, default_upper_items);
}

fn initExprItemLists(
    self: anytype,
    len: usize,
) ![]std.ArrayListUnmanaged(ExprId) {
    const lists = try self.allocator.alloc(std.ArrayListUnmanaged(ExprId), len);
    for (lists) |*items| items.* = .{};
    return lists;
}

fn deinitExprItemLists(
    self: anytype,
    lists: []std.ArrayListUnmanaged(ExprId),
) void {
    for (lists) |*items| items.deinit(self.allocator);
    self.allocator.free(lists);
}

fn rebuildBindingExprs(
    self: anytype,
    binder_item_lists: []const std.ArrayListUnmanaged(ExprId),
    profile: StructuralProfile,
) ![]ExprId {
    const binder_exprs = try self.allocator.alloc(ExprId, binder_item_lists.len);
    errdefer self.allocator.free(binder_exprs);

    for (binder_item_lists, 0..) |items, idx| {
        binder_exprs[idx] = try StructuralItems.rebuildStructuralExpr(
            self,
            items.items,
            profile.headTermId(),
            profile.unitTermId(),
        );
    }
    return binder_exprs;
}
