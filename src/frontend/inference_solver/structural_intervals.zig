const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralItems = @import("./structural_items.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const StructuralInterval = types.StructuralInterval;
const StructuralJointObligation = types.StructuralJointObligation;
const StructuralProfile = types.StructuralProfile;
const BranchState = types.BranchState;

pub fn bindingSatisfiesStructural(
    self: anytype,
    state: *BranchState,
    space: BinderSpace,
    idx: usize,
    expr_id: ExprId,
) anyerror!bool {
    const intervals = BranchStateOps.getStructuralIntervals(self, state, space);
    if (idx >= intervals.len) return true;
    const interval = intervals[idx] orelse return true;
    return try exprWithinInterval(self, expr_id, interval);
}

pub fn exprWithinInterval(
    self: anytype,
    expr_id: ExprId,
    interval: StructuralInterval,
) anyerror!bool {
    const canonical_expr = try self.canonicalizer.canonicalize(expr_id);
    return try structuralExprSubset(
        self,
        interval.lower_expr,
        canonical_expr,
        interval.head_term_id,
        interval.unit_term_id,
    ) and try structuralExprSubset(
        self,
        canonical_expr,
        interval.upper_expr,
        interval.head_term_id,
        interval.unit_term_id,
    );
}

pub fn structuralExprSubset(
    self: anytype,
    lhs_expr: ExprId,
    rhs_expr: ExprId,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!bool {
    const profile = try StructuralItems.structuralProfileFor(
        self,
        head_term_id,
        unit_term_id,
    );

    var lhs_items = std.ArrayListUnmanaged(ExprId){};
    defer lhs_items.deinit(self.allocator);
    var rhs_items = std.ArrayListUnmanaged(ExprId){};
    defer rhs_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        lhs_expr,
        profile,
        &lhs_items,
    );
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        rhs_expr,
        profile,
        &rhs_items,
    );
    return switch (profile.fragment) {
        .au, .aui => try orderedExprItemsAreSubset(
            self,
            lhs_items.items,
            rhs_items.items,
        ),
        .acu, .acui => try exprBagIsSubset(
            self,
            lhs_items.items,
            rhs_items.items,
        ),
    };
}

pub fn unionStructuralExprs(
    self: anytype,
    lhs_expr: ExprId,
    rhs_expr: ExprId,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!ExprId {
    const profile = try StructuralItems.structuralProfileFor(
        self,
        head_term_id,
        unit_term_id,
    );
    if (profile.fragment != .acui) return error.UnifyMismatch;

    var lhs_items = std.ArrayListUnmanaged(ExprId){};
    defer lhs_items.deinit(self.allocator);
    var rhs_items = std.ArrayListUnmanaged(ExprId){};
    defer rhs_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        lhs_expr,
        profile,
        &lhs_items,
    );
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        rhs_expr,
        profile,
        &rhs_items,
    );

    var merged = std.ArrayListUnmanaged(ExprId){};
    defer merged.deinit(self.allocator);
    try appendExprSetUnion(self, &merged, lhs_items.items, rhs_items.items);
    return try StructuralItems.rebuildStructuralExpr(
        self,
        merged.items,
        head_term_id,
        unit_term_id,
    );
}

pub fn intersectStructuralExprs(
    self: anytype,
    lhs_expr: ExprId,
    rhs_expr: ExprId,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!ExprId {
    const profile = try StructuralItems.structuralProfileFor(
        self,
        head_term_id,
        unit_term_id,
    );
    if (profile.fragment != .acui) return error.UnifyMismatch;

    var lhs_items = std.ArrayListUnmanaged(ExprId){};
    defer lhs_items.deinit(self.allocator);
    var rhs_items = std.ArrayListUnmanaged(ExprId){};
    defer rhs_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        lhs_expr,
        profile,
        &lhs_items,
    );
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        rhs_expr,
        profile,
        &rhs_items,
    );

    var merged = std.ArrayListUnmanaged(ExprId){};
    defer merged.deinit(self.allocator);
    try appendExprSetIntersection(self, &merged, lhs_items.items, rhs_items.items);
    return try StructuralItems.rebuildStructuralExpr(
        self,
        merged.items,
        head_term_id,
        unit_term_id,
    );
}

pub fn orderedExprItemsAreSubset(
    self: anytype,
    lhs: []const ExprId,
    rhs: []const ExprId,
) anyerror!bool {
    var lhs_idx: usize = 0;
    var rhs_idx: usize = 0;
    while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
        if (try SemanticCompare.bindingCompatible(
            self,
            lhs[lhs_idx],
            rhs[rhs_idx],
        )) {
            lhs_idx += 1;
        }
        rhs_idx += 1;
    }
    return lhs_idx == lhs.len;
}

pub fn exprBagIsSubset(
    self: anytype,
    lhs: []const ExprId,
    rhs: []const ExprId,
) anyerror!bool {
    if (lhs.len > rhs.len) return false;

    // Compatibility is semantic rather than exact identity, so ACU/ACUI
    // subset checks need a real bipartite matching pass.
    const rhs_matches = try self.allocator.alloc(?usize, rhs.len);
    defer self.allocator.free(rhs_matches);
    @memset(rhs_matches, null);

    const seen_rhs = try self.allocator.alloc(bool, rhs.len);
    defer self.allocator.free(seen_rhs);

    for (lhs, 0..) |_, lhs_idx| {
        @memset(seen_rhs, false);
        if (!try tryAugmentBagMatching(
            self,
            lhs,
            rhs,
            lhs_idx,
            seen_rhs,
            rhs_matches,
        )) {
            return false;
        }
    }
    return true;
}

pub fn tryAugmentBagMatching(
    self: anytype,
    lhs: []const ExprId,
    rhs: []const ExprId,
    lhs_idx: usize,
    seen_rhs: []bool,
    rhs_matches: []?usize,
) anyerror!bool {
    for (rhs, 0..) |rhs_item, rhs_idx| {
        if (seen_rhs[rhs_idx]) continue;
        if (!try SemanticCompare.bindingCompatible(
            self,
            lhs[lhs_idx],
            rhs_item,
        )) {
            continue;
        }
        seen_rhs[rhs_idx] = true;
        if (rhs_matches[rhs_idx]) |prev_lhs_idx| {
            if (!try tryAugmentBagMatching(
                self,
                lhs,
                rhs,
                prev_lhs_idx,
                seen_rhs,
                rhs_matches,
            )) {
                continue;
            }
        }
        rhs_matches[rhs_idx] = lhs_idx;
        return true;
    }
    return false;
}

pub fn appendExprSetUnion(
    self: anytype,
    out: *std.ArrayListUnmanaged(ExprId),
    lhs: []const ExprId,
    rhs: []const ExprId,
) anyerror!void {
    for (lhs) |item| {
        try appendEquivalentSetItem(self, out, item);
    }
    for (rhs) |item| {
        try appendEquivalentSetItem(self, out, item);
    }
}

pub fn appendExprSetIntersection(
    self: anytype,
    out: *std.ArrayListUnmanaged(ExprId),
    lhs: []const ExprId,
    rhs: []const ExprId,
) anyerror!void {
    const used = try self.allocator.alloc(bool, rhs.len);
    defer self.allocator.free(used);
    @memset(used, false);
    for (lhs) |lhs_item| {
        for (rhs, 0..) |rhs_item, rhs_idx| {
            if (used[rhs_idx]) continue;
            const common = try SemanticCompare.commonStructuralTarget(
                self,
                lhs_item,
                rhs_item,
            ) orelse continue;
            used[rhs_idx] = true;
            try appendEquivalentSetItem(self, out, common);
            break;
        }
    }
}

pub fn appendEquivalentSetItem(
    self: anytype,
    out: *std.ArrayListUnmanaged(ExprId),
    expr_id: ExprId,
) anyerror!void {
    try StructuralItems.appendSortedStructuralItem(self, out, expr_id, true);
}

pub fn structuralItemsContainCompatible(
    self: anytype,
    items: []const ExprId,
    item: ExprId,
) anyerror!bool {
    for (items) |candidate| {
        if (try SemanticCompare.bindingCompatible(self, candidate, item)) {
            return true;
        }
    }
    return false;
}

pub fn obligationCompatibleWithState(
    self: anytype,
    state: *BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
) anyerror!bool {
    const profile = try StructuralItems.structuralProfileFor(
        self,
        obligation.head_term_id,
        obligation.unit_term_id,
    );

    const bindings = BranchStateOps.getBindings(self, state, space);
    const intervals = BranchStateOps.getStructuralIntervals(self, state, space);
    var lower_parts = std.ArrayListUnmanaged(ExprId){};
    defer lower_parts.deinit(self.allocator);
    var upper_parts = std.ArrayListUnmanaged(ExprId){};
    defer upper_parts.deinit(self.allocator);
    var have_full_upper = true;

    for (obligation.binder_idxs) |binder_idx| {
        if (binder_idx >= bindings.len) return false;
        if (bindings[binder_idx]) |binding| {
            try lower_parts.append(self.allocator, binding);
            try upper_parts.append(self.allocator, binding);
            continue;
        }
        if (binder_idx < intervals.len) {
            if (intervals[binder_idx]) |interval| {
                if (interval.head_term_id != obligation.head_term_id or
                    interval.unit_term_id != obligation.unit_term_id)
                {
                    return false;
                }
                try lower_parts.append(self.allocator, interval.lower_expr);
                try upper_parts.append(self.allocator, interval.upper_expr);
                continue;
            }
        }
        have_full_upper = false;
    }

    if (lower_parts.items.len != 0) {
        const lower_expr = try combineStructuralExprs(
            self,
            profile,
            lower_parts.items,
        );
        if (!try structuralExprSubset(
            self,
            lower_expr,
            obligation.upper_expr,
            obligation.head_term_id,
            obligation.unit_term_id,
        )) {
            return false;
        }
    }
    if (have_full_upper) {
        const upper_expr = try combineStructuralExprs(
            self,
            profile,
            upper_parts.items,
        );
        if (!try structuralExprSubset(
            self,
            obligation.lower_expr,
            upper_expr,
            obligation.head_term_id,
            obligation.unit_term_id,
        )) {
            return false;
        }
    }
    return true;
}

pub fn obligationSatisfied(
    self: anytype,
    bindings: []const ?ExprId,
    obligation: StructuralJointObligation,
) anyerror!bool {
    const combined = try combineStructuralBindingExprs(
        self,
        bindings,
        obligation.binder_idxs,
        obligation.head_term_id,
        obligation.unit_term_id,
    );
    return try structuralExprSubset(
        self,
        obligation.lower_expr,
        combined,
        obligation.head_term_id,
        obligation.unit_term_id,
    ) and try structuralExprSubset(
        self,
        combined,
        obligation.upper_expr,
        obligation.head_term_id,
        obligation.unit_term_id,
    );
}

pub fn combineStructuralBindingExprs(
    self: anytype,
    bindings: []const ?ExprId,
    binder_idxs: []const usize,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!ExprId {
    const profile = try StructuralItems.structuralProfileFor(
        self,
        head_term_id,
        unit_term_id,
    );

    var exprs = std.ArrayListUnmanaged(ExprId){};
    defer exprs.deinit(self.allocator);
    for (binder_idxs) |binder_idx| {
        const expr_id = bindings[binder_idx] orelse {
            return error.MissingBinderAssignment;
        };
        try exprs.append(self.allocator, expr_id);
    }
    return try combineStructuralExprs(self, profile, exprs.items);
}

pub fn combineStructuralExprs(
    self: anytype,
    profile: StructuralProfile,
    exprs: []const ExprId,
) anyerror!ExprId {
    var items = std.ArrayListUnmanaged(ExprId){};
    defer items.deinit(self.allocator);
    for (exprs) |expr_id| {
        var binding_items = std.ArrayListUnmanaged(ExprId){};
        defer binding_items.deinit(self.allocator);
        try StructuralItems.collectCanonicalStructuralItems(
            self,
            expr_id,
            profile,
            &binding_items,
        );
        for (binding_items.items) |item| {
            try StructuralItems.appendStructuralItem(self, profile, &items, item);
        }
    }
    return try StructuralItems.rebuildStructuralExpr(
        self,
        items.items,
        profile.headTermId(),
        profile.unitTermId(),
    );
}
