const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const AcuiSupport = @import("../../acui_support.zig");
const compareExprIds = AcuiSupport.compareExprIds;
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const Support = @import("../support.zig");
const NonAcuiTarget = @import("../non_acui_target.zig");
const Cover = @import("./cover.zig");
const Normalize = @import("./normalize.zig");
const Types = @import("../types.zig");

const CommonTargetResult = Types.CommonTargetResult;
const AcuiLeaf = Types.AcuiLeaf;

pub fn buildAcuiCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    const relation =
        Support.resolveRelationForExpr(self, lhs) orelse return null;
    const acui = try Cover.sharedStructuralCombiner(self, lhs, rhs) orelse {
        return null;
    };

    var lhs_leaves = std.ArrayListUnmanaged(AcuiLeaf){};
    defer lhs_leaves.deinit(self.allocator);
    var rhs_leaves = std.ArrayListUnmanaged(AcuiLeaf){};
    defer rhs_leaves.deinit(self.allocator);
    try Normalize.collectAcuiLeaves(self, lhs, acui.head_term_id, &lhs_leaves);
    try Normalize.collectAcuiLeaves(self, rhs, acui.head_term_id, &rhs_leaves);

    const lhs_exact = try self.allocator.alloc(bool, lhs_leaves.items.len);
    defer self.allocator.free(lhs_exact);
    const rhs_exact = try self.allocator.alloc(bool, rhs_leaves.items.len);
    defer self.allocator.free(rhs_exact);
    const lhs_claimed =
        try self.allocator.alloc(bool, lhs_leaves.items.len);
    defer self.allocator.free(lhs_claimed);
    const rhs_claimed =
        try self.allocator.alloc(bool, rhs_leaves.items.len);
    defer self.allocator.free(rhs_claimed);
    @memset(lhs_exact, false);
    @memset(rhs_exact, false);
    @memset(lhs_claimed, false);
    @memset(rhs_claimed, false);

    var common_items = std.ArrayListUnmanaged(ExprId){};
    defer common_items.deinit(self.allocator);
    try cancelExactAcuiItems(
        self,
        lhs_leaves.items,
        rhs_leaves.items,
        lhs_exact,
        rhs_exact,
        &common_items,
    );
    try pairCommonAcuiLeaves(
        self,
        lhs_leaves.items,
        rhs_leaves.items,
        lhs_exact,
        rhs_exact,
        &common_items,
    );

    try claimOppositeConcreteLeaves(
        self,
        lhs_leaves.items,
        lhs_exact,
        lhs_claimed,
        rhs_leaves.items,
        rhs_exact,
        relation,
        acui,
    );
    try claimOppositeConcreteLeaves(
        self,
        rhs_leaves.items,
        rhs_exact,
        rhs_claimed,
        lhs_leaves.items,
        lhs_exact,
        relation,
        acui,
    );

    var target_items = std.ArrayListUnmanaged(ExprId){};
    defer target_items.deinit(self.allocator);
    try target_items.appendSlice(self.allocator, common_items.items);

    for (lhs_leaves.items, 0..) |leaf, idx| {
        if (lhs_exact[idx]) continue;
        if (leaf.is_def) {
            if (!lhs_claimed[idx]) return null;
            try target_items.append(self.allocator, leaf.old_expr);
            continue;
        }
        if (leaf.new_expr == leaf.old_expr) return null;
    }
    for (rhs_leaves.items, 0..) |leaf, idx| {
        if (rhs_exact[idx]) continue;
        if (leaf.is_def) {
            if (!rhs_claimed[idx]) return null;
            try target_items.append(self.allocator, leaf.old_expr);
            continue;
        }
        if (leaf.new_expr == leaf.old_expr) return null;
    }

    const target_expr = try Cover.buildCanonicalAcuiFromItems(
        self,
        target_items.items,
        acui,
    );

    const lhs_result = try Normalize.buildAcuiRewriteConversion(
        self,
        lhs,
        relation,
        acui,
        lhs_leaves.items,
    );
    const rhs_result = try Normalize.buildAcuiRewriteConversion(
        self,
        rhs,
        relation,
        acui,
        rhs_leaves.items,
    );
    if (lhs_result.result_expr != target_expr or
        rhs_result.result_expr != target_expr)
    {
        return null;
    }

    return .{
        .target_expr = target_expr,
        .lhs_conv_line_idx = lhs_result.conv_line_idx,
        .rhs_conv_line_idx = rhs_result.conv_line_idx,
    };
}

pub fn pairCommonAcuiLeaves(
    self: anytype,
    lhs: []AcuiLeaf,
    rhs: []AcuiLeaf,
    lhs_exact: []bool,
    rhs_exact: []bool,
    common_items: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    for (lhs, 0..) |*lhs_leaf, lhs_idx| {
        if (lhs_exact[lhs_idx]) continue;
        for (rhs, 0..) |*rhs_leaf, rhs_idx| {
            if (rhs_exact[rhs_idx]) continue;
            const common = try NonAcuiTarget.buildNonAcuiCommonTarget(
                self,
                lhs_leaf.old_expr,
                rhs_leaf.old_expr,
            ) orelse continue;
            lhs_exact[lhs_idx] = true;
            rhs_exact[rhs_idx] = true;
            lhs_leaf.new_expr = common.target_expr;
            lhs_leaf.conv_line_idx = common.lhs_conv_line_idx;
            rhs_leaf.new_expr = common.target_expr;
            rhs_leaf.conv_line_idx = common.rhs_conv_line_idx;
            try common_items.append(self.allocator, common.target_expr);
            break;
        }
    }
}

pub fn claimOppositeConcreteLeaves(
    self: anytype,
    owners: []AcuiLeaf,
    owner_exact: []const bool,
    owner_claimed: []bool,
    concretes: []AcuiLeaf,
    concrete_exact: []const bool,
    relation: ResolvedRelation,
    acui: anytype,
) anyerror!void {
    for (owners, 0..) |owner, owner_idx| {
        if (owner_exact[owner_idx] or !owner.is_def) continue;
        for (concretes, 0..) |*concrete, concrete_idx| {
            if (concrete_exact[concrete_idx] or concrete.is_def) continue;
            if (concrete.new_expr != concrete.old_expr) continue;
            const proof = try Cover.buildConcreteToDefCoverProof(
                self,
                concrete.old_expr,
                owner.old_expr,
                relation,
                acui,
            ) orelse continue;
            concrete.new_expr = owner.old_expr;
            concrete.conv_line_idx = proof;
            owner_claimed[owner_idx] = true;
        }
    }
}

pub fn cancelExactAcuiItems(
    self: anytype,
    lhs: []const AcuiLeaf,
    rhs: []const AcuiLeaf,
    lhs_exact: []bool,
    rhs_exact: []bool,
    common_items: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    var lhs_idx: usize = 0;
    var rhs_idx: usize = 0;
    while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
        switch (compareExprIds(
            self.theorem,
            lhs[lhs_idx].old_expr,
            rhs[rhs_idx].old_expr,
        )) {
            .lt => lhs_idx += 1,
            .gt => rhs_idx += 1,
            .eq => {
                lhs_exact[lhs_idx] = true;
                rhs_exact[rhs_idx] = true;
                try common_items.append(
                    self.allocator,
                    lhs[lhs_idx].old_expr,
                );
                lhs_idx += 1;
                rhs_idx += 1;
            },
        }
    }
}
