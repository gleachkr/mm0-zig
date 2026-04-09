const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const AcuiSupport = @import("../../acui_support.zig");
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const ChildNorm = @import("../child_norm.zig");
const ProofEmit = @import("../proof_emit.zig");
const Support = @import("../support.zig");
const Cover = @import("./cover.zig");
const Types = @import("../types.zig");

const NormalizeResult = Types.NormalizeResult;
const AcuiLeaf = Types.AcuiLeaf;

pub fn buildAcuiRewriteConversion(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
    leaves: []const AcuiLeaf,
) anyerror!NormalizeResult {
    var next_leaf: usize = 0;
    const replaced = try rewriteAcuiLeaves(
        self,
        expr_id,
        relation,
        acui,
        leaves,
        &next_leaf,
    );
    const rewritten = switch (self.theorem.interner.node(replaced.result_expr).*) {
        .app => |rewritten_app| try ChildNorm.normalizeChildren(
            self,
            replaced.result_expr,
            rewritten_app,
        ),
        .variable => NormalizeResult{
            .result_expr = replaced.result_expr,
            .conv_line_idx = null,
        },
    };
    const exact = try Cover.normalizeStructuralExact(
        self,
        rewritten.result_expr,
        relation,
        acui,
    );
    const replaced_to_rewritten = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        replaced.result_expr,
        rewritten.result_expr,
        replaced.conv_line_idx,
        rewritten.conv_line_idx,
    );
    const proof = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        rewritten.result_expr,
        exact.result_expr,
        replaced_to_rewritten,
        exact.conv_line_idx,
    );
    return .{
        .result_expr = exact.result_expr,
        .conv_line_idx = proof,
    };
}

pub fn normalizeStructural(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!NormalizeResult {
    const node = self.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        else => return .{ .result_expr = expr_id, .conv_line_idx = null },
    };
    if (app.term_id != acui.head_term_id or app.args.len != 2) {
        return .{ .result_expr = expr_id, .conv_line_idx = null };
    }

    var leaves = std.ArrayListUnmanaged(AcuiLeaf){};
    defer leaves.deinit(self.allocator);
    try collectAcuiLeaves(self, expr_id, acui.head_term_id, &leaves);

    const unit_expr = try ProofEmit.unitExpr(self, acui);
    try applySameSideAbsorption(self, leaves.items, unit_expr, relation, acui);

    var next_leaf: usize = 0;
    const replaced = try rewriteAcuiLeaves(
        self,
        expr_id,
        relation,
        acui,
        leaves.items,
        &next_leaf,
    );
    const rewritten = switch (self.theorem.interner.node(replaced.result_expr).*) {
        .app => |rewritten_app| try ChildNorm.normalizeChildren(
            self,
            replaced.result_expr,
            rewritten_app,
        ),
        .variable => NormalizeResult{
            .result_expr = replaced.result_expr,
            .conv_line_idx = null,
        },
    };
    const exact = try Cover.normalizeStructuralExact(
        self,
        rewritten.result_expr,
        relation,
        acui,
    );
    const replaced_to_rewritten = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        replaced.result_expr,
        rewritten.result_expr,
        replaced.conv_line_idx,
        rewritten.conv_line_idx,
    );
    const proof = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        rewritten.result_expr,
        exact.result_expr,
        replaced_to_rewritten,
        exact.conv_line_idx,
    );
    return .{
        .result_expr = exact.result_expr,
        .conv_line_idx = proof,
    };
}

pub fn collectAcuiLeaves(
    self: anytype,
    expr_id: ExprId,
    head_term_id: u32,
    out: *std.ArrayListUnmanaged(AcuiLeaf),
) anyerror!void {
    var support = Support.acuiSupport(self);
    var infos = std.ArrayListUnmanaged(AcuiSupport.LeafInfo){};
    defer infos.deinit(self.allocator);
    try support.collectLeafInfos(expr_id, head_term_id, &infos);
    try out.ensureUnusedCapacity(self.allocator, infos.items.len);
    for (infos.items) |info| {
        out.appendAssumeCapacity(.{
            .old_expr = info.expr_id,
            .new_expr = info.expr_id,
            .is_def = info.is_def,
            .conv_line_idx = null,
        });
    }
}

pub fn applySameSideAbsorption(
    self: anytype,
    leaves: []AcuiLeaf,
    unit_expr: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!void {
    const infos = try self.allocator.alloc(AcuiSupport.LeafInfo, leaves.len);
    defer self.allocator.free(infos);
    for (leaves, 0..) |leaf, idx| {
        infos[idx] = .{
            .expr_id = leaf.old_expr,
            .is_def = leaf.is_def,
        };
    }

    var support = Support.acuiSupport(self);
    const targets = try support.computeSameSideTargets(infos, unit_expr, acui);
    defer self.allocator.free(targets);

    for (leaves, targets) |*leaf, target| {
        if (target == leaf.old_expr) continue;
        const proof = try Cover.buildConcreteToDefCoverProof(
            self,
            leaf.old_expr,
            target,
            relation,
            acui,
        ) orelse return error.MissingStructuralMetadata;
        leaf.new_expr = target;
        leaf.conv_line_idx = proof;
    }
}

pub fn rewriteAcuiLeaves(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
    leaves: []const AcuiLeaf,
    next_leaf: *usize,
) anyerror!NormalizeResult {
    const node = self.theorem.interner.node(expr_id);
    switch (node.*) {
        .app => |app| {
            if (app.term_id == acui.head_term_id and app.args.len == 2) {
                const left = try rewriteAcuiLeaves(
                    self,
                    app.args[0],
                    relation,
                    acui,
                    leaves,
                    next_leaf,
                );
                const right = try rewriteAcuiLeaves(
                    self,
                    app.args[1],
                    relation,
                    acui,
                    leaves,
                    next_leaf,
                );
                const new_args = [_]ExprId{
                    left.result_expr,
                    right.result_expr,
                };
                const old_args = [_]ExprId{ app.args[0], app.args[1] };
                const new_expr = if (left.result_expr == app.args[0] and
                    right.result_expr == app.args[1])
                    expr_id
                else
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &new_args,
                    );
                return .{
                    .result_expr = new_expr,
                    .conv_line_idx = try ProofEmit.emitCongruenceLine(
                        self,
                        acui.head_term_id,
                        &old_args,
                        &new_args,
                        &[_]?usize{
                            left.conv_line_idx,
                            right.conv_line_idx,
                        },
                    ),
                };
            }
        },
        .variable => {},
    }

    if (next_leaf.* >= leaves.len) return error.MissingStructuralMetadata;
    const leaf = leaves[next_leaf.*];
    next_leaf.* += 1;
    if (leaf.old_expr != expr_id) return error.MissingStructuralMetadata;
    return .{
        .result_expr = leaf.new_expr,
        .conv_line_idx = if (leaf.conv_line_idx) |idx|
            idx
        else
            try ProofEmit.emitTransparentRelationProof(
                self,
                relation,
                leaf.old_expr,
                leaf.new_expr,
            ),
    };
}
