const ExprId = @import("../../compiler_expr.zig").ExprId;
const DefOps = @import("../../def_ops.zig");
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const NonAcuiTarget = @import("../non_acui_target.zig");
const ProofEmit = @import("../proof_emit.zig");
const Support = @import("../support.zig");
const Canonical = @import("./canonical.zig");
const Types = @import("../types.zig");

const NormalizeResult = Types.NormalizeResult;

pub fn buildConcreteToDefCoverProof(
    self: anytype,
    concrete_expr: ExprId,
    def_expr: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!?usize {
    if (try NonAcuiTarget.buildNonAcuiCommonTarget(
        self,
        def_expr,
        concrete_expr,
    )) |common| {
        if (common.target_expr == def_expr) {
            return common.rhs_conv_line_idx;
        }
        if (common.target_expr == concrete_expr) {
            const def_to_concrete = common.lhs_conv_line_idx orelse {
                return null;
            };
            return try ProofEmit.emitSymm(
                self,
                relation,
                def_expr,
                concrete_expr,
                def_to_concrete,
            );
        }
        const concrete_to_target = common.rhs_conv_line_idx orelse {
            return null;
        };
        const def_to_target = common.lhs_conv_line_idx orelse return null;
        const target_to_def = try ProofEmit.emitSymm(
            self,
            relation,
            def_expr,
            common.target_expr,
            def_to_target,
        );
        return try ProofEmit.composeTransitivity(
            self,
            relation,
            concrete_expr,
            common.target_expr,
            def_expr,
            concrete_to_target,
            target_to_def,
        );
    }

    var def_ops = DefOps.Context.initWithRegistry(
        self.allocator,
        self.theorem,
        self.env,
        self.registry,
    );
    defer def_ops.deinit();

    const witness = try def_ops.instantiateDefTowardAcuiItem(
        def_expr,
        concrete_expr,
        acui.head_term_id,
    ) orelse return null;
    const def_to_witness = try ProofEmit.emitTransparentRelationProof(
        self,
        relation,
        def_expr,
        witness,
    );
    if (witness == concrete_expr) {
        return try ProofEmit.emitSymm(
            self,
            relation,
            def_expr,
            concrete_expr,
            def_to_witness orelse return null,
        );
    }

    const witness_to_concrete = if (isAcuiExpr(
        self,
        witness,
        acui.head_term_id,
    )) blk: {
        const exact = try normalizeStructuralExact(
            self,
            witness,
            relation,
            acui,
        );
        if (exact.result_expr != concrete_expr) return null;
        break :blk exact.conv_line_idx;
    } else return null;

    const def_to_concrete = try ProofEmit.composeTransitivity(
        self,
        relation,
        def_expr,
        witness,
        concrete_expr,
        def_to_witness,
        witness_to_concrete,
    ) orelse return null;
    return try ProofEmit.emitSymm(
        self,
        relation,
        def_expr,
        concrete_expr,
        def_to_concrete,
    );
}

pub fn isAcuiExpr(
    self: anytype,
    expr_id: ExprId,
    head_term_id: u32,
) bool {
    const node = self.theorem.interner.node(expr_id);
    return switch (node.*) {
        .app => |app| app.term_id == head_term_id and app.args.len == 2,
        .variable => false,
    };
}

pub fn sharedStructuralCombiner(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) ?ResolvedStructuralCombiner {
    var support = Support.acuiSupport(self);
    return support.sharedStructuralCombiner(lhs, rhs);
}

pub fn buildCanonicalAcuiFromItems(
    self: anytype,
    items: []const ExprId,
    acui: ResolvedStructuralCombiner,
) anyerror!ExprId {
    var support = Support.acuiSupport(self);
    return try support.buildCanonicalAcuiFromItems(items, acui);
}

pub fn rebuildAcuiTree(
    self: anytype,
    items: []const ExprId,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!ExprId {
    var support = Support.acuiSupport(self);
    return try support.rebuildAcuiTree(items, head_term_id, unit_term_id);
}

pub fn normalizeStructuralExact(
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
    return try Canonical.mergeCanonical(
        self,
        expr_id,
        app.args[0],
        app.args[1],
        relation,
        acui,
    );
}
