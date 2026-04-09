const ExprId = @import("../expr.zig").ExprId;
const DefOps = @import("../def_ops.zig");
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;
const Support = @import("./support.zig");
const Core = @import("./core.zig");
const Acui = @import("./acui.zig");
const NonAcuiTarget = @import("./non_acui_target.zig");
const ProofEmit = @import("./proof_emit.zig");
const Types = @import("./types.zig");

const CommonTargetResult = Types.CommonTargetResult;

pub fn buildCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    if (lhs == rhs) {
        return .{
            .target_expr = lhs,
            .lhs_conv_line_idx = null,
            .rhs_conv_line_idx = null,
        };
    }

    if (try buildDirectTransparentCommonTarget(self, lhs, rhs)) |direct| {
        return direct;
    }
    if (try buildSemanticDefCommonTarget(self, lhs, rhs)) |semantic| {
        return semantic;
    }
    if (try Acui.buildAcuiCommonTarget(self, lhs, rhs)) |acui| {
        return acui;
    }
    return try NonAcuiTarget.buildNonAcuiCommonTarget(self, lhs, rhs);
}

pub fn buildDirectTransparentCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    const relation = Support.resolveRelationForExpr(self, lhs) orelse return null;

    var def_ops = DefOps.Context.initWithRegistry(
        self.allocator,
        self.theorem,
        self.env,
        self.registry,
    );
    defer def_ops.deinit();

    if ((try def_ops.compareTransparent(lhs, rhs)) != null) {
        return .{
            .target_expr = rhs,
            .lhs_conv_line_idx = try ProofEmit.emitTransparentRelationProof(
                self,
                relation,
                lhs,
                rhs,
            ),
            .rhs_conv_line_idx = null,
        };
    }
    if ((try def_ops.compareTransparent(rhs, lhs)) != null) {
        return .{
            .target_expr = lhs,
            .lhs_conv_line_idx = null,
            .rhs_conv_line_idx = try ProofEmit.emitTransparentRelationProof(
                self,
                relation,
                rhs,
                lhs,
            ),
        };
    }
    return null;
}

pub fn buildSemanticDefCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    const relation = Support.resolveRelationForExpr(self, lhs) orelse return null;
    if (try buildSemanticCommonTargetFromDef(self, lhs, rhs, relation)) |result| {
        return result;
    }
    if (try buildSemanticCommonTargetFromDef(self, rhs, lhs, relation)) |result| {
        return .{
            .target_expr = result.target_expr,
            .lhs_conv_line_idx = result.rhs_conv_line_idx,
            .rhs_conv_line_idx = result.lhs_conv_line_idx,
        };
    }
    return null;
}

pub fn buildSemanticCommonTargetFromDef(
    self: anytype,
    def_expr: ExprId,
    other_expr: ExprId,
    relation: ResolvedRelation,
) anyerror!?CommonTargetResult {
    var def_ops = DefOps.Context.initWithRegistry(
        self.allocator,
        self.theorem,
        self.env,
        self.registry,
    );
    defer def_ops.deinit();

    const witness = try def_ops.instantiateDefTowardExpr(
        def_expr,
        other_expr,
    ) orelse return null;
    const def_to_witness = try ProofEmit.emitTransparentRelationProof(
        self,
        relation,
        def_expr,
        witness,
    );
    const norm_witness = try Core.normalize(self, witness);
    if (norm_witness.result_expr == other_expr) {
        return .{
            .target_expr = other_expr,
            .lhs_conv_line_idx = try ProofEmit.composeTransitivity(
                self,
                relation,
                def_expr,
                witness,
                other_expr,
                def_to_witness,
                norm_witness.conv_line_idx,
            ),
            .rhs_conv_line_idx = null,
        };
    }

    const common = try buildCommonTarget(
        self,
        norm_witness.result_expr,
        other_expr,
    ) orelse return null;
    const witness_to_common = try ProofEmit.composeTransitivity(
        self,
        relation,
        witness,
        norm_witness.result_expr,
        common.target_expr,
        norm_witness.conv_line_idx,
        common.lhs_conv_line_idx,
    );
    return .{
        .target_expr = common.target_expr,
        .lhs_conv_line_idx = try ProofEmit.composeTransitivity(
            self,
            relation,
            def_expr,
            witness,
            common.target_expr,
            def_to_witness,
            witness_to_common,
        ),
        .rhs_conv_line_idx = common.rhs_conv_line_idx,
    };
}
