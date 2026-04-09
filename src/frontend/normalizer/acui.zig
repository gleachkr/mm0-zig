const ExprId = @import("../compiler_expr.zig").ExprId;
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../rewrite_registry.zig").ResolvedStructuralCombiner;
const Target = @import("./acui/target.zig");
const Normalize = @import("./acui/normalize.zig");
const Types = @import("./types.zig");

const NormalizeResult = Types.NormalizeResult;
const CommonTargetResult = Types.CommonTargetResult;

pub fn buildAcuiCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    return try Target.buildAcuiCommonTarget(self, lhs, rhs);
}

pub fn normalizeStructural(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!NormalizeResult {
    return try Normalize.normalizeStructural(self, expr_id, relation, acui);
}
