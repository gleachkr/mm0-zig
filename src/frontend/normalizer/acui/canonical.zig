const ExprId = @import("../../compiler_expr.zig").ExprId;
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const ProofEmit = @import("../proof_emit.zig");
const Insert = @import("./insert.zig");
const Types = @import("../types.zig");

const NormalizeResult = Types.NormalizeResult;

pub fn mergeCanonical(
    self: anytype,
    current_expr: ExprId,
    left: ExprId,
    right: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!NormalizeResult {
    const unit_expr = try ProofEmit.unitExpr(self, acui);
    if (left == unit_expr) {
        return .{
            .result_expr = right,
            .conv_line_idx = try ProofEmit.emitLeftUnit(
                self,
                current_expr,
                right,
                relation,
                acui,
            ),
        };
    }

    const left_node = self.theorem.interner.node(left);
    switch (left_node.*) {
        .app => |left_app| {
            if (left_app.term_id == acui.head_term_id and
                left_app.args.len == 2)
            {
                const tail_expr = try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ left_app.args[1], right },
                );
                const assoc_target = try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ left_app.args[0], tail_expr },
                );
                const assoc_idx = try ProofEmit.emitAssoc(
                    self,
                    left_app.args[0],
                    left_app.args[1],
                    right,
                    relation,
                    acui,
                );
                const merged_tail = try mergeCanonical(
                    self,
                    tail_expr,
                    left_app.args[1],
                    right,
                    relation,
                    acui,
                );
                const lifted_tail = if (merged_tail.conv_line_idx) |tail_idx|
                    try ProofEmit.emitCongruenceLine(
                        self,
                        acui.head_term_id,
                        &[_]ExprId{ left_app.args[0], tail_expr },
                        &[_]ExprId{
                            left_app.args[0],
                            merged_tail.result_expr,
                        },
                        &[_]?usize{ null, tail_idx },
                    )
                else
                    null;
                const after_tail = if (merged_tail.result_expr == tail_expr)
                    assoc_target
                else
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{
                            left_app.args[0],
                            merged_tail.result_expr,
                        },
                    );
                const inserted = try Insert.insertItem(
                    self,
                    after_tail,
                    left_app.args[0],
                    merged_tail.result_expr,
                    relation,
                    acui,
                );
                const first = try ProofEmit.composeTransitivity(
                    self,
                    relation,
                    current_expr,
                    assoc_target,
                    after_tail,
                    assoc_idx,
                    lifted_tail,
                );
                const proof = try ProofEmit.composeTransitivity(
                    self,
                    relation,
                    current_expr,
                    after_tail,
                    inserted.result_expr,
                    first,
                    inserted.conv_line_idx,
                );
                return .{
                    .result_expr = inserted.result_expr,
                    .conv_line_idx = proof,
                };
            }
        },
        .variable => {},
    }

    return try Insert.insertItem(
        self,
        current_expr,
        left,
        right,
        relation,
        acui,
    );
}
