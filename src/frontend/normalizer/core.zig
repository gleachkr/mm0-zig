const ExprId = @import("../expr.zig").ExprId;
const ChildNorm = @import("./child_norm.zig");
const Support = @import("./support.zig");
const Acui = @import("./acui.zig");
const ProofEmit = @import("./proof_emit.zig");
const Types = @import("./types.zig");

const NormalizeResult = Types.NormalizeResult;

pub fn normalize(self: anytype, expr_id: ExprId) anyerror!NormalizeResult {
    if (self.cache.get(expr_id)) |cached| {
        return cached;
    }

    const result = try normalizeUncached(self, expr_id);
    try self.cache.put(expr_id, result);
    return result;
}

pub fn normalizeUncached(
    self: anytype,
    expr_id: ExprId,
) anyerror!NormalizeResult {
    const node = self.theorem.interner.node(expr_id);

    const child_result = switch (node.*) {
        .app => |app| try ChildNorm.normalizeChildren(self, expr_id, app),
        .variable => NormalizeResult{
            .result_expr = expr_id,
            .conv_line_idx = null,
        },
    };

    const relation = Support.resolveRelationForExpr(self, expr_id) orelse {
        return child_result;
    };

    var current = child_result.result_expr;
    var current_proof = child_result.conv_line_idx;

    while (true) {
        const current_node = self.theorem.interner.node(current);
        if (current_node.* != .app) break;
        const app = current_node.app;
        const acui = self.registry.resolveStructuralCombiner(
            self.env,
            app.term_id,
        ) orelse break;
        const structural = try Acui.normalizeStructural(
            self,
            current,
            relation,
            acui,
        );
        if (structural.result_expr == current and
            structural.conv_line_idx == null)
        {
            break;
        }
        current_proof = try ProofEmit.composeTransitivity(
            self,
            relation,
            expr_id,
            current,
            structural.result_expr,
            current_proof,
            structural.conv_line_idx,
        );
        current = structural.result_expr;
    }

    while (true) {
        const cur_node = self.theorem.interner.node(current);
        const head_id = switch (cur_node.*) {
            .app => |app| app.term_id,
            .variable => break,
        };

        const rules = self.registry.getRewriteRules(head_id);
        var applied = false;
        for (rules) |rule| {
            if (self.step_count >= self.step_limit) break;

            const match_result = try ProofEmit.tryApplyRule(
                self,
                relation,
                current,
                rule,
            );
            if (match_result) |step_result| {
                self.step_count += 1;
                const rhs_norm = try normalize(self, step_result.result_expr);
                const rhs_proof = try ProofEmit.composeTransitivity(
                    self,
                    relation,
                    current,
                    step_result.result_expr,
                    rhs_norm.result_expr,
                    step_result.conv_line_idx,
                    rhs_norm.conv_line_idx,
                );
                current_proof = try ProofEmit.composeTransitivity(
                    self,
                    relation,
                    expr_id,
                    current,
                    rhs_norm.result_expr,
                    current_proof,
                    rhs_proof,
                );
                current = rhs_norm.result_expr;
                applied = true;
                break;
            }
        }
        if (!applied) break;
    }

    return .{
        .result_expr = current,
        .conv_line_idx = current_proof,
    };
}
