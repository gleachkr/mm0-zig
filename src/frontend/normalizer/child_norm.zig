const ExprId = @import("../expr.zig").ExprId;
const ExprNode = @import("../expr.zig").ExprNode;
const ProofEmit = @import("./proof_emit.zig");
const Types = @import("./types.zig");

const NormalizeResult = Types.NormalizeResult;

pub fn normalizeChildren(
    self: anytype,
    expr_id: ExprId,
    app: ExprNode.App,
) anyerror!NormalizeResult {
    const new_args = try self.allocator.alloc(ExprId, app.args.len);
    defer self.allocator.free(new_args);
    const child_proofs = try self.allocator.alloc(?usize, app.args.len);
    defer self.allocator.free(child_proofs);

    var any_changed = false;
    for (app.args, 0..) |arg, idx| {
        const child_result = try self.normalize(arg);
        new_args[idx] = child_result.result_expr;
        child_proofs[idx] = child_result.conv_line_idx;
        any_changed = any_changed or child_result.result_expr != arg;
    }

    if (!any_changed) {
        return .{
            .result_expr = expr_id,
            .conv_line_idx = null,
        };
    }

    const new_expr = try self.theorem.interner.internApp(app.term_id, new_args);
    const proof = try ProofEmit.emitCongruenceLine(
        self,
        app.term_id,
        app.args,
        new_args,
        child_proofs,
    );
    return .{
        .result_expr = new_expr,
        .conv_line_idx = proof,
    };
}
