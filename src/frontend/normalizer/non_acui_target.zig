const ExprId = @import("../compiler_expr.zig").ExprId;
const ProofEmit = @import("./proof_emit.zig");
const Types = @import("./types.zig");

const CommonTargetResult = Types.CommonTargetResult;

pub fn buildNonAcuiCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    const lhs_node = self.theorem.interner.node(lhs);
    const rhs_node = self.theorem.interner.node(rhs);
    const lhs_app = switch (lhs_node.*) {
        .app => |value| value,
        .variable => return null,
    };
    const rhs_app = switch (rhs_node.*) {
        .app => |value| value,
        .variable => return null,
    };
    if (lhs_app.term_id != rhs_app.term_id or
        lhs_app.args.len != rhs_app.args.len)
    {
        return null;
    }

    const target_args = try self.allocator.alloc(ExprId, lhs_app.args.len);
    const lhs_child_proofs =
        try self.allocator.alloc(?usize, lhs_app.args.len);
    const rhs_child_proofs =
        try self.allocator.alloc(?usize, lhs_app.args.len);
    var any_changed = false;
    for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
        if (lhs_arg == rhs_arg) {
            target_args[idx] = lhs_arg;
            lhs_child_proofs[idx] = null;
            rhs_child_proofs[idx] = null;
            continue;
        }
        const child = try self.buildCommonTarget(lhs_arg, rhs_arg) orelse {
            return null;
        };
        target_args[idx] = child.target_expr;
        lhs_child_proofs[idx] = child.lhs_conv_line_idx;
        rhs_child_proofs[idx] = child.rhs_conv_line_idx;
        any_changed = true;
    }
    if (!any_changed) {
        return null;
    }

    const target_expr = try self.theorem.interner.internApp(
        lhs_app.term_id,
        target_args,
    );
    return .{
        .target_expr = target_expr,
        .lhs_conv_line_idx = try ProofEmit.emitCongruenceLine(
            self,
            lhs_app.term_id,
            lhs_app.args,
            target_args,
            lhs_child_proofs,
        ),
        .rhs_conv_line_idx = try ProofEmit.emitCongruenceLine(
            self,
            rhs_app.term_id,
            rhs_app.args,
            target_args,
            rhs_child_proofs,
        ),
    };
}
