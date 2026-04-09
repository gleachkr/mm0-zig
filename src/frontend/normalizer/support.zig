const ExprId = @import("../compiler_expr.zig").ExprId;
const AcuiSupport = @import("../acui_support.zig");
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;

pub fn acuiSupport(self: anytype) AcuiSupport.Context {
    return AcuiSupport.Context.init(
        self.allocator,
        self.theorem,
        self.env,
        self.registry,
    );
}

pub fn getExprSort(self: anytype, expr_id: ExprId) ?[]const u8 {
    const node = self.theorem.interner.node(expr_id);
    return switch (node.*) {
        .app => |app| if (app.term_id < self.env.terms.items.len)
            self.env.terms.items[app.term_id].ret_sort_name
        else
            null,
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| if (idx < self.theorem.arg_infos.len)
                self.theorem.arg_infos[idx].sort_name
            else
                null,
            .dummy_var => |idx| if (idx < self.theorem.theorem_dummies.items.len)
                self.theorem.theorem_dummies.items[idx].sort_name
            else
                null,
        },
    };
}

pub fn resolveRelationForExpr(
    self: anytype,
    expr_id: ExprId,
) ?ResolvedRelation {
    const sort = getExprSort(self, expr_id) orelse return null;
    return self.registry.resolveRelation(self.env, sort);
}
