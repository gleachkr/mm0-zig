const ExprId = @import("../expr.zig").ExprId;
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
        .variable, .placeholder => self.theorem.currentLeafSortName(expr_id),
    };
}

pub fn resolveRelationForExpr(
    self: anytype,
    expr_id: ExprId,
) ?ResolvedRelation {
    const sort = getExprSort(self, expr_id) orelse return null;
    return self.registry.resolveRelation(self.env, sort);
}
