const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const RewriteRule = @import("./rewrite_registry.zig").RewriteRule;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;

pub const Canonicalizer = struct {
    pub const Error = error{
        OutOfMemory,
        TemplateBinderOutOfRange,
        TooManyTheoremExprs,
        UnknownSort,
        Overflow,
    };

    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    cache: std.AutoHashMap(ExprId, ExprId),
    step_count: usize = 0,
    step_limit: usize = 1000,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        env: *const GlobalEnv,
    ) Canonicalizer {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = registry,
            .cache = std.AutoHashMap(ExprId, ExprId).init(allocator),
        };
    }

    pub fn canonicalize(
        self: *Canonicalizer,
        expr_id: ExprId,
    ) Error!ExprId {
        if (self.cache.get(expr_id)) |cached| {
            return cached;
        }
        const result = try self.canonicalizeUncached(expr_id);
        try self.cache.put(expr_id, result);
        return result;
    }

    fn canonicalizeUncached(
        self: *Canonicalizer,
        expr_id: ExprId,
    ) Error!ExprId {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .variable => expr_id,
            .app => |app| blk: {
                const new_args = try self.allocator.alloc(ExprId, app.args.len);
                defer self.allocator.free(new_args);

                var changed = false;
                for (app.args, 0..) |arg, idx| {
                    new_args[idx] = try self.canonicalize(arg);
                    changed = changed or new_args[idx] != arg;
                }

                const current = if (changed)
                    try self.theorem.interner.internApp(app.term_id, new_args)
                else
                    expr_id;

                break :blk if (self.registry.resolveStructuralCombiner(
                    self.env,
                    app.term_id,
                )) |acui|
                    try self.canonicalizeAcui(current, acui)
                else
                    try self.canonicalizeRewrite(current);
            },
        };
    }

    fn canonicalizeRewrite(
        self: *Canonicalizer,
        expr_id: ExprId,
    ) Error!ExprId {
        var current = expr_id;
        while (self.step_count < self.step_limit) {
            const node = self.theorem.interner.node(current);
            const head_id = switch (node.*) {
                .app => |app| app.term_id,
                .variable => break,
            };
            const rules = self.registry.getRewriteRules(head_id);
            var changed = false;
            for (rules) |rule| {
                if (try self.tryApplyRule(current, rule)) |next| {
                    self.step_count += 1;
                    current = try self.canonicalize(next);
                    changed = true;
                    break;
                }
            }
            if (!changed) break;
        }
        return current;
    }

    fn tryApplyRule(
        self: *Canonicalizer,
        expr_id: ExprId,
        rule: RewriteRule,
    ) Error!?ExprId {
        const bindings = try self.allocator.alloc(?ExprId, rule.num_binders);
        defer self.allocator.free(bindings);
        @memset(bindings, null);

        if (!self.theorem.matchTemplate(rule.lhs, expr_id, bindings)) {
            return null;
        }

        const concrete = try self.allocator.alloc(ExprId, rule.num_binders);
        defer self.allocator.free(concrete);
        for (bindings, 0..) |binding, idx| {
            concrete[idx] = binding orelse return null;
        }
        return try self.theorem.instantiateTemplate(rule.rhs, concrete);
    }

    fn canonicalizeAcui(
        self: *Canonicalizer,
        expr_id: ExprId,
        acui: ResolvedStructuralCombiner,
    ) Error!ExprId {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            else => return expr_id,
        };
        if (app.term_id != acui.head_term_id or app.args.len != 2) {
            return expr_id;
        }
        return try self.mergeCanonical(app.args[0], app.args[1], acui);
    }

    fn mergeCanonical(
        self: *Canonicalizer,
        left: ExprId,
        right: ExprId,
        acui: ResolvedStructuralCombiner,
    ) Error!ExprId {
        if (left == try self.unitExpr(acui)) return right;

        const left_node = self.theorem.interner.node(left);
        return switch (left_node.*) {
            .app => |left_app| if (left_app.term_id == acui.head_term_id and
                left_app.args.len == 2)
            blk: {
                const merged_tail = try self.mergeCanonical(
                    left_app.args[1],
                    right,
                    acui,
                );
                break :blk try self.insertItem(
                    left_app.args[0],
                    merged_tail,
                    acui,
                );
            } else try self.insertItem(left, right, acui),
            .variable => try self.insertItem(left, right, acui),
        };
    }

    fn insertItem(
        self: *Canonicalizer,
        item: ExprId,
        canon: ExprId,
        acui: ResolvedStructuralCombiner,
    ) !ExprId {
        const unit_expr = try self.unitExpr(acui);
        if (item == unit_expr) return canon;
        if (canon == unit_expr) return item;

        const canon_node = self.theorem.interner.node(canon);
        return switch (canon_node.*) {
            .variable => blk: {
                const cmp = compareExprIds(self.theorem, item, canon);
                if (cmp == .gt and acui.comm_id != null) {
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ canon, item },
                    );
                }
                if (cmp == .eq and acui.idem_id != null) break :blk canon;
                break :blk try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ item, canon },
                );
            },
            .app => |canon_app| blk: {
                if (canon_app.term_id != acui.head_term_id or
                    canon_app.args.len != 2)
                {
                    const cmp = compareExprIds(self.theorem, item, canon);
                    if (cmp == .gt and acui.comm_id != null) {
                        break :blk try self.theorem.interner.internApp(
                            acui.head_term_id,
                            &[_]ExprId{ canon, item },
                        );
                    }
                    if (cmp == .eq and acui.idem_id != null) break :blk canon;
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ item, canon },
                    );
                }

                const head = canon_app.args[0];
                const rest = canon_app.args[1];
                const cmp = compareExprIds(self.theorem, item, head);
                if (cmp == .eq and acui.idem_id != null) break :blk canon;
                if (cmp != .gt or acui.comm_id == null) {
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ item, canon },
                    );
                }
                const inserted = try self.insertItem(item, rest, acui);
                break :blk try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ head, inserted },
                );
            },
        };
    }

    fn unitExpr(
        self: *Canonicalizer,
        acui: ResolvedStructuralCombiner,
    ) Error!ExprId {
        return try self.theorem.interner.internApp(acui.unit_term_id, &.{});
    }
};

pub fn compareExprIds(
    theorem: *const TheoremContext,
    lhs: ExprId,
    rhs: ExprId,
) std.math.Order {
    if (lhs == rhs) return .eq;
    const lhs_node = theorem.interner.node(lhs);
    const rhs_node = theorem.interner.node(rhs);
    return switch (lhs_node.*) {
        .variable => |lhs_var| switch (rhs_node.*) {
            .variable => |rhs_var| compareVarIds(lhs_var, rhs_var),
            .app => .lt,
        },
        .app => |lhs_app| switch (rhs_node.*) {
            .variable => .gt,
            .app => |rhs_app| blk: {
                const term_cmp = std.math.order(lhs_app.term_id, rhs_app.term_id);
                if (term_cmp != .eq) break :blk term_cmp;
                const len_cmp = std.math.order(lhs_app.args.len, rhs_app.args.len);
                if (len_cmp != .eq) break :blk len_cmp;
                for (lhs_app.args, rhs_app.args) |l_arg, r_arg| {
                    const cmp = compareExprIds(theorem, l_arg, r_arg);
                    if (cmp != .eq) break :blk cmp;
                }
                break :blk .eq;
            },
        },
    };
}

fn compareVarIds(lhs: anytype, rhs: @TypeOf(lhs)) std.math.Order {
    return switch (lhs) {
        .theorem_var => |lhs_id| switch (rhs) {
            .theorem_var => |rhs_id| std.math.order(lhs_id, rhs_id),
            .dummy_var => .lt,
        },
        .dummy_var => |lhs_id| switch (rhs) {
            .theorem_var => .gt,
            .dummy_var => |rhs_id| std.math.order(lhs_id, rhs_id),
        },
    };
}
