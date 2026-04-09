const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const RewriteRule = @import("./rewrite_registry.zig").RewriteRule;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const AcuiSupport = @import("./acui_support.zig");

pub const compareExprIds = AcuiSupport.compareExprIds;

pub const Canonicalizer = struct {
    pub const Error = anyerror;

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

    fn acuiSupport(self: *Canonicalizer) AcuiSupport.Context {
        return AcuiSupport.Context.init(
            self.allocator,
            self.theorem,
            self.env,
            self.registry,
        );
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
        var support = self.acuiSupport();
        return try support.canonicalizeAcui(expr_id, acui);
    }
};
