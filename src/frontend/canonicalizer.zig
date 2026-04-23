const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const BindingValidation = @import("./binding_validation.zig");
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
            .placeholder => expr_id,
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

                break :blk if (try self.registry.resolveStructuralCombiner(
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
                .placeholder => break,
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
        if (!try self.validateRewriteBindings(rule, concrete)) {
            return null;
        }
        return try self.theorem.instantiateTemplate(rule.rhs, concrete);
    }

    fn validateRewriteBindings(
        self: *Canonicalizer,
        rule: RewriteRule,
        bindings: []const ExprId,
    ) Error!bool {
        if (rule.rule_id >= self.env.rules.items.len) return false;
        const rule_decl = &self.env.rules.items[rule.rule_id];

        var infos: [56]BindingValidation.ExprInfo = undefined;
        std.debug.assert(bindings.len <= infos.len);
        for (bindings, 0..) |binding, idx| {
            infos[idx] = try BindingValidation.currentExprInfo(
                self.env,
                self.theorem,
                binding,
            );
        }
        return BindingValidation.firstViolation(
            rule_decl.args,
            infos[0..bindings.len],
        ) == null;
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

test "canonicalizer rejects rewrite bindings with forbidden deps" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);

    const TemplateExpr = @import("./rules.zig").TemplateExpr;
    const arr_term_id: u32 = 0;
    const sb_ty_term_id: u32 = 1;
    try env.term_names.put("arr", arr_term_id);
    try env.term_names.put("sb_ty", sb_ty_term_id);
    try env.terms.append(allocator, .{
        .name = "arr",
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .ret_sort_name = "ty",
        .is_def = false,
        .body = null,
    });
    try env.terms.append(allocator, .{
        .name = "sb_ty",
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .ret_sort_name = "ty",
        .is_def = false,
        .body = null,
    });

    const lhs: TemplateExpr = .{ .app = .{
        .term_id = sb_ty_term_id,
        .args = try allocator.dupe(TemplateExpr, &.{
            TemplateExpr{ .binder = 0 },
            TemplateExpr{ .binder = 1 },
            TemplateExpr{ .app = .{
                .term_id = arr_term_id,
                .args = try allocator.dupe(TemplateExpr, &.{
                    TemplateExpr{ .binder = 2 },
                    TemplateExpr{ .binder = 3 },
                }),
            } },
        }),
    } };
    const rhs: TemplateExpr = .{ .app = .{
        .term_id = arr_term_id,
        .args = try allocator.dupe(TemplateExpr, &.{
            TemplateExpr{ .binder = 2 },
            TemplateExpr{ .binder = 3 },
        }),
    } };

    const rule_args = try allocator.dupe(ArgInfo, &.{
        ArgInfo{ .sort_name = "tm", .bound = true, .deps = 0 },
        ArgInfo{ .sort_name = "tm", .bound = false, .deps = 1 },
        ArgInfo{ .sort_name = "ty", .bound = false, .deps = 0 },
        ArgInfo{ .sort_name = "ty", .bound = false, .deps = 0 },
    });
    try env.rule_names.put("sb_ty_arr", 0);
    try env.rules.append(allocator, .{
        .name = "sb_ty_arr",
        .args = rule_args,
        .arg_names = &.{},
        .hyps = &.{},
        .concl = lhs,
        .kind = .axiom,
        .is_local = false,
    });

    var rules = std.ArrayListUnmanaged(RewriteRule){};
    try rules.append(allocator, .{
        .rule_id = 0,
        .lhs = lhs,
        .rhs = rhs,
        .num_binders = rule_args.len,
        .head_term_id = sb_ty_term_id,
    });
    try registry.rewrites_by_head.put(sb_ty_term_id, rules);

    var theorem = TheoremContext.init(allocator);
    const theorem_args = [_]ArgInfo{
        .{ .sort_name = "tm", .bound = true, .deps = 1 },
        .{ .sort_name = "tm", .bound = false, .deps = 1 },
        .{ .sort_name = "ty", .bound = false, .deps = 1 },
        .{ .sort_name = "ty", .bound = false, .deps = 1 },
    };
    theorem.arg_infos = &theorem_args;
    try theorem.seedBinderCount(theorem_args.len);

    const x = theorem.theorem_vars.items[0];
    const u = theorem.theorem_vars.items[1];
    const a = theorem.theorem_vars.items[2];
    const b = theorem.theorem_vars.items[3];

    const arr_expr = try theorem.interner.internApp(arr_term_id, &.{ a, b });
    const expr = try theorem.interner.internApp(
        sb_ty_term_id,
        &.{ x, u, arr_expr },
    );

    var canonicalizer = Canonicalizer.init(
        allocator,
        &theorem,
        &registry,
        &env,
    );

    try std.testing.expectEqual(expr, try canonicalizer.canonicalize(expr));
}
