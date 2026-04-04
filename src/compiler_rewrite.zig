const std = @import("std");
const CompilerExpr = @import("./compiler_expr.zig");
const ExprId = CompilerExpr.ExprId;
const ExprInterner = CompilerExpr.ExprInterner;
const TheoremContext = CompilerExpr.TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;

pub const BundleId = u32;
pub const ConvId = u32;
pub const RuleIndex = u32;
pub const CongruenceIndex = u32;

pub const FailureInfo = struct {
    bundle_id: BundleId,
    expr_id: ExprId,
};

pub const CanonicalResult = struct {
    expr_id: ExprId,
    conv_id: ConvId,
};

pub const RelationBundle = struct {
    name: []const u8,
    sort_name: ?[]const u8 = null,
    relation_term_id: ?u32 = null,
};

pub const RewriteRule = struct {
    bundle_id: BundleId,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    binder_count: usize,
    priority: u32,
    rule_id: ?u32,
    name: ?[]const u8,

    fn deinit(self: *const RewriteRule, allocator: std.mem.Allocator) void {
        self.lhs.deinit(allocator);
        self.rhs.deinit(allocator);
    }
};

pub const CongruenceRule = struct {
    bundle_id: BundleId,
    term_id: u32,
    arg_bundles: []const BundleId,
    rule_id: ?u32,
    name: ?[]const u8,

    fn deinit(self: *const CongruenceRule, allocator: std.mem.Allocator) void {
        allocator.free(self.arg_bundles);
    }
};

pub const ConvNode = union(enum) {
    refl: ExprId,
    thm_step: ThmStep,
    symm: Symm,
    trans: Trans,
    congr: Congr,

    pub const ThmStep = struct {
        lhs: ExprId,
        rhs: ExprId,
        rule_id: ?u32,
        rule_name: ?[]const u8,
    };

    pub const Symm = struct {
        conv: ConvId,
        lhs: ExprId,
        rhs: ExprId,
    };

    pub const Trans = struct {
        left: ConvId,
        right: ConvId,
        lhs: ExprId,
        rhs: ExprId,
    };

    pub const Congr = struct {
        term_id: u32,
        lhs: ExprId,
        rhs: ExprId,
        arg_convs: []const ConvId,
    };

    fn deinit(self: *const ConvNode, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .congr => |congr| allocator.free(congr.arg_convs),
            else => {},
        }
    }
};

const CacheKey = struct {
    bundle_id: BundleId,
    expr_id: ExprId,
};

const CacheValue = struct {
    expr_id: ExprId,
    conv_id: ConvId,
};

const RewriteMatch = struct {
    rule_index: RuleIndex,
    bindings: []const ExprId,
};

pub const RewriteSystem = struct {
    allocator: std.mem.Allocator,
    bundles: std.ArrayListUnmanaged(RelationBundle) = .{},
    rewrite_rules: std.ArrayListUnmanaged(RewriteRule) = .{},
    congruence_rules: std.ArrayListUnmanaged(CongruenceRule) = .{},

    pub fn init(allocator: std.mem.Allocator) RewriteSystem {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *RewriteSystem) void {
        for (self.rewrite_rules.items) |*rule| {
            rule.deinit(self.allocator);
        }
        for (self.congruence_rules.items) |*rule| {
            rule.deinit(self.allocator);
        }
        self.bundles.deinit(self.allocator);
        self.rewrite_rules.deinit(self.allocator);
        self.congruence_rules.deinit(self.allocator);
    }

    pub fn addBundle(
        self: *RewriteSystem,
        name: []const u8,
        sort_name: ?[]const u8,
        relation_term_id: ?u32,
    ) !BundleId {
        try self.bundles.append(self.allocator, .{
            .name = name,
            .sort_name = sort_name,
            .relation_term_id = relation_term_id,
        });
        return std.math.cast(BundleId, self.bundles.items.len - 1) orelse {
            return error.TooManyRelationBundles;
        };
    }

    pub fn addRewriteRule(
        self: *RewriteSystem,
        bundle_id: BundleId,
        lhs: TemplateExpr,
        rhs: TemplateExpr,
        priority: u32,
        rule_id: ?u32,
        name: ?[]const u8,
    ) !RuleIndex {
        if (bundle_id >= self.bundles.items.len) return error.UnknownBundle;

        const lhs_copy = try lhs.clone(self.allocator);
        errdefer lhs_copy.deinit(self.allocator);
        const rhs_copy = try rhs.clone(self.allocator);
        errdefer rhs_copy.deinit(self.allocator);

        try self.rewrite_rules.append(self.allocator, .{
            .bundle_id = bundle_id,
            .lhs = lhs_copy,
            .rhs = rhs_copy,
            .binder_count = @max(lhs.binderCount(), rhs.binderCount()),
            .priority = priority,
            .rule_id = rule_id,
            .name = name,
        });
        return std.math.cast(RuleIndex, self.rewrite_rules.items.len - 1) orelse {
            return error.TooManyRewriteRules;
        };
    }

    pub fn addCongruenceRule(
        self: *RewriteSystem,
        bundle_id: BundleId,
        term_id: u32,
        arg_bundles: []const BundleId,
        rule_id: ?u32,
        name: ?[]const u8,
    ) !CongruenceIndex {
        if (bundle_id >= self.bundles.items.len) return error.UnknownBundle;
        const copied_bundles = try self.allocator.dupe(BundleId, arg_bundles);
        errdefer self.allocator.free(copied_bundles);
        try self.congruence_rules.append(self.allocator, .{
            .bundle_id = bundle_id,
            .term_id = term_id,
            .arg_bundles = copied_bundles,
            .rule_id = rule_id,
            .name = name,
        });
        return std.math.cast(
            CongruenceIndex,
            self.congruence_rules.items.len - 1,
        ) orelse {
            return error.TooManyCongruenceRules;
        };
    }

    fn findCongruenceRule(
        self: *const RewriteSystem,
        bundle_id: BundleId,
        term_id: u32,
    ) ?*const CongruenceRule {
        for (self.congruence_rules.items) |*rule| {
            if (rule.bundle_id != bundle_id) continue;
            if (rule.term_id != term_id) continue;
            return rule;
        }
        return null;
    }

    fn findBestRewriteMatch(
        self: *const RewriteSystem,
        allocator: std.mem.Allocator,
        interner: *const ExprInterner,
        bundle_id: BundleId,
        expr_id: ExprId,
    ) !?RewriteMatch {
        var best_index: ?RuleIndex = null;
        var best_priority: u32 = std.math.maxInt(u32);
        var best_bindings: ?[]const ExprId = null;

        for (self.rewrite_rules.items, 0..) |rule, idx| {
            if (rule.bundle_id != bundle_id) continue;

            const temp = try allocator.alloc(?ExprId, rule.binder_count);
            defer allocator.free(temp);
            @memset(temp, null);

            if (!matchTemplate(interner, rule.lhs, expr_id, temp)) continue;

            const concrete = try allocator.alloc(ExprId, temp.len);
            errdefer allocator.free(concrete);
            for (temp, 0..) |binding, binding_idx| {
                concrete[binding_idx] = binding orelse {
                    return error.UnboundRewriteBinder;
                };
            }

            const rule_index = std.math.cast(RuleIndex, idx) orelse {
                allocator.free(concrete);
                return error.TooManyRewriteRules;
            };
            const better = best_index == null or
                rule.priority < best_priority or
                (rule.priority == best_priority and rule_index < best_index.?);
            if (!better) {
                allocator.free(concrete);
                continue;
            }

            if (best_bindings) |bindings| allocator.free(bindings);
            best_index = rule_index;
            best_priority = rule.priority;
            best_bindings = concrete;
        }

        if (best_index) |rule_index| {
            return .{
                .rule_index = rule_index,
                .bindings = best_bindings.?,
            };
        }
        return null;
    }
};

pub const Canonicalizer = struct {
    allocator: std.mem.Allocator,
    system: *const RewriteSystem,
    theorem: *TheoremContext,
    conv_nodes: std.ArrayListUnmanaged(ConvNode) = .{},
    cache: std.AutoHashMapUnmanaged(CacheKey, CacheValue) = .empty,
    active: std.AutoHashMapUnmanaged(CacheKey, void) = .empty,
    step_cap: usize,
    step_count: usize = 0,
    last_failure: ?FailureInfo = null,

    pub fn init(
        allocator: std.mem.Allocator,
        system: *const RewriteSystem,
        theorem: *TheoremContext,
        step_cap: usize,
    ) Canonicalizer {
        return .{
            .allocator = allocator,
            .system = system,
            .theorem = theorem,
            .step_cap = step_cap,
        };
    }

    pub fn deinit(self: *Canonicalizer) void {
        for (self.conv_nodes.items) |*conv_node| {
            conv_node.deinit(self.allocator);
        }
        self.conv_nodes.deinit(self.allocator);
        self.cache.deinit(self.allocator);
        self.active.deinit(self.allocator);
    }

    pub fn canonicalize(
        self: *Canonicalizer,
        bundle_id: BundleId,
        expr_id: ExprId,
    ) anyerror!CanonicalResult {
        if (bundle_id >= self.system.bundles.items.len) return error.UnknownBundle;
        return try self.canonicalizeInner(bundle_id, expr_id);
    }

    pub fn node(self: *const Canonicalizer, conv_id: ConvId) *const ConvNode {
        return &self.conv_nodes.items[@intCast(conv_id)];
    }

    pub fn convLhs(self: *const Canonicalizer, conv_id: ConvId) ExprId {
        return switch (self.node(conv_id).*) {
            .refl => |expr_id| expr_id,
            .thm_step => |step| step.lhs,
            .symm => |symm| symm.lhs,
            .trans => |trans| trans.lhs,
            .congr => |congr| congr.lhs,
        };
    }

    pub fn convRhs(self: *const Canonicalizer, conv_id: ConvId) ExprId {
        return switch (self.node(conv_id).*) {
            .refl => |expr_id| expr_id,
            .thm_step => |step| step.rhs,
            .symm => |symm| symm.rhs,
            .trans => |trans| trans.rhs,
            .congr => |congr| congr.rhs,
        };
    }

    fn canonicalizeInner(
        self: *Canonicalizer,
        bundle_id: BundleId,
        expr_id: ExprId,
    ) anyerror!CanonicalResult {
        const key = CacheKey{ .bundle_id = bundle_id, .expr_id = expr_id };
        if (self.cache.get(key)) |cached| {
            return .{
                .expr_id = cached.expr_id,
                .conv_id = cached.conv_id,
            };
        }
        if (self.active.contains(key)) return error.RewriteCycleDetected;
        if (self.step_count >= self.step_cap) {
            self.last_failure = .{
                .bundle_id = bundle_id,
                .expr_id = expr_id,
            };
            return error.CanonicalizationStepLimitExceeded;
        }
        self.step_count += 1;

        try self.active.put(self.allocator, key, {});
        defer _ = self.active.remove(key);

        var current = expr_id;
        var total_conv = try self.pushRefl(expr_id);

        current = try self.applyCongruence(bundle_id, expr_id, &total_conv);

        if (try self.system.findBestRewriteMatch(
            self.allocator,
            &self.theorem.interner,
            bundle_id,
            current,
        )) |matched| {
            defer self.allocator.free(matched.bindings);
            const rule = self.system.rewrite_rules.items[matched.rule_index];
            const next = try self.theorem.instantiateTemplate(
                rule.rhs,
                matched.bindings,
            );
            const step_conv = try self.pushThmStep(
                current,
                next,
                rule.rule_id,
                rule.name,
            );
            total_conv = try self.pushTrans(total_conv, step_conv);
            const tail = try self.canonicalizeInner(bundle_id, next);
            total_conv = try self.pushTrans(total_conv, tail.conv_id);
            current = tail.expr_id;
        }

        const result = CanonicalResult{
            .expr_id = current,
            .conv_id = total_conv,
        };
        try self.cache.put(self.allocator, key, .{
            .expr_id = result.expr_id,
            .conv_id = result.conv_id,
        });
        return result;
    }

    fn applyCongruence(
        self: *Canonicalizer,
        bundle_id: BundleId,
        expr_id: ExprId,
        total_conv: *ConvId,
    ) anyerror!ExprId {
        const expr_node = self.theorem.interner.node(expr_id);
        const app = switch (expr_node.*) {
            .variable => return expr_id,
            .app => |app| app,
        };

        const rule = self.system.findCongruenceRule(bundle_id, app.term_id) orelse {
            return expr_id;
        };
        if (rule.arg_bundles.len != app.args.len) {
            return error.CongruenceArityMismatch;
        }

        const new_args = try self.allocator.alloc(ExprId, app.args.len);
        errdefer self.allocator.free(new_args);
        const arg_convs = try self.allocator.alloc(ConvId, app.args.len);
        errdefer self.allocator.free(arg_convs);

        var changed = false;
        for (app.args, rule.arg_bundles, 0..) |arg_id, arg_bundle, idx| {
            const result = try self.canonicalizeInner(arg_bundle, arg_id);
            new_args[idx] = result.expr_id;
            arg_convs[idx] = result.conv_id;
            if (result.expr_id != arg_id) changed = true;
        }

        if (!changed) {
            self.allocator.free(new_args);
            self.allocator.free(arg_convs);
            return expr_id;
        }

        const rebuilt = try self.theorem.interner.internAppOwned(
            app.term_id,
            new_args,
        );
        const congr = try self.pushCongruenceOwned(
            app.term_id,
            expr_id,
            rebuilt,
            arg_convs,
        );
        total_conv.* = try self.pushTrans(total_conv.*, congr);
        return rebuilt;
    }

    fn pushNode(self: *Canonicalizer, conv_node: ConvNode) !ConvId {
        try self.conv_nodes.append(self.allocator, conv_node);
        return std.math.cast(ConvId, self.conv_nodes.items.len - 1) orelse {
            return error.TooManyConvNodes;
        };
    }

    fn pushRefl(self: *Canonicalizer, expr_id: ExprId) !ConvId {
        return try self.pushNode(.{ .refl = expr_id });
    }

    pub fn pushSymm(self: *Canonicalizer, conv_id: ConvId) !ConvId {
        if (self.isRefl(conv_id)) return conv_id;
        return try self.pushNode(.{ .symm = .{
            .conv = conv_id,
            .lhs = self.convRhs(conv_id),
            .rhs = self.convLhs(conv_id),
        } });
    }

    fn pushThmStep(
        self: *Canonicalizer,
        lhs: ExprId,
        rhs: ExprId,
        rule_id: ?u32,
        rule_name: ?[]const u8,
    ) !ConvId {
        if (lhs == rhs) return try self.pushRefl(lhs);
        return try self.pushNode(.{ .thm_step = .{
            .lhs = lhs,
            .rhs = rhs,
            .rule_id = rule_id,
            .rule_name = rule_name,
        } });
    }

    fn pushTrans(
        self: *Canonicalizer,
        left: ConvId,
        right: ConvId,
    ) !ConvId {
        if (self.isRefl(left)) return right;
        if (self.isRefl(right)) return left;
        if (self.convRhs(left) != self.convLhs(right)) {
            return error.ConversionMismatch;
        }
        return try self.pushNode(.{ .trans = .{
            .left = left,
            .right = right,
            .lhs = self.convLhs(left),
            .rhs = self.convRhs(right),
        } });
    }

    fn pushCongruenceOwned(
        self: *Canonicalizer,
        term_id: u32,
        lhs: ExprId,
        rhs: ExprId,
        arg_convs: []ConvId,
    ) !ConvId {
        if (lhs == rhs) {
            self.allocator.free(arg_convs);
            return try self.pushRefl(lhs);
        }
        return try self.pushNode(.{ .congr = .{
            .term_id = term_id,
            .lhs = lhs,
            .rhs = rhs,
            .arg_convs = arg_convs,
        } });
    }

    fn isRefl(self: *const Canonicalizer, conv_id: ConvId) bool {
        return switch (self.node(conv_id).*) {
            .refl => true,
            else => false,
        };
    }
};

fn matchTemplate(
    interner: *const ExprInterner,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
) bool {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len) break :blk false;
            if (bindings[idx]) |bound_expr| {
                break :blk bound_expr == expr_id;
            }
            bindings[idx] = expr_id;
            break :blk true;
        },
        .app => |app| blk: {
            const node = interner.node(expr_id);
            const expr_app = switch (node.*) {
                .app => |expr_app| expr_app,
                .variable => break :blk false,
            };
            if (app.term_id != expr_app.term_id) break :blk false;
            if (app.args.len != expr_app.args.len) break :blk false;
            for (app.args, expr_app.args) |arg_template, arg_expr| {
                if (!matchTemplate(interner, arg_template, arg_expr, bindings)) {
                    break :blk false;
                }
            }
            break :blk true;
        },
    };
}
