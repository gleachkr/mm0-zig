const std = @import("std");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation = @import("./rewrite_registry.zig").ResolvedRelation;
const RewriteRule = @import("./rewrite_registry.zig").RewriteRule;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const AcuiSupport = @import("./acui_support.zig");
const compareExprIds = AcuiSupport.compareExprIds;
const DefOps = @import("./def_ops.zig");

const CheckedRef = @import("./compiler.zig").CheckedRef;
const CheckedLine = @import("./compiler.zig").CheckedLine;
const appendRuleLine = @import("./compiler.zig").appendRuleLine;
const appendTransportLine = @import("./compiler.zig").appendTransportLine;

pub const NormalizeResult = struct {
    result_expr: ExprId,
    /// Index into the lines array of the conversion proof line,
    /// or null if the expression is unchanged (refl).
    conv_line_idx: ?usize,
};

pub const CommonTargetResult = struct {
    target_expr: ExprId,
    lhs_conv_line_idx: ?usize,
    rhs_conv_line_idx: ?usize,
};

const AcuiLeaf = struct {
    old_expr: ExprId,
    new_expr: ExprId,
    is_def: bool,
    conv_line_idx: ?usize = null,
};

pub const Normalizer = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    lines: *std.ArrayListUnmanaged(CheckedLine),
    cache: std.AutoHashMap(ExprId, NormalizeResult),
    step_count: usize = 0,
    step_limit: usize = 1000,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        env: *const GlobalEnv,
        lines: *std.ArrayListUnmanaged(CheckedLine),
    ) Normalizer {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = registry,
            .lines = lines,
            .cache = std.AutoHashMap(ExprId, NormalizeResult).init(allocator),
        };
    }

    pub const Error = anyerror;

    fn acuiSupport(self: *Normalizer) AcuiSupport.Context {
        return AcuiSupport.Context.init(
            self.allocator,
            self.theorem,
            self.env,
            self.registry,
        );
    }

    pub fn normalize(self: *Normalizer, expr_id: ExprId) Error!NormalizeResult {
        if (self.cache.get(expr_id)) |cached| {
            return cached;
        }

        const result = try self.normalizeUncached(expr_id);
        try self.cache.put(expr_id, result);
        return result;
    }

    fn getExprSort(self: *const Normalizer, expr_id: ExprId) ?[]const u8 {
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
        self: *Normalizer,
        expr_id: ExprId,
    ) ?ResolvedRelation {
        const sort = self.getExprSort(expr_id) orelse return null;
        return self.registry.resolveRelation(self.env, sort);
    }

    pub fn buildCommonTarget(
        self: *Normalizer,
        lhs: ExprId,
        rhs: ExprId,
    ) Error!?CommonTargetResult {
        if (lhs == rhs) {
            return .{
                .target_expr = lhs,
                .lhs_conv_line_idx = null,
                .rhs_conv_line_idx = null,
            };
        }

        if (try self.buildDirectTransparentCommonTarget(lhs, rhs)) |direct| {
            return direct;
        }
        if (try self.buildAcuiCommonTarget(lhs, rhs)) |acui| {
            return acui;
        }
        return try self.buildNonAcuiCommonTarget(lhs, rhs);
    }

    fn buildNonAcuiCommonTarget(
        self: *Normalizer,
        lhs: ExprId,
        rhs: ExprId,
    ) Error!?CommonTargetResult {
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
        const lhs_child_proofs = try self.allocator.alloc(?usize, lhs_app.args.len);
        const rhs_child_proofs = try self.allocator.alloc(?usize, lhs_app.args.len);
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
            .lhs_conv_line_idx = try self.emitCongruenceLine(
                lhs_app.term_id,
                lhs_app.args,
                target_args,
                lhs_child_proofs,
            ),
            .rhs_conv_line_idx = try self.emitCongruenceLine(
                rhs_app.term_id,
                rhs_app.args,
                target_args,
                rhs_child_proofs,
            ),
        };
    }

    fn buildDirectTransparentCommonTarget(
        self: *Normalizer,
        lhs: ExprId,
        rhs: ExprId,
    ) Error!?CommonTargetResult {
        const relation = self.resolveRelationForExpr(lhs) orelse return null;

        var def_ops = DefOps.Context.init(
            self.allocator,
            self.theorem,
            self.env,
        );
        defer def_ops.deinit();

        if ((try def_ops.planConversionByDefOpening(lhs, rhs)) != null) {
            return .{
                .target_expr = rhs,
                .lhs_conv_line_idx = try self.emitTransparentRelationProof(
                    relation,
                    lhs,
                    rhs,
                ),
                .rhs_conv_line_idx = null,
            };
        }
        if ((try def_ops.planConversionByDefOpening(rhs, lhs)) != null) {
            return .{
                .target_expr = lhs,
                .lhs_conv_line_idx = null,
                .rhs_conv_line_idx = try self.emitTransparentRelationProof(
                    relation,
                    rhs,
                    lhs,
                ),
            };
        }
        return null;
    }

    fn buildAcuiCommonTarget(
        self: *Normalizer,
        lhs: ExprId,
        rhs: ExprId,
    ) Error!?CommonTargetResult {
        const relation = self.resolveRelationForExpr(lhs) orelse return null;
        const acui = self.sharedStructuralCombiner(lhs, rhs) orelse return null;

        var lhs_leaves = std.ArrayListUnmanaged(AcuiLeaf){};
        defer lhs_leaves.deinit(self.allocator);
        var rhs_leaves = std.ArrayListUnmanaged(AcuiLeaf){};
        defer rhs_leaves.deinit(self.allocator);
        try self.collectAcuiLeaves(lhs, acui.head_term_id, &lhs_leaves);
        try self.collectAcuiLeaves(rhs, acui.head_term_id, &rhs_leaves);

        const lhs_exact = try self.allocator.alloc(bool, lhs_leaves.items.len);
        const rhs_exact = try self.allocator.alloc(bool, rhs_leaves.items.len);
        const lhs_claimed = try self.allocator.alloc(bool, lhs_leaves.items.len);
        const rhs_claimed = try self.allocator.alloc(bool, rhs_leaves.items.len);
        @memset(lhs_exact, false);
        @memset(rhs_exact, false);
        @memset(lhs_claimed, false);
        @memset(rhs_claimed, false);

        var common_items = std.ArrayListUnmanaged(ExprId){};
        defer common_items.deinit(self.allocator);
        try self.cancelExactAcuiItems(
            lhs_leaves.items,
            rhs_leaves.items,
            lhs_exact,
            rhs_exact,
            &common_items,
        );
        try self.pairCommonAcuiLeaves(
            lhs_leaves.items,
            rhs_leaves.items,
            lhs_exact,
            rhs_exact,
            &common_items,
        );

        try self.claimOppositeConcreteLeaves(
            lhs_leaves.items,
            lhs_exact,
            lhs_claimed,
            rhs_leaves.items,
            rhs_exact,
            relation,
            acui,
        );
        try self.claimOppositeConcreteLeaves(
            rhs_leaves.items,
            rhs_exact,
            rhs_claimed,
            lhs_leaves.items,
            lhs_exact,
            relation,
            acui,
        );

        var target_items = std.ArrayListUnmanaged(ExprId){};
        defer target_items.deinit(self.allocator);
        try target_items.appendSlice(self.allocator, common_items.items);

        for (lhs_leaves.items, 0..) |leaf, idx| {
            if (lhs_exact[idx]) continue;
            if (leaf.is_def) {
                if (!lhs_claimed[idx]) {
                    return null;
                }
                try target_items.append(self.allocator, leaf.old_expr);
                continue;
            }
            if (leaf.new_expr == leaf.old_expr) {
                return null;
            }
        }
        for (rhs_leaves.items, 0..) |leaf, idx| {
            if (rhs_exact[idx]) continue;
            if (leaf.is_def) {
                if (!rhs_claimed[idx]) {
                    return null;
                }
                try target_items.append(self.allocator, leaf.old_expr);
                continue;
            }
            if (leaf.new_expr == leaf.old_expr) {
                return null;
            }
        }

        const target_expr = try self.buildCanonicalAcuiFromItems(
            target_items.items,
            acui,
        );

        const lhs_result = try self.buildAcuiRewriteConversion(
            lhs,
            relation,
            acui,
            lhs_leaves.items,
        );
        const rhs_result = try self.buildAcuiRewriteConversion(
            rhs,
            relation,
            acui,
            rhs_leaves.items,
        );
        if (lhs_result.result_expr != target_expr or
            rhs_result.result_expr != target_expr)
        {
            return null;
        }

        return .{
            .target_expr = target_expr,
            .lhs_conv_line_idx = lhs_result.conv_line_idx,
            .rhs_conv_line_idx = rhs_result.conv_line_idx,
        };
    }

    fn pairCommonAcuiLeaves(
        self: *Normalizer,
        lhs: []AcuiLeaf,
        rhs: []AcuiLeaf,
        lhs_exact: []bool,
        rhs_exact: []bool,
        common_items: *std.ArrayListUnmanaged(ExprId),
    ) Error!void {
        for (lhs, 0..) |*lhs_leaf, lhs_idx| {
            if (lhs_exact[lhs_idx]) continue;
            for (rhs, 0..) |*rhs_leaf, rhs_idx| {
                if (rhs_exact[rhs_idx]) continue;
                const common = try self.buildNonAcuiCommonTarget(
                    lhs_leaf.old_expr,
                    rhs_leaf.old_expr,
                ) orelse continue;
                lhs_exact[lhs_idx] = true;
                rhs_exact[rhs_idx] = true;
                lhs_leaf.new_expr = common.target_expr;
                lhs_leaf.conv_line_idx = common.lhs_conv_line_idx;
                rhs_leaf.new_expr = common.target_expr;
                rhs_leaf.conv_line_idx = common.rhs_conv_line_idx;
                try common_items.append(
                    self.allocator,
                    common.target_expr,
                );
                break;
            }
        }
    }

    fn claimOppositeConcreteLeaves(
        self: *Normalizer,
        owners: []AcuiLeaf,
        owner_exact: []const bool,
        owner_claimed: []bool,
        concretes: []AcuiLeaf,
        concrete_exact: []const bool,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!void {
        for (owners, 0..) |owner, owner_idx| {
            if (owner_exact[owner_idx] or !owner.is_def) continue;
            for (concretes, 0..) |*concrete, concrete_idx| {
                if (concrete_exact[concrete_idx] or concrete.is_def) continue;
                if (concrete.new_expr != concrete.old_expr) continue;
                const proof = try self.buildConcreteToDefCoverProof(
                    concrete.old_expr,
                    owner.old_expr,
                    relation,
                    acui,
                ) orelse continue;
                concrete.new_expr = owner.old_expr;
                concrete.conv_line_idx = proof;
                owner_claimed[owner_idx] = true;
            }
        }
    }

    fn buildConcreteToDefCoverProof(
        self: *Normalizer,
        concrete_expr: ExprId,
        def_expr: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!?usize {
        if (try self.buildNonAcuiCommonTarget(def_expr, concrete_expr)) |common| {
            if (common.target_expr == def_expr) {
                return common.rhs_conv_line_idx;
            }
            if (common.target_expr == concrete_expr) {
                const def_to_concrete = common.lhs_conv_line_idx orelse return null;
                return try self.emitSymm(
                    relation,
                    def_expr,
                    concrete_expr,
                    def_to_concrete,
                );
            }
            const concrete_to_target = common.rhs_conv_line_idx orelse {
                return null;
            };
            const def_to_target = common.lhs_conv_line_idx orelse return null;
            const target_to_def = try self.emitSymm(
                relation,
                def_expr,
                common.target_expr,
                def_to_target,
            );
            return try self.composeTransitivity(
                relation,
                concrete_expr,
                common.target_expr,
                def_expr,
                concrete_to_target,
                target_to_def,
            );
        }

        var def_ops = DefOps.Context.init(
            self.allocator,
            self.theorem,
            self.env,
        );
        defer def_ops.deinit();

        const witness = try def_ops.instantiateDefTowardAcuiItem(
            def_expr,
            concrete_expr,
            acui.head_term_id,
        ) orelse return null;
        const def_to_witness = try self.emitTransparentRelationProof(
            relation,
            def_expr,
            witness,
        );
        if (witness == concrete_expr) {
            return try self.emitSymm(
                relation,
                def_expr,
                concrete_expr,
                def_to_witness orelse return null,
            );
        }

        const witness_to_concrete = if (self.isAcuiExpr(
            witness,
            acui.head_term_id,
        )) blk: {
            const exact = try self.normalizeStructuralExact(
                witness,
                relation,
                acui,
            );
            if (exact.result_expr != concrete_expr) return null;
            break :blk exact.conv_line_idx;
        } else return null;

        const def_to_concrete = try self.composeTransitivity(
            relation,
            def_expr,
            witness,
            concrete_expr,
            def_to_witness,
            witness_to_concrete,
        ) orelse return null;
        return try self.emitSymm(
            relation,
            def_expr,
            concrete_expr,
            def_to_concrete,
        );
    }

    fn isAcuiExpr(
        self: *Normalizer,
        expr_id: ExprId,
        head_term_id: u32,
    ) bool {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| app.term_id == head_term_id and app.args.len == 2,
            .variable => false,
        };
    }

    fn sharedStructuralCombiner(
        self: *Normalizer,
        lhs: ExprId,
        rhs: ExprId,
    ) ?ResolvedStructuralCombiner {
        var support = self.acuiSupport();
        return support.sharedStructuralCombiner(lhs, rhs);
    }

    fn cancelExactAcuiItems(
        self: *Normalizer,
        lhs: []const AcuiLeaf,
        rhs: []const AcuiLeaf,
        lhs_exact: []bool,
        rhs_exact: []bool,
        common_items: *std.ArrayListUnmanaged(ExprId),
    ) Error!void {
        var lhs_idx: usize = 0;
        var rhs_idx: usize = 0;
        while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
            switch (compareExprIds(
                self.theorem,
                lhs[lhs_idx].old_expr,
                rhs[rhs_idx].old_expr,
            )) {
                .lt => lhs_idx += 1,
                .gt => rhs_idx += 1,
                .eq => {
                    lhs_exact[lhs_idx] = true;
                    rhs_exact[rhs_idx] = true;
                    try common_items.append(
                        self.allocator,
                        lhs[lhs_idx].old_expr,
                    );
                    lhs_idx += 1;
                    rhs_idx += 1;
                },
            }
        }
    }

    fn buildCanonicalAcuiFromItems(
        self: *Normalizer,
        items: []const ExprId,
        acui: ResolvedStructuralCombiner,
    ) Error!ExprId {
        var support = self.acuiSupport();
        return try support.buildCanonicalAcuiFromItems(items, acui);
    }

    fn buildAcuiRewriteConversion(
        self: *Normalizer,
        expr_id: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
        leaves: []const AcuiLeaf,
    ) Error!NormalizeResult {
        var next_leaf: usize = 0;
        const replaced = try self.rewriteAcuiLeaves(
            expr_id,
            relation,
            acui,
            leaves,
            &next_leaf,
        );
        const rewritten = switch (self.theorem.interner.node(replaced.result_expr).*) {
            .app => |rewritten_app| try self.normalizeChildren(
                replaced.result_expr,
                rewritten_app,
            ),
            .variable => NormalizeResult{
                .result_expr = replaced.result_expr,
                .conv_line_idx = null,
            },
        };
        const exact = try self.normalizeStructuralExact(
            rewritten.result_expr,
            relation,
            acui,
        );
        const replaced_to_rewritten = try self.composeTransitivity(
            relation,
            expr_id,
            replaced.result_expr,
            rewritten.result_expr,
            replaced.conv_line_idx,
            rewritten.conv_line_idx,
        );
        const proof = try self.composeTransitivity(
            relation,
            expr_id,
            rewritten.result_expr,
            exact.result_expr,
            replaced_to_rewritten,
            exact.conv_line_idx,
        );
        return .{
            .result_expr = exact.result_expr,
            .conv_line_idx = proof,
        };
    }

    fn rebuildAcuiTree(
        self: *Normalizer,
        items: []const ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) Error!ExprId {
        var support = self.acuiSupport();
        return try support.rebuildAcuiTree(items, head_term_id, unit_term_id);
    }

    fn normalizeUncached(self: *Normalizer, expr_id: ExprId) Error!NormalizeResult {
        const node = self.theorem.interner.node(expr_id);

        const child_result = switch (node.*) {
            .app => |app| try self.normalizeChildren(expr_id, app),
            .variable => NormalizeResult{
                .result_expr = expr_id,
                .conv_line_idx = null,
            },
        };

        const relation = self.resolveRelationForExpr(expr_id) orelse {
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
            const structural = try self.normalizeStructural(
                current,
                relation,
                acui,
            );
            if (structural.result_expr == current and
                structural.conv_line_idx == null)
            {
                break;
            }
            current_proof = try self.composeTransitivity(
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

                const match_result = try self.tryApplyRule(relation, current, rule);
                if (match_result) |step_result| {
                    self.step_count += 1;
                    const rhs_norm = try self.normalize(step_result.result_expr);
                    const rhs_proof = try self.composeTransitivity(
                        relation,
                        current,
                        step_result.result_expr,
                        rhs_norm.result_expr,
                        step_result.conv_line_idx,
                        rhs_norm.conv_line_idx,
                    );
                    current_proof = try self.composeTransitivity(
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

    fn normalizeChildren(
        self: *Normalizer,
        expr_id: ExprId,
        app: ExprNode.App,
    ) Error!NormalizeResult {
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
        const proof = try self.emitCongruenceLine(
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

    fn normalizeStructural(
        self: *Normalizer,
        expr_id: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!NormalizeResult {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            else => return .{ .result_expr = expr_id, .conv_line_idx = null },
        };
        if (app.term_id != acui.head_term_id or app.args.len != 2) {
            return .{ .result_expr = expr_id, .conv_line_idx = null };
        }

        var leaves = std.ArrayListUnmanaged(AcuiLeaf){};
        defer leaves.deinit(self.allocator);
        try self.collectAcuiLeaves(expr_id, acui.head_term_id, &leaves);

        const unit_expr = try self.unitExpr(acui);
        try self.applySameSideAbsorption(
            leaves.items,
            unit_expr,
            relation,
            acui,
        );

        var next_leaf: usize = 0;
        const replaced = try self.rewriteAcuiLeaves(
            expr_id,
            relation,
            acui,
            leaves.items,
            &next_leaf,
        );
        const rewritten = switch (self.theorem.interner.node(replaced.result_expr).*) {
            .app => |rewritten_app| try self.normalizeChildren(
                replaced.result_expr,
                rewritten_app,
            ),
            .variable => NormalizeResult{
                .result_expr = replaced.result_expr,
                .conv_line_idx = null,
            },
        };
        const exact = try self.normalizeStructuralExact(
            rewritten.result_expr,
            relation,
            acui,
        );
        const replaced_to_rewritten = try self.composeTransitivity(
            relation,
            expr_id,
            replaced.result_expr,
            rewritten.result_expr,
            replaced.conv_line_idx,
            rewritten.conv_line_idx,
        );
        const proof = try self.composeTransitivity(
            relation,
            expr_id,
            rewritten.result_expr,
            exact.result_expr,
            replaced_to_rewritten,
            exact.conv_line_idx,
        );
        return .{
            .result_expr = exact.result_expr,
            .conv_line_idx = proof,
        };
    }

    fn normalizeStructuralExact(
        self: *Normalizer,
        expr_id: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!NormalizeResult {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            else => return .{ .result_expr = expr_id, .conv_line_idx = null },
        };
        if (app.term_id != acui.head_term_id or app.args.len != 2) {
            return .{ .result_expr = expr_id, .conv_line_idx = null };
        }
        return try self.mergeCanonical(
            expr_id,
            app.args[0],
            app.args[1],
            relation,
            acui,
        );
    }

    fn collectAcuiLeaves(
        self: *Normalizer,
        expr_id: ExprId,
        head_term_id: u32,
        out: *std.ArrayListUnmanaged(AcuiLeaf),
    ) Error!void {
        var support = self.acuiSupport();
        var infos = std.ArrayListUnmanaged(AcuiSupport.LeafInfo){};
        defer infos.deinit(self.allocator);
        try support.collectLeafInfos(expr_id, head_term_id, &infos);
        try out.ensureUnusedCapacity(self.allocator, infos.items.len);
        for (infos.items) |info| {
            out.appendAssumeCapacity(.{
                .old_expr = info.expr_id,
                .new_expr = info.expr_id,
                .is_def = info.is_def,
                .conv_line_idx = null,
            });
        }
    }

    fn applySameSideAbsorption(
        self: *Normalizer,
        leaves: []AcuiLeaf,
        unit_expr: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!void {
        const infos = try self.allocator.alloc(AcuiSupport.LeafInfo, leaves.len);
        defer self.allocator.free(infos);
        for (leaves, 0..) |leaf, idx| {
            infos[idx] = .{
                .expr_id = leaf.old_expr,
                .is_def = leaf.is_def,
            };
        }

        var support = self.acuiSupport();
        const targets = try support.computeSameSideTargets(
            infos,
            unit_expr,
            acui,
        );
        defer self.allocator.free(targets);

        for (leaves, targets) |*leaf, target| {
            if (target == leaf.old_expr) continue;
            const proof = try self.buildConcreteToDefCoverProof(
                leaf.old_expr,
                target,
                relation,
                acui,
            ) orelse return error.MissingStructuralMetadata;
            leaf.new_expr = target;
            leaf.conv_line_idx = proof;
        }
    }

    fn rewriteAcuiLeaves(
        self: *Normalizer,
        expr_id: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
        leaves: []const AcuiLeaf,
        next_leaf: *usize,
    ) Error!NormalizeResult {
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .app => |app| {
                if (app.term_id == acui.head_term_id and app.args.len == 2) {
                    const left = try self.rewriteAcuiLeaves(
                        app.args[0],
                        relation,
                        acui,
                        leaves,
                        next_leaf,
                    );
                    const right = try self.rewriteAcuiLeaves(
                        app.args[1],
                        relation,
                        acui,
                        leaves,
                        next_leaf,
                    );
                    const new_args = [_]ExprId{
                        left.result_expr,
                        right.result_expr,
                    };
                    const old_args = [_]ExprId{ app.args[0], app.args[1] };
                    const new_expr = if (left.result_expr == app.args[0] and
                        right.result_expr == app.args[1])
                        expr_id
                    else
                        try self.theorem.interner.internApp(
                            acui.head_term_id,
                            &new_args,
                        );
                    return .{
                        .result_expr = new_expr,
                        .conv_line_idx = try self.emitCongruenceLine(
                            acui.head_term_id,
                            &old_args,
                            &new_args,
                            &[_]?usize{
                                left.conv_line_idx,
                                right.conv_line_idx,
                            },
                        ),
                    };
                }
            },
            .variable => {},
        }

        if (next_leaf.* >= leaves.len) return error.MissingStructuralMetadata;
        const leaf = leaves[next_leaf.*];
        next_leaf.* += 1;
        if (leaf.old_expr != expr_id) return error.MissingStructuralMetadata;
        return .{
            .result_expr = leaf.new_expr,
            .conv_line_idx = if (leaf.conv_line_idx) |idx|
                idx
            else
                try self.emitTransparentRelationProof(
                    relation,
                    leaf.old_expr,
                    leaf.new_expr,
                ),
        };
    }

    fn emitTransparentRelationProof(
        self: *Normalizer,
        relation: ResolvedRelation,
        source_expr: ExprId,
        target_expr: ExprId,
    ) Error!?usize {
        if (source_expr == target_expr) return null;
        const source_rel = try self.buildRelExpr(
            relation,
            source_expr,
            source_expr,
        );
        const target_rel = try self.buildRelExpr(
            relation,
            source_expr,
            target_expr,
        );
        const refl_idx = try self.emitRefl(relation, source_expr);
        return try appendTransportLine(
            self.lines,
            self.allocator,
            target_rel,
            source_rel,
            .{ .line = refl_idx },
        );
    }

    fn mergeCanonical(
        self: *Normalizer,
        current_expr: ExprId,
        left: ExprId,
        right: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!NormalizeResult {
        const unit_expr = try self.unitExpr(acui);
        if (left == unit_expr) {
            return .{
                .result_expr = right,
                .conv_line_idx = try self.emitLeftUnit(current_expr, right, relation, acui),
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
                    const assoc_idx = try self.emitAssoc(
                        left_app.args[0],
                        left_app.args[1],
                        right,
                        relation,
                        acui,
                    );
                    const merged_tail = try self.mergeCanonical(
                        tail_expr,
                        left_app.args[1],
                        right,
                        relation,
                        acui,
                    );
                    const lifted_tail = if (merged_tail.conv_line_idx) |tail_idx|
                        try self.emitCongruenceLine(
                            acui.head_term_id,
                            &[_]ExprId{ left_app.args[0], tail_expr },
                            &[_]ExprId{ left_app.args[0], merged_tail.result_expr },
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
                    const inserted = try self.insertItem(
                        after_tail,
                        left_app.args[0],
                        merged_tail.result_expr,
                        relation,
                        acui,
                    );
                    const first = try self.composeTransitivity(
                        relation,
                        current_expr,
                        assoc_target,
                        after_tail,
                        assoc_idx,
                        lifted_tail,
                    );
                    const proof = try self.composeTransitivity(
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

        return try self.insertItem(
            current_expr,
            left,
            right,
            relation,
            acui,
        );
    }

    fn insertItem(
        self: *Normalizer,
        current_expr: ExprId,
        item: ExprId,
        canon: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!NormalizeResult {
        const unit_expr = try self.unitExpr(acui);
        if (item == unit_expr) {
            return .{
                .result_expr = canon,
                .conv_line_idx = try self.emitLeftUnit(current_expr, canon, relation, acui),
            };
        }
        if (canon == unit_expr) {
            return .{
                .result_expr = item,
                .conv_line_idx = try self.emitRightUnit(item, relation, acui),
            };
        }

        const canon_node = self.theorem.interner.node(canon);
        switch (canon_node.*) {
            .variable => {
                return try self.insertIntoAtom(
                    current_expr,
                    item,
                    canon,
                    relation,
                    acui,
                );
            },
            .app => |canon_app| {
                if (canon_app.term_id != acui.head_term_id or
                    canon_app.args.len != 2)
                {
                    return try self.insertIntoAtom(
                        current_expr,
                        item,
                        canon,
                        relation,
                        acui,
                    );
                }

                const head = canon_app.args[0];
                const rest = canon_app.args[1];
                const cmp = compareExprIds(self.theorem, item, head);
                if (cmp == .eq and acui.idem_id != null) {
                    const assoc_sym_idx = try self.emitAssocSymm(
                        item,
                        head,
                        rest,
                        relation,
                        acui,
                    );
                    const inner_old = try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ item, head },
                    );
                    const idem_idx = try self.emitIdem(item, relation, acui);
                    const lifted = try self.emitCongruenceLine(
                        acui.head_term_id,
                        &[_]ExprId{ inner_old, rest },
                        &[_]ExprId{ item, rest },
                        &[_]?usize{ idem_idx, null },
                    );
                    const proof = try self.composeTransitivity(
                        relation,
                        current_expr,
                        try switchAssoc(self, item, head, rest, acui),
                        canon,
                        assoc_sym_idx,
                        lifted,
                    );
                    return .{
                        .result_expr = canon,
                        .conv_line_idx = proof,
                    };
                }
                if (cmp != .gt or acui.comm_id == null) {
                    return .{
                        .result_expr = current_expr,
                        .conv_line_idx = null,
                    };
                }

                const assoc_sym_target = try switchAssoc(
                    self,
                    item,
                    head,
                    rest,
                    acui,
                );
                const assoc_sym_idx = try self.emitAssocSymm(
                    item,
                    head,
                    rest,
                    relation,
                    acui,
                );
                const inner_old = try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ item, head },
                );
                const inner_new = try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ head, item },
                );
                const comm_idx = try self.emitComm(item, head, relation, acui);
                const lifted_comm = try self.emitCongruenceLine(
                    acui.head_term_id,
                    &[_]ExprId{ inner_old, rest },
                    &[_]ExprId{ inner_new, rest },
                    &[_]?usize{ comm_idx, null },
                );
                const assoc_idx = try self.emitAssoc(
                    head,
                    item,
                    rest,
                    relation,
                    acui,
                );
                const before_rec = try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ item, rest },
                );
                const rec = try self.insertItem(
                    before_rec,
                    item,
                    rest,
                    relation,
                    acui,
                );
                const lifted_rec = if (rec.conv_line_idx) |rec_idx|
                    try self.emitCongruenceLine(
                        acui.head_term_id,
                        &[_]ExprId{ head, before_rec },
                        &[_]ExprId{ head, rec.result_expr },
                        &[_]?usize{ null, rec_idx },
                    )
                else
                    null;
                const first = try self.composeTransitivity(
                    relation,
                    current_expr,
                    assoc_sym_target,
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ inner_new, rest },
                    ),
                    assoc_sym_idx,
                    lifted_comm,
                );
                const second = try self.composeTransitivity(
                    relation,
                    current_expr,
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ inner_new, rest },
                    ),
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ head, before_rec },
                    ),
                    first,
                    assoc_idx,
                );
                const proof = try self.composeTransitivity(
                    relation,
                    current_expr,
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ head, before_rec },
                    ),
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ head, rec.result_expr },
                    ),
                    second,
                    lifted_rec,
                );
                return .{
                    .result_expr = if (rec.result_expr == before_rec)
                        try self.theorem.interner.internApp(
                            acui.head_term_id,
                            &[_]ExprId{ head, before_rec },
                        )
                    else
                        try self.theorem.interner.internApp(
                            acui.head_term_id,
                            &[_]ExprId{ head, rec.result_expr },
                        ),
                    .conv_line_idx = proof,
                };
            },
        }
    }

    fn insertIntoAtom(
        self: *Normalizer,
        current_expr: ExprId,
        item: ExprId,
        atom: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!NormalizeResult {
        const cmp = compareExprIds(self.theorem, item, atom);
        if (cmp == .eq and acui.idem_id != null) {
            return .{
                .result_expr = atom,
                .conv_line_idx = try self.emitIdem(item, relation, acui),
            };
        }
        if (cmp != .gt or acui.comm_id == null) {
            return .{
                .result_expr = current_expr,
                .conv_line_idx = null,
            };
        }
        const target = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ atom, item },
        );
        _ = target;
        return .{
            .result_expr = try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ atom, item },
            ),
            .conv_line_idx = try self.emitComm(item, atom, relation, acui),
        };
    }

    fn tryApplyRule(
        self: *Normalizer,
        relation: ResolvedRelation,
        expr_id: ExprId,
        rule: RewriteRule,
    ) Error!?NormalizeResult {
        const bindings = try self.allocator.alloc(?ExprId, rule.num_binders);
        defer self.allocator.free(bindings);
        @memset(bindings, null);

        if (!self.theorem.matchTemplate(rule.lhs, expr_id, bindings)) {
            return null;
        }

        const concrete = try self.allocator.alloc(ExprId, rule.num_binders);
        for (bindings, 0..) |binding, idx| {
            concrete[idx] = binding orelse {
                self.allocator.free(concrete);
                return null;
            };
        }

        if (rule.rule_id >= self.env.rules.items.len) {
            self.allocator.free(concrete);
            return null;
        }
        const rule_decl = &self.env.rules.items[rule.rule_id];
        if (rule_decl.args.len != concrete.len) {
            self.allocator.free(concrete);
            return null;
        }
        validateRewriteBindings(
            self.env,
            self.theorem,
            rule_decl.args,
            concrete,
        ) catch {
            self.allocator.free(concrete);
            return null;
        };

        const rhs_expr = try self.theorem.instantiateTemplate(rule.rhs, concrete);
        const step_expr = try self.buildRelExpr(relation, expr_id, rhs_expr);

        const line_idx = try appendRuleLine(
            self.lines,
            self.allocator,
            step_expr,
            rule.rule_id,
            concrete,
            &.{},
        );

        return .{
            .result_expr = rhs_expr,
            .conv_line_idx = line_idx,
        };
    }

    fn emitCongruenceLine(
        self: *Normalizer,
        term_id: u32,
        old_args: []const ExprId,
        new_args: []const ExprId,
        child_proofs: []const ?usize,
    ) Error!?usize {
        var any_changed = false;
        for (old_args, new_args) |old_arg, new_arg| {
            any_changed = any_changed or old_arg != new_arg;
        }
        if (!any_changed) return null;

        const term_decl = if (term_id < self.env.terms.items.len)
            &self.env.terms.items[term_id]
        else
            return error.MissingCongruenceRule;
        const congr_rule = self.registry.getCongruenceRule(term_id) orelse {
            return error.MissingCongruenceRule;
        };

        const bindings = try self.allocator.alloc(ExprId, congr_rule.num_binders);
        var binding_idx: usize = 0;
        var ref_count: usize = 0;
        for (term_decl.args) |arg| {
            if (!arg.bound) ref_count += 1;
        }

        const refs = try self.allocator.alloc(CheckedRef, ref_count);
        var ref_idx: usize = 0;
        for (old_args, new_args, term_decl.args, 0..) |
            old_arg,
            new_arg,
            arg_decl,
            idx,
        | {
            if (arg_decl.bound) {
                if (old_arg != new_arg) return error.MissingCongruenceRule;
                bindings[binding_idx] = old_arg;
                binding_idx += 1;
                continue;
            }

            bindings[binding_idx] = old_arg;
            bindings[binding_idx + 1] = new_arg;
            binding_idx += 2;

            if (child_proofs[idx]) |proof_idx| {
                refs[ref_idx] = .{ .line = proof_idx };
                ref_idx += 1;
                continue;
            }
            if (old_arg == new_arg) {
                const child_rel = self.registry.resolveRelation(
                    self.env,
                    arg_decl.sort_name,
                ) orelse return error.MissingCongruenceRule;
                refs[ref_idx] = .{ .line = try self.emitRefl(child_rel, old_arg) };
                ref_idx += 1;
                continue;
            }
            return error.MissingCongruenceRule;
        }

        if (binding_idx != bindings.len or ref_idx != refs.len) {
            return error.MissingCongruenceRule;
        }

        const old_expr = try self.theorem.interner.internApp(term_id, old_args);
        const new_expr = try self.theorem.interner.internApp(term_id, new_args);
        const parent_relation = self.resolveRelationForExpr(old_expr) orelse {
            return error.MissingCongruenceRule;
        };
        const expr = try self.buildRelExpr(parent_relation, old_expr, new_expr);

        return try appendRuleLine(
            self.lines,
            self.allocator,
            expr,
            congr_rule.rule_id,
            bindings,
            refs,
        );
    }

    fn emitRefl(
        self: *Normalizer,
        relation: ResolvedRelation,
        expr_id: ExprId,
    ) Error!usize {
        const refl_expr = try self.buildRelExpr(relation, expr_id, expr_id);
        const bindings = try self.allocator.alloc(ExprId, 1);
        bindings[0] = expr_id;

        return try appendRuleLine(
            self.lines,
            self.allocator,
            refl_expr,
            relation.refl_id,
            bindings,
            &.{},
        );
    }

    fn emitAssoc(
        self: *Normalizer,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!usize {
        const lhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ a, b },
                ),
                c,
            },
        );
        const rhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{
                a,
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ b, c },
                ),
            },
        );
        const expr = try self.buildRelExpr(relation, lhs, rhs);
        const bindings = try self.allocator.alloc(ExprId, 3);
        bindings[0] = a;
        bindings[1] = b;
        bindings[2] = c;

        return try appendRuleLine(
            self.lines,
            self.allocator,
            expr,
            acui.assoc_id,
            bindings,
            &.{},
        );
    }

    fn emitAssocSymm(
        self: *Normalizer,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!usize {
        const assoc_idx = try self.emitAssoc(a, b, c, relation, acui);
        const lhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ a, b },
                ),
                c,
            },
        );
        const rhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{
                a,
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ b, c },
                ),
            },
        );
        return try self.emitSymm(relation, lhs, rhs, assoc_idx);
    }

    fn emitComm(
        self: *Normalizer,
        a: ExprId,
        b: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!usize {
        const lhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ a, b },
        );
        const rhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ b, a },
        );
        const expr = try self.buildRelExpr(relation, lhs, rhs);
        const bindings = try self.allocator.alloc(ExprId, 2);
        bindings[0] = a;
        bindings[1] = b;

        return try appendRuleLine(
            self.lines,
            self.allocator,
            expr,
            acui.comm_id orelse return error.MissingStructuralMetadata,
            bindings,
            &.{},
        );
    }

    fn emitIdem(
        self: *Normalizer,
        a: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!usize {
        const lhs = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ a, a },
        );
        const expr = try self.buildRelExpr(relation, lhs, a);
        const bindings = try self.allocator.alloc(ExprId, 1);
        bindings[0] = a;

        return try appendRuleLine(
            self.lines,
            self.allocator,
            expr,
            acui.idem_id orelse return error.MissingStructuralMetadata,
            bindings,
            &.{},
        );
    }

    fn emitLeftUnit(
        self: *Normalizer,
        current_expr: ExprId,
        result_expr: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!usize {
        const bindings = try self.allocator.alloc(ExprId, 1);
        bindings[0] = result_expr;

        const theorem_expr = if (acui.left_unit_rule_reversed)
            try self.buildRelExpr(relation, result_expr, current_expr)
        else
            try self.buildRelExpr(relation, current_expr, result_expr);

        const unit_idx = try appendRuleLine(
            self.lines,
            self.allocator,
            theorem_expr,
            acui.left_unit_rule_id,
            bindings,
            &.{},
        );
        if (!acui.left_unit_rule_reversed) return unit_idx;
        return try self.emitSymm(relation, result_expr, current_expr, unit_idx);
    }

    fn emitRightUnit(
        self: *Normalizer,
        item: ExprId,
        relation: ResolvedRelation,
        acui: ResolvedStructuralCombiner,
    ) Error!usize {
        const unit_expr = try self.unitExpr(acui);
        const current_expr = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ item, unit_expr },
        );
        const swapped = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ unit_expr, item },
        );
        const comm_idx = try self.emitComm(item, unit_expr, relation, acui);
        const unit_idx = try self.emitLeftUnit(swapped, item, relation, acui);
        return try self.composeTransitivityLine(
            relation,
            current_expr,
            swapped,
            item,
            comm_idx,
            unit_idx,
        );
    }

    pub fn composeTransitivity(
        self: *Normalizer,
        relation: ResolvedRelation,
        original: ExprId,
        mid: ExprId,
        final: ExprId,
        first_proof: ?usize,
        second_proof: ?usize,
    ) Error!?usize {
        if (first_proof == null) return second_proof;
        if (second_proof == null) return first_proof;
        return try self.composeTransitivityLine(
            relation,
            original,
            mid,
            final,
            first_proof.?,
            second_proof.?,
        );
    }

    fn composeTransitivityLine(
        self: *Normalizer,
        relation: ResolvedRelation,
        original: ExprId,
        mid: ExprId,
        final: ExprId,
        first_proof: usize,
        second_proof: usize,
    ) Error!usize {
        const trans_expr = try self.buildRelExpr(relation, original, final);
        const bindings = try self.allocator.alloc(ExprId, 3);
        bindings[0] = original;
        bindings[1] = mid;
        bindings[2] = final;

        const refs = try self.allocator.alloc(CheckedRef, 2);
        refs[0] = .{ .line = first_proof };
        refs[1] = .{ .line = second_proof };

        return try appendRuleLine(
            self.lines,
            self.allocator,
            trans_expr,
            relation.trans_id,
            bindings,
            refs,
        );
    }

    fn buildRelExpr(
        self: *Normalizer,
        relation: ResolvedRelation,
        lhs: ExprId,
        rhs: ExprId,
    ) Error!ExprId {
        return try self.theorem.interner.internApp(
            relation.rel_term_id,
            &[_]ExprId{ lhs, rhs },
        );
    }

    fn unitExpr(
        self: *Normalizer,
        acui: ResolvedStructuralCombiner,
    ) Error!ExprId {
        return try self.theorem.interner.internApp(acui.unit_term_id, &.{});
    }

    pub fn emitTransport(
        self: *Normalizer,
        relation: ResolvedRelation,
        target_expr: ExprId,
        source_expr: ExprId,
        conv_line_idx: usize,
        source_line: CheckedRef,
    ) Error!usize {
        const transport_id = relation.transport_id orelse {
            return error.MissingTransport;
        };
        const bindings = try self.allocator.alloc(ExprId, 2);
        bindings[0] = source_expr;
        bindings[1] = target_expr;

        const refs = try self.allocator.alloc(CheckedRef, 2);
        refs[0] = .{ .line = conv_line_idx };
        refs[1] = source_line;

        return try appendRuleLine(
            self.lines,
            self.allocator,
            target_expr,
            transport_id,
            bindings,
            refs,
        );
    }

    pub fn emitSymm(
        self: *Normalizer,
        relation: ResolvedRelation,
        a: ExprId,
        b: ExprId,
        proof_line_idx: usize,
    ) Error!usize {
        const symm_expr = try self.buildRelExpr(relation, b, a);
        const bindings = try self.allocator.alloc(ExprId, 2);
        bindings[0] = a;
        bindings[1] = b;

        const refs = try self.allocator.alloc(CheckedRef, 1);
        refs[0] = .{ .line = proof_line_idx };

        return try appendRuleLine(
            self.lines,
            self.allocator,
            symm_expr,
            relation.symm_id,
            bindings,
            refs,
        );
    }
};

fn switchAssoc(
    self: *Normalizer,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    acui: ResolvedStructuralCombiner,
) Normalizer.Error!ExprId {
    return try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{
            try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ a, b },
            ),
            c,
        },
    );
}

const ExprInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

fn validateRewriteBindings(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expected_args: []const ArgInfo,
    bindings: []const ExprId,
) !void {
    if (expected_args.len != bindings.len) return error.SortMismatch;

    var deps_buf: [56]u55 = undefined;
    var deps_len: usize = 0;
    for (expected_args, bindings) |expected, expr_id| {
        const info = try rewriteExprInfo(env, theorem, expr_id);
        if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
            return error.SortMismatch;
        }
        if (expected.bound) {
            if (!info.bound) return error.BoundnessMismatch;
            var k: usize = 0;
            while (k < deps_len) : (k += 1) {
                if (deps_buf[k] & info.deps != 0) return error.DepViolation;
            }
            deps_buf[deps_len] = info.deps;
            deps_len += 1;
            continue;
        }
        for (0..deps_len) |k| {
            if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0) continue;
            if (deps_buf[k] & info.deps != 0) return error.DepViolation;
        }
    }
}

fn rewriteExprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !ExprInfo {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= theorem.arg_infos.len) {
                    return error.UnknownTheoremVariable;
                }
                const arg = theorem.arg_infos[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                    .deps = arg.deps,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                    .deps = dummy.deps,
                };
            },
        },
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            var deps: u55 = 0;
            for (app.args) |arg_id| {
                deps |= (try rewriteExprInfo(env, theorem, arg_id)).deps;
            }
            break :blk .{
                .sort_name = env.terms.items[app.term_id].ret_sort_name,
                .bound = false,
                .deps = deps,
            };
        },
    };
}
