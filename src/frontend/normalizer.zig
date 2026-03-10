const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation = @import("./rewrite_registry.zig").ResolvedRelation;
const RewriteRule = @import("./rewrite_registry.zig").RewriteRule;

const CheckedRef = @import("./compiler.zig").CheckedRef;
const CheckedLine = @import("./compiler.zig").CheckedLine;

pub const NormalizeResult = struct {
    result_expr: ExprId,
    /// Index into the lines array of the conversion proof line,
    /// or null if the expression is unchanged (refl).
    conv_line_idx: ?usize,
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

    /// Normalize an expression bottom-up, returning the result and
    /// optionally a line index proving `relation(source, result)`.
    pub const Error = error{ MissingCongruenceRule, OutOfMemory, TooManyTheoremExprs, TemplateBinderOutOfRange, MissingTransport };

    pub fn normalize(self: *Normalizer, expr_id: ExprId) Error!NormalizeResult {
        if (self.cache.get(expr_id)) |cached| {
            return cached;
        }

        const result = try self.normalizeUncached(expr_id);
        try self.cache.put(expr_id, result);
        return result;
    }

    /// Look up the return sort of an expression (app nodes only).
    fn getExprSort(self: *const Normalizer, expr_id: ExprId) ?[]const u8 {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| if (app.term_id < self.env.terms.items.len)
                self.env.terms.items[app.term_id].ret_sort_name
            else
                null,
            .variable => null,
        };
    }

    /// Resolve the relation for the sort of the given expression.
    fn resolveRelationForExpr(self: *Normalizer, expr_id: ExprId) ?ResolvedRelation {
        const sort = self.getExprSort(expr_id) orelse return null;
        return self.registry.resolveRelation(self.env, sort);
    }

    fn normalizeUncached(self: *Normalizer, expr_id: ExprId) Error!NormalizeResult {
        const node = self.theorem.interner.node(expr_id);

        // Step 1: Normalize children via congruence
        const congr_result = switch (node.*) {
            .app => |app| try self.normalizeChildren(expr_id, app),
            .variable => NormalizeResult{
                .result_expr = expr_id,
                .conv_line_idx = null,
            },
        };

        // Determine relation for this expression's sort
        const relation = self.resolveRelationForExpr(expr_id) orelse {
            // No relation for this sort — can't apply head rules
            return congr_result;
        };

        // Step 2: Repeatedly apply head rewrite rules
        var current = congr_result.result_expr;
        var current_proof = congr_result.conv_line_idx;
        var changed = true;

        while (changed) {
            changed = false;
            const cur_node = self.theorem.interner.node(current);
            const head_id = switch (cur_node.*) {
                .app => |app| app.term_id,
                .variable => break,
            };

            const rules = self.registry.getRewriteRules(head_id);
            for (rules) |rule| {
                if (self.step_count >= self.step_limit) break;

                const match_result = try self.tryApplyRule(relation, current, rule);
                if (match_result) |step_result| {
                    self.step_count += 1;

                    // Recursively normalize the RHS (the rewrite may have
                    // introduced new redexes in subexpressions).
                    const rhs_norm = try self.normalize(step_result.result_expr);
                    const final_expr = rhs_norm.result_expr;
                    const rhs_proof = try self.composeTransitivity(
                        relation,
                        current,
                        step_result.result_expr,
                        final_expr,
                        step_result.conv_line_idx,
                        rhs_norm.conv_line_idx,
                    );

                    // Compose: current_proof ∘ rhs_proof
                    current_proof = try self.composeTransitivity(
                        relation,
                        expr_id,
                        current,
                        final_expr,
                        current_proof,
                        rhs_proof,
                    );
                    current = final_expr;
                    changed = true;
                    break; // restart from the first rule
                }
            }
        }

        return NormalizeResult{
            .result_expr = current,
            .conv_line_idx = current_proof,
        };
    }

    fn normalizeChildren(
        self: *Normalizer,
        expr_id: ExprId,
        app: ExprNode.App,
    ) Error!NormalizeResult {
        const term_decl = if (app.term_id < self.env.terms.items.len)
            &self.env.terms.items[app.term_id]
        else
            return NormalizeResult{ .result_expr = expr_id, .conv_line_idx = null };

        // Normalize each child, looking up per-child relations
        var any_changed = false;
        const new_args = try self.allocator.alloc(ExprId, app.args.len);
        var child_proofs = try self.allocator.alloc(?usize, app.args.len);
        const child_relations = try self.allocator.alloc(?ResolvedRelation, app.args.len);

        for (app.args, 0..) |arg, idx| {
            // Get child sort from parent term's arg declaration
            if (idx < term_decl.args.len) {
                const child_sort = term_decl.args[idx].sort_name;
                const child_rel = self.registry.resolveRelation(self.env, child_sort);
                child_relations[idx] = child_rel;

                if (child_rel != null) {
                    const child_result = try self.normalize(arg);
                    new_args[idx] = child_result.result_expr;
                    child_proofs[idx] = child_result.conv_line_idx;
                    if (child_result.result_expr != arg) any_changed = true;
                    continue;
                }
            } else {
                child_relations[idx] = null;
            }
            // No relation for this sort — skip normalization
            new_args[idx] = arg;
            child_proofs[idx] = null;
        }

        if (!any_changed) {
            self.allocator.free(new_args);
            self.allocator.free(child_proofs);
            self.allocator.free(child_relations);
            return NormalizeResult{
                .result_expr = expr_id,
                .conv_line_idx = null,
            };
        }

        // Build the new expression
        const new_expr = try self.theorem.interner.internApp(app.term_id, new_args);
        self.allocator.free(new_args);

        // Build congruence proof
        const congr_rule = self.registry.getCongruenceRule(app.term_id) orelse {
            self.allocator.free(child_proofs);
            self.allocator.free(child_relations);
            return error.MissingCongruenceRule;
        };

        // The congruence rule has the form:
        //   congr (a1 b1: s) (a2 b2: s) ... : rel(a1,b1) > rel(a2,b2) > ... > rel(f(a1..),f(b1..))
        // Binders: a1, b1, a2, b2, ... (pairs for each arg)
        // Hyps: rel(a1,b1), rel(a2,b2), ...
        // So bindings = [a1, b1, a2, b2, ...]
        const congr_bindings = try self.allocator.alloc(ExprId, congr_rule.num_binders);
        for (app.args, 0..) |original_arg, idx| {
            const norm = try self.normalize(original_arg);
            if (idx * 2 + 1 < congr_bindings.len) {
                congr_bindings[idx * 2] = original_arg;
                congr_bindings[idx * 2 + 1] = norm.result_expr;
            }
        }

        // Build refs: for each child that changed, reference its proof line;
        // for unchanged children, emit a refl line using the child's relation
        const refs = try self.allocator.alloc(CheckedRef, app.args.len);
        for (app.args, 0..) |original_arg, idx| {
            if (child_proofs[idx]) |proof_idx| {
                refs[idx] = .{ .line = proof_idx };
            } else {
                const rel = child_relations[idx] orelse {
                    self.allocator.free(child_proofs);
                    self.allocator.free(child_relations);
                    self.allocator.free(refs);
                    self.allocator.free(congr_bindings);
                    return error.MissingCongruenceRule;
                };
                const refl_line = try self.emitRefl(rel, original_arg);
                refs[idx] = .{ .line = refl_line };
            }
        }
        self.allocator.free(child_proofs);
        self.allocator.free(child_relations);

        // Build the congruence expression: rel(f(a1..an), f(b1..bn))
        // Determine the parent relation from the expression's sort
        const parent_relation = self.resolveRelationForExpr(expr_id) orelse
            return error.MissingCongruenceRule;
        const congr_expr = try self.buildRelExpr(parent_relation, expr_id, new_expr);

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = congr_expr,
            .rule_id = congr_rule.rule_id,
            .bindings = congr_bindings,
            .refs = refs,
        });

        return NormalizeResult{
            .result_expr = new_expr,
            .conv_line_idx = line_idx,
        };
    }

    fn tryApplyRule(
        self: *Normalizer,
        relation: ResolvedRelation,
        expr_id: ExprId,
        rule: RewriteRule,
    ) Error!?NormalizeResult {
        // Try to match the LHS template against expr_id
        const bindings = try self.allocator.alloc(?ExprId, rule.num_binders);
        @memset(bindings, null);

        if (!self.theorem.matchTemplate(rule.lhs, expr_id, bindings)) {
            self.allocator.free(bindings);
            return null;
        }

        // Check all bindings resolved
        const concrete = try self.allocator.alloc(ExprId, rule.num_binders);
        for (bindings, 0..) |b, idx| {
            concrete[idx] = b orelse {
                self.allocator.free(bindings);
                self.allocator.free(concrete);
                return null;
            };
        }
        self.allocator.free(bindings);

        // Compute the RHS
        const rhs_expr = try self.theorem.instantiateTemplate(rule.rhs, concrete);

        // Build the rule application line: rel(lhs, rhs)
        const step_expr = try self.buildRelExpr(relation, expr_id, rhs_expr);

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = step_expr,
            .rule_id = rule.rule_id,
            .bindings = concrete,
            .refs = &.{},
        });

        return NormalizeResult{
            .result_expr = rhs_expr,
            .conv_line_idx = line_idx,
        };
    }

    fn emitRefl(self: *Normalizer, relation: ResolvedRelation, expr_id: ExprId) Error!usize {
        // refl: rel(a, a)
        const refl_expr = try self.buildRelExpr(relation, expr_id, expr_id);
        const bindings = try self.allocator.alloc(ExprId, 1);
        bindings[0] = expr_id;

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = refl_expr,
            .rule_id = relation.refl_id,
            .bindings = bindings,
            .refs = &.{},
        });
        return line_idx;
    }

    fn composeTransitivity(
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

        // trans: rel(a,b) > rel(b,c) > rel(a,c)
        const trans_expr = try self.buildRelExpr(relation, original, final);
        const bindings = try self.allocator.alloc(ExprId, 3);
        bindings[0] = original;
        bindings[1] = mid;
        bindings[2] = final;

        const refs = try self.allocator.alloc(CheckedRef, 2);
        refs[0] = .{ .line = first_proof.? };
        refs[1] = .{ .line = second_proof.? };

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = trans_expr,
            .rule_id = relation.trans_id,
            .bindings = bindings,
            .refs = refs,
        });
        return line_idx;
    }

    fn buildRelExpr(self: *Normalizer, relation: ResolvedRelation, lhs: ExprId, rhs: ExprId) Error!ExprId {
        return try self.theorem.interner.internApp(
            relation.rel_term_id,
            &[_]ExprId{ lhs, rhs },
        );
    }

    /// Emit a transport line: given a proof of `rel(a, b)` and a proof of `a`,
    /// produce a proof of `b`.
    pub fn emitTransport(
        self: *Normalizer,
        relation: ResolvedRelation,
        target_expr: ExprId,
        source_expr: ExprId,
        conv_line_idx: usize,
        source_line: CheckedRef,
    ) Error!usize {
        const transport_id = relation.transport_id orelse return error.MissingTransport;
        // transport: rel(a, b) > a > b
        const bindings = try self.allocator.alloc(ExprId, 2);
        bindings[0] = source_expr;
        bindings[1] = target_expr;

        const refs = try self.allocator.alloc(CheckedRef, 2);
        refs[0] = .{ .line = conv_line_idx };
        refs[1] = source_line;

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = target_expr,
            .rule_id = transport_id,
            .bindings = bindings,
            .refs = refs,
        });
        return line_idx;
    }

    /// Emit a symmetry line: given a proof of `rel(a, b)`, produce `rel(b, a)`.
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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = symm_expr,
            .rule_id = relation.symm_id,
            .bindings = bindings,
            .refs = refs,
        });
        return line_idx;
    }
};
