const std = @import("std");
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
const compareExprIds = @import("./canonicalizer.zig").compareExprIds;

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

    pub const Error = error{
        MissingCongruenceRule,
        MissingStructuralMetadata,
        MissingTransport,
        OutOfMemory,
        TemplateBinderOutOfRange,
        TooManyTheoremExprs,
    };

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
            .variable => null,
        };
    }

    pub fn resolveRelationForExpr(
        self: *Normalizer,
        expr_id: ExprId,
    ) ?ResolvedRelation {
        const sort = self.getExprSort(expr_id) orelse return null;
        return self.registry.resolveRelation(self.env, sort);
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

        const current_node = self.theorem.interner.node(current);
        if (current_node.* == .app) {
            const app = current_node.app;
            if (self.registry.resolveStructuralCombiner(
                self.env,
                app.term_id,
            )) |acui| {
                const structural = try self.normalizeStructural(
                    current,
                    relation,
                    acui,
                );
                current_proof = try self.composeTransitivity(
                    relation,
                    expr_id,
                    current,
                    structural.result_expr,
                    current_proof,
                    structural.conv_line_idx,
                );
                current = structural.result_expr;
                return .{
                    .result_expr = current,
                    .conv_line_idx = current_proof,
                };
            }
        }

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
                    changed = true;
                    break;
                }
            }
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
        return try self.mergeCanonical(
            expr_id,
            app.args[0],
            app.args[1],
            relation,
            acui,
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

        const rhs_expr = try self.theorem.instantiateTemplate(rule.rhs, concrete);
        const step_expr = try self.buildRelExpr(relation, expr_id, rhs_expr);

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = step_expr,
            .rule_id = rule.rule_id,
            .bindings = concrete,
            .refs = &.{},
        });

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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = expr,
            .rule_id = congr_rule.rule_id,
            .bindings = bindings,
            .refs = refs,
        });
        return line_idx;
    }

    fn emitRefl(
        self: *Normalizer,
        relation: ResolvedRelation,
        expr_id: ExprId,
    ) Error!usize {
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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = expr,
            .rule_id = acui.assoc_id,
            .bindings = bindings,
            .refs = &.{},
        });
        return line_idx;
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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = expr,
            .rule_id = acui.comm_id orelse return error.MissingStructuralMetadata,
            .bindings = bindings,
            .refs = &.{},
        });
        return line_idx;
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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = expr,
            .rule_id = acui.idem_id orelse return error.MissingStructuralMetadata,
            .bindings = bindings,
            .refs = &.{},
        });
        return line_idx;
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

        const unit_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = theorem_expr,
            .rule_id = acui.left_unit_rule_id,
            .bindings = bindings,
            .refs = &.{},
        });
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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = trans_expr,
            .rule_id = relation.trans_id,
            .bindings = bindings,
            .refs = refs,
        });
        return line_idx;
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

        const line_idx = self.lines.items.len;
        try self.lines.append(self.allocator, .{
            .expr = target_expr,
            .rule_id = transport_id,
            .bindings = bindings,
            .refs = refs,
        });
        return line_idx;
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

