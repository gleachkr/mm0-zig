const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ViewDecl = @import("./compiler_views.zig").ViewDecl;
const RecoverDecl = @import("./compiler_views.zig").RecoverDecl;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;

const BinderSpace = enum {
    rule,
    view,
};

const MatchConstraint = struct {
    template: TemplateExpr,
    actual: ExprId,
};

const BranchState = struct {
    rule_bindings: []?ExprId,
    view_bindings: ?[]?ExprId,
};

pub const Solver = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    view: ?*const ViewDecl,
    canonicalizer: Canonicalizer,

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        theorem: *const TheoremContext,
        registry: *RewriteRegistry,
        rule: *const RuleDecl,
        view: ?*const ViewDecl,
    ) Solver {
        return .{
            .allocator = allocator,
            .env = env,
            .theorem = theorem,
            .registry = registry,
            .rule = rule,
            .view = view,
            .canonicalizer = Canonicalizer.init(
                allocator,
                @constCast(theorem),
                registry,
                env,
            ),
        };
    }

    pub fn solve(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        line_expr: ExprId,
    ) anyerror![]const ExprId {
        var states = std.ArrayListUnmanaged(BranchState){};
        try states.append(self.allocator, try self.initState(partial_bindings));

        if (self.view) |view| {
            var constraints = std.ArrayListUnmanaged(MatchConstraint){};
            for (view.hyps, ref_exprs) |hyp, actual| {
                try constraints.append(self.allocator, .{
                    .template = hyp,
                    .actual = actual,
                });
            }
            try constraints.append(self.allocator, .{
                .template = view.concl,
                .actual = line_expr,
            });
            states = try self.applyConstraints(states.items, constraints.items, .view);
            states = try self.applyRecovers(states.items, view.recovers);
            try self.propagateViewBindings(states.items, view);
        } else {
            var constraints = std.ArrayListUnmanaged(MatchConstraint){};
            for (self.rule.hyps, ref_exprs) |hyp, actual| {
                try constraints.append(self.allocator, .{
                    .template = hyp,
                    .actual = actual,
                });
            }
            try constraints.append(self.allocator, .{
                .template = self.rule.concl,
                .actual = line_expr,
            });
            states = try self.applyConstraints(states.items, constraints.items, .rule);
        }

        return try self.pickUniqueSolution(states.items);
    }

    fn initState(
        self: *Solver,
        partial_bindings: []const ?ExprId,
    ) !BranchState {
        const rule_bindings = try self.allocator.dupe(?ExprId, partial_bindings);
        const view_bindings = if (self.view) |view| blk: {
            const result = try self.allocator.alloc(?ExprId, view.num_binders);
            @memset(result, null);
            for (view.binder_map, 0..) |mapping, idx| {
                const rule_idx = mapping orelse continue;
                result[idx] = partial_bindings[rule_idx];
            }
            break :blk result;
        } else null;
        return .{
            .rule_bindings = rule_bindings,
            .view_bindings = view_bindings,
        };
    }

    fn applyConstraints(
        self: *Solver,
        states: []const BranchState,
        constraints: []const MatchConstraint,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var current = std.ArrayListUnmanaged(BranchState){};
        try current.appendSlice(self.allocator, states);

        for (constraints) |constraint| {
            var next = std.ArrayListUnmanaged(BranchState){};
            for (current.items) |state| {
                const matches = try self.matchExpr(
                    constraint.template,
                    constraint.actual,
                    space,
                    state,
                );
                try next.appendSlice(self.allocator, matches);
            }
            if (next.items.len == 0) return error.UnifyMismatch;
            current = next;
        }
        return current;
    }

    fn applyRecovers(
        self: *Solver,
        states: []const BranchState,
        recovers: []const RecoverDecl,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        for (states) |state| {
            var new_state = try self.cloneState(state);
            var ok = true;
            for (recovers) |recover| {
                self.applyRecover(&new_state, recover) catch {
                    ok = false;
                    break;
                };
            }
            if (ok) try next.append(self.allocator, new_state);
        }
        if (next.items.len == 0) return error.UnifyMismatch;
        return next;
    }

    fn propagateViewBindings(
        self: *Solver,
        states: []BranchState,
        view: *const ViewDecl,
    ) anyerror!void {
        _ = self;
        for (states) |*state| {
            const view_bindings = state.view_bindings orelse continue;
            for (view.binder_map, 0..) |mapping, vi| {
                const rule_idx = mapping orelse continue;
                const binding = view_bindings[vi] orelse continue;
                if (state.rule_bindings[rule_idx]) |existing| {
                    if (existing != binding) return error.ViewBindingConflict;
                } else {
                    state.rule_bindings[rule_idx] = binding;
                }
            }
        }
    }

    fn pickUniqueSolution(
        self: *Solver,
        states: []const BranchState,
    ) anyerror![]const ExprId {
        if (states.len == 0) return error.UnifyMismatch;

        var unique_idx: ?usize = null;
        for (states, 0..) |state, idx| {
            for (state.rule_bindings) |binding| {
                if (binding == null) return error.MissingBinderAssignment;
            }
            if (unique_idx == null) {
                unique_idx = idx;
                continue;
            }
            if (!sameRuleBindings(
                states[unique_idx.?].rule_bindings,
                state.rule_bindings,
            )) {
                return error.AmbiguousAcuiMatch;
            }
        }

        const chosen = states[unique_idx.?].rule_bindings;
        const result = try self.allocator.alloc(ExprId, chosen.len);
        for (chosen, 0..) |binding, idx| {
            result[idx] = binding.?;
        }
        return result;
    }

    fn matchExpr(
        self: *Solver,
        template: TemplateExpr,
        actual: ExprId,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        if (try self.matchAcui(template, actual, space, state)) |states| {
            return states;
        }

        return switch (template) {
            .binder => |idx| blk: {
                var new_state = try self.cloneState(state);
                const bindings = self.getBindings(&new_state, space);
                if (idx >= bindings.len) break :blk &.{};
                if (bindings[idx]) |existing| {
                    if (!try self.bindingCompatible(existing, actual)) {
                        break :blk &.{};
                    }
                } else {
                    bindings[idx] = try self.canonicalizer.canonicalize(actual);
                }
                const out = try self.allocator.alloc(BranchState, 1);
                out[0] = new_state;
                break :blk out;
            },
            .app => |app| blk: {
                const node = self.theorem.interner.node(actual);
                const actual_app = switch (node.*) {
                    .app => |value| value,
                    .variable => break :blk &.{},
                };
                if (actual_app.term_id != app.term_id or
                    actual_app.args.len != app.args.len)
                {
                    break :blk &.{};
                }
                var states = std.ArrayListUnmanaged(BranchState){};
                try states.append(self.allocator, try self.cloneState(state));
                for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
                    var next = std.ArrayListUnmanaged(BranchState){};
                    for (states.items) |current| {
                        const matches = try self.matchExpr(
                            tmpl_arg,
                            actual_arg,
                            space,
                            current,
                        );
                        try next.appendSlice(self.allocator, matches);
                    }
                    if (next.items.len == 0) break :blk &.{};
                    states = next;
                }
                break :blk try states.toOwnedSlice(self.allocator);
            },
        };
    }

    fn matchAcui(
        self: *Solver,
        template: TemplateExpr,
        actual: ExprId,
        space: BinderSpace,
        state: BranchState,
    ) anyerror!?[]BranchState {
        const app = switch (template) {
            .app => |value| value,
            .binder => return null,
        };
        const acui = self.registry.resolveStructuralCombiner(self.env, app.term_id)
            orelse return null;

        var template_items = std.ArrayListUnmanaged(TemplateExpr){};
        var remainder: ?usize = null;
        try self.collectTemplateAcuiItems(
            template,
            space,
            acui,
            &template_items,
            &remainder,
        );

        const canon_actual = try self.canonicalizer.canonicalize(actual);
        var actual_items = std.ArrayListUnmanaged(ExprId){};
        try self.collectConcreteAcuiItems(canon_actual, acui, &actual_items);

        var matches = std.ArrayListUnmanaged(BranchState){};
        try self.matchAcuiItems(
            template_items.items,
            actual_items.items,
            remainder,
            space,
            state,
            &matches,
            acui,
        );
        if (matches.items.len == 0) return &.{};
        return try matches.toOwnedSlice(self.allocator);
    }

    fn matchAcuiItems(
        self: *Solver,
        template_items: []const TemplateExpr,
        actual_items: []const ExprId,
        remainder: ?usize,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        acui: anytype,
    ) anyerror!void {
        const used = try self.allocator.alloc(bool, actual_items.len);
        @memset(used, false);
        try self.matchAcuiItemsRec(
            template_items,
            actual_items,
            remainder,
            space,
            0,
            used,
            state,
            out,
            acui,
        );
    }

    fn matchAcuiItemsRec(
        self: *Solver,
        template_items: []const TemplateExpr,
        actual_items: []const ExprId,
        remainder: ?usize,
        space: BinderSpace,
        next_item: usize,
        used: []bool,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        acui: anytype,
    ) anyerror!void {
        if (next_item >= template_items.len) {
            var leftover = std.ArrayListUnmanaged(ExprId){};
            for (actual_items, used) |actual_item, is_used| {
                if (!is_used) try leftover.append(self.allocator, actual_item);
            }
            const remainder_expr = try self.rebuildAcui(
                leftover.items,
                acui.head_term_id,
                acui.unit_term_id,
            );
            var final_state = try self.cloneState(state);
            if (remainder) |idx| {
                const bindings = self.getBindings(&final_state, space);
                if (bindings[idx]) |existing| {
                    if (!try self.bindingCompatible(existing, remainder_expr)) {
                        return;
                    }
                } else {
                    bindings[idx] = remainder_expr;
                }
            } else if (leftover.items.len != 0) {
                return;
            }
            try out.append(self.allocator, final_state);
            return;
        }

        for (actual_items, 0..) |actual_item, actual_idx| {
            if (used[actual_idx]) continue;
            const matches = try self.matchExpr(
                template_items[next_item],
                actual_item,
                space,
                state,
            );
            for (matches) |next_state| {
                const next_used = try self.allocator.dupe(bool, used);
                next_used[actual_idx] = true;
                try self.matchAcuiItemsRec(
                    template_items,
                    actual_items,
                    remainder,
                    space,
                    next_item + 1,
                    next_used,
                    next_state,
                    out,
                    acui,
                );
            }
        }
    }

    fn collectTemplateAcuiItems(
        self: *Solver,
        template: TemplateExpr,
        space: BinderSpace,
        acui: anytype,
        out: *std.ArrayListUnmanaged(TemplateExpr),
        remainder: *?usize,
    ) anyerror!void {
        switch (template) {
            .binder => |idx| {
                if (self.isAcuiRemainderBinder(space, idx, acui.head_term_id)) {
                    if (remainder.* != null) {
                        return error.MultipleAcuiRemainders;
                    }
                    remainder.* = idx;
                    return;
                }
                try out.append(self.allocator, template);
            },
            .app => |app| {
                if (app.term_id == acui.head_term_id and app.args.len == 2) {
                    try self.collectTemplateAcuiItems(
                        app.args[0],
                        space,
                        acui,
                        out,
                        remainder,
                    );
                    try self.collectTemplateAcuiItems(
                        app.args[1],
                        space,
                        acui,
                        out,
                        remainder,
                    );
                    return;
                }
                if (app.term_id == acui.unit_term_id and app.args.len == 0) {
                    return;
                }
                try out.append(self.allocator, template);
            },
        }
    }

    fn collectConcreteAcuiItems(
        self: *Solver,
        expr_id: ExprId,
        acui: anytype,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => try out.append(self.allocator, expr_id),
            .app => |app| {
                if (app.term_id == acui.head_term_id and app.args.len == 2) {
                    try self.collectConcreteAcuiItems(app.args[0], acui, out);
                    try self.collectConcreteAcuiItems(app.args[1], acui, out);
                    return;
                }
                if (app.term_id == acui.unit_term_id and app.args.len == 0) {
                    return;
                }
                try out.append(self.allocator, expr_id);
            },
        }
    }

    fn rebuildAcui(
        self: *Solver,
        items: []const ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        if (items.len == 0) {
            return try @constCast(&self.theorem.interner).internApp(
                unit_term_id,
                &.{},
            );
        }
        if (items.len == 1) return items[0];

        var current = items[items.len - 1];
        var idx = items.len - 1;
        while (idx > 0) {
            idx -= 1;
            current = try @constCast(&self.theorem.interner).internApp(
                head_term_id,
                &[_]ExprId{ items[idx], current },
            );
        }
        return current;
    }

    fn isAcuiRemainderBinder(
        self: *Solver,
        space: BinderSpace,
        idx: usize,
        head_term_id: u32,
    ) bool {
        const sort_name = self.getBinderSort(space, idx) orelse return false;
        const term_decl = if (head_term_id < self.env.terms.items.len)
            &self.env.terms.items[head_term_id]
        else
            return false;
        return std.mem.eql(u8, sort_name, term_decl.ret_sort_name);
    }

    fn getBinderSort(self: *Solver, space: BinderSpace, idx: usize) ?[]const u8 {
        return switch (space) {
            .rule => if (idx < self.rule.args.len)
                self.rule.args[idx].sort_name
            else
                null,
            .view => if (self.view) |view|
                if (idx < view.arg_infos.len)
                    view.arg_infos[idx].sort_name
                else
                    null
            else
                null,
        };
    }

    fn getBindings(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) []?ExprId {
        _ = self;
        return switch (space) {
            .rule => state.rule_bindings,
            .view => state.view_bindings.?,
        };
    }

    fn bindingCompatible(
        self: *Solver,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!bool {
        if (lhs == rhs) return true;
        return try self.canonicalizer.canonicalize(lhs) ==
            try self.canonicalizer.canonicalize(rhs);
    }

    fn cloneState(
        self: *Solver,
        state: BranchState,
    ) anyerror!BranchState {
        return .{
            .rule_bindings = try self.allocator.dupe(?ExprId, state.rule_bindings),
            .view_bindings = if (state.view_bindings) |bindings|
                try self.allocator.dupe(?ExprId, bindings)
            else
                null,
        };
    }

    fn applyRecover(
        self: *Solver,
        state: *BranchState,
        recover: RecoverDecl,
    ) anyerror!void {
        const view_bindings = state.view_bindings orelse return error.RecoverWithoutView;
        if (view_bindings[recover.target_view_idx] != null) return;

        const source = view_bindings[recover.source_view_idx] orelse {
            return error.RecoverSourceUnsolved;
        };
        const pattern = view_bindings[recover.pattern_view_idx] orelse {
            return error.RecoverPatternUnsolved;
        };
        const hole = view_bindings[recover.hole_view_idx] orelse {
            return error.RecoverHoleUnsolved;
        };

        var candidate: ?ExprId = null;
        const found = try self.recoverBindingCandidate(
            source,
            pattern,
            hole,
            &candidate,
        );
        if (!found) return error.RecoverHoleNotFound;
        view_bindings[recover.target_view_idx] = candidate;
    }

    fn recoverBindingCandidate(
        self: *Solver,
        source_expr: ExprId,
        pattern_expr: ExprId,
        hole_expr: ExprId,
        candidate: *?ExprId,
    ) anyerror!bool {
        if (pattern_expr == hole_expr) {
            if (candidate.*) |existing| {
                if (existing != source_expr) return error.RecoverConflict;
            } else {
                candidate.* = source_expr;
            }
            return true;
        }
        if (source_expr == pattern_expr) return false;

        const source_node = self.theorem.interner.node(source_expr);
        const pattern_node = self.theorem.interner.node(pattern_expr);
        return switch (pattern_node.*) {
            .variable => error.RecoverStructureMismatch,
            .app => |pattern_app| switch (source_node.*) {
                .variable => error.RecoverStructureMismatch,
                .app => |source_app| blk: {
                    if (source_app.term_id != pattern_app.term_id or
                        source_app.args.len != pattern_app.args.len)
                    {
                        return error.RecoverStructureMismatch;
                    }
                    var found = false;
                    for (source_app.args, pattern_app.args) |source_arg, pattern_arg| {
                        found = (try self.recoverBindingCandidate(
                            source_arg,
                            pattern_arg,
                            hole_expr,
                            candidate,
                        )) or found;
                    }
                    break :blk found;
                },
            },
        };
    }
};

fn sameRuleBindings(lhs: []const ?ExprId, rhs: []const ?ExprId) bool {
    if (lhs.len != rhs.len) return false;
    for (lhs, rhs) |l, r| {
        if (l != r) return false;
    }
    return true;
}
