const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ViewDecl = @import("./compiler_views.zig").ViewDecl;
const DerivedBinding = @import("./compiler_views.zig").DerivedBinding;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("./acui_support.zig");
const compareExprIds = AcuiSupport.compareExprIds;
const DerivedBindings = @import("./derived_bindings.zig");
const DefOps = @import("./def_ops.zig");

const BinderSpace = enum {
    rule,
    view,
};

const MatchConstraint = struct {
    template: TemplateExpr,
    actual: ExprId,
};

const AcuiInterval = struct {
    // For a single ACUI remainder binder Γ, accumulate constraints as
    // lower_expr ⊆ Γ ⊆ upper_expr.
    head_term_id: u32,
    unit_term_id: u32,
    lower_expr: ExprId,
    upper_expr: ExprId,
};

const BranchState = struct {
    rule_bindings: []?ExprId,
    view_bindings: ?[]?ExprId,
    rule_acui_intervals: []?AcuiInterval,
    view_acui_intervals: ?[]?AcuiInterval,
};

pub const Solver = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    view: ?*const ViewDecl,
    canonicalizer: Canonicalizer,

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        theorem: *TheoremContext,
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
            states = try self.applyConstraints(
                states.items,
                constraints.items,
                .view,
            );
            states = try self.finalizeAcuiStates(states.items, .view);
            states = try self.applyDerivedBindings(
                states.items,
                view.derived_bindings,
            );
            states = try self.finalizeAcuiStates(states.items, .view);
            try self.propagateViewBindings(states.items, view);
            states = try self.finalizeAcuiStates(states.items, .rule);
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
            states = try self.applyConstraints(
                states.items,
                constraints.items,
                .rule,
            );
            states = try self.finalizeAcuiStates(states.items, .rule);
        }

        return try self.pickUniqueSolution(states.items);
    }

    fn initState(
        self: *Solver,
        partial_bindings: []const ?ExprId,
    ) !BranchState {
        const rule_bindings = try self.allocator.dupe(?ExprId, partial_bindings);
        const rule_acui_intervals =
            try self.allocator.alloc(?AcuiInterval, partial_bindings.len);
        @memset(rule_acui_intervals, null);
        const view_bindings = if (self.view) |view| blk: {
            const result = try self.allocator.alloc(?ExprId, view.num_binders);
            @memset(result, null);
            for (view.binder_map, 0..) |mapping, idx| {
                const rule_idx = mapping orelse continue;
                result[idx] = partial_bindings[rule_idx];
            }
            break :blk result;
        } else null;
        const view_acui_intervals = if (self.view) |view| blk: {
            const result =
                try self.allocator.alloc(?AcuiInterval, view.num_binders);
            @memset(result, null);
            break :blk result;
        } else null;
        return .{
            .rule_bindings = rule_bindings,
            .view_bindings = view_bindings,
            .rule_acui_intervals = rule_acui_intervals,
            .view_acui_intervals = view_acui_intervals,
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

    fn applyDerivedBindings(
        self: *Solver,
        states: []const BranchState,
        derived_bindings: []const DerivedBinding,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        var first_err: ?anyerror = null;
        for (states) |state| {
            const new_state = try self.cloneState(state);
            const view_bindings = new_state.view_bindings orelse {
                try next.append(self.allocator, new_state);
                continue;
            };
            DerivedBindings.applyDerivedBindings(
                self.theorem,
                view_bindings,
                derived_bindings,
            ) catch |err| {
                if (first_err == null) first_err = err;
                continue;
            };
            try next.append(self.allocator, new_state);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    fn finalizeAcuiStates(
        self: *Solver,
        states: []const BranchState,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        var first_err: ?anyerror = null;
        for (states) |state| {
            var new_state = try self.cloneState(state);
            self.finalizeAcuiBindings(&new_state, space) catch |err| {
                if (first_err == null) first_err = err;
                continue;
            };
            try next.append(self.allocator, new_state);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    fn finalizeAcuiBindings(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!void {
        const bindings = self.getBindings(state, space);
        const intervals = self.getAcuiIntervals(state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            if (bindings[idx]) |existing| {
                if (!try self.exprWithinInterval(existing, interval)) {
                    return error.UnifyMismatch;
                }
                continue;
            }
            bindings[idx] = interval.lower_expr;
        }
    }

    fn propagateViewBindings(
        self: *Solver,
        states: []BranchState,
        view: *const ViewDecl,
    ) anyerror!void {
        for (states) |*state| {
            const view_bindings = state.view_bindings orelse continue;
            for (view.binder_map, 0..) |mapping, vi| {
                const rule_idx = mapping orelse continue;
                const binding = view_bindings[vi] orelse continue;
                if (state.rule_bindings[rule_idx]) |existing| {
                    if (!try self.bindingCompatible(existing, binding)) {
                        return error.ViewBindingConflict;
                    }
                } else {
                    if (!try self.bindingSatisfiesAcui(
                        state,
                        .rule,
                        rule_idx,
                        binding,
                    )) {
                        return error.ViewBindingConflict;
                    }
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
            if (!try self.sameRuleBindingsCompatible(
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
                    if (!try self.bindingSatisfiesAcui(
                        &new_state,
                        space,
                        idx,
                        actual,
                    )) {
                        break :blk &.{};
                    }
                    bindings[idx] = actual;
                }
                const out = try self.allocator.alloc(BranchState, 1);
                out[0] = new_state;
                break :blk out;
            },
            .app => |app| blk: {
                const node = self.theorem.interner.node(actual);
                const actual_app = switch (node.*) {
                    .app => |value| value,
                    .variable => {
                        break :blk try self.matchExprTransparent(
                            template,
                            actual,
                            space,
                            state,
                        );
                    },
                };
                if (actual_app.term_id != app.term_id or
                    actual_app.args.len != app.args.len)
                {
                    break :blk try self.matchExprTransparent(
                        template,
                        actual,
                        space,
                        state,
                    );
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
        const acui = self.registry.resolveStructuralCombiner(self.env, app.term_id) orelse return null;

        const bindings = self.getBindings(@constCast(&state), space);

        var template_items = std.ArrayListUnmanaged(TemplateExpr){};
        defer template_items.deinit(self.allocator);
        var pre_required = std.ArrayListUnmanaged(ExprId){};
        defer pre_required.deinit(self.allocator);
        var remainder: ?usize = null;
        try self.collectTemplateAcuiItems(
            template,
            space,
            acui,
            &template_items,
            &remainder,
            bindings,
            &pre_required,
        );

        var actual_items = std.ArrayListUnmanaged(ExprId){};
        defer actual_items.deinit(self.allocator);
        try self.collectCanonicalAcuiSetItems(
            actual,
            acui.head_term_id,
            acui.unit_term_id,
            &actual_items,
        );

        const used = try self.allocator.alloc(bool, actual_items.items.len);
        defer self.allocator.free(used);
        @memset(used, false);

        // Pre-mark actual items that match bound remainder binders
        for (pre_required.items) |required| {
            var found = false;
            for (actual_items.items, 0..) |actual_item, idx| {
                if (compareExprIds(self.theorem, required, actual_item) == .eq) {
                    used[idx] = true;
                    found = true;
                    break;
                }
            }
            if (!found) return &.{};
        }

        var matches = std.ArrayListUnmanaged(BranchState){};
        try self.matchAcuiObligations(
            template_items.items,
            actual_items.items,
            remainder,
            space,
            0,
            used,
            state,
            &matches,
            acui.head_term_id,
            acui.unit_term_id,
        );
        if (matches.items.len == 0) return &.{};
        return try matches.toOwnedSlice(self.allocator);
    }

    fn matchAcuiObligations(
        self: *Solver,
        template_items: []const TemplateExpr,
        actual_items: []const ExprId,
        remainder: ?usize,
        space: BinderSpace,
        next_item: usize,
        used: []bool,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!void {
        if (next_item >= template_items.len) {
            try self.appendAcuiIntervalState(
                actual_items,
                used,
                remainder,
                space,
                state,
                out,
                head_term_id,
                unit_term_id,
            );
            return;
        }

        for (actual_items, 0..) |actual_item, actual_idx| {
            const matches = try self.matchExpr(
                template_items[next_item],
                actual_item,
                space,
                state,
            );
            for (matches) |next_state| {
                const was_used = used[actual_idx];
                used[actual_idx] = true;
                try self.matchAcuiObligations(
                    template_items,
                    actual_items,
                    remainder,
                    space,
                    next_item + 1,
                    used,
                    next_state,
                    out,
                    head_term_id,
                    unit_term_id,
                );
                used[actual_idx] = was_used;
            }
        }
    }

    fn appendAcuiIntervalState(
        self: *Solver,
        actual_items: []const ExprId,
        used: []const bool,
        remainder: ?usize,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!void {
        if (remainder == null) {
            for (used) |is_used| {
                if (!is_used) return;
            }
            try out.append(self.allocator, try self.cloneState(state));
            return;
        }

        const interval = try self.buildAcuiInterval(
            actual_items,
            used,
            head_term_id,
            unit_term_id,
        );
        var final_state = try self.cloneState(state);
        const remainder_idx = remainder.?;
        const intervals = self.getAcuiIntervals(&final_state, space);
        const bindings = self.getBindings(&final_state, space);
        const combined = if (intervals[remainder_idx]) |existing|
            (try self.combineAcuiIntervals(existing, interval)) orelse return
        else
            interval;

        if (bindings[remainder_idx]) |existing| {
            if (!try self.exprWithinInterval(existing, combined)) return;
        }
        intervals[remainder_idx] = combined;
        try out.append(self.allocator, final_state);
    }

    fn buildAcuiInterval(
        self: *Solver,
        actual_items: []const ExprId,
        used: []const bool,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!AcuiInterval {
        var lower_items = std.ArrayListUnmanaged(ExprId){};
        defer lower_items.deinit(self.allocator);
        for (actual_items, used) |actual_item, is_used| {
            if (!is_used) try lower_items.append(self.allocator, actual_item);
        }
        return .{
            .head_term_id = head_term_id,
            .unit_term_id = unit_term_id,
            .lower_expr = try self.rebuildAcui(
                lower_items.items,
                head_term_id,
                unit_term_id,
            ),
            .upper_expr = try self.rebuildAcui(
                actual_items,
                head_term_id,
                unit_term_id,
            ),
        };
    }

    fn combineAcuiIntervals(
        self: *Solver,
        lhs: AcuiInterval,
        rhs: AcuiInterval,
    ) anyerror!?AcuiInterval {
        if (lhs.head_term_id != rhs.head_term_id or
            lhs.unit_term_id != rhs.unit_term_id)
        {
            return error.UnifyMismatch;
        }

        const lower_expr = try self.unionAcuiExprs(
            lhs.lower_expr,
            rhs.lower_expr,
            lhs.head_term_id,
            lhs.unit_term_id,
        );
        const upper_expr = try self.intersectAcuiExprs(
            lhs.upper_expr,
            rhs.upper_expr,
            lhs.head_term_id,
            lhs.unit_term_id,
        );
        if (!try self.acuiExprSubset(
            lower_expr,
            upper_expr,
            lhs.head_term_id,
            lhs.unit_term_id,
        )) {
            return null;
        }

        return .{
            .head_term_id = lhs.head_term_id,
            .unit_term_id = lhs.unit_term_id,
            .lower_expr = lower_expr,
            .upper_expr = upper_expr,
        };
    }

    fn collectTemplateAcuiItems(
        self: *Solver,
        template: TemplateExpr,
        space: BinderSpace,
        acui: anytype,
        out: *std.ArrayListUnmanaged(TemplateExpr),
        remainder: *?usize,
        bindings: []const ?ExprId,
        pre_required: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        switch (template) {
            .binder => |idx| {
                if (self.isAcuiRemainderBinder(space, idx, acui.head_term_id)) {
                    if (idx < bindings.len) {
                        if (bindings[idx]) |bound_value| {
                            try self.collectConcreteAcuiSetItems(
                                bound_value,
                                acui.head_term_id,
                                acui.unit_term_id,
                                pre_required,
                            );
                            return;
                        }
                    }
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
                        bindings,
                        pre_required,
                    );
                    try self.collectTemplateAcuiItems(
                        app.args[1],
                        space,
                        acui,
                        out,
                        remainder,
                        bindings,
                        pre_required,
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

    fn collectCanonicalAcuiSetItems(
        self: *Solver,
        expr_id: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        try self.collectConcreteAcuiSetItems(
            try self.canonicalizer.canonicalize(expr_id),
            head_term_id,
            unit_term_id,
            out,
        );
    }

    fn collectConcreteAcuiSetItems(
        self: *Solver,
        expr_id: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => try self.appendAcuiSetItem(out, expr_id),
            .app => |app| {
                if (app.term_id == head_term_id and app.args.len == 2) {
                    try self.collectConcreteAcuiSetItems(
                        app.args[0],
                        head_term_id,
                        unit_term_id,
                        out,
                    );
                    try self.collectConcreteAcuiSetItems(
                        app.args[1],
                        head_term_id,
                        unit_term_id,
                        out,
                    );
                    return;
                }
                if (app.term_id == unit_term_id and app.args.len == 0) {
                    return;
                }
                try self.appendAcuiSetItem(out, expr_id);
            },
        }
    }

    fn appendAcuiSetItem(
        self: *Solver,
        out: *std.ArrayListUnmanaged(ExprId),
        expr_id: ExprId,
    ) anyerror!void {
        if (out.items.len == 0) {
            try out.append(self.allocator, expr_id);
            return;
        }

        switch (compareExprIds(
            self.theorem,
            out.items[out.items.len - 1],
            expr_id,
        )) {
            .lt => {
                try out.append(self.allocator, expr_id);
                return;
            },
            .eq => return,
            .gt => {},
        }

        var insert_at: usize = 0;
        while (insert_at < out.items.len) : (insert_at += 1) {
            switch (compareExprIds(
                self.theorem,
                out.items[insert_at],
                expr_id,
            )) {
                .lt => continue,
                .eq => return,
                .gt => break,
            }
        }

        try out.insert(self.allocator, insert_at, expr_id);
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

    fn getAcuiIntervals(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) []?AcuiInterval {
        _ = self;
        return switch (space) {
            .rule => state.rule_acui_intervals,
            .view => state.view_acui_intervals.?,
        };
    }

    fn bindingSatisfiesAcui(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
        idx: usize,
        expr_id: ExprId,
    ) anyerror!bool {
        const intervals = self.getAcuiIntervals(state, space);
        if (idx >= intervals.len) return true;
        const interval = intervals[idx] orelse return true;
        return try self.exprWithinInterval(expr_id, interval);
    }

    fn exprWithinInterval(
        self: *Solver,
        expr_id: ExprId,
        interval: AcuiInterval,
    ) anyerror!bool {
        const canonical_expr = try self.canonicalizer.canonicalize(expr_id);
        return try self.acuiExprSubset(
            interval.lower_expr,
            canonical_expr,
            interval.head_term_id,
            interval.unit_term_id,
        ) and try self.acuiExprSubset(
            canonical_expr,
            interval.upper_expr,
            interval.head_term_id,
            interval.unit_term_id,
        );
    }

    fn acuiExprSubset(
        self: *Solver,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!bool {
        var lhs_items = std.ArrayListUnmanaged(ExprId){};
        defer lhs_items.deinit(self.allocator);
        var rhs_items = std.ArrayListUnmanaged(ExprId){};
        defer rhs_items.deinit(self.allocator);
        try self.collectCanonicalAcuiSetItems(
            lhs_expr,
            head_term_id,
            unit_term_id,
            &lhs_items,
        );
        try self.collectCanonicalAcuiSetItems(
            rhs_expr,
            head_term_id,
            unit_term_id,
            &rhs_items,
        );
        return sortedExprSetIsSubset(
            self.theorem,
            lhs_items.items,
            rhs_items.items,
        );
    }

    fn unionAcuiExprs(
        self: *Solver,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        var lhs_items = std.ArrayListUnmanaged(ExprId){};
        defer lhs_items.deinit(self.allocator);
        var rhs_items = std.ArrayListUnmanaged(ExprId){};
        defer rhs_items.deinit(self.allocator);
        try self.collectCanonicalAcuiSetItems(
            lhs_expr,
            head_term_id,
            unit_term_id,
            &lhs_items,
        );
        try self.collectCanonicalAcuiSetItems(
            rhs_expr,
            head_term_id,
            unit_term_id,
            &rhs_items,
        );

        var merged = std.ArrayListUnmanaged(ExprId){};
        defer merged.deinit(self.allocator);
        try merged.ensureTotalCapacity(
            self.allocator,
            lhs_items.items.len + rhs_items.items.len,
        );
        try appendSortedExprSetUnion(
            self.theorem,
            self.allocator,
            &merged,
            lhs_items.items,
            rhs_items.items,
        );
        return try self.rebuildAcui(
            merged.items,
            head_term_id,
            unit_term_id,
        );
    }

    fn intersectAcuiExprs(
        self: *Solver,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        var lhs_items = std.ArrayListUnmanaged(ExprId){};
        defer lhs_items.deinit(self.allocator);
        var rhs_items = std.ArrayListUnmanaged(ExprId){};
        defer rhs_items.deinit(self.allocator);
        try self.collectCanonicalAcuiSetItems(
            lhs_expr,
            head_term_id,
            unit_term_id,
            &lhs_items,
        );
        try self.collectCanonicalAcuiSetItems(
            rhs_expr,
            head_term_id,
            unit_term_id,
            &rhs_items,
        );

        var merged = std.ArrayListUnmanaged(ExprId){};
        defer merged.deinit(self.allocator);
        try merged.ensureTotalCapacity(
            self.allocator,
            @min(lhs_items.items.len, rhs_items.items.len),
        );
        try appendSortedExprSetIntersection(
            self.theorem,
            self.allocator,
            &merged,
            lhs_items.items,
            rhs_items.items,
        );
        return try self.rebuildAcui(
            merged.items,
            head_term_id,
            unit_term_id,
        );
    }

    fn bindingCompatible(
        self: *Solver,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!bool {
        if (lhs == rhs) return true;
        const lhs_canon = try self.canonicalizer.canonicalize(lhs);
        const rhs_canon = try self.canonicalizer.canonicalize(rhs);
        if (lhs_canon == rhs_canon) return true;
        return try self.exprMatchesTransparent(lhs_canon, rhs_canon);
    }

    fn exprMatchesTransparent(
        self: *Solver,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!bool {
        var def_ops = DefOps.Context.init(
            self.allocator,
            self.theorem,
            self.env,
        );
        defer def_ops.deinit();
        return (def_ops.compareTransparent(lhs, rhs) catch |err| switch (err) {
            error.DependencySlotExhausted => return false,
            else => return err,
        }) != null;
    }

    fn matchExprTransparent(
        self: *Solver,
        template: TemplateExpr,
        actual: ExprId,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        var new_state = try self.cloneState(state);
        const bindings = self.getBindings(&new_state, space);
        const old_bindings = switch (space) {
            .rule => state.rule_bindings,
            .view => state.view_bindings.?,
        };

        var def_ops = DefOps.Context.init(
            self.allocator,
            self.theorem,
            self.env,
        );
        defer def_ops.deinit();
        if (!(def_ops.matchTemplateTransparent(
            template,
            actual,
            bindings,
        ) catch |err| switch (err) {
            error.DependencySlotExhausted => return &.{},
            else => return err,
        })) {
            return &.{};
        }
        for (bindings, old_bindings, 0..) |binding, old_binding, idx| {
            const expr_id = binding orelse continue;
            if (old_binding != null) continue;
            if (!try self.bindingSatisfiesAcui(
                &new_state,
                space,
                idx,
                expr_id,
            )) {
                return &.{};
            }
        }

        const out = try self.allocator.alloc(BranchState, 1);
        out[0] = new_state;
        return out;
    }

    fn sameRuleBindingsCompatible(
        self: *Solver,
        lhs: []const ?ExprId,
        rhs: []const ?ExprId,
    ) anyerror!bool {
        if (lhs.len != rhs.len) return false;
        for (lhs, rhs) |l, r| {
            if (l == null or r == null) {
                if (l != r) return false;
                continue;
            }
            if (!try self.bindingCompatible(l.?, r.?)) return false;
        }
        return true;
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
            .rule_acui_intervals = try self.allocator.dupe(
                ?AcuiInterval,
                state.rule_acui_intervals,
            ),
            .view_acui_intervals = if (state.view_acui_intervals) |intervals|
                try self.allocator.dupe(?AcuiInterval, intervals)
            else
                null,
        };
    }
};

fn sortedExprSetIsSubset(
    theorem: *const TheoremContext,
    lhs: []const ExprId,
    rhs: []const ExprId,
) bool {
    var lhs_idx: usize = 0;
    var rhs_idx: usize = 0;
    while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
        switch (compareExprIds(theorem, lhs[lhs_idx], rhs[rhs_idx])) {
            .lt => return false,
            .eq => {
                lhs_idx += 1;
                rhs_idx += 1;
            },
            .gt => rhs_idx += 1,
        }
    }
    return lhs_idx == lhs.len;
}

fn appendSortedExprSetUnion(
    theorem: *const TheoremContext,
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(ExprId),
    lhs: []const ExprId,
    rhs: []const ExprId,
) !void {
    var lhs_idx: usize = 0;
    var rhs_idx: usize = 0;
    while (lhs_idx < lhs.len or rhs_idx < rhs.len) {
        if (lhs_idx >= lhs.len) {
            try out.append(allocator, rhs[rhs_idx]);
            rhs_idx += 1;
            continue;
        }
        if (rhs_idx >= rhs.len) {
            try out.append(allocator, lhs[lhs_idx]);
            lhs_idx += 1;
            continue;
        }
        switch (compareExprIds(theorem, lhs[lhs_idx], rhs[rhs_idx])) {
            .lt => {
                try out.append(allocator, lhs[lhs_idx]);
                lhs_idx += 1;
            },
            .eq => {
                try out.append(allocator, lhs[lhs_idx]);
                lhs_idx += 1;
                rhs_idx += 1;
            },
            .gt => {
                try out.append(allocator, rhs[rhs_idx]);
                rhs_idx += 1;
            },
        }
    }
}

fn appendSortedExprSetIntersection(
    theorem: *const TheoremContext,
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(ExprId),
    lhs: []const ExprId,
    rhs: []const ExprId,
) !void {
    var lhs_idx: usize = 0;
    var rhs_idx: usize = 0;
    while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
        switch (compareExprIds(theorem, lhs[lhs_idx], rhs[rhs_idx])) {
            .lt => lhs_idx += 1,
            .eq => {
                try out.append(allocator, lhs[lhs_idx]);
                lhs_idx += 1;
                rhs_idx += 1;
            },
            .gt => rhs_idx += 1,
        }
    }
}
