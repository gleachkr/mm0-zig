const builtin = @import("builtin");
const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const ViewDecl = @import("./compiler/views.zig").ViewDecl;
const DerivedBinding = @import("./compiler/views.zig").DerivedBinding;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("./acui_support.zig");
const compareExprIds = AcuiSupport.compareExprIds;
const DerivedBindings = @import("./derived_bindings.zig");
const DefOps = @import("./def_ops.zig");
const ViewTrace = @import("./view_trace.zig");

const BinderSpace = enum {
    rule,
    view,
};

const MatchConstraint = struct {
    template: TemplateExpr,
    actual: ExprId,
};

const StructuralFragment = enum {
    au,
    acu,
    aui,
    acui,
};

const StructuralProfile = struct {
    combiner: ResolvedStructuralCombiner,
    fragment: StructuralFragment,

    fn init(combiner: ResolvedStructuralCombiner) StructuralProfile {
        const fragment: StructuralFragment = if (combiner.comm_id != null) blk: {
            break :blk if (combiner.idem_id != null) .acui else .acu;
        } else blk: {
            break :blk if (combiner.idem_id != null) .aui else .au;
        };
        return .{
            .combiner = combiner,
            .fragment = fragment,
        };
    }

    fn headTermId(self: StructuralProfile) u32 {
        return self.combiner.head_term_id;
    }

    fn unitTermId(self: StructuralProfile) u32 {
        return self.combiner.unit_term_id;
    }

    fn isCommutative(self: StructuralProfile) bool {
        return switch (self.fragment) {
            .acu, .acui => true,
            .au, .aui => false,
        };
    }

    fn isIdempotent(self: StructuralProfile) bool {
        return switch (self.fragment) {
            .aui, .acui => true,
            .au, .acu => false,
        };
    }
};

const StructuralTemplateItem = union(enum) {
    template: TemplateExpr,
    exact: ExprId,
};

const StructuralRemainder = struct {
    binder_idx: usize,
    item_pos: usize,
};

const StructuralJointObligation = struct {
    head_term_id: u32,
    unit_term_id: u32,
    lower_expr: ExprId,
    upper_expr: ExprId,
    binder_idxs: []const usize,
};

const StructuralInterval = struct {
    // Per-binder structural bounds. For ACUI these are real lower / upper
    // set bounds; for the other fragments Stage 3 still uses exact
    // lower == upper intervals and carries multi-binder obligations
    // separately.
    head_term_id: u32,
    unit_term_id: u32,
    lower_expr: ExprId,
    upper_expr: ExprId,
};

const BranchState = struct {
    rule_bindings: []?ExprId,
    view_bindings: ?[]?ExprId,
    rule_structural_intervals: []?StructuralInterval,
    view_structural_intervals: ?[]?StructuralInterval,
    rule_structural_obligations: []StructuralJointObligation,
    view_structural_obligations: ?[]StructuralJointObligation,
};

pub const Solver = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    view: ?*const ViewDecl,
    canonicalizer: Canonicalizer,
    debug_inference: bool,
    ambiguity_warning: bool = false,

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        rule: *const RuleDecl,
        view: ?*const ViewDecl,
        debug_inference: bool,
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
            .debug_inference = debug_inference,
        };
    }

    pub fn hadAmbiguityWarning(self: *const Solver) bool {
        return self.ambiguity_warning;
    }

    // This entry point is supposed to infer omitted structural binders for
    // every fragment we advertise through `@acui`: AU, ACU, AUI, and ACUI.
    // That means preserving the fragment's order / multiplicity semantics
    // while still handling structural matches that leave several remainder
    // binders unresolved until later constraints or finalization.
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
            states = try self.finalizeStructuralStates(states.items, .view);
            states = try self.applyDerivedBindings(
                states.items,
                view.derived_bindings,
            );
            states = try self.finalizeStructuralStates(states.items, .view);
            try self.propagateViewBindings(states.items, view);
            states = try self.finalizeStructuralStates(states.items, .rule);
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
            states = try self.finalizeStructuralStates(states.items, .rule);
        }

        return try self.pickUniqueSolution(states.items);
    }

    fn initState(
        self: *Solver,
        partial_bindings: []const ?ExprId,
    ) !BranchState {
        const rule_bindings = try self.allocator.dupe(?ExprId, partial_bindings);
        const rule_structural_intervals =
            try self.allocator.alloc(
                ?StructuralInterval,
                partial_bindings.len,
            );
        @memset(rule_structural_intervals, null);
        const view_bindings = if (self.view) |view| blk: {
            const result = try self.allocator.alloc(?ExprId, view.num_binders);
            @memset(result, null);
            for (view.binder_map, 0..) |mapping, idx| {
                const rule_idx = mapping orelse continue;
                result[idx] = partial_bindings[rule_idx];
            }
            break :blk result;
        } else null;
        const view_structural_intervals = if (self.view) |view| blk: {
            const result = try self.allocator.alloc(
                ?StructuralInterval,
                view.num_binders,
            );
            @memset(result, null);
            break :blk result;
        } else null;
        const rule_structural_obligations =
            try self.allocator.alloc(StructuralJointObligation, 0);
        const view_structural_obligations = if (self.view != null)
            try self.allocator.alloc(StructuralJointObligation, 0)
        else
            null;
        return .{
            .rule_bindings = rule_bindings,
            .view_bindings = view_bindings,
            .rule_structural_intervals = rule_structural_intervals,
            .view_structural_intervals = view_structural_intervals,
            .rule_structural_obligations = rule_structural_obligations,
            .view_structural_obligations = view_structural_obligations,
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
                self.env,
                self.registry,
                .{ .view_bindings = view_bindings },
                derived_bindings,
                self.view.?.arg_names,
                false,
            ) catch |err| {
                if (first_err == null) first_err = err;
                continue;
            };
            try next.append(self.allocator, new_state);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    fn finalizeStructuralStates(
        self: *Solver,
        states: []const BranchState,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        var first_err: ?anyerror = null;
        for (states) |state| {
            const finalized = self.finalizeStructuralBindings(
                state,
                space,
            ) catch |err| {
                if (first_err == null) first_err = err;
                continue;
            };
            try next.appendSlice(self.allocator, finalized);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    fn finalizeStructuralBindings(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
    ) anyerror![]BranchState {
        var out = std.ArrayListUnmanaged(BranchState){};
        try self.searchStructuralFinalizations(state, space, &out);
        if (out.items.len == 0) return error.UnifyMismatch;
        return try out.toOwnedSlice(self.allocator);
    }

    fn searchStructuralFinalizations(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        var current = try self.cloneState(state);
        if (!try self.partialStructuralStateCompatible(&current, space)) {
            return;
        }

        if (self.nextUnresolvedStructuralObligation(&current, space)) |idx| {
            const obligations = self.getStructuralObligations(&current, space);
            const branches = try self.solveStructuralObligation(
                current,
                space,
                obligations[idx],
            );
            for (branches) |branch| {
                try self.searchStructuralFinalizations(branch, space, out);
            }
            return;
        }

        try self.fillDeterministicStructuralBindings(&current, space);
        if (!try self.allStructuralObligationsSatisfied(&current, space)) {
            return;
        }
        try self.appendUniqueStateForSpace(out, current, space);
    }

    fn partialStructuralStateCompatible(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!bool {
        const bindings = self.getBindings(state, space);
        const intervals = self.getStructuralIntervals(state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            const binding = bindings[idx] orelse continue;
            if (!try self.exprWithinInterval(binding, interval)) {
                return false;
            }
        }
        const obligations = self.getStructuralObligations(state, space);
        for (obligations) |obligation| {
            if (!try self.obligationCompatibleWithState(
                state,
                space,
                obligation,
            )) {
                return false;
            }
        }
        return true;
    }

    fn nextUnresolvedStructuralObligation(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) ?usize {
        const bindings = self.getBindings(state, space);
        const obligations = self.getStructuralObligations(state, space);
        var best_idx: ?usize = null;
        var best_unbound: usize = std.math.maxInt(usize);
        for (obligations, 0..) |obligation, idx| {
            var unbound: usize = 0;
            for (obligation.binder_idxs) |binder_idx| {
                if (binder_idx >= bindings.len or
                    bindings[binder_idx] == null)
                {
                    unbound += 1;
                }
            }
            if (unbound != 0 and unbound < best_unbound) {
                best_unbound = unbound;
                best_idx = idx;
            }
        }
        return best_idx;
    }

    fn fillDeterministicStructuralBindings(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!void {
        const bindings = self.getBindings(state, space);
        const intervals = self.getStructuralIntervals(state, space);
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

    fn allStructuralObligationsSatisfied(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!bool {
        const bindings = self.getBindings(state, space);
        const obligations = self.getStructuralObligations(state, space);
        for (obligations) |obligation| {
            for (obligation.binder_idxs) |binder_idx| {
                if (binder_idx >= bindings.len or
                    bindings[binder_idx] == null)
                {
                    return false;
                }
            }
            if (!try self.obligationSatisfied(bindings, obligation)) {
                return false;
            }
        }
        return true;
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
                    if (!try self.bindingSatisfiesStructural(
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

        var distinct_idxs = std.ArrayListUnmanaged(usize){};
        defer distinct_idxs.deinit(self.allocator);

        for (states, 0..) |state, idx| {
            for (state.rule_bindings) |binding| {
                if (binding == null) return error.MissingBinderAssignment;
            }

            var already_seen = false;
            for (distinct_idxs.items) |seen_idx| {
                if (try self.sameRuleBindingsCompatible(
                    states[seen_idx].rule_bindings,
                    state.rule_bindings,
                )) {
                    already_seen = true;
                    break;
                }
            }
            if (!already_seen) {
                try distinct_idxs.append(self.allocator, idx);
            }
        }

        if (distinct_idxs.items.len > 1) {
            self.ambiguity_warning = true;
            if (self.debug_inference) {
                try self.debugPrintAmbiguousSolutions(
                    states,
                    distinct_idxs.items,
                );
            }
        }

        const chosen = states[distinct_idxs.items[0]].rule_bindings;
        const result = try self.allocator.alloc(ExprId, chosen.len);
        for (chosen, 0..) |binding, idx| {
            result[idx] = binding.?;
        }
        return result;
    }

    fn debugPrintAmbiguousSolutions(
        self: *Solver,
        states: []const BranchState,
        distinct_idxs: []const usize,
    ) !void {
        if (comptime builtin.target.os.tag == .freestanding) return;

        debugPrint(
            "[debug:inference] omitted binders left {d} distinct final " ++
                "solutions; choosing the first\n",
            .{distinct_idxs.len},
        );
        for (distinct_idxs, 0..) |state_idx, choice_idx| {
            debugPrint(
                "[debug:inference]   solution {d}{s}\n",
                .{
                    choice_idx + 1,
                    if (choice_idx == 0) " (chosen)" else "",
                },
            );
            try self.debugPrintRuleBindings(states[state_idx].rule_bindings);
        }
    }

    fn debugPrintRuleBindings(
        self: *Solver,
        bindings: []const ?ExprId,
    ) !void {
        for (bindings, 0..) |binding, idx| {
            const name = self.rule.arg_names[idx] orelse "_";
            if (binding) |expr_id| {
                const text = try ViewTrace.formatExpr(
                    self.allocator,
                    self.theorem,
                    self.env,
                    expr_id,
                );
                defer self.allocator.free(text);
                debugPrint(
                    "[debug:inference]     {s}#{d} = {s}\n",
                    .{ name, idx, text },
                );
            } else {
                debugPrint(
                    "[debug:inference]     {s}#{d} = <null>\n",
                    .{ name, idx },
                );
            }
        }
    }

    fn matchExpr(
        self: *Solver,
        template: TemplateExpr,
        actual: ExprId,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        if (try self.matchStructural(template, actual, space, state)) |states| {
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
                    if (!try self.bindingSatisfiesStructural(
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

    fn matchStructural(
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
        const profile =
            self.resolveStructuralProfile(app.term_id) orelse return null;

        const bindings = self.getBindings(@constCast(&state), space);

        var template_items = std.ArrayListUnmanaged(StructuralTemplateItem){};
        defer template_items.deinit(self.allocator);
        var pre_required = std.ArrayListUnmanaged(ExprId){};
        defer pre_required.deinit(self.allocator);
        var remainders = std.ArrayListUnmanaged(StructuralRemainder){};
        defer remainders.deinit(self.allocator);
        try self.collectTemplateStructuralItems(
            template,
            space,
            profile,
            &template_items,
            &remainders,
            bindings,
            &pre_required,
        );

        var actual_items = std.ArrayListUnmanaged(ExprId){};
        defer actual_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            actual,
            profile,
            &actual_items,
        );

        if (!profile.isCommutative()) {
            if (pre_required.items.len != 0) return &.{};
            const matches = try self.matchOrderedStructural(
                template_items.items,
                actual_items.items,
                remainders.items,
                space,
                state,
                profile,
            );
            return matches;
        }

        const used = try self.allocator.alloc(bool, actual_items.items.len);
        defer self.allocator.free(used);
        @memset(used, false);

        for (pre_required.items) |required| {
            var found = false;
            for (actual_items.items, 0..) |actual_item, idx| {
                if (profile.fragment != .acui and used[idx]) continue;
                if (!try self.bindingCompatible(required, actual_item)) continue;
                used[idx] = true;
                found = true;
                break;
            }
            if (!found) return &.{};
        }

        var matches = std.ArrayListUnmanaged(BranchState){};
        try self.matchCommutativeStructuralObligations(
            template_items.items,
            actual_items.items,
            remainders.items,
            space,
            0,
            used,
            state,
            &matches,
            profile,
        );
        if (matches.items.len == 0) return &.{};
        return try matches.toOwnedSlice(self.allocator);
    }

    fn matchOrderedStructural(
        self: *Solver,
        template_items: []const StructuralTemplateItem,
        actual_items: []const ExprId,
        remainders: []const StructuralRemainder,
        space: BinderSpace,
        state: BranchState,
        profile: StructuralProfile,
    ) anyerror![]BranchState {
        if (actual_items.len < template_items.len) return &.{};

        const matched_positions =
            try self.allocator.alloc(usize, template_items.len);
        defer self.allocator.free(matched_positions);

        var out = std.ArrayListUnmanaged(BranchState){};
        try self.matchOrderedStructuralAnchors(
            template_items,
            actual_items,
            remainders,
            space,
            state,
            profile,
            0,
            0,
            matched_positions,
            &out,
        );
        if (out.items.len == 0) return &.{};
        return try out.toOwnedSlice(self.allocator);
    }

    fn matchOrderedStructuralAnchors(
        self: *Solver,
        template_items: []const StructuralTemplateItem,
        actual_items: []const ExprId,
        remainders: []const StructuralRemainder,
        space: BinderSpace,
        state: BranchState,
        profile: StructuralProfile,
        next_item: usize,
        actual_start: usize,
        matched_positions: []usize,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        if (next_item >= template_items.len) {
            try self.appendOrderedStructuralMatchState(
                actual_items,
                remainders,
                matched_positions[0..template_items.len],
                space,
                state,
                out,
                profile,
            );
            return;
        }

        var actual_idx = actual_start;
        while (actual_idx + (template_items.len - next_item) <= actual_items.len) : (actual_idx += 1) {
            const matches = try self.matchStructuralItem(
                template_items[next_item],
                actual_items[actual_idx],
                space,
                state,
            );
            for (matches) |next_state| {
                matched_positions[next_item] = actual_idx;
                try self.matchOrderedStructuralAnchors(
                    template_items,
                    actual_items,
                    remainders,
                    space,
                    next_state,
                    profile,
                    next_item + 1,
                    actual_idx + 1,
                    matched_positions,
                    out,
                );
            }
        }
    }

    fn appendOrderedStructuralMatchState(
        self: *Solver,
        actual_items: []const ExprId,
        remainders: []const StructuralRemainder,
        matched_positions: []const usize,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        profile: StructuralProfile,
    ) anyerror!void {
        var states = std.ArrayListUnmanaged(BranchState){};
        try states.append(self.allocator, try self.cloneState(state));

        var segment_start: usize = 0;
        var remainder_start: usize = 0;
        var segment_idx: usize = 0;
        while (segment_idx <= matched_positions.len) : (segment_idx += 1) {
            const segment_end = if (segment_idx < matched_positions.len)
                matched_positions[segment_idx]
            else
                actual_items.len;
            const segment_items = actual_items[segment_start..segment_end];

            const group_start = remainder_start;
            while (remainder_start < remainders.len and
                remainders[remainder_start].item_pos == segment_idx) : (remainder_start += 1)
            {}
            const group = remainders[group_start..remainder_start];

            var next = std.ArrayListUnmanaged(BranchState){};
            if (group.len == 0) {
                if (segment_items.len != 0) return;
                try next.appendSlice(self.allocator, states.items);
            } else if (group.len == 1) {
                for (states.items) |current| {
                    try self.appendExactStructuralIntervalState(
                        group[0].binder_idx,
                        segment_items,
                        space,
                        current,
                        &next,
                        profile,
                    );
                }
            } else {
                const interval = try self.buildExactStructuralInterval(
                    segment_items,
                    profile,
                );
                for (states.items) |current| {
                    try self.appendCombinedStructuralObligationState(
                        group,
                        interval,
                        space,
                        current,
                        &next,
                    );
                }
            }
            if (next.items.len == 0) return;
            states = next;

            if (segment_idx < matched_positions.len) {
                segment_start = matched_positions[segment_idx] + 1;
            }
        }

        try out.appendSlice(self.allocator, states.items);
    }

    fn matchCommutativeStructuralObligations(
        self: *Solver,
        template_items: []const StructuralTemplateItem,
        actual_items: []const ExprId,
        remainders: []const StructuralRemainder,
        space: BinderSpace,
        next_item: usize,
        used: []bool,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        profile: StructuralProfile,
    ) anyerror!void {
        if (next_item >= template_items.len) {
            try self.appendStructuralRemainderState(
                actual_items,
                used,
                remainders,
                space,
                state,
                out,
                profile,
            );
            return;
        }

        for (actual_items, 0..) |actual_item, actual_idx| {
            if (profile.fragment != .acui and used[actual_idx]) continue;
            const matches = try self.matchStructuralItem(
                template_items[next_item],
                actual_item,
                space,
                state,
            );
            for (matches) |next_state| {
                const was_used = used[actual_idx];
                used[actual_idx] = true;
                try self.matchCommutativeStructuralObligations(
                    template_items,
                    actual_items,
                    remainders,
                    space,
                    next_item + 1,
                    used,
                    next_state,
                    out,
                    profile,
                );
                used[actual_idx] = was_used;
            }
        }
    }

    fn matchStructuralItem(
        self: *Solver,
        item: StructuralTemplateItem,
        actual: ExprId,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        return switch (item) {
            .template => |tmpl| try self.matchExpr(tmpl, actual, space, state),
            .exact => |expected| blk: {
                if (!try self.bindingCompatible(expected, actual)) {
                    break :blk &.{};
                }
                const out = try self.allocator.alloc(BranchState, 1);
                out[0] = try self.cloneState(state);
                break :blk out;
            },
        };
    }

    fn appendStructuralRemainderState(
        self: *Solver,
        actual_items: []const ExprId,
        used: []const bool,
        remainders: []const StructuralRemainder,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        profile: StructuralProfile,
    ) anyerror!void {
        if (remainders.len == 0) {
            for (used) |is_used| {
                if (!is_used) return;
            }
            try out.append(self.allocator, try self.cloneState(state));
            return;
        }

        const interval = try self.buildStructuralInterval(
            actual_items,
            used,
            profile,
        );
        if (remainders.len == 1) {
            try self.appendCombinedStructuralIntervalState(
                remainders[0].binder_idx,
                interval,
                space,
                state,
                out,
            );
            return;
        }

        try self.appendCombinedStructuralObligationState(
            remainders,
            interval,
            space,
            state,
            out,
        );
    }

    fn appendExactStructuralIntervalState(
        self: *Solver,
        binder_idx: usize,
        items: []const ExprId,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
        profile: StructuralProfile,
    ) anyerror!void {
        try self.appendCombinedStructuralIntervalState(
            binder_idx,
            try self.buildExactStructuralInterval(items, profile),
            space,
            state,
            out,
        );
    }

    fn appendCombinedStructuralObligationState(
        self: *Solver,
        remainders: []const StructuralRemainder,
        interval: StructuralInterval,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        var final_state = try self.cloneState(state);
        const binder_idxs = try self.allocator.alloc(usize, remainders.len);
        for (remainders, 0..) |remainder, idx| {
            binder_idxs[idx] = remainder.binder_idx;
        }
        const obligation: StructuralJointObligation = .{
            .head_term_id = interval.head_term_id,
            .unit_term_id = interval.unit_term_id,
            .lower_expr = interval.lower_expr,
            .upper_expr = interval.upper_expr,
            .binder_idxs = binder_idxs,
        };
        if (!try self.obligationCompatibleWithState(
            &final_state,
            space,
            obligation,
        )) {
            self.allocator.free(binder_idxs);
            return;
        }

        var obligations = self.getStructuralObligations(&final_state, space);
        for (obligations, 0..) |existing, idx| {
            if (existing.head_term_id != obligation.head_term_id or
                existing.unit_term_id != obligation.unit_term_id or
                !std.mem.eql(
                    usize,
                    existing.binder_idxs,
                    obligation.binder_idxs,
                ))
            {
                continue;
            }
            const combined =
                (try self.combineStructuralObligations(
                    existing,
                    obligation,
                )) orelse {
                    self.allocator.free(binder_idxs);
                    return;
                };
            if (!try self.obligationCompatibleWithState(
                &final_state,
                space,
                combined,
            )) {
                self.allocator.free(binder_idxs);
                return;
            }
            obligations[idx].lower_expr = combined.lower_expr;
            obligations[idx].upper_expr = combined.upper_expr;
            self.allocator.free(binder_idxs);
            try out.append(self.allocator, final_state);
            return;
        }

        obligations = try self.allocator.realloc(
            obligations,
            obligations.len + 1,
        );
        self.setStructuralObligations(&final_state, space, obligations);
        obligations[obligations.len - 1] = obligation;
        try out.append(self.allocator, final_state);
    }

    fn appendCombinedStructuralIntervalState(
        self: *Solver,
        binder_idx: usize,
        interval: StructuralInterval,
        space: BinderSpace,
        state: BranchState,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        var final_state = try self.cloneState(state);
        const intervals = self.getStructuralIntervals(&final_state, space);
        const bindings = self.getBindings(&final_state, space);
        const combined = if (intervals[binder_idx]) |existing|
            (try self.combineStructuralIntervals(existing, interval)) orelse return
        else
            interval;

        if (bindings[binder_idx]) |existing| {
            if (!try self.exprWithinInterval(existing, combined)) return;
        }
        intervals[binder_idx] = combined;
        try out.append(self.allocator, final_state);
    }

    fn solveStructuralObligation(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
    ) anyerror![]BranchState {
        const profile = self.resolveStructuralProfile(
            obligation.head_term_id,
        ) orelse return error.UnifyMismatch;
        if (profile.unitTermId() != obligation.unit_term_id) {
            return error.UnifyMismatch;
        }
        return switch (profile.fragment) {
            .au, .aui => try self.solveOrderedStructuralObligation(
                state,
                space,
                obligation,
                profile,
            ),
            .acu => try self.solveAcuStructuralObligation(
                state,
                space,
                obligation,
                profile,
            ),
            .acui => try self.solveAcuiStructuralObligation(
                state,
                space,
                obligation,
                profile,
            ),
        };
    }

    fn solveOrderedStructuralObligation(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
        profile: StructuralProfile,
    ) anyerror![]BranchState {
        var target_items = std.ArrayListUnmanaged(ExprId){};
        defer target_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            obligation.lower_expr,
            profile,
            &target_items,
        );

        const binder_exprs = try self.allocator.alloc(
            ExprId,
            obligation.binder_idxs.len,
        );
        defer self.allocator.free(binder_exprs);

        var out = std.ArrayListUnmanaged(BranchState){};
        try self.searchOrderedStructuralObligationAssignments(
            state,
            space,
            obligation,
            profile,
            target_items.items,
            binder_exprs,
            0,
            0,
            &out,
        );
        return try out.toOwnedSlice(self.allocator);
    }

    fn searchOrderedStructuralObligationAssignments(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
        profile: StructuralProfile,
        target_items: []const ExprId,
        binder_exprs: []ExprId,
        binder_pos: usize,
        item_start: usize,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        if (binder_pos >= obligation.binder_idxs.len) {
            if (item_start != target_items.len) return;
            try self.appendStructuralCandidateState(
                state,
                space,
                obligation.binder_idxs,
                binder_exprs,
                out,
            );
            return;
        }

        var item_end = item_start;
        while (item_end <= target_items.len) : (item_end += 1) {
            const expr_id = try self.rebuildStructuralExpr(
                target_items[item_start..item_end],
                profile.headTermId(),
                profile.unitTermId(),
            );
            if (!try self.candidateBindingCompatible(
                &state,
                space,
                obligation.binder_idxs[binder_pos],
                expr_id,
            )) {
                continue;
            }
            binder_exprs[binder_pos] = expr_id;
            try self.searchOrderedStructuralObligationAssignments(
                state,
                space,
                obligation,
                profile,
                target_items,
                binder_exprs,
                binder_pos + 1,
                item_end,
                out,
            );
        }
    }

    fn solveAcuStructuralObligation(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
        profile: StructuralProfile,
    ) anyerror![]BranchState {
        var target_items = std.ArrayListUnmanaged(ExprId){};
        defer target_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            obligation.lower_expr,
            profile,
            &target_items,
        );

        const binder_items = try self.allocator.alloc(
            std.ArrayListUnmanaged(ExprId),
            obligation.binder_idxs.len,
        );
        defer {
            for (binder_items) |*items| items.deinit(self.allocator);
            self.allocator.free(binder_items);
        }
        for (binder_items) |*items| items.* = .{};

        var out = std.ArrayListUnmanaged(BranchState){};
        try self.searchAcuStructuralObligationAssignments(
            state,
            space,
            obligation,
            profile,
            target_items.items,
            binder_items,
            0,
            &out,
        );
        return try out.toOwnedSlice(self.allocator);
    }

    fn searchAcuStructuralObligationAssignments(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
        profile: StructuralProfile,
        target_items: []const ExprId,
        binder_items: []std.ArrayListUnmanaged(ExprId),
        item_pos: usize,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        if (item_pos >= target_items.len) {
            const binder_exprs = try self.allocator.alloc(
                ExprId,
                obligation.binder_idxs.len,
            );
            defer self.allocator.free(binder_exprs);
            for (binder_items, 0..) |items, idx| {
                binder_exprs[idx] = try self.rebuildStructuralExpr(
                    items.items,
                    profile.headTermId(),
                    profile.unitTermId(),
                );
            }
            try self.appendStructuralCandidateState(
                state,
                space,
                obligation.binder_idxs,
                binder_exprs,
                out,
            );
            return;
        }

        for (binder_items) |*items| {
            try items.append(self.allocator, target_items[item_pos]);
            try self.searchAcuStructuralObligationAssignments(
                state,
                space,
                obligation,
                profile,
                target_items,
                binder_items,
                item_pos + 1,
                out,
            );
            _ = items.pop();
        }
    }

    fn solveAcuiStructuralObligation(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
        profile: StructuralProfile,
    ) anyerror![]BranchState {
        var lower_items = std.ArrayListUnmanaged(ExprId){};
        defer lower_items.deinit(self.allocator);
        var upper_items = std.ArrayListUnmanaged(ExprId){};
        defer upper_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            obligation.lower_expr,
            profile,
            &lower_items,
        );
        try self.collectCanonicalStructuralItems(
            obligation.upper_expr,
            profile,
            &upper_items,
        );

        const binder_lowers = try self.allocator.alloc(
            std.ArrayListUnmanaged(ExprId),
            obligation.binder_idxs.len,
        );
        defer {
            for (binder_lowers) |*items| items.deinit(self.allocator);
            self.allocator.free(binder_lowers);
        }
        const binder_uppers = try self.allocator.alloc(
            std.ArrayListUnmanaged(ExprId),
            obligation.binder_idxs.len,
        );
        defer {
            for (binder_uppers) |*items| items.deinit(self.allocator);
            self.allocator.free(binder_uppers);
        }
        const binder_items = try self.allocator.alloc(
            std.ArrayListUnmanaged(ExprId),
            obligation.binder_idxs.len,
        );
        defer {
            for (binder_items) |*items| items.deinit(self.allocator);
            self.allocator.free(binder_items);
        }
        for (binder_lowers, binder_uppers, binder_items, obligation.binder_idxs) |
            *lower, *upper, *items, binder_idx|
        {
            lower.* = .{};
            upper.* = .{};
            items.* = .{};
            try self.collectAcuiBinderBounds(
                &state,
                space,
                binder_idx,
                profile,
                upper_items.items,
                lower,
                upper,
            );
        }

        var out = std.ArrayListUnmanaged(BranchState){};
        try self.searchAcuiStructuralObligationAssignments(
            state,
            space,
            obligation,
            profile,
            lower_items.items,
            upper_items.items,
            binder_lowers,
            binder_uppers,
            binder_items,
            0,
            &out,
        );
        return try out.toOwnedSlice(self.allocator);
    }

    fn searchAcuiStructuralObligationAssignments(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
        profile: StructuralProfile,
        lower_items: []const ExprId,
        upper_items: []const ExprId,
        binder_lowers: []const std.ArrayListUnmanaged(ExprId),
        binder_uppers: []const std.ArrayListUnmanaged(ExprId),
        binder_items: []std.ArrayListUnmanaged(ExprId),
        item_pos: usize,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        if (item_pos >= upper_items.len) {
            const binder_exprs = try self.allocator.alloc(
                ExprId,
                obligation.binder_idxs.len,
            );
            defer self.allocator.free(binder_exprs);
            for (binder_items, 0..) |items, idx| {
                binder_exprs[idx] = try self.rebuildStructuralExpr(
                    items.items,
                    profile.headTermId(),
                    profile.unitTermId(),
                );
            }
            try self.appendStructuralCandidateState(
                state,
                space,
                obligation.binder_idxs,
                binder_exprs,
                out,
            );
            return;
        }

        const item = upper_items[item_pos];
        const global_required = structuralItemsContain(
            self.theorem,
            lower_items,
            item,
        );
        var required_mask: usize = 0;
        var allowed_mask: usize = 0;
        for (binder_lowers, binder_uppers, 0..) |lower, upper, idx| {
            if (structuralItemsContain(self.theorem, upper.items, item)) {
                allowed_mask |= (@as(usize, 1) << @intCast(idx));
            }
            if (structuralItemsContain(self.theorem, lower.items, item)) {
                required_mask |= (@as(usize, 1) << @intCast(idx));
            }
        }
        if ((required_mask & ~allowed_mask) != 0) return;
        const optional_mask = allowed_mask & ~required_mask;
        var choice = optional_mask;
        while (true) {
            const subset = required_mask | choice;
            if (!global_required or subset != 0) {
                for (binder_items, 0..) |*items, idx| {
                    if ((subset & (@as(usize, 1) << @intCast(idx))) != 0) {
                        try items.append(self.allocator, item);
                    }
                }
                try self.searchAcuiStructuralObligationAssignments(
                    state,
                    space,
                    obligation,
                    profile,
                    lower_items,
                    upper_items,
                    binder_lowers,
                    binder_uppers,
                    binder_items,
                    item_pos + 1,
                    out,
                );
                for (binder_items, 0..) |*items, idx| {
                    if ((subset & (@as(usize, 1) << @intCast(idx))) != 0) {
                        _ = items.pop();
                    }
                }
            }
            if (choice == 0) break;
            choice = (choice - 1) & optional_mask;
        }
    }

    fn collectAcuiBinderBounds(
        self: *Solver,
        state: *const BranchState,
        space: BinderSpace,
        binder_idx: usize,
        profile: StructuralProfile,
        default_upper_items: []const ExprId,
        lower_out: *std.ArrayListUnmanaged(ExprId),
        upper_out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        const bindings = self.getBindings(@constCast(state), space);
        const intervals = self.getStructuralIntervals(@constCast(state), space);
        if (binder_idx < bindings.len) {
            if (bindings[binder_idx]) |binding| {
                try self.collectCanonicalStructuralItems(
                    binding,
                    profile,
                    lower_out,
                );
                try upper_out.appendSlice(self.allocator, lower_out.items);
                return;
            }
        }
        if (binder_idx < intervals.len) {
            if (intervals[binder_idx]) |interval| {
                try self.collectCanonicalStructuralItems(
                    interval.lower_expr,
                    profile,
                    lower_out,
                );
                try self.collectCanonicalStructuralItems(
                    interval.upper_expr,
                    profile,
                    upper_out,
                );
                return;
            }
        }
        try upper_out.appendSlice(self.allocator, default_upper_items);
    }

    fn appendStructuralCandidateState(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        binder_idxs: []const usize,
        binder_exprs: []const ExprId,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        var next_state = try self.cloneState(state);
        for (binder_idxs, binder_exprs) |binder_idx, expr_id| {
            if (!try self.applyStructuralBindingCandidate(
                &next_state,
                space,
                binder_idx,
                expr_id,
            )) {
                return;
            }
        }
        if (!try self.partialStructuralStateCompatible(&next_state, space)) {
            return;
        }
        try self.appendUniqueStateForSpace(out, next_state, space);
    }

    fn appendUniqueStateForSpace(
        self: *Solver,
        out: *std.ArrayListUnmanaged(BranchState),
        state: BranchState,
        space: BinderSpace,
    ) anyerror!void {
        const candidate_bindings = switch (space) {
            .rule => state.rule_bindings,
            .view => state.view_bindings orelse return,
        };
        for (out.items) |existing| {
            const existing_bindings = switch (space) {
                .rule => existing.rule_bindings,
                .view => existing.view_bindings orelse continue,
            };
            if (try self.sameBindingsCompatible(
                existing_bindings,
                candidate_bindings,
            )) {
                return;
            }
        }
        try out.append(self.allocator, state);
    }

    fn applyStructuralBindingCandidate(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
        binder_idx: usize,
        expr_id: ExprId,
    ) anyerror!bool {
        const bindings = self.getBindings(state, space);
        if (binder_idx >= bindings.len) return false;
        if (bindings[binder_idx]) |existing| {
            return try self.bindingCompatible(existing, expr_id);
        }
        if (!try self.bindingSatisfiesStructural(
            state,
            space,
            binder_idx,
            expr_id,
        )) {
            return false;
        }
        bindings[binder_idx] = expr_id;
        return true;
    }

    fn candidateBindingCompatible(
        self: *Solver,
        state: *const BranchState,
        space: BinderSpace,
        binder_idx: usize,
        expr_id: ExprId,
    ) anyerror!bool {
        const bindings = self.getBindings(@constCast(state), space);
        if (binder_idx >= bindings.len) return false;
        if (bindings[binder_idx]) |existing| {
            return try self.bindingCompatible(existing, expr_id);
        }
        return try self.bindingSatisfiesStructural(
            @constCast(state),
            space,
            binder_idx,
            expr_id,
        );
    }

    fn buildStructuralInterval(
        self: *Solver,
        actual_items: []const ExprId,
        used: []const bool,
        profile: StructuralProfile,
    ) anyerror!StructuralInterval {
        var lower_items = std.ArrayListUnmanaged(ExprId){};
        defer lower_items.deinit(self.allocator);
        for (actual_items, used) |actual_item, is_used| {
            if (!is_used) try lower_items.append(self.allocator, actual_item);
        }

        const lower_expr = try self.rebuildStructuralExpr(
            lower_items.items,
            profile.headTermId(),
            profile.unitTermId(),
        );
        const upper_expr = switch (profile.fragment) {
            .acui => try self.rebuildStructuralExpr(
                actual_items,
                profile.headTermId(),
                profile.unitTermId(),
            ),
            .au, .acu, .aui => lower_expr,
        };
        return .{
            .head_term_id = profile.headTermId(),
            .unit_term_id = profile.unitTermId(),
            .lower_expr = lower_expr,
            .upper_expr = upper_expr,
        };
    }

    fn buildExactStructuralInterval(
        self: *Solver,
        items: []const ExprId,
        profile: StructuralProfile,
    ) anyerror!StructuralInterval {
        const exact_expr = try self.rebuildStructuralExpr(
            items,
            profile.headTermId(),
            profile.unitTermId(),
        );
        return .{
            .head_term_id = profile.headTermId(),
            .unit_term_id = profile.unitTermId(),
            .lower_expr = exact_expr,
            .upper_expr = exact_expr,
        };
    }

    fn combineStructuralObligations(
        self: *Solver,
        lhs: StructuralJointObligation,
        rhs: StructuralJointObligation,
    ) anyerror!?StructuralJointObligation {
        if (lhs.head_term_id != rhs.head_term_id or
            lhs.unit_term_id != rhs.unit_term_id or
            !std.mem.eql(usize, lhs.binder_idxs, rhs.binder_idxs))
        {
            return error.UnifyMismatch;
        }
        const interval = (try self.combineStructuralIntervals(
            .{
                .head_term_id = lhs.head_term_id,
                .unit_term_id = lhs.unit_term_id,
                .lower_expr = lhs.lower_expr,
                .upper_expr = lhs.upper_expr,
            },
            .{
                .head_term_id = rhs.head_term_id,
                .unit_term_id = rhs.unit_term_id,
                .lower_expr = rhs.lower_expr,
                .upper_expr = rhs.upper_expr,
            },
        )) orelse return null;
        return .{
            .head_term_id = interval.head_term_id,
            .unit_term_id = interval.unit_term_id,
            .lower_expr = interval.lower_expr,
            .upper_expr = interval.upper_expr,
            .binder_idxs = lhs.binder_idxs,
        };
    }

    fn combineStructuralIntervals(
        self: *Solver,
        lhs: StructuralInterval,
        rhs: StructuralInterval,
    ) anyerror!?StructuralInterval {
        if (lhs.head_term_id != rhs.head_term_id or
            lhs.unit_term_id != rhs.unit_term_id)
        {
            return error.UnifyMismatch;
        }
        const profile = self.resolveStructuralProfile(lhs.head_term_id) orelse {
            return error.UnifyMismatch;
        };
        if (profile.unitTermId() != lhs.unit_term_id) {
            return error.UnifyMismatch;
        }

        return switch (profile.fragment) {
            .acui => blk: {
                const lower_expr = try self.unionStructuralExprs(
                    lhs.lower_expr,
                    rhs.lower_expr,
                    lhs.head_term_id,
                    lhs.unit_term_id,
                );
                const upper_expr = try self.intersectStructuralExprs(
                    lhs.upper_expr,
                    rhs.upper_expr,
                    lhs.head_term_id,
                    lhs.unit_term_id,
                );
                if (!try self.structuralExprSubset(
                    lower_expr,
                    upper_expr,
                    lhs.head_term_id,
                    lhs.unit_term_id,
                )) {
                    break :blk null;
                }
                break :blk .{
                    .head_term_id = lhs.head_term_id,
                    .unit_term_id = lhs.unit_term_id,
                    .lower_expr = lower_expr,
                    .upper_expr = upper_expr,
                };
            },
            .au, .acu, .aui => blk: {
                if (!try self.bindingCompatible(lhs.lower_expr, rhs.lower_expr)) {
                    break :blk null;
                }
                if (!try self.bindingCompatible(lhs.upper_expr, rhs.upper_expr)) {
                    break :blk null;
                }
                break :blk lhs;
            },
        };
    }

    fn collectTemplateStructuralItems(
        self: *Solver,
        template: TemplateExpr,
        space: BinderSpace,
        profile: StructuralProfile,
        out: *std.ArrayListUnmanaged(StructuralTemplateItem),
        remainders: *std.ArrayListUnmanaged(StructuralRemainder),
        bindings: []const ?ExprId,
        pre_required: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        switch (template) {
            .binder => |idx| {
                if (self.isStructuralRemainderBinder(space, idx, profile)) {
                    if (idx < bindings.len) {
                        if (bindings[idx]) |bound_value| {
                            var items = std.ArrayListUnmanaged(ExprId){};
                            defer items.deinit(self.allocator);
                            try self.collectCanonicalStructuralItems(
                                bound_value,
                                profile,
                                &items,
                            );
                            if (profile.isCommutative()) {
                                try pre_required.appendSlice(
                                    self.allocator,
                                    items.items,
                                );
                            } else {
                                for (items.items) |item| {
                                    try self.appendTemplateStructuralItem(
                                        profile,
                                        out,
                                        .{ .exact = item },
                                    );
                                }
                            }
                            return;
                        }
                    }
                    try remainders.append(self.allocator, .{
                        .binder_idx = idx,
                        .item_pos = out.items.len,
                    });
                    return;
                }
                try self.appendTemplateStructuralItem(
                    profile,
                    out,
                    .{ .template = template },
                );
            },
            .app => |app| {
                if (app.term_id == profile.headTermId() and app.args.len == 2) {
                    try self.collectTemplateStructuralItems(
                        app.args[0],
                        space,
                        profile,
                        out,
                        remainders,
                        bindings,
                        pre_required,
                    );
                    try self.collectTemplateStructuralItems(
                        app.args[1],
                        space,
                        profile,
                        out,
                        remainders,
                        bindings,
                        pre_required,
                    );
                    return;
                }
                if (app.term_id == profile.unitTermId() and app.args.len == 0) {
                    return;
                }
                try self.appendTemplateStructuralItem(
                    profile,
                    out,
                    .{ .template = template },
                );
            },
        }
    }

    fn collectCanonicalStructuralItems(
        self: *Solver,
        expr_id: ExprId,
        profile: StructuralProfile,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        try self.collectConcreteStructuralItems(
            try self.canonicalizer.canonicalize(expr_id),
            profile,
            out,
        );
    }

    fn collectConcreteStructuralItems(
        self: *Solver,
        expr_id: ExprId,
        profile: StructuralProfile,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => try self.appendStructuralItem(profile, out, expr_id),
            .app => |app| {
                if (app.term_id == profile.headTermId() and
                    app.args.len == 2)
                {
                    try self.collectConcreteStructuralItems(
                        app.args[0],
                        profile,
                        out,
                    );
                    try self.collectConcreteStructuralItems(
                        app.args[1],
                        profile,
                        out,
                    );
                    return;
                }
                if (app.term_id == profile.unitTermId() and
                    app.args.len == 0)
                {
                    return;
                }
                try self.appendStructuralItem(profile, out, expr_id);
            },
        }
    }

    fn appendStructuralItem(
        self: *Solver,
        profile: StructuralProfile,
        out: *std.ArrayListUnmanaged(ExprId),
        expr_id: ExprId,
    ) anyerror!void {
        switch (profile.fragment) {
            .au => try out.append(self.allocator, expr_id),
            .acu => try self.appendSortedStructuralItem(out, expr_id, false),
            .aui => {
                if (out.items.len != 0 and compareExprIds(
                    self.theorem,
                    out.items[out.items.len - 1],
                    expr_id,
                ) == .eq) return;
                try out.append(self.allocator, expr_id);
            },
            .acui => try self.appendSortedStructuralItem(out, expr_id, true),
        }
    }

    fn appendSortedStructuralItem(
        self: *Solver,
        out: *std.ArrayListUnmanaged(ExprId),
        expr_id: ExprId,
        dedup: bool,
    ) anyerror!void {
        if (out.items.len == 0) {
            try out.append(self.allocator, expr_id);
            return;
        }

        const last_cmp = compareExprIds(
            self.theorem,
            out.items[out.items.len - 1],
            expr_id,
        );
        if (last_cmp == .lt or last_cmp == .eq) {
            if (last_cmp == .eq and dedup) return;
            try out.append(self.allocator, expr_id);
            return;
        }

        var insert_at: usize = 0;
        while (insert_at < out.items.len) : (insert_at += 1) {
            const cmp = compareExprIds(
                self.theorem,
                out.items[insert_at],
                expr_id,
            );
            if (cmp == .lt) continue;
            if (cmp == .eq and dedup) return;
            if (cmp == .gt or (cmp == .eq and !dedup)) break;
        }
        try out.insert(self.allocator, insert_at, expr_id);
    }

    fn appendTemplateStructuralItem(
        self: *Solver,
        profile: StructuralProfile,
        out: *std.ArrayListUnmanaged(StructuralTemplateItem),
        item: StructuralTemplateItem,
    ) anyerror!void {
        if (profile.isIdempotent() and out.items.len != 0 and
            sameStructuralTemplateItem(out.items[out.items.len - 1], item))
        {
            return;
        }
        try out.append(self.allocator, item);
    }

    fn rebuildStructuralExpr(
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

    fn isStructuralRemainderBinder(
        self: *Solver,
        space: BinderSpace,
        idx: usize,
        profile: StructuralProfile,
    ) bool {
        const sort_name = self.getBinderSort(space, idx) orelse return false;
        const term_decl = if (profile.headTermId() < self.env.terms.items.len)
            &self.env.terms.items[profile.headTermId()]
        else
            return false;
        return std.mem.eql(u8, sort_name, term_decl.ret_sort_name);
    }

    fn resolveStructuralProfile(
        self: *Solver,
        head_term_id: u32,
    ) ?StructuralProfile {
        const combiner = self.registry.resolveStructuralCombiner(
            self.env,
            head_term_id,
        ) orelse return null;
        return StructuralProfile.init(combiner);
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

    fn getStructuralIntervals(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) []?StructuralInterval {
        _ = self;
        return switch (space) {
            .rule => state.rule_structural_intervals,
            .view => state.view_structural_intervals.?,
        };
    }

    fn getStructuralObligations(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) []StructuralJointObligation {
        _ = self;
        return switch (space) {
            .rule => state.rule_structural_obligations,
            .view => state.view_structural_obligations.?,
        };
    }

    fn setStructuralObligations(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
        obligations: []StructuralJointObligation,
    ) void {
        _ = self;
        switch (space) {
            .rule => state.rule_structural_obligations = obligations,
            .view => state.view_structural_obligations = obligations,
        }
    }

    fn bindingSatisfiesStructural(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
        idx: usize,
        expr_id: ExprId,
    ) anyerror!bool {
        const intervals = self.getStructuralIntervals(state, space);
        if (idx >= intervals.len) return true;
        const interval = intervals[idx] orelse return true;
        return try self.exprWithinInterval(expr_id, interval);
    }

    fn exprWithinInterval(
        self: *Solver,
        expr_id: ExprId,
        interval: StructuralInterval,
    ) anyerror!bool {
        const canonical_expr = try self.canonicalizer.canonicalize(expr_id);
        return try self.structuralExprSubset(
            interval.lower_expr,
            canonical_expr,
            interval.head_term_id,
            interval.unit_term_id,
        ) and try self.structuralExprSubset(
            canonical_expr,
            interval.upper_expr,
            interval.head_term_id,
            interval.unit_term_id,
        );
    }

    fn structuralExprSubset(
        self: *Solver,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!bool {
        const profile =
            self.resolveStructuralProfile(head_term_id) orelse return error.UnifyMismatch;
        if (profile.unitTermId() != unit_term_id) return error.UnifyMismatch;

        var lhs_items = std.ArrayListUnmanaged(ExprId){};
        defer lhs_items.deinit(self.allocator);
        var rhs_items = std.ArrayListUnmanaged(ExprId){};
        defer rhs_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            lhs_expr,
            profile,
            &lhs_items,
        );
        try self.collectCanonicalStructuralItems(
            rhs_expr,
            profile,
            &rhs_items,
        );
        return switch (profile.fragment) {
            .au, .aui => orderedExprItemsAreSubset(
                self.theorem,
                lhs_items.items,
                rhs_items.items,
            ),
            .acu => sortedExprBagIsSubset(
                self.theorem,
                lhs_items.items,
                rhs_items.items,
            ),
            .acui => sortedExprSetIsSubset(
                self.theorem,
                lhs_items.items,
                rhs_items.items,
            ),
        };
    }

    fn unionStructuralExprs(
        self: *Solver,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        const profile =
            self.resolveStructuralProfile(head_term_id) orelse return error.UnifyMismatch;
        if (profile.unitTermId() != unit_term_id) return error.UnifyMismatch;
        if (profile.fragment != .acui) return error.UnifyMismatch;

        var lhs_items = std.ArrayListUnmanaged(ExprId){};
        defer lhs_items.deinit(self.allocator);
        var rhs_items = std.ArrayListUnmanaged(ExprId){};
        defer rhs_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            lhs_expr,
            profile,
            &lhs_items,
        );
        try self.collectCanonicalStructuralItems(
            rhs_expr,
            profile,
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
        return try self.rebuildStructuralExpr(
            merged.items,
            head_term_id,
            unit_term_id,
        );
    }

    fn intersectStructuralExprs(
        self: *Solver,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        const profile =
            self.resolveStructuralProfile(head_term_id) orelse return error.UnifyMismatch;
        if (profile.unitTermId() != unit_term_id) return error.UnifyMismatch;
        if (profile.fragment != .acui) return error.UnifyMismatch;

        var lhs_items = std.ArrayListUnmanaged(ExprId){};
        defer lhs_items.deinit(self.allocator);
        var rhs_items = std.ArrayListUnmanaged(ExprId){};
        defer rhs_items.deinit(self.allocator);
        try self.collectCanonicalStructuralItems(
            lhs_expr,
            profile,
            &lhs_items,
        );
        try self.collectCanonicalStructuralItems(
            rhs_expr,
            profile,
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
        return try self.rebuildStructuralExpr(
            merged.items,
            head_term_id,
            unit_term_id,
        );
    }

    fn obligationCompatibleWithState(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
        obligation: StructuralJointObligation,
    ) anyerror!bool {
        const profile = self.resolveStructuralProfile(
            obligation.head_term_id,
        ) orelse return error.UnifyMismatch;
        if (profile.unitTermId() != obligation.unit_term_id) {
            return error.UnifyMismatch;
        }

        const bindings = self.getBindings(state, space);
        const intervals = self.getStructuralIntervals(state, space);
        var lower_parts = std.ArrayListUnmanaged(ExprId){};
        defer lower_parts.deinit(self.allocator);
        var upper_parts = std.ArrayListUnmanaged(ExprId){};
        defer upper_parts.deinit(self.allocator);
        var have_full_upper = true;

        for (obligation.binder_idxs) |binder_idx| {
            if (binder_idx >= bindings.len) return false;
            if (bindings[binder_idx]) |binding| {
                try lower_parts.append(self.allocator, binding);
                try upper_parts.append(self.allocator, binding);
                continue;
            }
            if (binder_idx < intervals.len) {
                if (intervals[binder_idx]) |interval| {
                    if (interval.head_term_id != obligation.head_term_id or
                        interval.unit_term_id != obligation.unit_term_id)
                    {
                        return false;
                    }
                    try lower_parts.append(
                        self.allocator,
                        interval.lower_expr,
                    );
                    try upper_parts.append(
                        self.allocator,
                        interval.upper_expr,
                    );
                    continue;
                }
            }
            have_full_upper = false;
        }

        if (lower_parts.items.len != 0) {
            const lower_expr = try self.combineStructuralExprs(
                profile,
                lower_parts.items,
            );
            if (!try self.structuralExprSubset(
                lower_expr,
                obligation.upper_expr,
                obligation.head_term_id,
                obligation.unit_term_id,
            )) {
                return false;
            }
        }
        if (have_full_upper) {
            const upper_expr = try self.combineStructuralExprs(
                profile,
                upper_parts.items,
            );
            if (!try self.structuralExprSubset(
                obligation.lower_expr,
                upper_expr,
                obligation.head_term_id,
                obligation.unit_term_id,
            )) {
                return false;
            }
        }
        return true;
    }

    fn obligationSatisfied(
        self: *Solver,
        bindings: []const ?ExprId,
        obligation: StructuralJointObligation,
    ) anyerror!bool {
        const combined = try self.combineStructuralBindingExprs(
            bindings,
            obligation.binder_idxs,
            obligation.head_term_id,
            obligation.unit_term_id,
        );
        return try self.structuralExprSubset(
            obligation.lower_expr,
            combined,
            obligation.head_term_id,
            obligation.unit_term_id,
        ) and try self.structuralExprSubset(
            combined,
            obligation.upper_expr,
            obligation.head_term_id,
            obligation.unit_term_id,
        );
    }

    fn combineStructuralBindingExprs(
        self: *Solver,
        bindings: []const ?ExprId,
        binder_idxs: []const usize,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        const profile = self.resolveStructuralProfile(head_term_id) orelse {
            return error.UnifyMismatch;
        };
        if (profile.unitTermId() != unit_term_id) return error.UnifyMismatch;

        var exprs = std.ArrayListUnmanaged(ExprId){};
        defer exprs.deinit(self.allocator);
        for (binder_idxs) |binder_idx| {
            const expr_id = bindings[binder_idx] orelse {
                return error.MissingBinderAssignment;
            };
            try exprs.append(self.allocator, expr_id);
        }
        return try self.combineStructuralExprs(profile, exprs.items);
    }

    fn combineStructuralExprs(
        self: *Solver,
        profile: StructuralProfile,
        exprs: []const ExprId,
    ) anyerror!ExprId {
        var items = std.ArrayListUnmanaged(ExprId){};
        defer items.deinit(self.allocator);
        for (exprs) |expr_id| {
            var binding_items = std.ArrayListUnmanaged(ExprId){};
            defer binding_items.deinit(self.allocator);
            try self.collectCanonicalStructuralItems(
                expr_id,
                profile,
                &binding_items,
            );
            for (binding_items.items) |item| {
                try self.appendStructuralItem(profile, &items, item);
            }
        }
        return try self.rebuildStructuralExpr(
            items.items,
            profile.headTermId(),
            profile.unitTermId(),
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
            if (!try self.bindingSatisfiesStructural(
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
        return try self.sameBindingsCompatible(lhs, rhs);
    }

    fn sameBindingsCompatible(
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
            .rule_structural_intervals = try self.allocator.dupe(
                ?StructuralInterval,
                state.rule_structural_intervals,
            ),
            .view_structural_intervals = if (state.view_structural_intervals) |intervals|
                try self.allocator.dupe(
                    ?StructuralInterval,
                    intervals,
                )
            else
                null,
            .rule_structural_obligations = try self.cloneStructuralObligations(
                state.rule_structural_obligations,
            ),
            .view_structural_obligations = if (state.view_structural_obligations) |obligations|
                try self.cloneStructuralObligations(obligations)
            else
                null,
        };
    }

    fn cloneStructuralObligations(
        self: *Solver,
        obligations: []const StructuralJointObligation,
    ) anyerror![]StructuralJointObligation {
        const result = try self.allocator.alloc(
            StructuralJointObligation,
            obligations.len,
        );
        for (obligations, 0..) |obligation, idx| {
            result[idx] = .{
                .head_term_id = obligation.head_term_id,
                .unit_term_id = obligation.unit_term_id,
                .lower_expr = obligation.lower_expr,
                .upper_expr = obligation.upper_expr,
                .binder_idxs = try self.allocator.dupe(
                    usize,
                    obligation.binder_idxs,
                ),
            };
        }
        return result;
    }
};

fn structuralItemsContain(
    theorem: *const TheoremContext,
    items: []const ExprId,
    item: ExprId,
) bool {
    for (items) |candidate| {
        switch (compareExprIds(theorem, candidate, item)) {
            .lt => continue,
            .eq => return true,
            .gt => return false,
        }
    }
    return false;
}

fn sameStructuralTemplateItem(
    lhs: StructuralTemplateItem,
    rhs: StructuralTemplateItem,
) bool {
    return switch (lhs) {
        .exact => |lhs_expr| switch (rhs) {
            .exact => |rhs_expr| lhs_expr == rhs_expr,
            .template => false,
        },
        .template => |lhs_tmpl| switch (rhs) {
            .exact => false,
            .template => |rhs_tmpl| sameTemplateExpr(lhs_tmpl, rhs_tmpl),
        },
    };
}

fn sameTemplateExpr(lhs: TemplateExpr, rhs: TemplateExpr) bool {
    return switch (lhs) {
        .binder => |lhs_idx| switch (rhs) {
            .binder => |rhs_idx| lhs_idx == rhs_idx,
            .app => false,
        },
        .app => |lhs_app| switch (rhs) {
            .binder => false,
            .app => |rhs_app| blk: {
                if (lhs_app.term_id != rhs_app.term_id or
                    lhs_app.args.len != rhs_app.args.len)
                {
                    break :blk false;
                }
                for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                    if (!sameTemplateExpr(lhs_arg, rhs_arg)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
        },
    };
}

fn orderedExprItemsAreSubset(
    theorem: *const TheoremContext,
    lhs: []const ExprId,
    rhs: []const ExprId,
) bool {
    var lhs_idx: usize = 0;
    var rhs_idx: usize = 0;
    while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
        if (compareExprIds(theorem, lhs[lhs_idx], rhs[rhs_idx]) == .eq) {
            lhs_idx += 1;
        }
        rhs_idx += 1;
    }
    return lhs_idx == lhs.len;
}

fn sortedExprBagIsSubset(
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

fn debugPrint(comptime fmt: []const u8, args: anytype) void {
    if (comptime builtin.target.os.tag == .freestanding) return;
    std.debug.print(fmt, args);
}
