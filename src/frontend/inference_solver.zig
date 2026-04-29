const builtin = @import("builtin");
const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const Expr = @import("../trusted/expressions.zig").Expr;
const SurfaceExpr = @import("./surface_expr.zig");
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ViewDecl = @import("./compiler/views.zig").ViewDecl;
const DerivedBinding = @import("./compiler/views.zig").DerivedBinding;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("./acui_support.zig");
const DerivedBindings = @import("./derived_bindings.zig");
const ViewTrace = @import("./view_trace.zig");
const DebugConfig = @import("./debug.zig").DebugConfig;
const DebugTrace = @import("./debug.zig");
const BranchStateOps = @import("./inference_solver/branch_state.zig");
const SemanticCompare = @import("./inference_solver/semantic_compare.zig");
const StructuralIntervals =
    @import("./inference_solver/structural_intervals.zig");
const StructuralItems = @import("./inference_solver/structural_items.zig");
const StructuralSearch = @import("./inference_solver/structural_search.zig");
const types = @import("./inference_solver/types.zig");
const BinderSpace = types.BinderSpace;
const MatchConstraint = types.MatchConstraint;
const StructuralJointObligation = types.StructuralJointObligation;
const BranchState = types.BranchState;

const SolutionPreference = enum {
    first,
    minimal_structural,
};

pub const AmbiguityReport = struct {
    distinct_solution_count: usize = 0,
    chosen_bindings: ?[]const u8 = null,
    alternative_bindings: ?[]const u8 = null,
};

pub const Solver = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    view: ?*const ViewDecl,
    canonicalizer: Canonicalizer,
    debug: DebugConfig,
    ambiguity_warning: bool = false,
    ambiguity_report: AmbiguityReport = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        rule: *const RuleDecl,
        view: ?*const ViewDecl,
        debug: DebugConfig,
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
            .debug = debug,
        };
    }

    pub fn deinit(self: *Solver) void {
        if (self.ambiguity_report.chosen_bindings) |summary| {
            self.allocator.free(summary);
        }
        if (self.ambiguity_report.alternative_bindings) |summary| {
            self.allocator.free(summary);
        }
        self.canonicalizer.cache.deinit();
    }

    pub fn hadAmbiguityWarning(self: *const Solver) bool {
        return self.ambiguity_warning;
    }

    pub fn getAmbiguityReport(self: *const Solver) ?AmbiguityReport {
        if (!self.ambiguity_warning) return null;
        return self.ambiguity_report;
    }

    pub fn structuralSupport(self: *Solver) AcuiSupport.Context {
        return AcuiSupport.Context.init(
            self.allocator,
            self.theorem,
            self.env,
            self.registry,
        );
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
        var states = try self.initialStates(partial_bindings);

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
            states = try self.finalizeViewAndRuleStates(states.items, view);
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

        return try self.pickUniqueSolution(
            states.items,
            .minimal_structural,
        );
    }

    pub fn solveHoleyConclusion(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        holey_concl: *const Expr,
    ) anyerror![]const ExprId {
        var states = try self.initialStates(partial_bindings);

        if (self.view) |view| {
            var constraints = std.ArrayListUnmanaged(MatchConstraint){};
            for (view.hyps, ref_exprs) |hyp, actual| {
                try constraints.append(self.allocator, .{
                    .template = hyp,
                    .actual = actual,
                });
            }
            states = try self.applyConstraints(
                states.items,
                constraints.items,
                .view,
            );
            states = try self.applySurfaceConstraint(
                states.items,
                view.concl,
                holey_concl,
                .view,
            );
            states = try self.finalizeViewAndRuleStates(states.items, view);
        } else {
            var constraints = std.ArrayListUnmanaged(MatchConstraint){};
            for (self.rule.hyps, ref_exprs) |hyp, actual| {
                try constraints.append(self.allocator, .{
                    .template = hyp,
                    .actual = actual,
                });
            }
            states = try self.applyConstraints(
                states.items,
                constraints.items,
                .rule,
            );
            states = try self.applySurfaceConstraint(
                states.items,
                self.rule.concl,
                holey_concl,
                .rule,
            );
            states = try self.finalizeStructuralStates(states.items, .rule);
        }

        return try self.pickUniqueSolution(
            states.items,
            .minimal_structural,
        );
    }

    fn initialStates(
        self: *Solver,
        partial_bindings: []const ?ExprId,
    ) !std.ArrayListUnmanaged(BranchState) {
        var states = std.ArrayListUnmanaged(BranchState){};
        try states.append(
            self.allocator,
            try BranchStateOps.initState(self, partial_bindings),
        );
        return states;
    }

    fn finalizeViewAndRuleStates(
        self: *Solver,
        states: []const BranchState,
        view: *const ViewDecl,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = try self.finalizeStructuralStates(states, .view);
        next = try self.applyDerivedBindings(next.items, view.derived_bindings);
        next = try self.finalizeStructuralStates(next.items, .view);
        try self.propagateViewBindings(next.items, view);
        next = try self.finalizeStructuralStates(next.items, .rule);
        return next;
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
                const matches = try StructuralSearch.matchExpr(
                    self,
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

    fn applySurfaceConstraint(
        self: *Solver,
        states: []const BranchState,
        template: TemplateExpr,
        actual: *const Expr,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        for (states) |state| {
            const matches = try self.matchSurfaceExpr(
                template,
                actual,
                space,
                state,
            );
            try next.appendSlice(self.allocator, matches);
        }
        if (next.items.len == 0) return error.UnifyMismatch;
        return next;
    }

    fn matchSurfaceExpr(
        self: *Solver,
        template: TemplateExpr,
        actual: *const Expr,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        if (actual.* == .hole) {
            const out = try self.allocator.alloc(BranchState, 1);
            out[0] = try BranchStateOps.cloneState(self, state);
            return out;
        }

        if (!SurfaceExpr.containsHole(actual)) {
            const actual_id = try self.theorem.internParsedExpr(actual);
            return try StructuralSearch.matchExpr(
                self,
                template,
                actual_id,
                space,
                state,
            );
        }

        return switch (template) {
            .binder => blk: {
                const out = try self.allocator.alloc(BranchState, 1);
                out[0] = try BranchStateOps.cloneState(self, state);
                break :blk out;
            },
            .app => |app| blk: {
                const actual_term = switch (actual.*) {
                    .term => |term| term,
                    .variable, .hole => break :blk &.{},
                };
                if (actual_term.id != app.term_id or
                    actual_term.args.len != app.args.len)
                {
                    break :blk &.{};
                }

                var states = std.ArrayListUnmanaged(BranchState){};
                try states.append(
                    self.allocator,
                    try BranchStateOps.cloneState(self, state),
                );
                for (app.args, actual_term.args) |tmpl_arg, actual_arg| {
                    var next = std.ArrayListUnmanaged(BranchState){};
                    for (states.items) |current| {
                        const matches = try self.matchSurfaceExpr(
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

    fn applyDerivedBindings(
        self: *Solver,
        states: []const BranchState,
        derived_bindings: []const DerivedBinding,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        var first_err: ?anyerror = null;
        for (states) |state| {
            const new_state = try BranchStateOps.cloneState(self, state);
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
        var current = try BranchStateOps.cloneState(self, state);
        if (!try self.partialStructuralStateCompatible(&current, space)) {
            return;
        }

        if (self.nextUnresolvedStructuralObligation(&current, space)) |idx| {
            const obligations = BranchStateOps.getStructuralObligations(self, &current, space);
            const branches = try StructuralSearch.solveStructuralObligation(
                self,
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
        try StructuralSearch.appendUniqueStateForSpace(
            self,
            out,
            current,
            space,
        );
    }

    pub fn partialStructuralStateCompatible(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!bool {
        const bindings = BranchStateOps.getBindings(self, state, space);
        const intervals = BranchStateOps.getStructuralIntervals(self, state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            const binding = bindings[idx] orelse continue;
            if (!try StructuralIntervals.exprWithinInterval(self, binding, interval)) {
                return false;
            }
        }
        const obligations = BranchStateOps.getStructuralObligations(self, state, space);
        for (obligations) |obligation| {
            if (!try StructuralIntervals.obligationCompatibleWithState(
                self,
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
        const bindings = BranchStateOps.getBindings(self, state, space);
        const obligations = BranchStateOps.getStructuralObligations(self, state, space);
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
        const bindings = BranchStateOps.getBindings(self, state, space);
        const intervals = BranchStateOps.getStructuralIntervals(self, state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            if (bindings[idx]) |existing| {
                if (!try StructuralIntervals.exprWithinInterval(self, existing, interval)) {
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
        const bindings = BranchStateOps.getBindings(self, state, space);
        const obligations = BranchStateOps.getStructuralObligations(self, state, space);
        for (obligations) |obligation| {
            for (obligation.binder_idxs) |binder_idx| {
                if (binder_idx >= bindings.len or
                    bindings[binder_idx] == null)
                {
                    return false;
                }
            }
            if (!try StructuralIntervals.obligationSatisfied(self, bindings, obligation)) {
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
                    if (!try SemanticCompare.bindingCompatible(self, existing, binding)) {
                        return error.ViewBindingConflict;
                    }
                } else {
                    if (!try StructuralIntervals.bindingSatisfiesStructural(
                        self,
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
        preference: SolutionPreference,
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
                if (try SemanticCompare.sameRuleBindingsCompatible(
                    self,
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

        const chosen_distinct_idx = try self.chooseDistinctSolution(
            states,
            distinct_idxs.items,
            preference,
        );
        if (distinct_idxs.items.len > 1) {
            self.ambiguity_warning = true;
            try self.captureAmbiguityReport(
                states,
                distinct_idxs.items,
                chosen_distinct_idx,
            );
            if (self.debug.inference) {
                try self.debugPrintAmbiguousSolutions(
                    states,
                    distinct_idxs.items,
                    chosen_distinct_idx,
                    preference,
                );
            }
        }

        const chosen = states[distinct_idxs.items[chosen_distinct_idx]]
            .rule_bindings;
        const result = try self.allocator.alloc(ExprId, chosen.len);
        for (chosen, 0..) |binding, idx| {
            result[idx] = binding.?;
        }
        return result;
    }

    fn chooseDistinctSolution(
        self: *Solver,
        states: []const BranchState,
        distinct_idxs: []const usize,
        preference: SolutionPreference,
    ) !usize {
        if (distinct_idxs.len == 0) return error.UnifyMismatch;
        switch (preference) {
            .first => return 0,
            .minimal_structural => {},
        }

        var best: usize = 0;
        var best_rank = try self.structuralBindingRank(
            states[distinct_idxs[0]].rule_bindings,
        );
        for (distinct_idxs[1..], 1..) |state_idx, distinct_idx| {
            const rank = try self.structuralBindingRank(
                states[state_idx].rule_bindings,
            );
            if (rank < best_rank) {
                best = distinct_idx;
                best_rank = rank;
            }
        }
        return best;
    }

    fn structuralBindingRank(
        self: *Solver,
        bindings: []const ?ExprId,
    ) !usize {
        var rank: usize = 0;
        for (bindings, 0..) |maybe_binding, idx| {
            const binding = maybe_binding orelse continue;
            const sort_name = StructuralItems.getBinderSort(
                self,
                .rule,
                idx,
            ) orelse continue;
            const combiner = try self.registry.resolveStructuralCombinerForSort(
                self.env,
                sort_name,
            ) orelse continue;
            const profile = types.StructuralProfile.init(combiner);
            var items = std.ArrayListUnmanaged(ExprId){};
            defer items.deinit(self.allocator);
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                binding,
                profile,
                &items,
            );
            rank += items.items.len;
        }
        return rank;
    }

    fn captureAmbiguityReport(
        self: *Solver,
        states: []const BranchState,
        distinct_idxs: []const usize,
        chosen_distinct_idx: usize,
    ) !void {
        self.ambiguity_report.distinct_solution_count = distinct_idxs.len;
        if (distinct_idxs.len == 0) return;

        self.ambiguity_report.chosen_bindings = try self.formatBindingSummary(
            states[distinct_idxs[chosen_distinct_idx]].rule_bindings,
        );
        if (distinct_idxs.len > 1) {
            const alt_idx: usize = if (chosen_distinct_idx == 0) 1 else 0;
            self.ambiguity_report.alternative_bindings = try self.formatBindingSummary(
                states[distinct_idxs[alt_idx]].rule_bindings,
            );
        }
    }

    fn formatBindingSummary(
        self: *Solver,
        bindings: []const ?ExprId,
    ) ![]const u8 {
        var out = std.ArrayListUnmanaged(u8){};
        errdefer out.deinit(self.allocator);

        var emitted: usize = 0;
        for (bindings, 0..) |binding, idx| {
            if (emitted == 3) break;
            if (emitted != 0) {
                try out.appendSlice(self.allocator, "; ");
            }

            const name = self.rule.arg_names[idx] orelse "_";
            try out.writer(self.allocator).print("{s} = ", .{name});
            if (binding) |expr_id| {
                const text = try ViewTrace.formatExpr(
                    self.allocator,
                    self.theorem,
                    self.env,
                    expr_id,
                );
                defer self.allocator.free(text);
                try appendTruncatedText(&out, self.allocator, text, 48);
            } else {
                try out.appendSlice(self.allocator, "<unsolved>");
            }
            emitted += 1;
        }

        if (bindings.len > emitted) {
            try out.writer(self.allocator).print(
                "; +{d} more",
                .{bindings.len - emitted},
            );
        }
        return try out.toOwnedSlice(self.allocator);
    }

    fn debugPrintAmbiguousSolutions(
        self: *Solver,
        states: []const BranchState,
        distinct_idxs: []const usize,
        chosen_distinct_idx: usize,
        preference: SolutionPreference,
    ) !void {
        if (comptime builtin.target.os.tag == .freestanding) return;

        DebugTrace.traceInference(
            self.debug,
            "omitted binders left {d} distinct final solutions; " ++
                "choosing by {s}",
            .{ distinct_idxs.len, solutionPreferenceName(preference) },
        );
        for (distinct_idxs, 0..) |state_idx, choice_idx| {
            DebugTrace.traceInference(
                self.debug,
                "  solution {d}{s}",
                .{
                    choice_idx + 1,
                    if (choice_idx == chosen_distinct_idx) " (chosen)" else "",
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
                DebugTrace.traceInference(
                    self.debug,
                    "    {s}#{d} = {s}",
                    .{ name, idx, text },
                );
            } else {
                DebugTrace.traceInference(
                    self.debug,
                    "    {s}#{d} = <null>",
                    .{ name, idx },
                );
            }
        }
    }
};

fn solutionPreferenceName(preference: SolutionPreference) []const u8 {
    return switch (preference) {
        .first => "first solution",
        .minimal_structural => "minimal structural residual",
    };
}

fn appendTruncatedText(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    text: []const u8,
    limit: usize,
) !void {
    if (text.len <= limit) {
        try out.appendSlice(allocator, text);
        return;
    }
    if (limit <= 1) {
        try out.appendSlice(allocator, text[0..limit]);
        return;
    }
    try out.appendSlice(allocator, text[0 .. limit - 1]);
    try out.appendSlice(allocator, "...");
}
