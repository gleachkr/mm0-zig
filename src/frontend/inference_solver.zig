const builtin = @import("builtin");
const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ViewDecl = @import("./compiler/views.zig").ViewDecl;
const DerivedBinding = @import("./compiler/views.zig").DerivedBinding;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("./acui_support.zig");
const DerivedBindings = @import("./derived_bindings.zig");
const ViewTrace = @import("./view_trace.zig");
const BranchStateOps = @import("./inference_solver/branch_state.zig");
const SemanticCompare = @import("./inference_solver/semantic_compare.zig");
const StructuralIntervals =
    @import("./inference_solver/structural_intervals.zig");
const StructuralSearch = @import("./inference_solver/structural_search.zig");
const types = @import("./inference_solver/types.zig");
const BinderSpace = types.BinderSpace;
const MatchConstraint = types.MatchConstraint;
const StructuralJointObligation = types.StructuralJointObligation;
const BranchState = types.BranchState;

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
        var states = std.ArrayListUnmanaged(BranchState){};
        try states.append(
            self.allocator,
            try BranchStateOps.initState(self, partial_bindings),
        );

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
};

fn debugPrint(comptime fmt: []const u8, args: anytype) void {
    if (comptime builtin.target.os.tag == .freestanding) return;
    std.debug.print(fmt, args);
}
