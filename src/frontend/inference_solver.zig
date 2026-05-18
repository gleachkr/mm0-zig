const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const Expr = @import("../trusted/expressions.zig").Expr;
const SurfaceExpr = @import("./surface_expr.zig");
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("./compiler/diag.zig");
const ViewDecl = @import("./compiler/views.zig").ViewDecl;
const DerivedBinding = @import("./compiler/views.zig").DerivedBinding;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("./acui_support.zig");
const DerivedBindings = @import("./compiler/derived_bindings.zig");
const DebugConfig = @import("./debug.zig").DebugConfig;
const BranchStateOps = @import("./inference_solver/branch_state.zig");
const SemanticCompare = @import("./inference_solver/semantic_compare.zig");
const StructuralIntervals =
    @import("./inference_solver/intervals.zig");
const StructuralMatcher = @import("./inference_solver/matcher.zig");
const StructuralObligationSolver =
    @import("./inference_solver/obligation_solver.zig");
const StructuralStateUpdates =
    @import("./inference_solver/state_updates.zig");
const Ambiguity = @import("./inference_solver/ambiguity_report.zig");
const types = @import("./inference_solver/types.zig");
const BinderSpace = types.BinderSpace;
const MatchConstraint = types.MatchConstraint;
const StructuralJointObligation = types.StructuralJointObligation;
const BranchState = types.BranchState;

const SolutionPreference = Ambiguity.SolutionPreference;
pub const AmbiguityReport = Ambiguity.AmbiguityReport;

const ConclusionConstraint = union(enum) {
    concrete: ExprId,
    surface: *const Expr,
};

pub const Solver = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    rule_id: u32,
    rule: *const RuleDecl,
    view: ?*const ViewDecl,
    canonicalizer: Canonicalizer,
    scratch: ?*CompilerDiag.Scratch,
    debug: DebugConfig,
    ambiguity_warning: bool = false,
    ambiguity_report: AmbiguityReport = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        rule_id: u32,
        rule: *const RuleDecl,
        view: ?*const ViewDecl,
        scratch: ?*CompilerDiag.Scratch,
        debug: DebugConfig,
    ) Solver {
        return .{
            .allocator = allocator,
            .env = env,
            .theorem = theorem,
            .registry = registry,
            .rule_id = rule_id,
            .rule = rule,
            .view = view,
            .canonicalizer = Canonicalizer.init(
                allocator,
                @constCast(theorem),
                registry,
                env,
            ),
            .scratch = scratch,
            .debug = debug,
        };
    }

    pub fn canUseNormalizedStructuralItemMatch(self: *const Solver) bool {
        // Final validation can now produce normalized transport. Structural
        // search may use normalized item matching as a branch-local inference aid
        // whenever diagnostic scratch is available. The expensive path is
        // still gated by structural competition and by exact/transparent
        // item matching failing first.
        return self.scratch != null;
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
        return try self.solveWithConclusion(
            partial_bindings,
            ref_exprs,
            .{ .concrete = line_expr },
        );
    }

    pub fn solveHoleyConclusion(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        holey_concl: *const Expr,
    ) anyerror![]const ExprId {
        return try self.solveWithConclusion(
            partial_bindings,
            ref_exprs,
            .{ .surface = holey_concl },
        );
    }

    fn solveWithConclusion(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        conclusion: ConclusionConstraint,
    ) anyerror![]const ExprId {
        var states = try self.initialStates(partial_bindings);

        if (self.view) |view| {
            states = try self.applyHypConstraints(
                states.items,
                view.hyps,
                ref_exprs,
                .view,
            );
            states = try self.applyConclusionConstraint(
                states.items,
                view.concl,
                conclusion,
                .view,
            );
            states = try self.finalizeViewAndRuleStates(states.items, view);
        } else {
            states = try self.applyHypConstraints(
                states.items,
                self.rule.hyps,
                ref_exprs,
                .rule,
            );
            states = try self.applyConclusionConstraint(
                states.items,
                self.rule.concl,
                conclusion,
                .rule,
            );
            states = try self.finalizeStructuralStates(states.items, .rule);
        }

        return try Ambiguity.pickUniqueSolution(
            self,
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

    fn applyHypConstraints(
        self: *Solver,
        states: []const BranchState,
        hyps: []const TemplateExpr,
        ref_exprs: []const ExprId,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var constraints = std.ArrayListUnmanaged(MatchConstraint){};
        defer constraints.deinit(self.allocator);
        for (hyps, ref_exprs) |hyp, actual| {
            try constraints.append(self.allocator, .{
                .template = hyp,
                .actual = actual,
            });
        }
        return try self.applyConstraints(states, constraints.items, space);
    }

    fn applyConclusionConstraint(
        self: *Solver,
        states: []const BranchState,
        template: TemplateExpr,
        conclusion: ConclusionConstraint,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        return switch (conclusion) {
            .concrete => |actual| blk: {
                const constraints = [_]MatchConstraint{.{
                    .template = template,
                    .actual = actual,
                }};
                break :blk try self.applyConstraints(
                    states,
                    constraints[0..],
                    space,
                );
            },
            .surface => |actual| try self.applySurfaceConstraint(
                states,
                template,
                actual,
                space,
            ),
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
                const matches = try StructuralMatcher.matchExpr(
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
            return try StructuralMatcher.matchExpr(
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

        if (nextUnresolvedStructuralObligation(&current, space)) |idx| {
            const obligations = BranchStateOps.getStructuralObligations(&current, space);
            const branches = try StructuralObligationSolver.solveStructuralObligation(
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
        try StructuralStateUpdates.appendUniqueStateForSpace(
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
        const bindings = BranchStateOps.getBindings(state, space);
        const intervals = BranchStateOps.getStructuralIntervals(state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            const binding = bindings[idx] orelse continue;
            if (!try StructuralIntervals.exprWithinInterval(self, binding, interval)) {
                return false;
            }
        }
        const obligations = BranchStateOps.getStructuralObligations(state, space);
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
        state: *BranchState,
        space: BinderSpace,
    ) ?usize {
        const bindings = BranchStateOps.getBindings(state, space);
        const obligations = BranchStateOps.getStructuralObligations(state, space);
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
        const bindings = BranchStateOps.getBindings(state, space);
        const intervals = BranchStateOps.getStructuralIntervals(state, space);
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
        const bindings = BranchStateOps.getBindings(state, space);
        const obligations = BranchStateOps.getStructuralObligations(state, space);
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
};
