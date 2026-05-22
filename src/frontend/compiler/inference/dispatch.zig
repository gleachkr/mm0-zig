const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const DefOps = @import("../../def_ops.zig");
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const UnifyReplay = @import("../../../trusted/unify_replay.zig");
const InferenceSolver = @import("../../inference_solver.zig").Solver;
const CompilerViews = @import("../views.zig");
const ViewDecl = CompilerViews.ViewDecl;
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const FreshSelect = @import("../fresh_select.zig");
const Emit = @import("../emit.zig");
const Context = @import("context.zig");
const Diagnostics = @import("diagnostics.zig");
const Validation = @import("validation.zig");
const Strategies = @import("strategies.zig");

const HiddenWitnessFreshContext = Context.HiddenWitnessFreshContext;
const InferenceContext = Context.InferenceContext;
const RuleInferenceContext = Context.RuleInferenceContext;
const buildInferenceFailureDiagnostic =
    Diagnostics.buildInferenceFailureDiagnostic;
const buildMissingBinderDiagnostic = Diagnostics.buildMissingBinderDiagnostic;
const addInferenceNotes = Diagnostics.addInferenceNotes;
const firstUnsolvedNamedBinder = Diagnostics.firstUnsolvedNamedBinder;
const traceInferenceAttempt = Diagnostics.traceInferenceAttempt;
const traceInferenceFailure = Diagnostics.traceInferenceFailure;
const validateBindingExpr = Validation.validateBindingExpr;
const buildViewSeedSetup = Strategies.buildViewSeedSetup;
const inferBindingsTransparentFromStrictFailure =
    Strategies.inferBindingsTransparentFromStrictFailure;
const inferBindingsByRuleMatchSession =
    Strategies.inferBindingsByRuleMatchSession;
const inferBindingsByMatchSeedState = Strategies.inferBindingsByMatchSeedState;
const maybeAddStructuralAmbiguityWarning =
    Strategies.maybeAddStructuralAmbiguityWarning;
const tryConcreteStructuralSolver = Strategies.tryConcreteStructuralSolver;
const tryConcreteRuleMatchSessionFallback =
    Strategies.tryConcreteRuleMatchSessionFallback;
const hasOmittedStructuralBindings = Strategies.hasOmittedStructuralBindings;

const StrictReplayFailure = struct {
    err: anyerror,
    partial_bindings: []const ?ExprId,
};

const StrictReplayResult = union(enum) {
    complete: []const ExprId,
    failed: StrictReplayFailure,
};

fn clonePartialBindings(
    allocator: std.mem.Allocator,
    bindings: []const ?ExprId,
) ![]const ?ExprId {
    return try allocator.dupe(?ExprId, bindings);
}

fn inferBindingsNoView(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
    prefer_structural: bool,
) ![]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule = context.rule;

    const has_structural = try hasOmittedStructuralBindings(
        env,
        registry,
        rule,
        partial_bindings,
    );
    const cached_unify = try context.cachedUnify();

    try traceInferenceAttempt(
        self.debug,
        allocator,
        theorem,
        env,
        rule,
        .strict_replay,
        partial_bindings,
        partial_bindings,
    );
    const strict_result = try strictInferBindingsDetailed(
        self,
        allocator,
        env,
        theorem,
        assertion,
        rule,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
        cached_unify,
    );
    switch (strict_result) {
        .complete => |bindings| return bindings,
        .failed => |failure| {
            defer allocator.free(failure.partial_bindings);
            self.restoreDiagnostic(null);
            try traceInferenceFailure(
                self.debug,
                allocator,
                theorem,
                env,
                rule,
                .strict_replay,
                failure.err,
                partial_bindings,
                failure.partial_bindings,
            );

            if (!prefer_structural) {
                try traceInferenceAttempt(
                    self.debug,
                    allocator,
                    theorem,
                    env,
                    rule,
                    .transparent_fallback,
                    partial_bindings,
                    failure.partial_bindings,
                );
                if (inferBindingsTransparentFromStrictFailure(
                    allocator,
                    env,
                    theorem,
                    rule,
                    partial_bindings,
                    failure.partial_bindings,
                    ref_exprs,
                    line_expr,
                )) |bindings| {
                    return bindings;
                } else |transparent_err| {
                    try traceInferenceFailure(
                        self.debug,
                        allocator,
                        theorem,
                        env,
                        rule,
                        .transparent_fallback,
                        transparent_err,
                        partial_bindings,
                        failure.partial_bindings,
                    );
                    self.restoreDiagnostic(null);
                }

                const seeds = try DefOps.BindingSeed.fromOptionalBindings(
                    allocator,
                    partial_bindings,
                );
                defer allocator.free(seeds);
                if (try tryConcreteRuleMatchSessionFallback(
                    self,
                    context,
                    line,
                    seeds,
                    fresh_context,
                    ref_exprs,
                    line_expr,
                    partial_bindings,
                    failure.partial_bindings,
                )) |bindings| {
                    self.restoreDiagnostic(null);
                    return bindings;
                }
            }

            if (prefer_structural or has_structural) {
                try traceInferenceAttempt(
                    self.debug,
                    allocator,
                    theorem,
                    env,
                    rule,
                    .structural_solver,
                    partial_bindings,
                    partial_bindings,
                );
                return try tryConcreteStructuralSolver(
                    self,
                    context,
                    line,
                    partial_bindings,
                    ref_exprs,
                    line_expr,
                );
            }

            if (failure.err == error.MissingBinderAssignment) {
                for (failure.partial_bindings, 0..) |binding, idx| {
                    if (binding != null) continue;
                    self.setProof(
                        try buildMissingBinderDiagnostic(
                            allocator,
                            env,
                            theorem,
                            assertion,
                            rule,
                            line,
                            .strict_replay,
                            partial_bindings,
                            failure.partial_bindings,
                            idx,
                        ),
                    );
                    return failure.err;
                }
            }
            self.setProof(
                try buildInferenceFailureDiagnostic(
                    allocator,
                    env,
                    theorem,
                    assertion,
                    rule,
                    line,
                    .transparent_fallback,
                    failure.err,
                    partial_bindings,
                    failure.partial_bindings,
                ),
            );
            return failure.err;
        },
    }
}

fn concreteBindingsToOptional(
    allocator: std.mem.Allocator,
    bindings: []const ExprId,
) ![]const ?ExprId {
    const optional = try allocator.alloc(?ExprId, bindings.len);
    for (bindings, 0..) |binding, idx| {
        optional[idx] = binding;
    }
    return optional;
}

fn templateHasMissingBinding(
    template: TemplateExpr,
    bindings: []const ?ExprId,
) bool {
    return switch (template) {
        .binder => |idx| idx >= bindings.len or bindings[idx] == null,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (templateHasMissingBinding(arg, bindings)) break :blk true;
            }
            break :blk false;
        },
    };
}

fn inferOptionalBindingsFromViewSeed(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line_expr: ExprId,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
    view: ViewDecl,
) !?[]const ?ExprId {
    const allocator = context.allocator;
    var view_seed_overrides: ?[]DefOps.BindingSeed = null;
    defer if (view_seed_overrides) |seeds| allocator.free(seeds);

    if (fresh_context) |fresh| {
        view_seed_overrides =
            try FreshSelect.seedRecoverHolesFromVarsPool(
                allocator,
                fresh.parser,
                context.env,
                context.theorem,
                fresh.theorem_vars,
                fresh.sort_vars,
                line_expr,
                ref_exprs,
                partial_bindings,
                view.num_binders,
                view.binder_map,
                view.arg_infos,
                view.derived_bindings,
            );
    }

    var seed_setup = switch (try buildViewSeedSetup(
        self,
        allocator,
        context.env,
        context.registry,
        context.theorem,
        context.rule,
        view,
        .{ .concrete = line_expr },
        ref_exprs,
        partial_bindings,
        view_seed_overrides,
    )) {
        .concrete => |bindings| {
            defer allocator.free(bindings);
            return try concreteBindingsToOptional(allocator, bindings);
        },
        .setup => |setup| setup,
    };
    defer seed_setup.deinit(allocator);

    const seeded = seed_setup.seeded_bindings orelse return null;
    if (templateHasMissingBinding(context.rule.concl, seeded)) return null;
    return try allocator.dupe(?ExprId, seeded);
}

pub fn inferBindings(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    use_advanced_inference: bool,
    prefer_structural_solver: bool,
) ![]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const scratch = context.scratch;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule_id = context.rule_id;
    const rule = context.rule;

    if (maybe_view == null) {
        return try inferBindingsNoView(
            self,
            context,
            line,
            partial_bindings,
            ref_exprs,
            line_expr,
            fresh_context,
            prefer_structural_solver,
        );
    }

    const view = maybe_view.?;

    if (use_advanced_inference) {
        var view_seed_overrides: ?[]DefOps.BindingSeed = null;
        defer if (view_seed_overrides) |seeds| allocator.free(seeds);

        if (fresh_context) |fresh| {
            view_seed_overrides =
                try FreshSelect.seedRecoverHolesFromVarsPool(
                    allocator,
                    fresh.parser,
                    env,
                    theorem,
                    fresh.theorem_vars,
                    fresh.sort_vars,
                    line_expr,
                    ref_exprs,
                    partial_bindings,
                    view.num_binders,
                    view.binder_map,
                    view.arg_infos,
                    view.derived_bindings,
                );
        }

        var seed_setup = switch (try buildViewSeedSetup(
            self,
            allocator,
            env,
            registry,
            theorem,
            rule,
            view,
            .{ .concrete = line_expr },
            ref_exprs,
            partial_bindings,
            view_seed_overrides,
        )) {
            .concrete => |bindings| return bindings,
            .setup => |setup| setup,
        };
        defer seed_setup.deinit(allocator);

        try traceInferenceAttempt(
            self.debug,
            allocator,
            theorem,
            env,
            rule,
            .structural_solver,
            partial_bindings,
            if (seed_setup.seeded_bindings) |stored|
                stored
            else
                partial_bindings,
        );

        const match_mark = scratch.mark();
        const match_result = (if (seed_setup.view_seed_state) |*seed_state|
            inferBindingsByMatchSeedState(
                context,
                seed_state,
                fresh_context,
                ref_exprs,
                line_expr,
                partial_bindings,
            )
        else
            inferBindingsByRuleMatchSession(
                context,
                seed_setup.session_seeds.?,
                fresh_context,
                ref_exprs,
                line_expr,
                partial_bindings,
            )) catch |err| {
            try traceInferenceFailure(
                self.debug,
                allocator,
                theorem,
                env,
                rule,
                .structural_solver,
                err,
                partial_bindings,
                if (seed_setup.seeded_bindings) |stored|
                    stored
                else
                    partial_bindings,
            );
            if (self.setProofScratchDiagnosticIfPresent(
                scratch,
                match_mark,
                env,
                .inference,
                .inference_failed,
                err,
                assertion.name,
                line.label,
                line.application.rule_name,
                line.ruleApplicationSpan(),
            )) {
                return err;
            }
            scratch.discard(match_mark);
            return err;
        };
        scratch.discard(match_mark);
        switch (match_result) {
            .concrete => |bindings| return bindings,
            .no_match => {},
            .unresolved_dummy_witness => {
                const solver_bindings = if (seed_setup.seeded_bindings) |stored|
                    stored
                else
                    partial_bindings;
                try traceInferenceFailure(
                    self.debug,
                    allocator,
                    theorem,
                    env,
                    rule,
                    .structural_solver,
                    error.UnresolvedDummyWitness,
                    partial_bindings,
                    solver_bindings,
                );
                self.setProof(
                    try buildInferenceFailureDiagnostic(
                        allocator,
                        env,
                        theorem,
                        assertion,
                        rule,
                        line,
                        .structural_solver,
                        error.UnresolvedDummyWitness,
                        partial_bindings,
                        solver_bindings,
                    ),
                );
                return error.UnresolvedDummyWitness;
            },
        }

        var solver = InferenceSolver.init(
            allocator,
            env,
            theorem,
            registry,
            rule_id,
            rule,
            &view,
            scratch,
            self.debug,
        );
        defer solver.deinit();
        const solver_bindings = if (seed_setup.seeded_bindings) |stored|
            stored
        else
            partial_bindings;
        const bindings = solver.solve(
            solver_bindings,
            ref_exprs,
            line_expr,
        ) catch |err| {
            try traceInferenceFailure(
                self.debug,
                allocator,
                theorem,
                env,
                rule,
                .structural_solver,
                err,
                partial_bindings,
                solver_bindings,
            );
            self.setProof(
                try buildInferenceFailureDiagnostic(
                    allocator,
                    env,
                    theorem,
                    assertion,
                    rule,
                    line,
                    .structural_solver,
                    err,
                    partial_bindings,
                    solver_bindings,
                ),
            );
            return err;
        };

        try maybeAddStructuralAmbiguityWarning(
            self,
            allocator,
            assertion,
            line,
            &solver,
        );
        return bindings;
    }

    try traceInferenceAttempt(
        self.debug,
        allocator,
        theorem,
        env,
        rule,
        .strict_replay,
        partial_bindings,
        partial_bindings,
    );

    const cached_unify = try context.cachedUnify();
    const strict_result = try strictInferBindingsDetailed(
        self,
        allocator,
        env,
        theorem,
        assertion,
        rule,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
        cached_unify,
    );
    switch (strict_result) {
        .complete => |bindings| return bindings,
        .failed => |strict_failure| {
            defer allocator.free(strict_failure.partial_bindings);
            if (self.getDiagnostic() != null) return strict_failure.err;
            self.setProof(
                try buildInferenceFailureDiagnostic(
                    allocator,
                    env,
                    theorem,
                    assertion,
                    rule,
                    line,
                    .strict_replay,
                    strict_failure.err,
                    partial_bindings,
                    strict_failure.partial_bindings,
                ),
            );
            return strict_failure.err;
        },
    }
}

fn strictInferBindingsDetailed(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    cached_unify: ?[]const u8,
) !StrictReplayResult {
    const unify = cached_unify orelse
        try Emit.buildRuleUnifyStream(allocator, rule);
    defer if (cached_unify == null) allocator.free(unify);

    var inference = try InferenceContext.init(
        allocator,
        theorem,
        partial_bindings,
        ref_exprs,
        line_expr,
    );
    defer inference.deinit();

    UnifyReplay.run(unify, 0, &inference) catch |err| {
        return .{ .failed = .{
            .err = err,
            .partial_bindings = try clonePartialBindings(
                allocator,
                inference.uheap.items[0..rule.args.len],
            ),
        } };
    };
    if (inference.ustack.items.len != 0) {
        return .{ .failed = .{
            .err = error.UnifyStackNotEmpty,
            .partial_bindings = try clonePartialBindings(
                allocator,
                inference.uheap.items[0..rule.args.len],
            ),
        } };
    }
    if (inference.next_hyp != 0) {
        return .{ .failed = .{
            .err = error.HypCountMismatch,
            .partial_bindings = try clonePartialBindings(
                allocator,
                inference.uheap.items[0..rule.args.len],
            ),
        } };
    }

    const snapshot = try clonePartialBindings(
        allocator,
        inference.uheap.items[0..rule.args.len],
    );
    errdefer allocator.free(snapshot);

    const bindings = try allocator.alloc(ExprId, rule.args.len);
    errdefer allocator.free(bindings);

    for (0..rule.args.len) |idx| {
        const binding = snapshot[idx] orelse {
            self.maybeSetProof(
                try buildMissingBinderDiagnostic(
                    allocator,
                    env,
                    theorem,
                    assertion,
                    rule,
                    line,
                    .strict_replay,
                    partial_bindings,
                    snapshot,
                    idx,
                ),
            );
            return .{ .failed = .{
                .err = error.MissingBinderAssignment,
                .partial_bindings = snapshot,
            } };
        };
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            var diag = CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = rule.arg_names[idx],
                .span = CompilerDiag.proofBindingDiagnosticSpan(
                    line,
                    rule.arg_names[idx],
                ),
                .detail = .{ .inference_failure = .{
                    .path = .strict_replay,
                    .first_unsolved_binder_name = firstUnsolvedNamedBinder(
                        rule,
                        snapshot,
                    ),
                } },
            }, .inference);
            try addInferenceNotes(
                allocator,
                &diag,
                env,
                theorem,
                rule,
                .strict_replay,
                partial_bindings,
                snapshot,
            );
            self.maybeSetProof(diag);
            return .{ .failed = .{
                .err = err,
                .partial_bindings = snapshot,
            } };
        };
        bindings[idx] = binding;
    }
    // Strict replay is only responsible for exact inference plus binder-local
    // sort and boundness checks.  Dependency failures may be repairable by
    // @freshen, so complete bindings must reach theorem-application
    // validation before they are rejected.
    allocator.free(snapshot);
    return .{ .complete = bindings };
}

pub fn inferOptionalBindingsAllowUnresolved(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    use_advanced_inference: bool,
    prefer_structural_solver: bool,
) ![]const ?ExprId {
    const allocator = context.allocator;
    if (inferBindings(
        self,
        context,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
        fresh_context,
        maybe_view,
        use_advanced_inference,
        prefer_structural_solver,
    )) |bindings| {
        defer allocator.free(bindings);
        return try concreteBindingsToOptional(allocator, bindings);
    } else |err| {
        if (err != error.MissingBinderAssignment) return err;
        self.restoreDiagnostic(null);
    }

    if (maybe_view) |view| {
        if (try inferOptionalBindingsFromViewSeed(
            self,
            context,
            line_expr,
            partial_bindings,
            ref_exprs,
            fresh_context,
            view,
        )) |bindings| {
            return bindings;
        }
        self.restoreDiagnostic(null);
    }

    const cached_unify = try context.cachedUnify();
    const strict_result = try strictInferBindingsDetailed(
        self,
        allocator,
        context.env,
        context.theorem,
        context.assertion,
        context.rule,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
        cached_unify,
    );
    return switch (strict_result) {
        .complete => |bindings| blk: {
            defer allocator.free(bindings);
            break :blk try concreteBindingsToOptional(allocator, bindings);
        },
        .failed => |failure| blk: {
            errdefer allocator.free(failure.partial_bindings);
            if (failure.err != error.MissingBinderAssignment) {
                allocator.free(failure.partial_bindings);
                return failure.err;
            }
            self.restoreDiagnostic(null);
            break :blk failure.partial_bindings;
        },
    };
}

pub fn strictInferBindings(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    const result = try strictInferBindingsDetailed(
        self,
        allocator,
        env,
        theorem,
        assertion,
        rule,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
        null,
    );
    return switch (result) {
        .complete => |bindings| bindings,
        .failed => |failure| {
            defer allocator.free(failure.partial_bindings);
            return failure.err;
        },
    };
}
