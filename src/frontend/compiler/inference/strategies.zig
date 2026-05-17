const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const DefOps = @import("../../def_ops.zig");
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const Expr = @import("../../../trusted/expressions.zig").Expr;
const SurfaceExpr = @import("../../surface_expr.zig");
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const InferenceSolver = @import("../../inference_solver.zig").Solver;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const CompilerViews = @import("../views.zig");
const ViewDecl = CompilerViews.ViewDecl;
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CompilerFresh = @import("../fresh.zig");
const DebugTrace = @import("../../debug.zig");
const NormalizedCompare = @import("../normalized_compare.zig");
const InferenceContextModule = @import("context.zig");
const InferenceValidation = @import("validation.zig");
const InferenceDiagnostics = @import("diagnostics.zig");

/// Result of an advanced rule match attempt.
pub const RuleMatchResult = union(enum) {
    /// Match succeeded and all bindings are concrete ExprIds.
    concrete: []const ExprId,
    /// The rule's hypotheses/conclusion did not match.
    no_match,
    /// Matching succeeded symbolically but still needs explicit bindings.
    unresolved_dummy_witness,
};

const RuleInferenceContext = InferenceContextModule.RuleInferenceContext;
const HiddenWitnessFreshContext =
    InferenceContextModule.HiddenWitnessFreshContext;
const exprInfo = InferenceValidation.exprInfo;
const buildMissingBinderDiagnostic =
    InferenceDiagnostics.buildMissingBinderDiagnostic;
const buildInferenceFailureDiagnostic =
    InferenceDiagnostics.buildInferenceFailureDiagnostic;
const addAmbiguityWarningNotes = InferenceDiagnostics.addAmbiguityWarningNotes;
const addFormattedInferenceNote =
    InferenceDiagnostics.addFormattedInferenceNote;
const traceInferenceFailure = InferenceDiagnostics.traceInferenceFailure;

const InferenceConclusion = union(enum) {
    concrete: ExprId,
    surface: *const Expr,
};

pub const ViewSeedSetup = struct {
    seeded_bindings: ?[]?ExprId = null,
    view_seed_state: ?DefOps.MatchSeedState = null,
    session_seeds: ?[]DefOps.BindingSeed = null,

    pub fn deinit(self: *ViewSeedSetup, allocator: std.mem.Allocator) void {
        if (self.seeded_bindings) |bindings| allocator.free(bindings);
        if (self.view_seed_state) |*state| state.deinit(allocator);
        if (self.session_seeds) |seeds| allocator.free(seeds);
    }

    pub fn diagnosticBindings(
        self: *const ViewSeedSetup,
        partial_bindings: []const ?ExprId,
    ) []const ?ExprId {
        return self.seeded_bindings orelse partial_bindings;
    }
};

pub const ViewSeedSetupResult = union(enum) {
    setup: ViewSeedSetup,
    concrete: []const ExprId,
};

fn clonePartialBindings(
    allocator: std.mem.Allocator,
    bindings: []const ?ExprId,
) ![]const ?ExprId {
    return try allocator.dupe(?ExprId, bindings);
}

pub fn canConvertTransparent(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    target_expr: ExprId,
    source_expr: ExprId,
) !bool {
    var def_ops = DefOps.Context.init(
        allocator,
        theorem,
        env,
    );
    defer def_ops.deinit();
    return (try def_ops.compareTransparent(
        target_expr,
        source_expr,
    )) != null;
}

fn bindingSeedsFromSeededBindings(
    allocator: std.mem.Allocator,
    seeded_bindings: []const ?ExprId,
    allow_semantic: []const bool,
    mode: DefOps.BindingMode,
) ![]DefOps.BindingSeed {
    const seeds = try allocator.alloc(
        DefOps.BindingSeed,
        seeded_bindings.len,
    );
    for (seeded_bindings, allow_semantic, 0..) |binding, allow, idx| {
        seeds[idx] = if (binding) |expr_id|
            if (allow)
                .{ .semantic = .{ .expr_id = expr_id, .mode = mode } }
            else
                .{ .exact = expr_id }
        else
            .none;
    }
    return seeds;
}

fn derivedViewRuleSeedMask(
    allocator: std.mem.Allocator,
    rule_arg_len: usize,
    view: ViewDecl,
) ![]bool {
    const mask = try allocator.alloc(bool, rule_arg_len);
    @memset(mask, false);
    for (view.derived_bindings) |binding| {
        const target_view_idx = switch (binding) {
            .recover => |recover| recover.target_view_idx,
            .abstract => |abstract| abstract.target_view_idx,
        };
        const rule_idx = view.binder_map[target_view_idx] orelse continue;
        mask[rule_idx] = true;
    }
    return mask;
}

fn bindingSeedsForViewReuse(
    allocator: std.mem.Allocator,
    explicit_bindings: []const ?ExprId,
    seeded_bindings: []const ?ExprId,
    derived_seed_mask: []const bool,
    mode: DefOps.BindingMode,
) ![]DefOps.BindingSeed {
    std.debug.assert(explicit_bindings.len == seeded_bindings.len);
    std.debug.assert(explicit_bindings.len == derived_seed_mask.len);

    const seeds = try allocator.alloc(
        DefOps.BindingSeed,
        seeded_bindings.len,
    );
    for (explicit_bindings, seeded_bindings, derived_seed_mask, 0..) |
        explicit,
        seeded,
        allow_view_seed,
        idx,
    | {
        seeds[idx] = if (explicit) |expr_id|
            .{ .exact = expr_id }
        else if (seeded) |expr_id|
            if (allow_view_seed)
                .{ .semantic = .{ .expr_id = expr_id, .mode = mode } }
            else
                .none
        else
            .none;
    }
    return seeds;
}

pub fn buildViewSeedSetup(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    view: ?ViewDecl,
    conclusion: InferenceConclusion,
    ref_exprs: []const ExprId,
    partial_bindings: []const ?ExprId,
    view_seed_overrides: ?[]const DefOps.BindingSeed,
) !ViewSeedSetupResult {
    var setup = ViewSeedSetup{};
    errdefer setup.deinit(allocator);

    const actual_view = view orelse {
        setup.session_seeds = try DefOps.BindingSeed.fromOptionalBindings(
            allocator,
            partial_bindings,
        );
        return .{ .setup = setup };
    };

    const seeded = try allocator.dupe(?ExprId, partial_bindings);
    var seeded_owned = true;
    errdefer if (seeded_owned) allocator.free(seeded);

    switch (conclusion) {
        .concrete => |line_expr| {
            CompilerViews.applyViewBindings(
                allocator,
                theorem,
                env,
                registry,
                &actual_view,
                line_expr,
                ref_exprs,
                seeded,
                view_seed_overrides,
                &setup.view_seed_state,
                self.debug.views,
            ) catch |err| {
                DebugTrace.traceViews(
                    self.debug,
                    "applyViewBindings failed for rule {s}: {s}",
                    .{ rule.name, @errorName(err) },
                );
                allocator.free(seeded);
                seeded_owned = false;
                setup.session_seeds =
                    try DefOps.BindingSeed.fromOptionalBindings(
                        allocator,
                        partial_bindings,
                    );
                return .{ .setup = setup };
            };
        },
        .surface => |surface_concl| {
            CompilerViews.applyViewBindingsSurfaceConclusion(
                allocator,
                theorem,
                env,
                registry,
                &actual_view,
                surface_concl,
                ref_exprs,
                seeded,
                view_seed_overrides,
                &setup.view_seed_state,
                self.debug.views,
            ) catch |err| {
                DebugTrace.traceViews(
                    self.debug,
                    "applyViewBindings failed for rule {s}: {s}",
                    .{ rule.name, @errorName(err) },
                );
                allocator.free(seeded);
                seeded_owned = false;
                setup.session_seeds =
                    try DefOps.BindingSeed.fromOptionalBindings(
                        allocator,
                        partial_bindings,
                    );
                return .{ .setup = setup };
            };
        },
    }

    if (!hasOmittedBindings(seeded)) {
        const bindings = try requireConcreteBindings(allocator, seeded);
        allocator.free(seeded);
        seeded_owned = false;
        return .{ .concrete = bindings };
    }

    setup.seeded_bindings = seeded;
    seeded_owned = false;

    const semantic_mask = try derivedViewRuleSeedMask(
        allocator,
        rule.args.len,
        actual_view,
    );
    defer allocator.free(semantic_mask);

    const concrete_seeds = try bindingSeedsForViewReuse(
        allocator,
        partial_bindings,
        seeded,
        semantic_mask,
        .transparent,
    );
    if (setup.view_seed_state) |*seed_state| {
        for (concrete_seeds, 0..) |seed, idx| {
            switch (seed) {
                .none => {},
                else => seed_state.bindings[idx] = seed,
            }
        }
        allocator.free(concrete_seeds);
    } else {
        setup.session_seeds = concrete_seeds;
    }

    return .{ .setup = setup };
}

fn inferBindingsTransparentWithSeeds(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    seeds: []const DefOps.BindingSeed,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    var def_ops = DefOps.Context.init(
        allocator,
        @constCast(theorem),
        env,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, seeds);
    defer session.deinit();

    for (rule.hyps, ref_exprs) |hyp, ref_expr| {
        if (!try session.matchTransparent(hyp, ref_expr)) {
            return error.UnifyMismatch;
        }
    }
    if (!try session.matchTransparent(rule.concl, line_expr)) {
        return error.UnifyMismatch;
    }
    // Use strict finalization here. This path is only for transparent
    // matching of ordinary theorem binders; hidden witnesses still fall
    // through to the structural solver.
    return try session.finalizeConcreteBindings();
}

pub fn inferBindingsTransparent(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    const seeds = try DefOps.BindingSeed.fromOptionalBindings(allocator, partial_bindings);
    defer allocator.free(seeds);

    return try inferBindingsTransparentWithSeeds(
        allocator,
        env,
        theorem,
        rule,
        seeds,
        ref_exprs,
        line_expr,
    );
}

fn bindingSeedsFromStrictFailure(
    allocator: std.mem.Allocator,
    explicit_bindings: []const ?ExprId,
    strict_bindings: []const ?ExprId,
) ![]DefOps.BindingSeed {
    std.debug.assert(explicit_bindings.len == strict_bindings.len);
    const seeds = try allocator.alloc(DefOps.BindingSeed, strict_bindings.len);
    for (strict_bindings, explicit_bindings, 0..) |binding, explicit, idx| {
        seeds[idx] = if (binding) |expr_id|
            if (explicit == null)
                .{ .semantic = .{
                    .expr_id = expr_id,
                    .mode = .transparent,
                } }
            else
                .{ .exact = expr_id }
        else
            .none;
    }
    return seeds;
}

pub fn inferBindingsTransparentFromStrictFailure(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    strict_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    const seeds = try bindingSeedsFromStrictFailure(
        allocator,
        explicit_bindings,
        strict_bindings,
    );
    defer allocator.free(seeds);

    return try inferBindingsTransparentWithSeeds(
        allocator,
        env,
        theorem,
        rule,
        seeds,
        ref_exprs,
        line_expr,
    );
}

fn matchRulePartNormalized(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: ExprId,
) !bool {
    return try NormalizedCompare.matchTemplate(
        allocator,
        env,
        registry,
        scratch,
        session,
        template,
        actual,
    );
}

fn matchRuleHypForInference(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: ExprId,
) !bool {
    if (try session.matchTransparentOrSemantic(template, actual)) return true;
    // This intentionally mirrors `Matching.tryMatchHypothesis`: a referenced
    // line may be stored in the raw form produced by its rule, while final
    // validation can transport it to the expected hypothesis. Binder inference
    // needs the same equivalence, otherwise a whole-line hole after a
    // normalized rule loses the structure needed to infer the next rule's
    // omitted binders.
    return try matchRulePartNormalized(
        allocator,
        env,
        registry,
        scratch,
        session,
        template,
        actual,
    );
}

/// Try to infer a complete candidate from referenced hypotheses only.
///
/// This is deliberately exact: no transparent, normalized, or structural
/// matching is performed here. The caller is expected to use it only when
/// exact refs are allowed to select the candidate before line validation.
pub fn inferBindingsFromRefsOnly(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
) !?[]const ExprId {
    const bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(bindings);

    for (rule.hyps, ref_exprs) |hyp, ref_expr| {
        if (!theorem.matchTemplate(hyp, ref_expr, bindings)) return null;
    }

    for (bindings) |binding| {
        if (binding == null) return null;
    }

    const concrete = try allocator.alloc(ExprId, bindings.len);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding.?;
    }
    return concrete;
}

fn matchRulePartNormalizedSurface(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: *const Expr,
) !bool {
    return try NormalizedCompare.matchSurface(
        allocator,
        env,
        registry,
        scratch,
        session,
        template,
        actual,
    );
}

fn sortUnresolvedFinalizationRoots(
    roots: []DefOps.UnresolvedDummyRoot,
) void {
    var i: usize = 1;
    while (i < roots.len) : (i += 1) {
        const root = roots[i];
        var j = i;
        while (j > 0 and roots[j - 1].root_slot > root.root_slot) : (j -= 1) {
            roots[j] = roots[j - 1];
        }
        roots[j] = root;
    }
}

fn tryFinalizeRuleMatchSession(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    fresh_context: ?HiddenWitnessFreshContext,
    line_deps: u55,
    ref_exprs: []const ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    if (session.finalizeConcreteBindings()) |bindings| {
        return .{ .concrete = bindings };
    } else |err| {
        if (err != error.UnresolvedDummyWitness) return err;
    }

    const fresh = fresh_context orelse return .unresolved_dummy_witness;

    const roots = try session.collectUnresolvedFinalizationRoots();
    defer allocator.free(roots);
    if (roots.len == 0) return .unresolved_dummy_witness;
    sortUnresolvedFinalizationRoots(roots);

    for (roots) |root| {
        if (!root.bound) return .unresolved_dummy_witness;
        if (fresh.sort_vars.getPool(root.sort_name) == null) {
            return .unresolved_dummy_witness;
        }
    }

    const extra_used_deps =
        try session.collectConcreteDepsForPendingFinalization();
    const needs = try allocator.alloc(CompilerFresh.HiddenRootNeed, roots.len);
    defer allocator.free(needs);
    for (roots, 0..) |root, idx| {
        needs[idx] = .{
            .root_slot = root.root_slot,
            .sort_name = root.sort_name,
        };
    }

    const hidden_assignments = CompilerFresh.assignHiddenRootsFromVarsPoolWithLineDeps(
        allocator,
        fresh.parser,
        env,
        session.shared.theorem,
        fresh.theorem_vars,
        fresh.sort_vars,
        line_deps,
        ref_exprs,
        explicit_bindings,
        extra_used_deps,
        needs,
    ) catch |assign_err| {
        if (assign_err == error.FreshNoAvailableVar) {
            return error.HiddenWitnessNoAvailableVar;
        }
        return assign_err;
    };
    defer allocator.free(hidden_assignments);

    const materialized = try allocator.alloc(
        DefOps.MaterializedDummyAssignment,
        hidden_assignments.len,
    );
    defer allocator.free(materialized);
    for (hidden_assignments, 0..) |assignment, idx| {
        materialized[idx] = .{
            .root_slot = assignment.root_slot,
            .expr_id = assignment.expr_id,
        };
    }
    try session.applyMaterializedDummyAssignments(materialized);

    if (session.finalizeConcreteBindings()) |bindings| {
        return .{ .concrete = bindings };
    } else |retry_err| {
        if (retry_err == error.UnresolvedDummyWitness) {
            return .unresolved_dummy_witness;
        }
        return retry_err;
    }
}

fn finishRuleMatchSession(
    context: *const RuleInferenceContext,
    session: *DefOps.RuleMatchSession,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const scratch = context.scratch;
    const rule = context.rule;

    for (rule.hyps, ref_exprs) |hyp, ref_expr| {
        if (try matchRuleHypForInference(
            allocator,
            env,
            registry,
            scratch,
            session,
            hyp,
            ref_expr,
        )) continue;
        return .no_match;
    }

    if (!try session.matchTransparentOrSemantic(rule.concl, line_expr)) {
        if (!try matchRulePartNormalized(
            allocator,
            env,
            registry,
            scratch,
            session,
            rule.concl,
            line_expr,
        )) {
            return .no_match;
        }
    }

    const line_deps = (try exprInfo(
        env,
        session.shared.theorem,
        session.shared.theorem.arg_infos,
        line_expr,
    )).deps;
    return try tryFinalizeRuleMatchSession(
        allocator,
        env,
        session,
        fresh_context,
        line_deps,
        ref_exprs,
        explicit_bindings,
    );
}

pub fn inferBindingsByRuleMatchSession(
    context: *const RuleInferenceContext,
    seeds: []const DefOps.BindingSeed,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    const allocator = context.allocator;
    const rule = context.rule;

    var def_ops = DefOps.Context.initWithRegistry(
        allocator,
        context.theorem,
        context.env,
        context.registry,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, seeds);
    defer session.deinit();

    return try finishRuleMatchSession(
        context,
        &session,
        fresh_context,
        ref_exprs,
        line_expr,
        explicit_bindings,
    );
}

pub fn inferBindingsByMatchSeedState(
    context: *const RuleInferenceContext,
    seed_state: *const DefOps.MatchSeedState,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    const allocator = context.allocator;
    const rule = context.rule;

    var def_ops = DefOps.Context.initWithRegistry(
        allocator,
        context.theorem,
        context.env,
        context.registry,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatchFromSeedState(
        rule.args,
        seed_state,
    );
    defer session.deinit();

    return try finishRuleMatchSession(
        context,
        &session,
        fresh_context,
        ref_exprs,
        line_expr,
        explicit_bindings,
    );
}

fn matchRulePartSurfaceWithRollback(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: *const Expr,
) !bool {
    const seeds = try session.resolveBindingSeeds();
    errdefer allocator.free(seeds);
    var snapshot = try session.exportMatchSeedState(seeds);
    defer snapshot.deinit(allocator);

    if (try matchRulePartSurface(theorem, session, template, actual)) {
        return true;
    }
    try session.restoreFromSeedState(&snapshot);
    return false;
}

fn matchRulePartSurface(
    theorem: *TheoremContext,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: *const Expr,
) !bool {
    if (actual.* == .hole) return true;
    return switch (template) {
        .binder => blk: {
            if (SurfaceExpr.containsHole(actual)) break :blk true;
            const actual_id = try theorem.internParsedExpr(actual);
            break :blk try session.matchTransparentOrSemantic(
                template,
                actual_id,
            );
        },
        .app => |app| blk: {
            const actual_term = switch (actual.*) {
                .term => |term| term,
                .variable, .hole => break :blk false,
            };
            if (actual_term.id != app.term_id) break :blk false;
            if (actual_term.args.len != app.args.len) break :blk false;
            for (app.args, actual_term.args) |tmpl_arg, actual_arg| {
                if (!try matchRulePartSurface(
                    theorem,
                    session,
                    tmpl_arg,
                    actual_arg,
                )) {
                    break :blk false;
                }
            }
            break :blk true;
        },
    };
}

fn finishHoleyRuleMatchSession(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    session: *DefOps.RuleMatchSession,
    fresh_context: ?HiddenWitnessFreshContext,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    holey_concl: *const Expr,
    diagnostic_bindings: []const ?ExprId,
) !RuleMatchResult {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const scratch = context.scratch;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule = context.rule;

    for (rule.hyps, ref_exprs) |hyp, ref_expr| {
        if (try matchRuleHypForInference(
            allocator,
            env,
            registry,
            scratch,
            session,
            hyp,
            ref_expr,
        )) continue;
        return .no_match;
    }

    const matched_concl = try matchRulePartSurfaceWithRollback(
        allocator,
        theorem,
        session,
        rule.concl,
        holey_concl,
    ) or try matchRulePartNormalizedSurface(
        allocator,
        env,
        registry,
        scratch,
        session,
        rule.concl,
        holey_concl,
    );
    if (!matched_concl) return .no_match;

    return tryFinalizeRuleMatchSession(
        allocator,
        env,
        session,
        fresh_context,
        holey_concl.deps(),
        ref_exprs,
        partial_bindings,
    ) catch |err| {
        if (err == error.MissingBinderAssignment) {
            const snapshot = try session.materializeOptionalBindings();
            defer allocator.free(snapshot);
            for (snapshot, 0..) |binding, idx| {
                if (binding != null) continue;
                self.setProof(
                    try buildMissingBinderDiagnostic(
                        allocator,
                        env,
                        theorem,
                        assertion,
                        rule,
                        line,
                        .structural_solver,
                        partial_bindings,
                        snapshot,
                        idx,
                    ),
                );
                break;
            }
        } else if (err == error.UnresolvedDummyWitness) {
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
                    diagnostic_bindings,
                ),
            );
        }
        return err;
    };
}

pub fn inferBindingsFromHoleyAdvanced(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    holey_concl: *const Expr,
    maybe_view: ?ViewDecl,
    fresh_context: ?HiddenWitnessFreshContext,
) ![]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule = context.rule;

    if (try tryInferHoleyStructuralSolver(
        self,
        context,
        line,
        partial_bindings,
        ref_exprs,
        holey_concl,
        maybe_view,
    )) |bindings| {
        self.restoreDiagnostic(null);
        return bindings;
    }

    var seed_setup = switch (try buildViewSeedSetup(
        self,
        allocator,
        env,
        registry,
        theorem,
        rule,
        maybe_view,
        .{ .surface = holey_concl },
        ref_exprs,
        partial_bindings,
        null,
    )) {
        .concrete => |bindings| return bindings,
        .setup => |setup| setup,
    };
    defer seed_setup.deinit(allocator);

    var def_ops = DefOps.Context.initWithRegistry(
        allocator,
        theorem,
        env,
        registry,
    );
    defer def_ops.deinit();

    var session = if (seed_setup.view_seed_state) |*seed_state|
        try def_ops.beginRuleMatchFromSeedState(rule.args, seed_state)
    else
        try def_ops.beginRuleMatch(rule.args, seed_setup.session_seeds.?);
    defer session.deinit();

    const diagnostic_bindings = seed_setup.diagnosticBindings(
        partial_bindings,
    );
    const result = finishHoleyRuleMatchSession(
        self,
        context,
        line,
        &session,
        fresh_context,
        partial_bindings,
        ref_exprs,
        holey_concl,
        diagnostic_bindings,
    ) catch |err| {
        return err;
    };
    return switch (result) {
        .concrete => |bindings| bindings,
        .no_match => {
            self.setProof(
                try buildInferenceFailureDiagnostic(
                    allocator,
                    env,
                    theorem,
                    assertion,
                    rule,
                    line,
                    .structural_solver,
                    error.UnifyMismatch,
                    partial_bindings,
                    diagnostic_bindings,
                ),
            );
            return error.UnifyMismatch;
        },
        .unresolved_dummy_witness => {
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
                    diagnostic_bindings,
                ),
            );
            return error.UnresolvedDummyWitness;
        },
    };
}

// Use the structural solver for holey conclusions, even when the visible
// hole is not itself a structural sort. A whole-line `_wff` can hide an `nd`
// conclusion whose context binder is recoverable only from ACUI hypotheses.
fn tryInferHoleyStructuralSolver(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    holey_concl: *const Expr,
    maybe_view: ?ViewDecl,
) !?[]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const scratch = context.scratch;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule_id = context.rule_id;
    const rule = context.rule;

    const has_structural_hole = try SurfaceExpr.containsStructuralHole(
        env,
        registry,
        holey_concl,
    );
    if (!has_structural_hole and !SurfaceExpr.containsHole(holey_concl)) {
        return null;
    }

    const minimal_line = if (has_structural_hole)
        try SurfaceExpr.lowerStructuralHolesToUnits(
            theorem,
            env,
            registry,
            holey_concl,
        )
    else
        null;

    var solver = InferenceSolver.init(
        allocator,
        env,
        theorem,
        registry,
        rule_id,
        rule,
        if (maybe_view) |*view| view else null,
        scratch,
        self.debug,
    );
    defer solver.deinit();

    const bindings = solver.solveHoleyConclusion(
        partial_bindings,
        ref_exprs,
        holey_concl,
    ) catch |holey_err| blk: {
        DebugTrace.traceInference(
            self.debug,
            "holey structural solver failed for rule {s}: {s}",
            .{ rule.name, @errorName(holey_err) },
        );
        const lowered = minimal_line orelse return null;
        break :blk solver.solve(
            partial_bindings,
            ref_exprs,
            lowered,
        ) catch |minimal_err| {
            DebugTrace.traceInference(
                self.debug,
                "minimal structural solver failed for rule {s}: {s}",
                .{ rule.name, @errorName(minimal_err) },
            );
            return null;
        };
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

pub fn maybeAddStructuralAmbiguityWarning(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
    line: anytype,
    solver: *InferenceSolver,
) !void {
    if (!solver.hadAmbiguityWarning()) return;
    var diag = CompilerDiag.withPhase(.{
        .severity = .warning,
        .kind = .inference_failed,
        .err = error.AmbiguousAcuiMatch,
        .source = .proof,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .span = line.ruleApplicationSpan(),
        .detail = .{ .inference_failure = .{
            .path = .structural_solver,
            .first_unsolved_binder_name = null,
        } },
    }, .inference);
    try addFormattedInferenceNote(
        allocator,
        &diag,
        "inference path: {s}",
        .{CompilerDiag.inferencePathName(.structural_solver)},
    );
    if (solver.getAmbiguityReport()) |report| {
        try addAmbiguityWarningNotes(allocator, &diag, report);
    }
    self.addWarning(diag);
}

pub fn tryConcreteStructuralSolver(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const scratch = context.scratch;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule_id = context.rule_id;
    const rule = context.rule;

    var solver = InferenceSolver.init(
        allocator,
        env,
        theorem,
        registry,
        rule_id,
        rule,
        null,
        scratch,
        self.debug,
    );
    defer solver.deinit();
    const bindings = solver.solve(
        partial_bindings,
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
            partial_bindings,
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
                partial_bindings,
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

pub fn tryConcreteRuleMatchSessionFallback(
    self: *CompilerContext,
    context: *const RuleInferenceContext,
    line: anytype,
    seeds: []const DefOps.BindingSeed,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
    diagnostic_bindings: []const ?ExprId,
) !?[]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const scratch = context.scratch;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule = context.rule;

    DebugTrace.traceInference(
        self.debug,
        "non-structural inference: trying normalized session fallback",
        .{},
    );
    const mark = scratch.mark();
    const result = inferBindingsByRuleMatchSession(
        context,
        seeds,
        fresh_context,
        ref_exprs,
        line_expr,
        explicit_bindings,
    ) catch |err| {
        try traceInferenceFailure(
            self.debug,
            allocator,
            theorem,
            env,
            rule,
            .normalized_session_fallback,
            err,
            explicit_bindings,
            diagnostic_bindings,
        );
        scratch.discard(mark);
        switch (err) {
            error.OutOfMemory => return err,
            else => return null,
        }
    };
    scratch.discard(mark);
    return switch (result) {
        .concrete => |bindings| bindings,
        .no_match => null,
        .unresolved_dummy_witness => blk: {
            self.setProof(
                try buildInferenceFailureDiagnostic(
                    allocator,
                    env,
                    theorem,
                    assertion,
                    rule,
                    line,
                    .normalized_session_fallback,
                    error.UnresolvedDummyWitness,
                    explicit_bindings,
                    diagnostic_bindings,
                ),
            );
            break :blk error.UnresolvedDummyWitness;
        },
    };
}

pub fn hasOmittedBindings(bindings: []const ?ExprId) bool {
    for (bindings) |binding| {
        if (binding == null) return true;
    }
    return false;
}

pub fn hasOmittedStructuralBindings(
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) !bool {
    for (bindings, 0..) |binding, idx| {
        if (binding != null) continue;
        if (idx >= rule.args.len) continue;
        if ((try registry.resolveStructuralCombinerForSort(
            env,
            rule.args[idx].sort_name,
        )) != null) {
            return true;
        }
    }
    return false;
}

/// Return true when a structural template subtree contains both an omitted
/// structural remainder and an already-fixed item.
///
/// This does not preempt a successful strict replay. It tells later inference
/// paths to avoid greedy transparent/session fallback and let the structural
/// solver rank any remaining ACUI-compatible completions by minimal residual
/// context instead. A bare context parameter, such as the `g` in a rule shaped
/// like `g |- ...`, is not enough to trigger this preference.
pub fn shouldPreferStructuralSolver(
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) !bool {
    if (!try hasOmittedStructuralBindings(env, registry, rule, bindings)) {
        return false;
    }
    for (rule.hyps) |hyp| {
        if (try templateContainsStructuralCompetition(
            env,
            registry,
            rule,
            bindings,
            hyp,
        )) {
            return true;
        }
    }
    return try templateContainsStructuralCompetition(
        env,
        registry,
        rule,
        bindings,
        rule.concl,
    );
}

fn templateContainsStructuralCompetition(
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    template: TemplateExpr,
) !bool {
    return switch (template) {
        .binder => false,
        .app => |app| blk: {
            const maybe_combiner = try registry.resolveStructuralCombiner(
                env,
                app.term_id,
            );
            if (maybe_combiner) |combiner| {
                if (try structuralTreeHasCompetition(
                    env,
                    rule,
                    bindings,
                    template,
                    combiner,
                )) {
                    break :blk true;
                }
            }
            for (app.args) |arg| {
                if (try templateContainsStructuralCompetition(
                    env,
                    registry,
                    rule,
                    bindings,
                    arg,
                )) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

fn structuralTreeHasCompetition(
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    template: TemplateExpr,
    combiner: ResolvedStructuralCombiner,
) !bool {
    var saw_omitted_remainder = false;
    var saw_fixed_item = false;
    try inspectStructuralTree(
        env,
        rule,
        bindings,
        template,
        combiner,
        &saw_omitted_remainder,
        &saw_fixed_item,
    );
    return saw_omitted_remainder and saw_fixed_item;
}

fn inspectStructuralTree(
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    template: TemplateExpr,
    combiner: ResolvedStructuralCombiner,
    saw_omitted_remainder: *bool,
    saw_fixed_item: *bool,
) !void {
    switch (template) {
        .binder => |idx| {
            if (isStructuralRemainderBinder(env, rule, idx, combiner)) {
                if (idx < bindings.len and bindings[idx] == null) {
                    saw_omitted_remainder.* = true;
                } else if (idx < bindings.len) {
                    saw_fixed_item.* = true;
                }
            } else if (idx < bindings.len and bindings[idx] != null) {
                saw_fixed_item.* = true;
            }
        },
        .app => |app| {
            if (app.term_id == combiner.head_term_id and app.args.len == 2) {
                try inspectStructuralTree(
                    env,
                    rule,
                    bindings,
                    app.args[0],
                    combiner,
                    saw_omitted_remainder,
                    saw_fixed_item,
                );
                try inspectStructuralTree(
                    env,
                    rule,
                    bindings,
                    app.args[1],
                    combiner,
                    saw_omitted_remainder,
                    saw_fixed_item,
                );
                return;
            }
            if (app.term_id == combiner.unit_term_id and app.args.len == 0 and
                combiner.supportsLeftUnit() and combiner.supportsRightUnit())
            {
                return;
            }
            if (templateItemIsFixed(bindings, template)) {
                saw_fixed_item.* = true;
            }
        },
    }
}

fn isStructuralRemainderBinder(
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    idx: usize,
    combiner: ResolvedStructuralCombiner,
) bool {
    if (idx >= rule.args.len) return false;
    if (combiner.head_term_id >= env.terms.items.len) return false;
    const structural_sort = env.terms.items[combiner.head_term_id].ret_sort_name;
    return std.mem.eql(u8, rule.args[idx].sort_name, structural_sort);
}

fn templateItemIsFixed(
    bindings: []const ?ExprId,
    template: TemplateExpr,
) bool {
    return switch (template) {
        .binder => |idx| idx < bindings.len and bindings[idx] != null,
        .app => |app| {
            for (app.args) |arg| {
                if (!templateItemIsFixed(bindings, arg)) return false;
            }
            return true;
        },
    };
}

pub fn requireConcreteBindings(
    allocator: std.mem.Allocator,
    partial_bindings: []const ?ExprId,
) ![]const ExprId {
    const bindings = try allocator.alloc(ExprId, partial_bindings.len);
    for (partial_bindings, 0..) |binding, idx| {
        bindings[idx] = binding orelse return error.MissingBinderAssignment;
    }
    return bindings;
}
