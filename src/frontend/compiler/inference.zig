const builtin = @import("builtin");
const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const DefOps = @import("../def_ops.zig");
const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const Expr = @import("../../trusted/expressions.zig").Expr;
const UnifyReplay = @import("../../trusted/unify_replay.zig");
const ProofLine = @import("../proof_script.zig").ProofLine;
const Span = @import("../proof_script.zig").Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const NormalizeSpec = @import("../rewrite_registry.zig").NormalizeSpec;
const Normalizer = @import("../normalizer.zig").Normalizer;
const Canonicalizer = @import("../canonicalizer.zig").Canonicalizer;
const InferenceSolver = @import("../inference_solver.zig").Solver;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const CompilerViews = @import("./views.zig");
const ViewDecl = CompilerViews.ViewDecl;
const CompilerDiag = @import("./diag.zig");
const CompilerFresh = @import("./fresh.zig");
const CompilerVars = @import("./vars.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const SortVarRegistry = CompilerVars.SortVarRegistry;
const NameExprMap = std.StringHashMap(*const Expr);
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Emit = @import("./emit.zig");

/// Result of an advanced rule match attempt.
pub const RuleMatchResult = union(enum) {
    /// Match succeeded and all bindings are concrete ExprIds.
    concrete: []const ExprId,
    /// The rule's hypotheses/conclusion did not match.
    no_match,
    /// Matching succeeded symbolically but still needs explicit bindings.
    unresolved_dummy_witness,
};

const ExprInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

pub const DepViolationDetail = struct {
    first_arg_idx: usize,
    second_arg_idx: usize,
};

pub const HiddenWitnessFreshContext = struct {
    parser: *MM0Parser,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
};

pub const InferenceContext = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    // Heap prefix `0..rule.args.len` stores inferred theorem arguments.
    // These slots start as either an explicit binding or `null` if omitted.
    // Any entries appended later by `UTermSave` are concrete by construction.
    uheap: std.ArrayListUnmanaged(?ExprId) = .{},
    ustack: std.ArrayListUnmanaged(ExprId) = .{},
    hyps: []const ExprId,
    next_hyp: usize,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        partial_bindings: []const ?ExprId,
        hyps: []const ExprId,
        line_expr: ExprId,
    ) !InferenceContext {
        var ctx = InferenceContext{
            .allocator = allocator,
            .theorem = theorem,
            .hyps = hyps,
            .next_hyp = hyps.len,
        };
        try ctx.uheap.appendSlice(allocator, partial_bindings);
        try ctx.ustack.append(allocator, line_expr);
        return ctx;
    }

    pub fn deinit(self: *InferenceContext) void {
        self.uheap.deinit(self.allocator);
        self.ustack.deinit(self.allocator);
    }

    pub fn uopRef(self: *InferenceContext, heap_id: u32) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        if (heap_id >= self.uheap.items.len) return error.UHeapOutOfBounds;
        if (self.uheap.items[heap_id]) |expected| {
            if (expr_id != expected) return error.UnifyMismatch;
        } else {
            // This is the one semantic difference from verifier-style unify:
            // the first encounter with an omitted binder solves it.
            self.uheap.items[heap_id] = expr_id;
        }
    }

    // Unify replay is exact replay. Def-aware inference lives in
    // higher-level solver paths rather than in the opcode interpreter.
    pub fn uopTerm(
        self: *InferenceContext,
        term_id: u32,
        save: bool,
    ) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return error.ExpectedTermApp,
        };
        if (app.term_id != term_id) return error.TermMismatch;
        if (save) try self.uheap.append(self.allocator, expr_id);
        var i = app.args.len;
        while (i > 0) {
            i -= 1;
            try self.ustack.append(self.allocator, app.args[i]);
        }
    }

    pub fn uopDummy(self: *InferenceContext, _: u32) !void {
        _ = self;
        return error.UDummyNotAllowed;
    }

    pub fn uopHyp(self: *InferenceContext) !void {
        if (self.next_hyp == 0) return error.HypCountMismatch;
        // See `buildRuleUnifyStream`: hypotheses are replayed from the end so
        // that they are matched in source order overall.
        self.next_hyp -= 1;
        try self.ustack.append(self.allocator, self.hyps[self.next_hyp]);
    }
};

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

fn exactBindingSeeds(
    allocator: std.mem.Allocator,
    partial_bindings: []const ?ExprId,
) ![]DefOps.BindingSeed {
    const seeds = try allocator.alloc(
        DefOps.BindingSeed,
        partial_bindings.len,
    );
    for (partial_bindings, 0..) |binding, idx| {
        seeds[idx] = if (binding) |expr_id|
            .{ .exact = expr_id }
        else
            .none;
    }
    return seeds;
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

pub fn inferBindingsTransparent(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    var def_ops = DefOps.Context.init(
        allocator,
        @constCast(theorem),
        env,
    );
    defer def_ops.deinit();

    const seeds = try exactBindingSeeds(allocator, partial_bindings);
    defer allocator.free(seeds);

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
    // Use strict finalization — transparent matching with exact seeds
    // should never produce unresolved hidden-dummy structure.
    return try session.finalizeConcreteBindings();
}

fn hypMarkedForNormalize(norm_spec: ?NormalizeSpec, hyp_idx: usize) bool {
    const spec = norm_spec orelse return false;
    for (spec.hyp_indices) |marked| {
        if (marked == hyp_idx) return true;
    }
    return false;
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
    var comparison = try session.beginNormalizedComparison(template, actual);
    defer comparison.deinit();

    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);

    var normalizer = Normalizer.initWithScratch(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
        &checked,
        scratch,
    );
    const expected_mark = scratch.mark();
    const normalized_expected =
        normalizer.normalize(comparison.expected_expr) catch |err| {
            return err;
        };
    scratch.discard(expected_mark);
    const actual_mark = scratch.mark();
    const normalized_actual =
        normalizer.normalize(comparison.actual_expr) catch |err| {
            return err;
        };
    scratch.discard(actual_mark);

    var canonicalizer = Canonicalizer.init(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
    );
    const canonical_expected = try canonicalizer.canonicalize(
        normalized_expected.result_expr,
    );
    const canonical_actual = try canonicalizer.canonicalize(
        normalized_actual.result_expr,
    );
    return try comparison.finish(
        canonical_expected,
        canonical_actual,
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
    line_expr: ExprId,
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

    const hidden_assignments = CompilerFresh.assignHiddenRootsFromVarsPool(
        allocator,
        fresh.parser,
        env,
        session.shared.theorem,
        fresh.theorem_vars,
        fresh.sort_vars,
        line_expr,
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
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    rule_id: u32,
    rule: *const RuleDecl,
    session: *DefOps.RuleMatchSession,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    const norm_spec = registry.getNormalizeSpec(rule_id);

    for (rule.hyps, ref_exprs, 0..) |hyp, ref_expr, hyp_idx| {
        if (try session.matchTransparent(hyp, ref_expr)) continue;
        if (hypMarkedForNormalize(norm_spec, hyp_idx) and
            try matchRulePartNormalized(
                allocator,
                env,
                registry,
                scratch,
                session,
                hyp,
                ref_expr,
            ))
        {
            continue;
        }
        return .no_match;
    }

    if (norm_spec != null and norm_spec.?.concl) {
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
    } else if (!try session.matchTransparent(rule.concl, line_expr)) {
        return .no_match;
    }

    return try tryFinalizeRuleMatchSession(
        allocator,
        env,
        session,
        fresh_context,
        line_expr,
        ref_exprs,
        explicit_bindings,
    );
}

fn inferBindingsByRuleMatchSession(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    theorem: *TheoremContext,
    rule_id: u32,
    rule: *const RuleDecl,
    seeds: []const DefOps.BindingSeed,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    var def_ops = DefOps.Context.initWithRegistry(
        allocator,
        theorem,
        env,
        registry,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, seeds);
    defer session.deinit();

    return try finishRuleMatchSession(
        allocator,
        env,
        registry,
        scratch,
        rule_id,
        rule,
        &session,
        fresh_context,
        ref_exprs,
        line_expr,
        explicit_bindings,
    );
}

fn inferBindingsByMatchSeedState(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    theorem: *TheoremContext,
    rule_id: u32,
    rule: *const RuleDecl,
    seed_state: *const DefOps.MatchSeedState,
    fresh_context: ?HiddenWitnessFreshContext,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    explicit_bindings: []const ?ExprId,
) !RuleMatchResult {
    var def_ops = DefOps.Context.initWithRegistry(
        allocator,
        theorem,
        env,
        registry,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatchFromSeedState(
        rule.args,
        seed_state,
    );
    defer session.deinit();

    return try finishRuleMatchSession(
        allocator,
        env,
        registry,
        scratch,
        rule_id,
        rule,
        &session,
        fresh_context,
        ref_exprs,
        line_expr,
        explicit_bindings,
    );
}

pub fn shouldUseAdvancedInference(
    rule_id: u32,
    maybe_view: ?ViewDecl,
    registry: *RewriteRegistry,
) bool {
    if (maybe_view != null) return true;
    return registry.getNormalizeSpec(rule_id) != null;
}

pub fn inferBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    theorem: *TheoremContext,
    assertion: AssertionStmt,
    rule_id: u32,
    rule: *const RuleDecl,
    line: ProofLine,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    use_advanced_inference: bool,
) ![]const ExprId {
    if (use_advanced_inference) {
        var seeded_bindings_storage: ?[]?ExprId = null;
        defer if (seeded_bindings_storage) |seeded| allocator.free(seeded);
        var view_seed_state: ?DefOps.MatchSeedState = null;
        defer if (view_seed_state) |*seed_state| seed_state.deinit(allocator);
        var session_seeds: ?[]DefOps.BindingSeed = null;
        defer if (session_seeds) |seeds| allocator.free(seeds);

        if (maybe_view) |view| {
            var view_seed_overrides: ?[]DefOps.BindingSeed = null;
            defer if (view_seed_overrides) |seeds| allocator.free(seeds);

            if (fresh_context) |fresh| {
                view_seed_overrides =
                    try CompilerFresh.seedRecoverHolesFromVarsPool(
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

            const seeded = try allocator.dupe(?ExprId, partial_bindings);
            CompilerViews.applyViewBindings(
                allocator,
                theorem,
                env,
                registry,
                &view,
                line_expr,
                ref_exprs,
                seeded,
                view_seed_overrides,
                &view_seed_state,
                self.debug.views,
            ) catch |err| {
                if (self.debug.views) {
                    debugPrint(
                        "[debug:views] applyViewBindings failed: {s}\n",
                        .{@errorName(err)},
                    );
                }
                allocator.free(seeded);
                session_seeds = try exactBindingSeeds(
                    allocator,
                    partial_bindings,
                );
            };
            if (session_seeds == null) {
                seeded_bindings_storage = seeded;

                if (!hasOmittedBindings(seeded)) {
                    return try requireConcreteBindings(allocator, seeded);
                }

                const semantic_mask = try derivedViewRuleSeedMask(
                    allocator,
                    rule.args.len,
                    view,
                );
                defer allocator.free(semantic_mask);

                const concrete_seeds = try bindingSeedsForViewReuse(
                    allocator,
                    partial_bindings,
                    seeded,
                    semantic_mask,
                    .transparent,
                );
                if (view_seed_state) |*seed_state| {
                    for (concrete_seeds, 0..) |seed, idx| {
                        switch (seed) {
                            .none => {},
                            else => seed_state.bindings[idx] = seed,
                        }
                    }
                    allocator.free(concrete_seeds);
                } else {
                    session_seeds = concrete_seeds;
                }
            }
        } else {
            session_seeds = try exactBindingSeeds(allocator, partial_bindings);
        }

        const match_mark = scratch.mark();
        const match_result = (if (view_seed_state) |*seed_state|
            inferBindingsByMatchSeedState(
                allocator,
                env,
                registry,
                scratch,
                theorem,
                rule_id,
                rule,
                seed_state,
                fresh_context,
                ref_exprs,
                line_expr,
                partial_bindings,
            )
        else
            inferBindingsByRuleMatchSession(
                allocator,
                env,
                registry,
                scratch,
                theorem,
                rule_id,
                rule,
                session_seeds.?,
                fresh_context,
                ref_exprs,
                line_expr,
                partial_bindings,
            )) catch |err| {
            if (CompilerDiag.setProofScratchDiagnosticIfPresent(
                self,
                scratch,
                match_mark,
                env,
                .inference,
                .inference_failed,
                err,
                assertion.name,
                line.label,
                line.rule_name,
                line.ruleApplicationSpan(),
            )) {
                return err;
            }
            scratch.discard(match_mark);
            return err;
        };
        scratch.discard(match_mark);
        switch (match_result) {
            .concrete => |bindings| {
                return bindings;
            },
            .no_match => {},
            .unresolved_dummy_witness => {
                CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                    .kind = .inference_failed,
                    .err = error.UnresolvedDummyWitness,
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = line.rule_name,
                    .span = line.ruleApplicationSpan(),
                }, .inference));
                return error.UnresolvedDummyWitness;
            },
        }

        var solver = InferenceSolver.init(
            allocator,
            env,
            theorem,
            registry,
            rule,
            if (maybe_view) |*view| view else null,
            self.debug.inference,
        );
        const solver_bindings = if (seeded_bindings_storage) |seeded|
            seeded
        else
            partial_bindings;
        const bindings = solver.solve(
            solver_bindings,
            ref_exprs,
            line_expr,
        ) catch |err| {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .inference_failed,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
            }, .inference));
            return err;
        };

        if (solver.hadAmbiguityWarning()) {
            self.addWarning(CompilerDiag.withPhase(.{
                .severity = .warning,
                .kind = .inference_failed,
                .err = error.AmbiguousAcuiMatch,
                .source = .proof,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
            }, .inference));
        }
        return bindings;
    }

    if (strictInferBindings(
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
    )) |b| {
        return b;
    } else |err| {
        if (self.last_diagnostic != null) return err;
        if (maybe_view == null) {
            const transparent = inferBindingsTransparent(
                allocator,
                env,
                theorem,
                rule,
                partial_bindings,
                ref_exprs,
                line_expr,
            ) catch |transparent_err| blk: {
                if (transparent_err == error.UnresolvedDummyWitness) {
                    CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                        .kind = .inference_failed,
                        .err = transparent_err,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .rule_name = line.rule_name,
                        .span = line.ruleApplicationSpan(),
                    }, .inference));
                    return transparent_err;
                }
                break :blk null;
            };
            if (transparent) |bindings| {
                return bindings;
            }
        }
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .inference_failed,
            .err = err,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.ruleApplicationSpan(),
        }, .inference));
        return err;
    }
}

pub fn strictInferBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ProofLine,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    const unify = try Emit.buildRuleUnifyStream(allocator, rule);

    var inference = try InferenceContext.init(
        allocator,
        theorem,
        partial_bindings,
        ref_exprs,
        line_expr,
    );
    defer inference.deinit();

    try UnifyReplay.run(unify, 0, &inference);
    if (inference.ustack.items.len != 0) {
        return error.UnifyStackNotEmpty;
    }
    if (inference.next_hyp != 0) {
        return error.HypCountMismatch;
    }

    const bindings = try allocator.alloc(ExprId, rule.args.len);
    for (0..rule.args.len) |idx| {
        const binding = inference.uheap.items[idx] orelse {
            const binder_name = rule.arg_names[idx] orelse "_";
            CompilerDiag.maybeSetProof(self, CompilerDiag.withPhase(.{
                .kind = .missing_binder_assignment,
                .err = error.MissingBinderAssignment,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx],
                .span = line.binding_list_span orelse line.rule_span,
                .detail = .{
                    .missing_binder_assignment = .{
                        .binder_name = binder_name,
                    },
                },
            }, .inference));
            return error.MissingBinderAssignment;
        };
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            CompilerDiag.maybeSetProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx],
                .span = CompilerDiag.proofBindingDiagnosticSpan(line, rule.arg_names[idx]),
            }, .inference));
            return err;
        };
        bindings[idx] = binding;
    }
    if (try firstDepViolation(
        env,
        theorem,
        assertion.args,
        rule.args,
        bindings,
    )) |_| {
        allocator.free(bindings);
        CompilerDiag.maybeSetProof(self, CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.ruleApplicationSpan(),
        }, .inference));
        return error.DepViolation;
    }
    return bindings;
}

pub fn validateResolvedBindings(
    self: anytype,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: ProofLine,
    rule: *const RuleDecl,
    bindings: []const ExprId,
) !void {
    for (bindings, 0..) |binding, idx| {
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx],
                .span = CompilerDiag.proofBindingDiagnosticSpan(line, rule.arg_names[idx]),
            }, .inference));
            return err;
        };
    }
    if (try firstDepViolation(
        env,
        theorem,
        assertion.args,
        rule.args,
        bindings,
    )) |_| {
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.ruleApplicationSpan(),
        }, .inference));
        return error.DepViolation;
    }
}

pub fn bindingsRespectRuleDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    bindings: []const ExprId,
) !bool {
    return (try firstDepViolation(
        env,
        theorem,
        theorem_args,
        rule_args,
        bindings,
    )) == null;
}

pub fn firstDepViolation(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    bindings: []const ExprId,
) !?DepViolationDetail {
    var bound_deps: [56]u55 = undefined;
    var bound_arg_indices: [56]usize = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_arg_indices: [56]usize = undefined;
    var prev_len: usize = 0;

    for (bindings, rule_args, 0..) |binding, expected, idx| {
        const info = try exprInfo(env, theorem, theorem_args, binding);
        if (expected.bound) {
            for (0..prev_len) |k| {
                if (prev_deps[k] & info.deps != 0) {
                    return .{
                        .first_arg_idx = prev_arg_indices[k],
                        .second_arg_idx = idx,
                    };
                }
            }
            bound_deps[bound_len] = info.deps;
            bound_arg_indices[bound_len] = idx;
            bound_len += 1;
        } else {
            for (0..bound_len) |k| {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0)
                    continue;
                if (bound_deps[k] & info.deps != 0) {
                    return .{
                        .first_arg_idx = bound_arg_indices[k],
                        .second_arg_idx = idx,
                    };
                }
            }
        }
        prev_deps[prev_len] = info.deps;
        prev_arg_indices[prev_len] = idx;
        prev_len += 1;
    }
    return null;
}

// Inference only solves equalities. We still need the same sort, boundness,
// and dependency checks that explicit parser-side argument parsing performs.
pub fn validateBindingExpr(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expected: ArgInfo,
    expr_id: ExprId,
) !void {
    const info = try exprInfo(env, theorem, theorem_args, expr_id);
    if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
        return error.SortMismatch;
    }
    // Match verifier semantics: bound params require bound exprs,
    // but regular params accept any expression (including bound vars).
    if (expected.bound and !info.bound) return error.BoundnessMismatch;
    // Note: dep checking is deferred to the verifier which checks deps
    // relative to the theorem's own bound variables.
}

pub fn exprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expr_id: ExprId,
) !ExprInfo {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= theorem_args.len) return error.UnknownTheoremVariable;
                const arg = theorem_args[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                    .deps = arg.deps,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                    .deps = dummy.deps,
                };
            },
        },
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            var deps: u55 = 0;
            for (app.args) |arg_id| {
                deps |= (try exprInfo(env, theorem, theorem_args, arg_id)).deps;
            }
            break :blk .{
                .sort_name = env.terms.items[app.term_id].ret_sort_name,
                .bound = false,
                .deps = deps,
            };
        },
    };
}

fn debugPrint(comptime fmt: []const u8, args: anytype) void {
    if (comptime builtin.target.os.tag == .freestanding) return;
    std.debug.print(fmt, args);
}

pub fn hasOmittedBindings(bindings: []const ?ExprId) bool {
    for (bindings) |binding| {
        if (binding == null) return true;
    }
    return false;
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
