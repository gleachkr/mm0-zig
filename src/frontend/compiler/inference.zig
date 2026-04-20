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
const ViewTrace = @import("../view_trace.zig");
const DebugConfig = @import("../debug.zig").DebugConfig;
const DebugTrace = @import("../debug.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const InferencePath = CompilerDiag.InferencePath;
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

pub const DepViolationDetail = CompilerDiag.DepViolationDiagnosticDetail;

const StrictReplayFailure = struct {
    err: anyerror,
    partial_bindings: []const ?ExprId,
};

const StrictReplayResult = union(enum) {
    complete: []const ExprId,
    failed: StrictReplayFailure,
};

const BindingSummaryMode = enum {
    explicit,
    inferred,
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
            .placeholder => return error.ExpectedTermApp,
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

fn buildInferenceFailureDiagnostic(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ProofLine,
    path: InferencePath,
    err: anyerror,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !Diagnostic {
    var diag = CompilerDiag.withPhase(.{
        .kind = .inference_failed,
        .err = err,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.rule_name,
        .span = line.ruleApplicationSpan(),
        .detail = .{ .inference_failure = .{
            .path = path,
            .first_unsolved_binder_name = firstUnsolvedNamedBinder(rule, current_bindings),
        } },
    }, .inference);
    try addInferenceNotes(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        path,
        explicit_bindings,
        current_bindings,
    );
    return diag;
}

fn buildMissingBinderDiagnostic(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ProofLine,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    missing_idx: usize,
) !Diagnostic {
    const binder_name = rule.arg_names[missing_idx] orelse "_";
    var diag = CompilerDiag.withPhase(.{
        .kind = .missing_binder_assignment,
        .err = error.MissingBinderAssignment,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.rule_name,
        .name = rule.arg_names[missing_idx],
        .span = line.binding_list_span orelse line.rule_span,
        .detail = .{ .missing_binder_assignment = .{
            .binder_name = binder_name,
            .path = path,
        } },
    }, .inference);
    try addInferenceNotes(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        path,
        explicit_bindings,
        current_bindings,
    );
    return diag;
}

fn addInferenceNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    try addFormattedInferenceNote(
        allocator,
        diag,
        "inference path: {s}",
        .{CompilerDiag.inferencePathName(path)},
    );

    const explicit_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .explicit,
    );
    defer allocator.free(explicit_summary);
    try addFormattedInferenceNote(
        allocator,
        diag,
        "explicit bindings: {s}",
        .{explicit_summary},
    );

    const inferred_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .inferred,
    );
    defer allocator.free(inferred_summary);
    try addFormattedInferenceNote(
        allocator,
        diag,
        "inferred bindings before failure: {s}",
        .{inferred_summary},
    );

    if (firstUnsolvedBinderLabel(rule, current_bindings)) |label| {
        try addFormattedInferenceNote(
            allocator,
            diag,
            "first unsolved binder: {s}",
            .{label},
        );
    }
}

fn addAmbiguityWarningNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    report: @import("../inference_solver.zig").AmbiguityReport,
) !void {
    if (report.chosen_bindings) |summary| {
        try addFormattedInferenceNote(
            allocator,
            diag,
            "chosen bindings: {s}",
            .{summary},
        );
    }
    if (report.alternative_bindings) |summary| {
        try addFormattedInferenceNote(
            allocator,
            diag,
            "alternative bindings: {s}",
            .{summary},
        );
    }
    try addFormattedInferenceNote(
        allocator,
        diag,
        "distinct solutions considered: {d}",
        .{report.distinct_solution_count},
    );
}

fn addFormattedInferenceNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    CompilerDiag.addNote(diag, message, .proof, null);
}

fn traceInferenceAttempt(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;
    DebugTrace.traceInference(
        config,
        "trying {s} for rule {s}",
        .{ CompilerDiag.inferencePathName(path), rule.name },
    );
    try traceInferenceBindingSummaries(
        config,
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
    );
}

fn traceInferenceFailure(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    path: InferencePath,
    err: anyerror,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;
    DebugTrace.traceInference(
        config,
        "{s} failed for rule {s}: {s}",
        .{
            CompilerDiag.inferencePathName(path),
            rule.name,
            @errorName(err),
        },
    );
    try traceInferenceBindingSummaries(
        config,
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
    );
}

fn traceInferenceBindingSummaries(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;

    const explicit_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .explicit,
    );
    defer allocator.free(explicit_summary);
    DebugTrace.traceInference(
        config,
        "  explicit bindings: {s}",
        .{explicit_summary},
    );

    const inferred_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .inferred,
    );
    defer allocator.free(inferred_summary);
    DebugTrace.traceInference(
        config,
        "  inferred bindings: {s}",
        .{inferred_summary},
    );

    if (firstUnsolvedBinderLabel(rule, current_bindings)) |label| {
        DebugTrace.traceInference(
            config,
            "  first unsolved binder: {s}",
            .{label},
        );
    }
}

fn buildBindingSummary(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    mode: BindingSummaryMode,
) ![]const u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    var emitted: usize = 0;
    var remaining: usize = 0;
    for (current_bindings, 0..) |binding, idx| {
        const is_explicit = idx < explicit_bindings.len and
            explicit_bindings[idx] != null;
        const include = switch (mode) {
            .explicit => is_explicit,
            .inferred => !is_explicit and binding != null,
        };
        if (!include) continue;

        if (emitted == 3) {
            remaining += 1;
            continue;
        }
        if (emitted != 0) {
            try out.appendSlice(allocator, "; ");
        }
        try appendBindingEntry(
            &out,
            allocator,
            theorem,
            env,
            rule,
            idx,
            binding,
        );
        emitted += 1;
    }

    if (emitted == 0) {
        try out.appendSlice(allocator, "none");
    } else if (remaining != 0) {
        try out.writer(allocator).print(
            "; +{d} more",
            .{remaining},
        );
    }
    return try out.toOwnedSlice(allocator);
}

fn appendBindingEntry(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    idx: usize,
    binding: ?ExprId,
) !void {
    try out.appendSlice(allocator, binderLabel(rule, idx));
    try out.appendSlice(allocator, " = ");
    if (binding) |expr_id| {
        const text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            expr_id,
        );
        defer allocator.free(text);
        try appendInferenceTruncatedText(out, allocator, text, 48);
        return;
    }
    try out.appendSlice(allocator, "<unsolved>");
}

fn appendInferenceTruncatedText(
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

fn firstUnsolvedNamedBinder(
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) ?[]const u8 {
    for (bindings, 0..) |binding, idx| {
        if (binding != null) continue;
        if (idx < rule.arg_names.len) {
            if (rule.arg_names[idx]) |name| return name;
        }
        return null;
    }
    return null;
}

fn firstUnsolvedBinderLabel(
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) ?[]const u8 {
    return firstUnsolvedNamedBinder(rule, bindings);
}

fn binderLabel(rule: *const RuleDecl, idx: usize) []const u8 {
    if (idx < rule.arg_names.len) {
        if (rule.arg_names[idx]) |name| return name;
    }
    return "_";
}

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
                DebugTrace.traceViews(
                    self.debug,
                    "applyViewBindings failed for rule {s}: {s}",
                    .{ rule.name, @errorName(err) },
                );
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

        try traceInferenceAttempt(
            self.debug,
            allocator,
            theorem,
            env,
            rule,
            .structural_solver,
            partial_bindings,
            if (seeded_bindings_storage) |seeded|
                seeded
            else
                partial_bindings,
        );

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
            try traceInferenceFailure(
                self.debug,
                allocator,
                theorem,
                env,
                rule,
                .structural_solver,
                err,
                partial_bindings,
                if (seeded_bindings_storage) |seeded|
                    seeded
                else
                    partial_bindings,
            );
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
                const solver_bindings = if (seeded_bindings_storage) |seeded|
                    seeded
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
                CompilerDiag.setProof(
                    self,
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
            rule,
            if (maybe_view) |*view| view else null,
            self.debug,
        );
        defer solver.deinit();
        const solver_bindings = if (seeded_bindings_storage) |seeded|
            seeded
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
            CompilerDiag.setProof(
                self,
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

        if (solver.hadAmbiguityWarning()) {
            var diag = CompilerDiag.withPhase(.{
                .severity = .warning,
                .kind = .inference_failed,
                .err = error.AmbiguousAcuiMatch,
                .source = .proof,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
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
    );
    switch (strict_result) {
        .complete => |bindings| return bindings,
        .failed => |strict_failure| {
            defer allocator.free(strict_failure.partial_bindings);
            if (self.last_diagnostic != null) return strict_failure.err;
            if (maybe_view == null) {
                try traceInferenceFailure(
                    self.debug,
                    allocator,
                    theorem,
                    env,
                    rule,
                    .strict_replay,
                    strict_failure.err,
                    partial_bindings,
                    strict_failure.partial_bindings,
                );
                try traceInferenceAttempt(
                    self.debug,
                    allocator,
                    theorem,
                    env,
                    rule,
                    .transparent_fallback,
                    partial_bindings,
                    strict_failure.partial_bindings,
                );
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
                        try traceInferenceFailure(
                            self.debug,
                            allocator,
                            theorem,
                            env,
                            rule,
                            .transparent_fallback,
                            transparent_err,
                            partial_bindings,
                            strict_failure.partial_bindings,
                        );
                        CompilerDiag.setProof(
                            self,
                            try buildInferenceFailureDiagnostic(
                                allocator,
                                env,
                                theorem,
                                assertion,
                                rule,
                                line,
                                .transparent_fallback,
                                transparent_err,
                                partial_bindings,
                                strict_failure.partial_bindings,
                            ),
                        );
                        return transparent_err;
                    }
                    break :blk null;
                };
                if (transparent) |bindings| {
                    return bindings;
                }
                CompilerDiag.setProof(
                    self,
                    try buildInferenceFailureDiagnostic(
                        allocator,
                        env,
                        theorem,
                        assertion,
                        rule,
                        line,
                        .transparent_fallback,
                        strict_failure.err,
                        partial_bindings,
                        strict_failure.partial_bindings,
                    ),
                );
                return strict_failure.err;
            }
            CompilerDiag.setProof(
                self,
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
) !StrictReplayResult {
    const unify = try Emit.buildRuleUnifyStream(allocator, rule);

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
            CompilerDiag.maybeSetProof(
                self,
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
                .rule_name = line.rule_name,
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
            CompilerDiag.maybeSetProof(self, diag);
            return .{ .failed = .{
                .err = err,
                .partial_bindings = snapshot,
            } };
        };
        bindings[idx] = binding;
    }
    if (try firstDepViolation(
        env,
        theorem,
        assertion.args,
        rule.args,
        rule.arg_names,
        bindings,
    )) |detail| {
        CompilerDiag.maybeSetProof(self, CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.ruleApplicationSpan(),
            .detail = .{ .dep_violation = detail },
        }, .theorem_application));
        return .{ .failed = .{
            .err = error.DepViolation,
            .partial_bindings = snapshot,
        } };
    }
    allocator.free(snapshot);
    return .{ .complete = bindings };
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
    );
    return switch (result) {
        .complete => |bindings| bindings,
        .failed => |failure| {
            defer allocator.free(failure.partial_bindings);
            return failure.err;
        },
    };
}

pub fn validateResolvedBindingsWithDebug(
    self: anytype,
    debug: DebugConfig,
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
        rule.arg_names,
        bindings,
    )) |detail| {
        DebugTrace.traceDependency(
            debug,
            "rule {s} on line {s} violates dependency constraints",
            .{ rule.name, line.label },
        );
        if (detail.first_arg_name) |first_name| {
            DebugTrace.traceDependency(
                debug,
                "  conflicting binders: {s} and {s}",
                .{
                    first_name,
                    detail.second_arg_name orelse "_",
                },
            );
        }
        DebugTrace.traceDependency(
            debug,
            "  deps: first=0x{x} second=0x{x}",
            .{ detail.first_deps, detail.second_deps },
        );
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.ruleApplicationSpan(),
            .detail = .{ .dep_violation = detail },
        }, .theorem_application));
        return error.DepViolation;
    }
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
    return validateResolvedBindingsWithDebug(
        self,
        .none,
        env,
        theorem,
        assertion,
        line,
        rule,
        bindings,
    );
}

pub fn bindingsRespectRuleDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    bindings: []const ExprId,
) !bool {
    return (try firstDepViolation(
        env,
        theorem,
        theorem_args,
        rule_args,
        rule_arg_names,
        bindings,
    )) == null;
}

pub fn firstDepViolation(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    bindings: []const ExprId,
) !?DepViolationDetail {
    var bound_deps: [56]u55 = undefined;
    var bound_arg_indices: [56]usize = undefined;
    var bound_infos: [56]ExprInfo = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_arg_indices: [56]usize = undefined;
    var prev_infos: [56]ExprInfo = undefined;
    var prev_len: usize = 0;

    for (bindings, rule_args, 0..) |binding, expected, idx| {
        const info = try exprInfo(env, theorem, theorem_args, binding);
        if (expected.bound) {
            for (0..prev_len) |k| {
                if (prev_deps[k] & info.deps != 0) {
                    return depViolationDetail(
                        rule_arg_names,
                        prev_arg_indices[k],
                        prev_infos[k],
                        idx,
                        info,
                    );
                }
            }
            bound_deps[bound_len] = info.deps;
            bound_arg_indices[bound_len] = idx;
            bound_infos[bound_len] = info;
            bound_len += 1;
        } else {
            for (0..bound_len) |k| {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0)
                    continue;
                if (bound_deps[k] & info.deps != 0) {
                    return depViolationDetail(
                        rule_arg_names,
                        bound_arg_indices[k],
                        bound_infos[k],
                        idx,
                        info,
                    );
                }
            }
        }
        prev_deps[prev_len] = info.deps;
        prev_arg_indices[prev_len] = idx;
        prev_infos[prev_len] = info;
        prev_len += 1;
    }
    return null;
}

fn depViolationDetail(
    rule_arg_names: []const ?[]const u8,
    first_idx: usize,
    first_info: ExprInfo,
    second_idx: usize,
    second_info: ExprInfo,
) DepViolationDetail {
    return .{
        .first_arg_idx = first_idx,
        .second_arg_idx = second_idx,
        .first_arg_name = if (first_idx < rule_arg_names.len)
            rule_arg_names[first_idx]
        else
            null,
        .second_arg_name = if (second_idx < rule_arg_names.len)
            rule_arg_names[second_idx]
        else
            null,
        .first_deps = first_info.deps,
        .second_deps = second_info.deps,
        .first_bound = first_info.bound,
        .second_bound = second_info.bound,
    };
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
    if (try theorem.leafInfoWithArgs(theorem_args, expr_id)) |leaf| {
        return .{
            .sort_name = leaf.sort_name,
            .bound = leaf.bound,
            .deps = leaf.deps,
        };
    }

    const app = switch (theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => unreachable,
    };
    if (app.term_id >= env.terms.items.len) return error.UnknownTerm;

    var deps: u55 = 0;
    for (app.args) |arg_id| {
        deps |= (try exprInfo(env, theorem, theorem_args, arg_id)).deps;
    }
    return .{
        .sort_name = env.terms.items[app.term_id].ret_sort_name,
        .bound = false,
        .deps = deps,
    };
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
