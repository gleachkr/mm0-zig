const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const Expr = @import("../../trusted/expressions.zig").Expr;
const ProofScript = @import("../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const RuleCatalog = @import("./rule_catalog.zig");
const CompilerViews = @import("./views.zig");
const FreshSelect = @import("./fresh_select.zig");
const CompilerDiag = @import("./diag.zig");
const CompilerContext = @import("./context.zig").CompilerContext;
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("./inference.zig");
const Check = @import("./check.zig");
const CompilerVars = @import("./vars.zig");

pub const NameExprMap = Check.NameExprMap;
pub const LabelIndexMap = Check.LabelIndexMap;
pub const FreshDecl = FreshSelect.FreshDecl;
pub const FreshenDecl = FreshSelect.FreshenDecl;
pub const ViewDecl = CompilerViews.ViewDecl;
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const Goal = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
    implicit_whole_conclusion: ?ExprId,

    fn lineAssertion(self: Goal) Check.LineAssertion {
        return switch (self) {
            .concrete => |expr| .{ .concrete = expr },
            .holey => |expr| .{ .holey = expr },
            .implicit_whole_conclusion => .implicit_whole_conclusion,
        };
    }

    fn expectedHint(self: Goal) ?ExprId {
        return switch (self) {
            .implicit_whole_conclusion => |hint| hint,
            else => null,
        };
    }
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    labels: *const LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
    available_rule_count: usize,
};

pub const AttemptOptions = struct {
    commit: bool = false,
    line_label: []const u8 = "<search>",
    assertion_span: Span = .{ .start = 0, .end = 0 },
    diagnostic_span: ?Span = null,
};

pub const AttemptResult = struct {
    allocator: std.mem.Allocator,
    committed: bool,
    line_idx: usize,
    checked_start: usize,
    checked_lines: []const CheckedLine,
    theorem: ?TheoremContext,
    theorem_vars: ?NameExprMap,

    pub fn deinit(self: *AttemptResult) void {
        if (!self.committed) {
            CheckedIr.deinitLines(self.allocator, self.checked_lines);
        }
        self.allocator.free(self.checked_lines);
        if (self.theorem_vars) |*vars| vars.deinit();
        if (self.theorem) |*theorem| theorem.deinit();
        self.* = undefined;
    }
};

pub const MatchKind = Check.ConclusionMatchKind;
pub const UnresolvedHypothesis = Check.UnresolvedHypothesis;

pub const ApplyCandidate = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    rule_name: []const u8,
    declaration_order: usize,
    match_kind: MatchKind,
    theorem: TheoremContext,
    bindings: []const ?ExprId,
    conclusion: ExprId,
    unresolved_hyps: []const UnresolvedHypothesis,

    pub fn deinit(self: *ApplyCandidate) void {
        self.allocator.free(self.bindings);
        self.allocator.free(self.unresolved_hyps);
        self.theorem.deinit();
        self.* = undefined;
    }
};

pub const ApplyResults = struct {
    allocator: std.mem.Allocator,
    candidates: []ApplyCandidate,

    pub fn deinit(self: *ApplyResults) void {
        for (self.candidates) |*candidate| {
            candidate.deinit();
        }
        self.allocator.free(self.candidates);
        self.* = undefined;
    }
};

pub const ApplyOptions = struct {
    max_results: ?usize = null,
};

pub const ExactCandidate = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    rule_name: []const u8,
    declaration_order: usize,
    match_kind: MatchKind,
    reference_match_kind: MatchKind,
    refs: []const ProofScript.Ref,
    application: RuleApplication,
    reference_rank: usize,

    pub fn deinit(self: *ExactCandidate) void {
        self.allocator.free(self.refs);
        self.* = undefined;
    }
};

pub const ExactResults = struct {
    allocator: std.mem.Allocator,
    candidates: []ExactCandidate,

    pub fn deinit(self: *ExactResults) void {
        for (self.candidates) |*candidate| {
            candidate.deinit();
        }
        self.allocator.free(self.candidates);
        self.* = undefined;
    }
};

pub const ExactOptions = struct {
    max_results: ?usize = null,
};

const Metadata = @import("./metadata.zig");
const Holes = @import("./holes.zig");
const DiagnosticSink = @import("./diagnostic_sink.zig").DiagnosticSink;
const ProofParser = ProofScript.Parser;

pub fn tryCandidate(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    options: AttemptOptions,
) !AttemptResult {
    const allocator = context.allocator;
    const saved_diag = compiler.getDiagnostic();

    var attempt_theorem = try theorem.clone();
    errdefer attempt_theorem.deinit();
    var attempt_theorem_vars = try Check.cloneNameExprMap(
        allocator,
        theorem_vars,
    );
    errdefer attempt_theorem_vars.deinit();

    var scratch_checked = std.ArrayListUnmanaged(CheckedLine){};
    defer scratch_checked.deinit(allocator);
    try scratch_checked.appendSlice(allocator, context.checked.items);
    const checked_mark = scratch_checked.items.len;

    var attempt_context = Check.RuleApplyContext{
        .allocator = allocator,
        .parser = context.parser,
        .env = context.env,
        .registry = context.registry,
        .rule_catalog = context.rule_catalog,
        .fresh_bindings = context.fresh_bindings,
        .freshen_bindings = context.freshen_bindings,
        .views = context.views,
        .sort_vars = context.sort_vars,
        .assertion = context.assertion,
        .labels = context.labels,
        .checked = &scratch_checked,
        .diag_scratch = context.diag_scratch,
        .rule_unify_cache = context.rule_unify_cache,
    };
    const line = Check.ApplicationLine{
        .label = options.line_label,
        .application = application,
        .assertion_span = options.assertion_span,
    };
    const diag_context = Check.ApplicationDiagnosticContext{
        .theorem_name = context.assertion.name,
        .line_label = options.line_label,
        .span = options.diagnostic_span,
    };
    const diag_mark = context.diag_scratch.mark();

    const attempt = Check.applyRuleApplication(
        compiler,
        &attempt_context,
        application,
        goal.lineAssertion(),
        goal.expectedHint(),
        diag_context,
        line,
        &attempt_theorem,
        &attempt_theorem_vars,
    ) catch |err| {
        CheckedIr.rollbackToMark(allocator, &scratch_checked, checked_mark);
        context.diag_scratch.discard(diag_mark);
        compiler.restoreDiagnostic(saved_diag);
        return err;
    };
    context.diag_scratch.discard(diag_mark);
    compiler.restoreDiagnostic(saved_diag);

    errdefer CheckedIr.rollbackToMark(
        allocator,
        &scratch_checked,
        checked_mark,
    );
    const new_lines = try allocator.dupe(
        CheckedLine,
        scratch_checked.items[checked_mark..],
    );
    scratch_checked.shrinkRetainingCapacity(checked_mark);

    if (options.commit) {
        errdefer {
            CheckedIr.deinitLines(allocator, new_lines);
            allocator.free(new_lines);
        }
        try context.checked.appendSlice(allocator, new_lines);
        var old_theorem = theorem.*;
        theorem.* = attempt_theorem;
        old_theorem.deinit();
        theorem_vars.deinit();
        theorem_vars.* = attempt_theorem_vars;
        return .{
            .allocator = allocator,
            .committed = true,
            .line_idx = attempt.line_idx,
            .checked_start = checked_mark,
            .checked_lines = new_lines,
            .theorem = null,
            .theorem_vars = null,
        };
    }

    return .{
        .allocator = allocator,
        .committed = false,
        .line_idx = attempt.line_idx,
        .checked_start = checked_mark,
        .checked_lines = new_lines,
        .theorem = attempt_theorem,
        .theorem_vars = attempt_theorem_vars,
    };
}

const RefPoolEntry = struct {
    ref: ProofScript.Ref,
    order: usize,
};

pub fn exact(
    compiler: *CompilerContext,
    context: *const Context,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: ExactOptions,
) !ExactResults {
    const allocator = context.allocator;
    var apply_results = try apply(
        compiler,
        context,
        goal,
        theorem,
        theorem_vars,
        .{},
    );
    defer apply_results.deinit();

    const pool = try buildReferencePool(allocator, context, theorem);
    defer allocator.free(pool);

    var candidates = std.ArrayListUnmanaged(ExactCandidate){};
    errdefer {
        for (candidates.items) |*candidate| {
            candidate.deinit();
        }
        candidates.deinit(allocator);
    }

    for (apply_results.candidates) |apply_candidate| {
        const hyp_count = apply_candidate.unresolved_hyps.len;
        if (hyp_count > 0 and pool.len == 0) continue;
        const indices = try allocator.alloc(usize, hyp_count);
        defer allocator.free(indices);
        @memset(indices, 0);

        var done = false;
        while (!done) {
            const refs = try refsFromIndices(allocator, pool, indices);
            defer allocator.free(refs);
            const reference_rank = rankReferenceIndices(pool.len, indices);
            const application = RuleApplication{
                .rule_name = apply_candidate.rule_name,
                .rule_span = .{ .start = 0, .end = 0 },
                .refs_span = if (refs.len == 0) null else .{ .start = 0, .end = 0 },
                .refs = refs,
                .span = .{ .start = 0, .end = 0 },
            };

            var attempt_theorem = try theorem.clone();
            defer attempt_theorem.deinit();
            var attempt_vars = try Check.cloneNameExprMap(
                allocator,
                theorem_vars,
            );
            defer attempt_vars.deinit();
            var attempt = tryCandidate(
                compiler,
                context,
                application,
                goal,
                &attempt_theorem,
                &attempt_vars,
                .{},
            ) catch |err| {
                if (err == error.OutOfMemory) return err;
                done = !advanceReferenceIndices(indices, pool.len);
                continue;
            };
            defer attempt.deinit();
            const reference_match_kind = classifyReferenceMatches(
                allocator,
                context,
                apply_candidate.rule_id,
                &attempt,
                refs,
            ) catch |err| switch (err) {
                error.OutOfMemory => return err,
                else => .normalized,
            };

            const owned_refs = try allocator.dupe(ProofScript.Ref, refs);
            errdefer allocator.free(owned_refs);
            const owned_application = RuleApplication{
                .rule_name = apply_candidate.rule_name,
                .rule_span = .{ .start = 0, .end = 0 },
                .refs_span = if (owned_refs.len == 0) null else .{ .start = 0, .end = 0 },
                .refs = owned_refs,
                .span = .{ .start = 0, .end = 0 },
            };
            try candidates.append(allocator, .{
                .allocator = allocator,
                .rule_id = apply_candidate.rule_id,
                .rule_name = apply_candidate.rule_name,
                .declaration_order = apply_candidate.declaration_order,
                .match_kind = apply_candidate.match_kind,
                .reference_match_kind = reference_match_kind,
                .refs = owned_refs,
                .application = owned_application,
                .reference_rank = reference_rank,
            });
            done = !advanceReferenceIndices(indices, pool.len);
        }
    }

    std.mem.sort(
        ExactCandidate,
        candidates.items,
        {},
        exactCandidateLessThan,
    );
    if (options.max_results) |max| {
        if (max < candidates.items.len) {
            for (candidates.items[max..]) |*candidate| {
                candidate.deinit();
            }
            candidates.shrinkRetainingCapacity(max);
        }
    }
    return .{
        .allocator = allocator,
        .candidates = try candidates.toOwnedSlice(allocator),
    };
}

pub fn apply(
    compiler: *CompilerContext,
    context: *const Context,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: ApplyOptions,
) !ApplyResults {
    const allocator = context.allocator;
    var candidates = std.ArrayListUnmanaged(ApplyCandidate){};
    errdefer {
        for (candidates.items) |*candidate| {
            candidate.deinit();
        }
        candidates.deinit(allocator);
    }

    const rule_limit = @min(
        context.available_rule_count,
        context.env.rules.items.len,
    );
    const saved_diag = compiler.getDiagnostic();
    for (context.env.rules.items[0..rule_limit], 0..) |rule, rule_idx| {
        var attempt_theorem = try theorem.clone();
        var attempt_theorem_owned = true;
        errdefer if (attempt_theorem_owned) attempt_theorem.deinit();
        var attempt_vars = try Check.cloneNameExprMap(
            allocator,
            theorem_vars,
        );
        var attempt_vars_owned = true;
        errdefer if (attempt_vars_owned) attempt_vars.deinit();
        const diag_mark = context.diag_scratch.mark();
        const application = RuleApplication{
            .rule_name = rule.name,
            .rule_span = .{ .start = 0, .end = 0 },
            .span = .{ .start = 0, .end = 0 },
        };
        const line = Check.ApplicationLine{
            .label = "<search>",
            .application = application,
            .assertion_span = .{ .start = 0, .end = 0 },
        };
        const diag_context = Check.ApplicationDiagnosticContext{
            .theorem_name = context.assertion.name,
            .line_label = "<search>",
            .span = null,
        };

        const apply_context = Check.RuleApplyContext{
            .allocator = allocator,
            .parser = context.parser,
            .env = context.env,
            .registry = context.registry,
            .rule_catalog = context.rule_catalog,
            .fresh_bindings = context.fresh_bindings,
            .freshen_bindings = context.freshen_bindings,
            .views = context.views,
            .sort_vars = context.sort_vars,
            .assertion = context.assertion,
            .labels = context.labels,
            .checked = context.checked,
            .diag_scratch = context.diag_scratch,
            .rule_unify_cache = context.rule_unify_cache,
        };
        var probe = Check.probeRuleConclusion(
            compiler,
            &apply_context,
            application,
            goal.lineAssertion(),
            goal.expectedHint(),
            diag_context,
            line,
            @intCast(rule_idx),
            &attempt_theorem,
            &attempt_vars,
        ) catch |err| {
            if (err == error.OutOfMemory) return err;
            context.diag_scratch.discard(diag_mark);
            compiler.restoreDiagnostic(saved_diag);
            attempt_vars.deinit();
            attempt_vars_owned = false;
            attempt_theorem.deinit();
            attempt_theorem_owned = false;
            continue;
        };
        errdefer probe.deinit();
        context.diag_scratch.discard(diag_mark);
        compiler.restoreDiagnostic(saved_diag);
        attempt_vars.deinit();
        attempt_vars_owned = false;

        try candidates.append(allocator, .{
            .allocator = allocator,
            .rule_id = probe.rule_id,
            .rule_name = probe.rule_name,
            .declaration_order = rule_idx,
            .match_kind = probe.match_kind,
            .theorem = attempt_theorem,
            .bindings = probe.bindings,
            .conclusion = probe.displayed_conclusion,
            .unresolved_hyps = probe.unresolved_hyps,
        });
        attempt_theorem_owned = false;
        probe.bindings = &.{};
        probe.unresolved_hyps = &.{};
        probe.deinit();
    }
    compiler.restoreDiagnostic(saved_diag);
    std.mem.sort(
        ApplyCandidate,
        candidates.items,
        {},
        applyCandidateLessThan,
    );
    if (options.max_results) |max| {
        if (max < candidates.items.len) {
            for (candidates.items[max..]) |*candidate| {
                candidate.deinit();
            }
            candidates.shrinkRetainingCapacity(max);
        }
    }
    return .{
        .allocator = allocator,
        .candidates = try candidates.toOwnedSlice(allocator),
    };
}

fn classifyReferenceMatches(
    allocator: std.mem.Allocator,
    context: *const Context,
    rule_id: u32,
    attempt: *AttemptResult,
    refs: []const ProofScript.Ref,
) !MatchKind {
    if (refs.len == 0) return .exact;
    const attempt_theorem = if (attempt.theorem) |*value|
        value
    else
        return error.MissingSearchAttemptTheorem;
    const rule_line = try applicationRuleLineFromAttempt(
        context,
        attempt,
        rule_id,
        refs.len,
    );
    const rule = if (rule_line.rule_id < context.env.rules.items.len)
        &context.env.rules.items[rule_line.rule_id]
    else
        return error.UnknownRule;

    var result: MatchKind = .exact;
    for (refs, 0..) |ref, idx| {
        if (idx >= rule.hyps.len) return error.MissingSearchRuleLine;
        const actual = try sourceRefExpr(context, attempt_theorem, ref);
        const expected = try attempt_theorem.instantiateTemplate(
            rule.hyps[idx],
            rule_line.bindings,
        );
        result = maxMatchKind(result, try classifyReferenceMatch(
            allocator,
            context,
            attempt_theorem,
            actual,
            expected,
        ));
    }
    return result;
}

fn applicationRuleLineFromAttempt(
    context: *const Context,
    attempt: *const AttemptResult,
    initial_rule_id: u32,
    ref_count: usize,
) !CheckedLine.RuleLine {
    var line_idx = attempt.line_idx;
    var steps: usize = 0;
    while (steps <= attempt.checked_lines.len) : (steps += 1) {
        const line = attemptCheckedLine(attempt, line_idx) orelse {
            return error.MissingSearchRuleLine;
        };
        switch (line.data) {
            .rule => |rule_line| {
                if (rule_line.refs.len == ref_count and
                    isRuleInFallbackChain(
                        context,
                        initial_rule_id,
                        rule_line.rule_id,
                    ))
                {
                    return rule_line;
                }
                line_idx = sourceLineForRule(rule_line) orelse {
                    return error.MissingSearchRuleLine;
                };
            },
            .transport => |transport| {
                line_idx = switch (transport.source) {
                    .line => |source| source,
                    .hyp => return error.MissingSearchRuleLine,
                };
            },
        }
    }
    return error.MissingSearchRuleLine;
}

fn attemptCheckedLine(
    attempt: *const AttemptResult,
    absolute_idx: usize,
) ?*const CheckedLine {
    if (absolute_idx < attempt.checked_start) return null;
    const relative_idx = absolute_idx - attempt.checked_start;
    if (relative_idx >= attempt.checked_lines.len) return null;
    return &attempt.checked_lines[relative_idx];
}

fn isRuleInFallbackChain(
    context: *const Context,
    initial_rule_id: u32,
    actual_rule_id: u32,
) bool {
    var current = initial_rule_id;
    var steps: usize = 0;
    while (steps <= context.env.rules.items.len) : (steps += 1) {
        if (current == actual_rule_id) return true;
        current = context.registry.getFallbackRule(current) orelse return false;
    }
    return false;
}

fn sourceLineForRule(rule_line: CheckedLine.RuleLine) ?usize {
    if (rule_line.refs.len < 2) return null;
    return switch (rule_line.refs[1]) {
        .line => |line| line,
        .hyp => null,
    };
}

fn sourceRefExpr(
    context: *const Context,
    theorem: *const TheoremContext,
    ref: ProofScript.Ref,
) !ExprId {
    return switch (ref) {
        .hyp => |hyp| blk: {
            if (hyp.index == 0 or hyp.index > theorem.theorem_hyps.items.len) {
                return error.UnknownHypothesisRef;
            }
            break :blk theorem.theorem_hyps.items[hyp.index - 1];
        },
        .line => |line| blk: {
            const line_idx = context.labels.get(line.label) orelse {
                return error.UnknownLabel;
            };
            if (line_idx >= context.checked.items.len) {
                return error.UnknownLabel;
            }
            break :blk context.checked.items[line_idx].expr;
        },
        .application => error.UnexpectedInlineRef,
    };
}

fn classifyReferenceMatch(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    actual: ExprId,
    expected: ExprId,
) !MatchKind {
    if (actual == expected) return .exact;
    if (try Inference.canConvertTransparent(
        allocator,
        theorem,
        context.env,
        expected,
        actual,
    )) {
        return .transparent;
    }
    return .normalized;
}

fn maxMatchKind(lhs: MatchKind, rhs: MatchKind) MatchKind {
    return if (matchKindRank(lhs) >= matchKindRank(rhs)) lhs else rhs;
}

fn buildReferencePool(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *const TheoremContext,
) ![]RefPoolEntry {
    var pool = std.ArrayListUnmanaged(RefPoolEntry){};
    errdefer pool.deinit(allocator);

    for (theorem.theorem_hyps.items, 0..) |_, idx| {
        try pool.append(allocator, .{
            .ref = .{ .hyp = .{
                .index = idx + 1,
                .span = .{ .start = 0, .end = 0 },
            } },
            .order = idx,
        });
    }

    var line_refs = std.ArrayListUnmanaged(RefPoolEntry){};
    defer line_refs.deinit(allocator);
    var labels = context.labels.iterator();
    while (labels.next()) |entry| {
        const line_idx = entry.value_ptr.*;
        if (line_idx >= context.checked.items.len) continue;
        try line_refs.append(allocator, .{
            .ref = .{ .line = .{
                .label = entry.key_ptr.*,
                .span = .{ .start = 0, .end = 0 },
            } },
            .order = line_idx,
        });
    }
    std.mem.sort(RefPoolEntry, line_refs.items, {}, refPoolEntryLessThan);
    try pool.appendSlice(allocator, line_refs.items);
    return try pool.toOwnedSlice(allocator);
}

fn refPoolEntryLessThan(_: void, lhs: RefPoolEntry, rhs: RefPoolEntry) bool {
    if (lhs.order != rhs.order) return lhs.order < rhs.order;
    return refNameLessThan(lhs.ref, rhs.ref);
}

fn refNameLessThan(lhs: ProofScript.Ref, rhs: ProofScript.Ref) bool {
    return switch (lhs) {
        .hyp => |lhs_hyp| switch (rhs) {
            .hyp => |rhs_hyp| lhs_hyp.index < rhs_hyp.index,
            .line, .application => true,
        },
        .line => |lhs_line| switch (rhs) {
            .hyp => false,
            .line => |rhs_line| std.mem.lessThan(
                u8,
                lhs_line.label,
                rhs_line.label,
            ),
            .application => true,
        },
        .application => false,
    };
}

fn refsFromIndices(
    allocator: std.mem.Allocator,
    pool: []const RefPoolEntry,
    indices: []const usize,
) ![]const ProofScript.Ref {
    const refs = try allocator.alloc(ProofScript.Ref, indices.len);
    for (indices, 0..) |pool_idx, idx| {
        refs[idx] = pool[pool_idx].ref;
    }
    return refs;
}

fn advanceReferenceIndices(indices: []usize, base: usize) bool {
    if (indices.len == 0) return false;
    var idx = indices.len;
    while (idx > 0) {
        idx -= 1;
        indices[idx] += 1;
        if (indices[idx] < base) return true;
        indices[idx] = 0;
    }
    return false;
}

fn rankReferenceIndices(base: usize, indices: []const usize) usize {
    if (base == 0) return 0;
    var rank: usize = 0;
    for (indices) |idx| {
        rank = std.math.mul(usize, rank, base) catch
            std.math.maxInt(usize);
        rank = std.math.add(usize, rank, idx) catch
            std.math.maxInt(usize);
    }
    return rank;
}

fn exactCandidateLessThan(
    _: void,
    lhs: ExactCandidate,
    rhs: ExactCandidate,
) bool {
    const lhs_rank = exactCandidateMatchRank(lhs);
    const rhs_rank = exactCandidateMatchRank(rhs);
    if (lhs_rank != rhs_rank) return lhs_rank < rhs_rank;

    const lhs_conclusion_rank = matchKindRank(lhs.match_kind);
    const rhs_conclusion_rank = matchKindRank(rhs.match_kind);
    if (lhs_conclusion_rank != rhs_conclusion_rank) {
        return lhs_conclusion_rank < rhs_conclusion_rank;
    }

    const lhs_ref_rank = matchKindRank(lhs.reference_match_kind);
    const rhs_ref_rank = matchKindRank(rhs.reference_match_kind);
    if (lhs_ref_rank != rhs_ref_rank) return lhs_ref_rank < rhs_ref_rank;

    if (lhs.declaration_order != rhs.declaration_order) {
        return lhs.declaration_order < rhs.declaration_order;
    }
    if (lhs.refs.len != rhs.refs.len) return lhs.refs.len < rhs.refs.len;
    return lhs.reference_rank < rhs.reference_rank;
}

fn exactCandidateMatchRank(candidate: ExactCandidate) u8 {
    return @max(
        matchKindRank(candidate.match_kind),
        matchKindRank(candidate.reference_match_kind),
    );
}

fn applyCandidateLessThan(
    _: void,
    lhs: ApplyCandidate,
    rhs: ApplyCandidate,
) bool {
    const lhs_rank = matchKindRank(lhs.match_kind);
    const rhs_rank = matchKindRank(rhs.match_kind);
    if (lhs_rank != rhs_rank) return lhs_rank < rhs_rank;
    return lhs.declaration_order < rhs.declaration_order;
}

fn matchKindRank(kind: MatchKind) u8 {
    return switch (kind) {
        .exact => 0,
        .transparent => 1,
        .view => 2,
        .normalized => 3,
    };
}

const TestFixture = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    registry: RewriteRegistry,
    rule_catalog: RuleCatalog.Catalog,
    fresh_bindings: std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: std.AutoHashMap(u32, []const FreshenDecl),
    views: std.AutoHashMap(u32, ViewDecl),
    sort_vars: SortVarRegistry,
    assertion: @import("../parse_recovery.zig").AssertionStmt,
    available_rule_count: usize,
};

fn fixtureFor(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !TestFixture {
    return fixtureForSearchPoint(
        allocator,
        mm0_src,
        theorem_name,
        false,
    );
}

fn fixtureForFullEnv(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !TestFixture {
    return fixtureForSearchPoint(
        allocator,
        mm0_src,
        theorem_name,
        true,
    );
}

fn fixtureForSearchPoint(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
    include_trailing_rules: bool,
) !TestFixture {
    var fixture = TestFixture{
        .parser = MM0Parser.init(mm0_src, allocator),
        .env = GlobalEnv.init(allocator),
        .registry = RewriteRegistry.init(allocator),
        .rule_catalog = try RuleCatalog.build(allocator, mm0_src),
        .fresh_bindings = std.AutoHashMap(
            u32,
            []const FreshDecl,
        ).init(allocator),
        .freshen_bindings = std.AutoHashMap(
            u32,
            []const FreshenDecl,
        ).init(allocator),
        .views = std.AutoHashMap(u32, ViewDecl).init(allocator),
        .sort_vars = SortVarRegistry.init(allocator),
        .assertion = undefined,
        .available_rule_count = 0,
    };
    var found_theorem = false;

    while (try fixture.parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processSortMetadata(
                    &fixture.parser,
                    sort_stmt,
                    fixture.parser.last_annotations,
                    &fixture.sort_vars,
                );
            },
            .term => |term_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processTermMetadata(
                    &fixture.env,
                    &fixture.registry,
                    term_stmt,
                    fixture.parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                if (!found_theorem and
                    std.mem.eql(u8, assertion.name, theorem_name))
                {
                    fixture.assertion = assertion;
                    fixture.available_rule_count =
                        fixture.env.rules.items.len;
                    found_theorem = true;
                    if (!include_trailing_rules) return fixture;
                    continue;
                }
                try fixture.env.addStmt(stmt);
                try Metadata.processAssertionMetadata(
                    allocator,
                    &fixture.parser,
                    &fixture.env,
                    &fixture.registry,
                    &fixture.fresh_bindings,
                    &fixture.freshen_bindings,
                    &fixture.views,
                    assertion,
                    fixture.parser.last_annotations,
                );
            },
        }
    }
    if (found_theorem) return fixture;
    return error.MissingTheorem;
}

fn readProofCase(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

fn parseGoal(
    fixture: *TestFixture,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !Goal {
    const parsed = try Holes.parseAssertion(
        &fixture.parser,
        theorem,
        theorem_vars,
        &fixture.sort_vars,
        text,
    );
    return switch (parsed) {
        .concrete => |expr| .{ .concrete = expr },
        .holey => |expr| .{ .holey = expr },
    };
}

fn runSearchLine(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    fixture: *TestFixture,
    labels: *LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
    line: ProofScript.ProofLine,
    commit: bool,
) !AttemptResult {
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = labels,
        .checked = checked,
        .diag_scratch = diag_scratch,
        .rule_unify_cache = rule_unify_cache,
        .available_rule_count = fixture.available_rule_count,
    };
    return tryCandidate(
        compiler,
        &context,
        line.application,
        try parseGoal(fixture, theorem, theorem_vars, line.assertion.text),
        theorem,
        theorem_vars,
        .{
            .commit = commit,
            .line_label = line.label,
            .assertion_span = line.assertion.span,
            .diagnostic_span = line.span,
        },
    );
}

fn expectCaseLineSearch(
    stem: []const u8,
    theorem_name: []const u8,
    line_index: usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);

    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer {
        CheckedIr.deinitLines(allocator, checked.items);
        checked.deinit(allocator);
    }
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    for (block.lines[0..line_index]) |line| {
        var result = try runSearchLine(
            allocator,
            &compiler,
            &fixture,
            &labels,
            &checked,
            &theorem,
            &theorem_vars,
            &diag_scratch,
            &cache,
            line,
            true,
        );
        defer result.deinit();
        try labels.put(line.label, result.line_idx);
    }

    var result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[line_index],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try CheckedIr.validateLines(&result.theorem.?, result.checked_lines);
    try std.testing.expectEqual(line_index, checked.items.len);
}

fn expectApplyContains(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    rule_name: []const u8,
    match_kind: ?MatchKind,
    unresolved_count: ?usize,
    null_expected_count: ?usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, "");
    var compiler = CompilerContext.init(mm0_src, "", .none, &sink);
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        goal_text,
    );
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();

    for (results.candidates) |candidate| {
        if (!std.mem.eql(u8, candidate.rule_name, rule_name)) continue;
        if (match_kind) |expected_kind| {
            try std.testing.expectEqual(expected_kind, candidate.match_kind);
        }
        if (unresolved_count) |expected_count| {
            try std.testing.expectEqual(
                expected_count,
                candidate.unresolved_hyps.len,
            );
        }
        if (null_expected_count) |expected_count| {
            var actual_count: usize = 0;
            for (candidate.unresolved_hyps) |hyp| {
                if (hyp.expected == null) actual_count += 1;
            }
            try std.testing.expectEqual(expected_count, actual_count);
        }
        try std.testing.expectEqual(@as(usize, 0), checked.items.len);
        return;
    }
    return error.ExpectedApplyCandidate;
}

fn expectApplyNotContains(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    rule_name: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureForFullEnv(allocator, mm0_src, theorem_name);
    const excluded_rule_id = fixture.env.getRuleId(rule_name) orelse {
        return error.ExpectedExcludedRuleInEnv;
    };
    _ = excluded_rule_id;
    var sink = DiagnosticSink.init(mm0_src, "");
    var compiler = CompilerContext.init(mm0_src, "", .none, &sink);
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        goal_text,
    );
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();

    for (results.candidates) |candidate| {
        if (std.mem.eql(u8, candidate.rule_name, rule_name)) {
            return error.UnexpectedApplyCandidate;
        }
    }
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
}

fn expectRuleIsUnavailableAtSearchPoint(
    mm0_src: []const u8,
    theorem_name: []const u8,
    rule_name: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureForFullEnv(allocator, mm0_src, theorem_name);
    const rule_id = fixture.env.getRuleId(rule_name) orelse {
        return error.ExpectedExcludedRuleInEnv;
    };
    try std.testing.expect(
        @as(usize, @intCast(rule_id)) >= fixture.available_rule_count,
    );
}

fn expectApplyRuleOrder(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    max_results: ?usize,
    expected_names: []const []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, "");
    var compiler = CompilerContext.init(mm0_src, "", .none, &sink);
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        goal_text,
    );
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{ .max_results = max_results },
    );
    defer results.deinit();

    try std.testing.expectEqual(expected_names.len, results.candidates.len);
    for (expected_names, results.candidates) |expected, actual| {
        try std.testing.expectEqualStrings(expected, actual.rule_name);
    }
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
}

fn expectExactRuleOrderWithPrefix(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    prefix_count: usize,
    max_results: ?usize,
    expected_names: []const []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = if (proof_src.len == 0)
        null
    else
        try proof_parser.nextBlock();

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer {
        CheckedIr.deinitLines(allocator, checked.items);
        checked.deinit(allocator);
    }
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    if (prefix_count > 0) {
        const actual_block = block orelse return error.MissingBlock;
        for (actual_block.lines[0..prefix_count]) |line| {
            var result = try runSearchLine(
                allocator,
                &compiler,
                &fixture,
                &labels,
                &checked,
                &theorem,
                &theorem_vars,
                &diag_scratch,
                &cache,
                line,
                true,
            );
            defer result.deinit();
            try labels.put(line.label, result.line_idx);
        }
    }

    const checked_before = checked.items.len;

    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, goal_text);
    var results = try exact(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{ .max_results = max_results },
    );
    defer results.deinit();
    try std.testing.expectEqual(checked_before, checked.items.len);

    try std.testing.expectEqual(
        expected_names.len,
        results.candidates.len,
    );
    for (expected_names, 0..) |expected, idx| {
        try std.testing.expectEqualStrings(
            expected,
            results.candidates[idx].rule_name,
        );
        var attempt_theorem = try theorem.clone();
        defer attempt_theorem.deinit();
        var attempt_vars = try Check.cloneNameExprMap(
            allocator,
            &theorem_vars,
        );
        defer attempt_vars.deinit();
        var attempt = try tryCandidate(
            &compiler,
            &context,
            results.candidates[idx].application,
            goal,
            &attempt_theorem,
            &attempt_vars,
            .{},
        );
        defer attempt.deinit();
        try CheckedIr.validateLines(
            &attempt.theorem.?,
            attempt.checked_lines,
        );
    }
}

fn expectExactRuleOrder(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    expected_names: []const []const u8,
) !void {
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        "",
        theorem_name,
        goal_text,
        0,
        null,
        expected_names,
    );
}

fn expectInlineSearch(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    line_index: usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    var result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[line_index],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
}

test "search candidate matches exactly" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectInlineSearch(mm0_src, proof_src, "t", 0);
}

test "apply search finds exact zero-hypothesis candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "P", "p", .exact, 0, 0);
}

test "apply search returns unresolved hypotheses" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "P", "id", .exact, 1, 0);
}

test "apply search allows hyp-only unresolved binders" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ Q $;
    ;
    try expectApplyContains(mm0_src, "t", "Q", "mp", .exact, 2, 2);
}

test "apply search matches through transparent defs" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_def_transport",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    try expectApplyContains(
        mm0_src,
        "concl_transport",
        "id a",
        "ax_expanded",
        .transparent,
        0,
        0,
    );
}

test "apply search matches through normalization" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort mor;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term mor_eq (f g: mor): wff;
        \\infixl mor_eq: $~$ prec 15;
        \\term comp (f g: mor): mor;
        \\infixl comp: $o$ prec 35;
        \\term F: mor;
        \\term G: mor;
        \\term H: mor;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation mor mor_eq mor_refl mor_trans mor_sym _
        \\axiom mor_refl (f: mor): $ f ~ f $;
        \\axiom mor_trans (f g h: mor):
        \\  $ f ~ g $ > $ g ~ h $ > $ f ~ h $;
        \\axiom mor_sym (f g: mor): $ f ~ g $ > $ g ~ f $;
        \\--| @congr
        \\axiom mor_eq_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ (f1 ~ g1) <-> (f2 ~ g2) $;
        \\--| @congr
        \\axiom comp_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ f1 o g1 ~ f2 o g2 $;
        \\--| @rewrite
        \\axiom comp_assoc (f g h: mor): $ (f o g) o h ~ f o (g o h) $;
        \\axiom assoc_refl: $ ((F o G) o H) ~ ((F o G) o H) $;
        \\def assoc_norm: wff = $ F o (G o H) ~ F o (G o H) $;
        \\theorem normalize_goal: $ assoc_norm $;
    ;
    try expectApplyContains(
        mm0_src,
        "normalize_goal",
        "assoc_norm",
        "assoc_refl",
        .normalized,
        0,
        0,
    );
}

test "apply search matches through view and recover" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_recover_basic",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    try expectApplyContains(
        mm0_src,
        "inst_use",
        "A. x (P x) -> P u",
        "ax_inst",
        .view,
        0,
        0,
    );
}

test "apply search does not return future rules" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ Q $;
        \\axiom future_q: $ Q $;
    ;
    try expectRuleIsUnavailableAtSearchPoint(mm0_src, "t", "future_q");
    try expectApplyNotContains(mm0_src, "t", "Q", "future_q");
}

test "apply search max_results preserves ranked declaration order" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p1: $ P $;
        \\axiom p2: $ P $;
        \\axiom p3: $ P $;
        \\theorem t: $ P $;
    ;
    try expectApplyRuleOrder(
        mm0_src,
        "t",
        "P",
        2,
        &[_][]const u8{ "p1", "p2" },
    );
}

test "apply search rejects partial dependency violations" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term rel {x y: obj}: wff;
        \\axiom rel_bad {x y: obj} (p: wff): $ p $ > $ rel x y $;
        \\theorem t {z: obj}: $ rel z z $;
    ;
    try expectApplyNotContains(mm0_src, "t", "rel z z", "rel_bad");
}

test "apply search keeps view candidates with unresolved hypotheses" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term raw (a: wff): wff;
        \\def shown (a: wff): wff = $ raw a $;
        \\--| @view (a b: wff): $ b $ > $ shown a $
        \\axiom view_use (a b: wff): $ b $ > $ raw a $;
        \\theorem t: $ shown P $;
    ;
    try expectApplyContains(
        mm0_src,
        "t",
        "shown P",
        "view_use",
        .transparent,
        1,
        1,
    );
}

test "apply search rejects freshness-invalid candidates" {
    const mm0_src =
        \\--| @vars x
        \\provable sort wff;
        \\term top: wff;
        \\--| @fresh a
        \\--| @fresh b
        \\axiom use_fresh_pair {a b: wff}: $ top $;
        \\theorem t: $ top $;
    ;
    try expectApplyNotContains(mm0_src, "t", "top", "use_fresh_pair");
}

test "apply search does not use checked proof lines as refs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom p: $ P $;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer {
        CheckedIr.deinitLines(allocator, checked.items);
        checked.deinit(allocator);
    }
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    var line_result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[0],
        true,
    );
    defer line_result.deinit();
    try labels.put(block.lines[0].label, line_result.line_idx);

    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, "Q");
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();

    for (results.candidates) |candidate| {
        if (!std.mem.eql(u8, candidate.rule_name, "mp")) continue;
        var null_count: usize = 0;
        for (candidate.unresolved_hyps) |hyp| {
            if (hyp.expected == null) null_count += 1;
        }
        try std.testing.expectEqual(@as(usize, 2), null_count);
        try std.testing.expectEqual(@as(usize, 1), checked.items.len);
        return;
    }
    return error.ExpectedApplyCandidate;
}

test "exact search finds zero-hypothesis proof" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(mm0_src, "t", "P", &[_][]const u8{"p"});
}

fn expectFirstExactRefs(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    prefix_count: usize,
    expected_rule: []const u8,
    expected_refs: []const ProofScript.Ref,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = if (proof_src.len == 0)
        null
    else
        try proof_parser.nextBlock();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer {
        CheckedIr.deinitLines(allocator, checked.items);
        checked.deinit(allocator);
    }
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    if (prefix_count > 0) {
        const actual_block = block orelse return error.MissingBlock;
        for (actual_block.lines[0..prefix_count]) |line| {
            var result = try runSearchLine(
                allocator,
                &compiler,
                &fixture,
                &labels,
                &checked,
                &theorem,
                &theorem_vars,
                &diag_scratch,
                &cache,
                line,
                true,
            );
            defer result.deinit();
            try labels.put(line.label, result.line_idx);
        }
    }

    const checked_before = checked.items.len;

    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, goal_text);
    var results = try exact(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();
    try std.testing.expectEqual(checked_before, checked.items.len);
    try std.testing.expect(results.candidates.len > 0);
    const candidate = results.candidates[0];
    try std.testing.expectEqualStrings(expected_rule, candidate.rule_name);
    try std.testing.expectEqual(expected_refs.len, candidate.refs.len);
    for (expected_refs, candidate.refs) |expected, actual| {
        switch (expected) {
            .hyp => |expected_hyp| switch (actual) {
                .hyp => |actual_hyp| try std.testing.expectEqual(
                    expected_hyp.index,
                    actual_hyp.index,
                ),
                else => return error.ExpectedHypRef,
            },
            .line => |expected_line| switch (actual) {
                .line => |actual_line| try std.testing.expectEqualStrings(
                    expected_line.label,
                    actual_line.label,
                ),
                else => return error.ExpectedLineRef,
            },
            .application => return error.UnexpectedInlineRef,
        }
    }
}

test "exact search uses one theorem hypothesis" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "P",
        0,
        "id",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search uses one previous line" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom p: $ P $;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P -> Q $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "t",
        "Q",
        1,
        "mp",
        &[_]ProofScript.Ref{
            .{ .line = .{
                .label = "l1",
                .span = .{ .start = 0, .end = 0 },
            } },
            .{ .hyp = .{
                .index = 1,
                .span = .{ .start = 0, .end = 0 },
            } },
        },
    );
}

test "exact search uses multiple theorem hypotheses" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P $ > $ P -> Q $ > $ Q $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "Q",
        0,
        "mp",
        &[_]ProofScript.Ref{
            .{ .hyp = .{
                .index = 1,
                .span = .{ .start = 0, .end = 0 },
            } },
            .{ .hyp = .{
                .index = 2,
                .span = .{ .start = 0, .end = 0 },
            } },
        },
    );
}

test "exact search matches refs through transparent defs" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_def_transport",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    const proof_src =
        \\hyp_transport
        \\-------------
        \\l1: $ a -> a $ by ax_expanded (a := $ a $) []
    ;
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "hyp_transport",
        "a",
        1,
        "use_id",
        &[_]ProofScript.Ref{.{ .line = .{
            .label = "l1",
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search matches refs through normalization" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort mor;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term mor_eq (f g: mor): wff;
        \\infixl mor_eq: $~$ prec 15;
        \\term comp (f g: mor): mor;
        \\infixl comp: $o$ prec 35;
        \\term F: mor;
        \\term G: mor;
        \\term H: mor;
        \\term P: wff;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation mor mor_eq mor_refl mor_trans mor_sym _
        \\axiom mor_refl (f: mor): $ f ~ f $;
        \\axiom mor_trans (f g h: mor):
        \\  $ f ~ g $ > $ g ~ h $ > $ f ~ h $;
        \\axiom mor_sym (f g: mor): $ f ~ g $ > $ g ~ f $;
        \\--| @congr
        \\axiom mor_eq_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ (f1 ~ g1) <-> (f2 ~ g2) $;
        \\--| @congr
        \\axiom comp_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ f1 o g1 ~ f2 o g2 $;
        \\--| @rewrite
        \\axiom comp_assoc (f g h: mor): $ (f o g) o h ~ f o (g o h) $;
        \\axiom assoc_refl: $ ((F o G) o H) ~ ((F o G) o H) $;
        \\axiom use_norm:
        \\  $ F o (G o H) ~ F o (G o H) $ > $ P $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ ((F o G) o H) ~ ((F o G) o H) $ by assoc_refl
    ;
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "t",
        "P",
        1,
        "use_norm",
        &[_]ProofScript.Ref{.{ .line = .{
            .label = "l1",
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search handles successful fallback applications" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom have_p: $ P $;
        \\axiom fallback_use: $ P $ > $ Q $;
        \\--| @fallback fallback_use
        \\axiom bad_use: $ R $ > $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by have_p
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "Q",
        1,
        null,
        &[_][]const u8{ "fallback_use", "bad_use" },
    );
}

test "exact search returns no result when a hypothesis is unavailable" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(mm0_src, "t", "P", &[_][]const u8{});
}

test "exact search does not use later proof lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom p: $ P $;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P -> Q $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "Q",
        0,
        null,
        &[_][]const u8{},
    );
}

test "exact search orders refs deterministically" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "P",
        0,
        "id",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search orders successful rules deterministically" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p1: $ P $;
        \\axiom p2: $ P $;
        \\axiom p3: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(
        mm0_src,
        "t",
        "P",
        &[_][]const u8{ "p1", "p2", "p3" },
    );
}

test "exact search max_results preserves ranked declaration order" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p1: $ P $;
        \\axiom p2: $ P $;
        \\axiom p3: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        "",
        "t",
        "P",
        0,
        2,
        &[_][]const u8{ "p1", "p2" },
    );
}

test "exact search leaves checked prefix unchanged on failure" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom id (a: wff): $ a $ > $ a $;
        \\theorem t: $ P $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "Q",
        1,
        null,
        &[_][]const u8{},
    );
}

test "exact search prefers exact refs over transparent refs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\def id (p: wff): wff = $ p $;
        \\axiom use_p: $ P $ > $ P $;
        \\theorem t: $ id P $ > $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "P",
        0,
        "use_p",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 2,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "apply candidate can compile after user supplies refs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P $ > $ P -> Q $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by mp [#1, #2]
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, "Q");
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();
    var found_mp = false;
    for (results.candidates) |candidate| {
        found_mp = found_mp or std.mem.eql(u8, candidate.rule_name, "mp");
    }
    try std.testing.expect(found_mp);

    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[0],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try CheckedIr.validateLines(&result.theorem.?, result.checked_lines);
}

test "search candidate failure leaves no checked lines" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by p
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();
    const line = block.lines[0];
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        line.assertion.text,
    );
    const interner_count = theorem.interner.count();
    const vars_len = theorem.theorem_vars.items.len;
    const dummies_len = theorem.theorem_dummies.items.len;
    const placeholders_len = theorem.theorem_placeholders.items.len;
    const theorem_vars_count = theorem_vars.count();

    try std.testing.expectError(
        error.ConclusionMismatch,
        tryCandidate(
            &compiler,
            &context,
            line.application,
            goal,
            &theorem,
            &theorem_vars,
            .{
                .line_label = line.label,
                .assertion_span = line.assertion.span,
                .diagnostic_span = line.span,
            },
        ),
    );
    try std.testing.expectEqual(interner_count, theorem.interner.count());
    try std.testing.expectEqual(vars_len, theorem.theorem_vars.items.len);
    try std.testing.expectEqual(dummies_len, theorem.theorem_dummies.items.len);
    try std.testing.expectEqual(
        placeholders_len,
        theorem.theorem_placeholders.items.len,
    );
    try std.testing.expectEqual(theorem_vars_count, theorem_vars.count());
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
    try std.testing.expectEqual(@as(usize, 0), diag_scratch.entries.items.len);
    try std.testing.expect(compiler.getDiagnostic() == null);
}

test "search candidate uses transparent definition conversion" {
    try expectCaseLineSearch("pass_def_transport", "hyp_transport", 1);
}

test "search candidate uses normalization and transport" {
    try expectCaseLineSearch(
        "pass_normalize_def_transport_concl",
        "normalize_def_transport_concl",
        0,
    );
}

test "search candidate uses view inference" {
    try expectCaseLineSearch("pass_view_basic", "imp_refl", 3);
}

test "search candidate uses view recover" {
    try expectCaseLineSearch("pass_recover_basic", "inst_use", 0);
}

test "search candidate rejects boundness failures" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort nat;
        \\term all {x: nat} (p: wff x): wff;
        \\prefix all: $A.$ prec 41;
        \\axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
        \\theorem gen_bad (n: nat) (q: wff): $ q $ > $ q $;
    ;
    const proof_src =
        \\gen_bad
        \\-------
        \\l1: $ q $ by ax_gen (x := $ n $, p := $ q $) [#1]
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "gen_bad");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    const err = runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[0],
        false,
    );
    try std.testing.expectError(error.BoundnessMismatch, err);
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
    try std.testing.expectEqual(@as(usize, 0), diag_scratch.entries.items.len);
    try std.testing.expect(compiler.getDiagnostic() == null);
}
