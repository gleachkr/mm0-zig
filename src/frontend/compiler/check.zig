const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const ExprModule = @import("../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const ProofLine = @import("../proof_script.zig").ProofLine;
const Ref = @import("../proof_script.zig").Ref;
const RuleApplication = @import("../proof_script.zig").RuleApplication;
const Span = @import("../proof_script.zig").Span;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const TheoremBlock = @import("../proof_script.zig").TheoremBlock;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const CompilerViews = @import("./views.zig");
const CompilerFresh = @import("./fresh.zig");
const CompilerFreshen = @import("./freshen.zig");
const RuleCatalog = @import("./rule_catalog.zig");
const ViewDecl = CompilerViews.ViewDecl;
const FreshDecl = CompilerFresh.FreshDecl;
const FreshenDecl = CompilerFresh.FreshenDecl;
const CompilerDiag = @import("./diag.zig");
const Normalize = @import("./normalize.zig");
const ViewTrace = @import("../view_trace.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Inference = @import("./inference.zig");
const Matching = @import("./check/matching.zig");
const TheoremBoundary = @import("./theorem_boundary.zig");
const CompilerVars = @import("./vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;
const Holes = @import("./holes.zig");

const NameExprMap = std.StringHashMap(*const Expr);
const LabelIndexMap = std.StringHashMap(usize);

const SuccessfulLineAttempt = struct {
    line_idx: usize,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,
};

const LineAssertion = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
    implicit_whole_conclusion,

    fn fromParsed(parsed: Holes.ParsedAssertion) LineAssertion {
        return switch (parsed) {
            .concrete => |expr_id| .{ .concrete = expr_id },
            .holey => |expr| .{ .holey = expr },
        };
    }
};

const CandidateElaboration = struct {
    resolved_bindings: []const ExprId,
    raw_conclusion: ExprId,
    displayed_conclusion: ExprId,
};

const ApplicationDiagnosticContext = struct {
    theorem_name: []const u8,
    line_label: ?[]const u8,
    span: ?Span,

    fn fromLine(assertion: AssertionStmt, line: ProofLine) @This() {
        return .{
            .theorem_name = assertion.name,
            .line_label = line.label,
            .span = line.span,
        };
    }
};

const ApplicationLine = struct {
    label: []const u8,
    application: RuleApplication,
    assertion_span: Span,

    fn fromLine(line: ProofLine) @This() {
        return .{
            .label = line.label,
            .application = line.application,
            .assertion_span = line.assertion.span,
        };
    }

    fn forInline(parent: ApplicationLine, application: RuleApplication) @This() {
        return .{
            .label = parent.label,
            .application = application,
            .assertion_span = application.span,
        };
    }

    pub fn ruleApplicationSpan(self: @This()) Span {
        return self.application.ruleApplicationSpan();
    }

    pub fn refsOrRuleSpan(self: @This()) Span {
        return self.application.refsOrRuleSpan();
    }

    pub fn bindingSpan(self: @This(), binder_name: ?[]const u8) ?Span {
        return self.application.bindingSpan(binder_name);
    }
};

const RuleApplyContext = struct {
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
};

pub fn checkTheoremBlock(
    self: anytype,
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
    block: TheoremBlock,
    theorem: *TheoremContext,
    theorem_concl: ExprId,
) ![]const CheckedLine {
    var theorem_vars = try buildTheoremVarMap(allocator, assertion);
    defer theorem_vars.deinit();

    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();

    var checked = std.ArrayListUnmanaged(CheckedLine){};
    var rule_unify_cache = Inference.RuleUnifyCache.init(allocator);
    defer rule_unify_cache.deinit();
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var last_line: ?ExprId = null;
    var last_line_idx: ?usize = null;
    var last_label: ?[]const u8 = null;
    var last_span: ?Span = null;

    for (block.lines) |line| {
        if (labels.contains(line.label)) {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .duplicate_label,
                .err = error.DuplicateLabel,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .name = line.label,
                .span = line.label_span,
            }, .theorem_application));
            return error.DuplicateLabel;
        }

        const parsed_assertion = try parseProofLineAssertion(
            self,
            parser,
            theorem,
            &theorem_vars,
            sort_vars,
            assertion,
            line,
        );
        const line_assertion = LineAssertion.fromParsed(parsed_assertion);

        const apply_context: RuleApplyContext = .{
            .allocator = allocator,
            .parser = parser,
            .env = env,
            .registry = registry,
            .rule_catalog = rule_catalog,
            .fresh_bindings = fresh_bindings,
            .freshen_bindings = freshen_bindings,
            .views = views,
            .sort_vars = sort_vars,
            .assertion = assertion,
            .labels = &labels,
            .checked = &checked,
            .diag_scratch = &diag_scratch,
            .rule_unify_cache = &rule_unify_cache,
        };
        const attempt = try applyRuleApplication(
            self,
            &apply_context,
            line.application,
            line_assertion,
            null,
            ApplicationDiagnosticContext.fromLine(assertion, line),
            ApplicationLine.fromLine(line),
            theorem,
            &theorem_vars,
        );

        try labels.put(line.label, attempt.line_idx);
        last_line = checked.items[attempt.line_idx].expr;
        last_line_idx = attempt.line_idx;
        last_label = line.label;
        last_span = line.span;
    }

    const final_line = last_line orelse {
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .empty_proof_block,
            .err = error.EmptyProofBlock,
            .theorem_name = assertion.name,
            .block_name = block.name,
            .span = block.name_span,
        }, .final_reconciliation));
        return error.EmptyProofBlock;
    };
    if (final_line != theorem_concl) {
        if (last_line_idx) |line_idx| {
            const final_mark = diag_scratch.mark();
            const checked_mark = checked.items.len;
            var final_report: TheoremBoundary.ReconciliationReport = .{};
            if ((TheoremBoundary.tryReconcileFinalConclusion(
                allocator,
                theorem,
                registry,
                env,
                &checked,
                &diag_scratch,
                theorem_concl,
                final_line,
                line_idx,
                self.debug,
                &final_report,
            ) catch |err| {
                if (CompilerDiag.takeScratchDetail(
                    &diag_scratch,
                    final_mark,
                    env,
                    err,
                )) |detail| {
                    var diag = CompilerDiag.withPhase(.{
                        .kind = .generic,
                        .err = err,
                        .theorem_name = assertion.name,
                        .line_label = last_label,
                        .span = last_span,
                        .detail = detail,
                    }, .final_reconciliation);
                    addBoundaryAttemptNotes(&diag, final_report);
                    CompilerDiag.setProof(self, diag);
                    return err;
                }
                diag_scratch.discard(final_mark);
                return err;
            })) {
                diag_scratch.discard(final_mark);
                try ensureConcreteCheckedIrRange(
                    self,
                    env,
                    theorem,
                    assertion.name,
                    checked.items[checked_mark..],
                    last_label,
                    last_span,
                    .final_reconciliation,
                );
                return try checked.toOwnedSlice(allocator);
            }
            diag_scratch.discard(final_mark);
            var diag = CompilerDiag.withPhase(.{
                .kind = .final_line_mismatch,
                .err = error.FinalLineMismatch,
                .theorem_name = assertion.name,
                .line_label = last_label,
                .span = last_span,
            }, .final_reconciliation);
            addBoundaryAttemptNotes(&diag, final_report);
            CompilerDiag.setProof(self, diag);
            return error.FinalLineMismatch;
        }
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .final_line_mismatch,
            .err = error.FinalLineMismatch,
            .theorem_name = assertion.name,
            .line_label = last_label,
            .span = last_span,
        }, .final_reconciliation));
        return error.FinalLineMismatch;
    }
    return try checked.toOwnedSlice(allocator);
}

fn parseProofLineAssertion(
    self: anytype,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    line: ProofLine,
) !Holes.ParsedAssertion {
    return Holes.parseAssertion(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        line.assertion.text,
    ) catch |err| {
        CompilerDiag.setProof(self, CompilerDiag.proofMathParseDiagnostic(
            parser,
            .parse_assertion,
            err,
            assertion.name,
            line.label,
            line.application.rule_name,
            null,
            line.assertion.span,
        ));
        return err;
    };
}

fn applyRuleApplication(
    self: anytype,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    diag_context: ApplicationDiagnosticContext,
    line: ApplicationLine,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) anyerror!SuccessfulLineAttempt {
    const allocator = context.allocator;
    const initial_rule_id = try lookupRuleApplicationId(
        self,
        context.env,
        context.rule_catalog,
        diag_context,
        application,
    );
    const saved_diag = getDiagnostic(self);

    var first_diag: ?Diagnostic = null;
    var first_err: ?anyerror = null;
    var seen_candidates = std.AutoHashMap(u32, void).init(allocator);
    defer seen_candidates.deinit();
    var candidate_rule_id = initial_rule_id;

    while (true) {
        const seen = try seen_candidates.getOrPut(candidate_rule_id);
        if (seen.found_existing) {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.FallbackCycle,
                .theorem_name = diag_context.theorem_name,
                .line_label = diag_context.line_label,
                .rule_name = application.rule_name,
                .span = application.rule_span,
            }, .theorem_application));
            return error.FallbackCycle;
        }

        const next_fallback = context.registry.getFallbackRule(
            candidate_rule_id,
        );
        const speculative = first_err != null or next_fallback != null;
        restoreDiagnostic(self, if (speculative) null else saved_diag);
        const checked_mark = context.checked.items.len;

        if (speculative) {
            var attempt_theorem = try theorem.clone();
            var attempt_theorem_vars = cloneNameExprMap(
                allocator,
                theorem_vars,
            ) catch |err| {
                attempt_theorem.deinit();
                return err;
            };

            var attempt = tryApplyRuleApplicationWithCandidate(
                self,
                context,
                application,
                line_assertion,
                expected_conclusion_hint,
                line,
                candidate_rule_id,
                &attempt_theorem,
                &attempt_theorem_vars,
            ) catch |err| {
                CheckedIr.rollbackToMark(allocator, context.checked, checked_mark);
                attempt_theorem_vars.deinit();
                attempt_theorem.deinit();
                if (first_err == null) {
                    first_err = err;
                    first_diag = getDiagnostic(self);
                }
                candidate_rule_id = next_fallback orelse {
                    var diag = first_diag orelse saved_diag;
                    if (first_diag != null) {
                        if (diag) |*actual_diag| {
                            addFallbackFailureNote(
                                actual_diag,
                                line_assertion,
                                line,
                            );
                        }
                    }
                    restoreDiagnostic(self, diag);
                    return first_err.?;
                };
                continue;
            };

            validateAttemptCheckedIrRange(
                self,
                context.env,
                &attempt.theorem,
                diag_context.theorem_name,
                context.checked.items[checked_mark..],
                diag_context.line_label,
                diag_context.span,
                .theorem_application,
                saved_diag,
            ) catch |err| {
                CheckedIr.rollbackToMark(allocator, context.checked, checked_mark);
                attempt.theorem_vars.deinit();
                attempt.theorem.deinit();
                return err;
            };

            var old_theorem = theorem.*;
            theorem.* = attempt.theorem;
            old_theorem.deinit();
            theorem_vars.deinit();
            theorem_vars.* = attempt.theorem_vars;
            restoreDiagnostic(self, saved_diag);
            return attempt;
        }

        const attempt = tryApplyRuleApplicationWithCandidate(
            self,
            context,
            application,
            line_assertion,
            expected_conclusion_hint,
            line,
            candidate_rule_id,
            theorem,
            theorem_vars,
        ) catch |err| {
            return err;
        };

        try validateAttemptCheckedIrRange(
            self,
            context.env,
            theorem,
            diag_context.theorem_name,
            context.checked.items[checked_mark..],
            diag_context.line_label,
            diag_context.span,
            .theorem_application,
            saved_diag,
        );

        restoreDiagnostic(self, saved_diag);
        return attempt;
    }
}

fn tryApplyRuleApplicationWithCandidate(
    self: anytype,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    line: ApplicationLine,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) anyerror!SuccessfulLineAttempt {
    const allocator = context.allocator;
    const parser = context.parser;
    const env = context.env;
    const registry = context.registry;
    const assertion = context.assertion;
    const checked = context.checked;
    const diag_scratch = context.diag_scratch;
    const rule = &env.rules.items[rule_id];
    const diag_line = line;
    if (application.refs.len != rule.hyps.len) {
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .ref_count_mismatch,
            .err = error.RefCountMismatch,
            .theorem_name = assertion.name,
            .line_label = diag_line.label,
            .rule_name = application.rule_name,
            .span = application.refsOrRuleSpan(),
        }, .theorem_application));
        return error.RefCountMismatch;
    }

    const partial_bindings = try parseBindings(
        self,
        allocator,
        parser,
        theorem,
        theorem_vars,
        context.sort_vars,
        assertion.name,
        rule,
        application,
        diag_line,
    );
    defer allocator.free(partial_bindings);

    const expected_refs = try inferExpectedRefsForInlineApplications(
        allocator,
        theorem,
        rule,
        line_assertion,
        expected_conclusion_hint,
        partial_bindings,
    );
    defer allocator.free(expected_refs);

    // Ownership of `refs` flows asymmetrically. The freshen path duplicates it
    // internally and we free our copy explicitly on success below. The normal
    // path passes it to `Matching.tryBuildConclusionLine`, which transfers
    // ownership to a CheckedLine via `appendRuleLine`; from then on,
    // `rollbackToMark` (in the fallback handler) or final teardown will free it.
    // We therefore deliberately omit an `errdefer free(refs)` here: it would
    // double-free in the late-error case where `appendRuleLine` already stored
    // refs in a CheckedLine before a subsequent step (e.g. `appendTransportLine`
    // or `emitTransport`) failed. The trade-off is that errors before refs is
    // stored leak this small allocation; that matches pre-refactor behavior.
    const refs = try allocator.alloc(CheckedRef, application.refs.len);
    const ref_exprs = try allocator.alloc(ExprId, application.refs.len);
    defer allocator.free(ref_exprs);
    try elaborateRefs(
        self,
        context,
        diag_line,
        theorem,
        theorem_vars,
        application.refs,
        expected_refs,
        refs,
        ref_exprs,
    );

    // Keep the user's explicit bindings separate from @fresh selections.
    // applyFreshBindings mutates partial_bindings in-place, and later
    // hole-filled validation must still know which @fresh targets were
    // generated automatically rather than written by the user.
    const explicit_bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(explicit_bindings);

    if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
        try applyFreshBindings(
            self,
            parser,
            env,
            theorem,
            theorem_vars,
            context.sort_vars,
            assertion.name,
            rule,
            diag_line,
            try lineAssertionKnownDeps(
                env,
                theorem,
                rule,
                line_assertion,
                partial_bindings,
            ),
            ref_exprs,
            partial_bindings,
            rule_fresh,
        );
    }
    const maybe_view = context.views.get(rule_id);
    const had_omitted = Inference.hasOmittedBindings(partial_bindings);
    const has_omitted_structural = had_omitted and
        try Inference.hasOmittedStructuralBindings(
            env,
            registry,
            rule,
            partial_bindings,
        );
    // When an omitted structural remainder and a fixed item share a
    // structural subtree, several ACUI-compatible decompositions may exist.
    // A strict replay success is still accepted as the fast exact answer.
    // If exact inference cannot settle the application, prefer the structural
    // solver over greedy transparent/session fallback so remaining choices
    // are ranked by minimal residual context.
    const prefer_structural_solver = had_omitted and
        try Inference.shouldPreferStructuralSolver(
            env,
            registry,
            rule,
            partial_bindings,
        );
    const rule_has_advanced_inference =
        Inference.shouldUseAdvancedInference(maybe_view) or
        has_omitted_structural;
    const use_advanced_inference = had_omitted and
        rule_has_advanced_inference;

    if (maybe_view) |view| {
        if (!use_advanced_inference) {
            switch (line_assertion) {
                .concrete => |line_expr| {
                    CompilerViews.applyViewBindings(
                        allocator,
                        theorem,
                        env,
                        registry,
                        &view,
                        line_expr,
                        ref_exprs,
                        partial_bindings,
                        null,
                        null,
                        self.debug.views,
                    ) catch |err| {
                        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                            .kind = .generic,
                            .err = err,
                            .theorem_name = assertion.name,
                            .line_label = diag_line.label,
                            .rule_name = diag_line.application.rule_name,
                            .span = diag_line.ruleApplicationSpan(),
                        }, .theorem_application));
                        return err;
                    };
                },
                .holey, .implicit_whole_conclusion => {},
            }
        }
    }

    const fresh_context: Inference.HiddenWitnessFreshContext = .{
        .parser = parser,
        .theorem_vars = theorem_vars,
        .sort_vars = context.sort_vars,
    };

    const bindings = try inferCandidateBindings(
        self,
        allocator,
        env,
        registry,
        diag_scratch,
        theorem,
        assertion,
        rule_id,
        rule,
        diag_line,
        line_assertion,
        partial_bindings,
        ref_exprs,
        expected_conclusion_hint,
        fresh_context,
        maybe_view,
        had_omitted,
        rule_has_advanced_inference,
        use_advanced_inference,
        has_omitted_structural,
        prefer_structural_solver,
        context.rule_unify_cache,
    );

    var resolved_bindings = bindings;
    var freshened_bindings: ?CompilerFreshen.FreshenResult = null;
    Inference.validateResolvedBindingsWithDebug(
        self,
        self.debug,
        env,
        theorem,
        assertion,
        diag_line,
        rule,
        resolved_bindings,
    ) catch |err| {
        if (err != error.DepViolation) return err;
        const rule_freshen = context.freshen_bindings.get(rule_id) orelse return err;
        const dep_detail = (try Inference.firstDepViolation(
            env,
            theorem,
            assertion.args,
            rule.args,
            rule.arg_names,
            resolved_bindings,
        )) orelse return err;
        var freshen_report: CompilerFreshen.FreshenAttemptReport = .{};
        freshened_bindings = CompilerFreshen.tryFreshenBindings(
            allocator,
            parser,
            env,
            registry,
            theorem,
            theorem_vars,
            context.sort_vars,
            rule,
            try resolveLineAssertionForBindings(
                self,
                allocator,
                parser,
                theorem,
                env,
                registry,
                diag_scratch,
                assertion,
                diag_line,
                rule,
                line_assertion,
                resolved_bindings,
            ),
            ref_exprs,
            resolved_bindings,
            rule_freshen,
            dep_detail,
            checked,
            diag_scratch,
            self.debug,
            &freshen_report,
        ) catch |fresh_err| {
            var diag = CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = fresh_err,
                .theorem_name = assertion.name,
                .line_label = diag_line.label,
                .rule_name = application.rule_name,
                .span = application.ruleApplicationSpan(),
                .detail = .{ .dep_violation = dep_detail },
            }, .theorem_application);
            try addFreshenAttemptNotes(allocator, &diag, rule, freshen_report);
            CompilerDiag.setProof(self, diag);
            return fresh_err;
        } orelse return err;
        resolved_bindings = freshened_bindings.?.bindings;
        if (try Inference.firstDepViolation(
            env,
            theorem,
            assertion.args,
            rule.args,
            rule.arg_names,
            resolved_bindings,
        )) |remaining_dep_detail| {
            var diag = CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.AlphaRewriteSearchFailed,
                .theorem_name = assertion.name,
                .line_label = diag_line.label,
                .rule_name = application.rule_name,
                .span = application.ruleApplicationSpan(),
                .detail = .{ .dep_violation = remaining_dep_detail },
            }, .theorem_application);
            try addFreshenAttemptNotes(allocator, &diag, rule, freshen_report);
            CompilerDiag.setProof(self, diag);
            return error.AlphaRewriteSearchFailed;
        }
        restoreDiagnostic(self, null);
        try Inference.validateResolvedBindingsWithDebug(
            self,
            self.debug,
            env,
            theorem,
            assertion,
            diag_line,
            rule,
            resolved_bindings,
        );
    };
    restoreDiagnostic(self, null);

    if (freshened_bindings) |freshened| {
        if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
            try validateFreshBindingsAgainstLine(
                self,
                allocator,
                env,
                theorem,
                assertion.name,
                rule,
                diag_line,
                try resolveLineAssertionForBindings(
                    self,
                    allocator,
                    parser,
                    theorem,
                    env,
                    registry,
                    diag_scratch,
                    assertion,
                    diag_line,
                    rule,
                    line_assertion,
                    bindings,
                ),
                ref_exprs,
                explicit_bindings,
                bindings,
                rule_fresh,
            );
        }
        const line_idx = applyFreshenedRuleLine(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            try resolveLineAssertionForBindings(
                self,
                allocator,
                parser,
                theorem,
                env,
                registry,
                diag_scratch,
                assertion,
                diag_line,
                rule,
                line_assertion,
                bindings,
            ),
            rule,
            rule_id,
            bindings,
            freshened,
            refs,
            ref_exprs,
        ) catch |err| {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = diag_line.label,
                .rule_name = diag_line.application.rule_name,
                .span = diag_line.ruleApplicationSpan(),
            }, .theorem_application));
            return err;
        };
        allocator.free(refs);
        return .{
            .line_idx = line_idx,
            .theorem = theorem.*,
            .theorem_vars = theorem_vars.*,
        };
    }

    for (ref_exprs, application.refs, 0..) |actual, ref, idx| {
        const expected = try theorem.instantiateTemplate(
            rule.hyps[idx],
            resolved_bindings,
        );
        const match_mark = diag_scratch.mark();
        if (Matching.tryMatchHypothesis(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            self.debug,
            idx,
            refs[idx],
            actual,
            expected,
        ) catch |err| {
            if (CompilerDiag.setProofScratchDiagnosticIfPresent(
                self,
                diag_scratch,
                match_mark,
                env,
                .theorem_application,
                .generic,
                err,
                assertion.name,
                diag_line.label,
                application.rule_name,
                refSpan(application.refs[idx]),
            )) {
                return err;
            }
            diag_scratch.discard(match_mark);
            return err;
        }) |matched_ref| {
            diag_scratch.discard(match_mark);
            refs[idx] = matched_ref;
            continue;
        }
        diag_scratch.discard(match_mark);
        const span = switch (ref) {
            .hyp => |hyp| hyp.span,
            .line => |label| label.span,
            .application => |inline_app| inline_app.span,
        };
        var diag = switch (ref) {
            .hyp => |hyp| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = diag_line.label,
                .rule_name = diag_line.application.rule_name,
                .span = span,
                .detail = .{
                    .hypothesis_ref = .{
                        .index = hyp.index,
                    },
                },
            }, .theorem_application),
            .line => |label| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = diag_line.label,
                .rule_name = diag_line.application.rule_name,
                .name = label.label,
                .span = span,
            }, .theorem_application),
            .application => |inline_app| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = diag_line.label,
                .rule_name = diag_line.application.rule_name,
                .name = inline_app.rule_name,
                .span = span,
            }, .theorem_application),
        };
        try addComparisonSnapshotNotes(
            allocator,
            &diag,
            theorem,
            env,
            registry,
            diag_scratch,
            expected,
            actual,
            true,
        );
        CompilerDiag.setProof(self, diag);
        return error.HypothesisMismatch;
    }

    const candidate = try elaborateCandidateLine(
        self,
        allocator,
        parser,
        theorem,
        env,
        registry,
        diag_scratch,
        assertion,
        diag_line,
        rule,
        line_assertion,
        resolved_bindings,
    );

    if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
        try validateFreshBindingsAgainstLine(
            self,
            allocator,
            env,
            theorem,
            assertion.name,
            rule,
            diag_line,
            candidate.displayed_conclusion,
            ref_exprs,
            explicit_bindings,
            candidate.resolved_bindings,
            rule_fresh,
        );
    }

    const concl_mark = diag_scratch.mark();
    const line_idx = (Matching.tryBuildConclusionLine(
        allocator,
        theorem,
        registry,
        env,
        checked,
        diag_scratch,
        self.debug,
        candidate.displayed_conclusion,
        candidate.raw_conclusion,
        rule_id,
        candidate.resolved_bindings,
        refs,
    ) catch |err| {
        if (CompilerDiag.setProofScratchDiagnosticIfPresent(
            self,
            diag_scratch,
            concl_mark,
            env,
            .theorem_application,
            .generic,
            err,
            assertion.name,
            diag_line.label,
            diag_line.application.rule_name,
            diag_line.assertion_span,
        )) {
            return err;
        }
        diag_scratch.discard(concl_mark);
        return err;
    }) orelse {
        diag_scratch.discard(concl_mark);
        var diag = CompilerDiag.withPhase(.{
            .kind = .conclusion_mismatch,
            .err = error.ConclusionMismatch,
            .theorem_name = assertion.name,
            .line_label = diag_line.label,
            .rule_name = diag_line.application.rule_name,
            .span = diag_line.assertion_span,
        }, .theorem_application);
        try addComparisonSnapshotNotes(
            allocator,
            &diag,
            theorem,
            env,
            registry,
            diag_scratch,
            candidate.raw_conclusion,
            candidate.displayed_conclusion,
            true,
        );
        CompilerDiag.setProof(self, diag);
        return error.ConclusionMismatch;
    };
    diag_scratch.discard(concl_mark);

    return .{
        .line_idx = line_idx,
        .theorem = theorem.*,
        .theorem_vars = theorem_vars.*,
    };
}

fn resolveLineAssertionForBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ApplicationLine,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    bindings: []const ExprId,
) !ExprId {
    return switch (line_assertion) {
        .concrete => |line_expr| line_expr,
        .implicit_whole_conclusion => try theorem.instantiateTemplate(
            rule.concl,
            bindings,
        ),
        .holey => |holey| blk: {
            const expected_line = try theorem.instantiateTemplate(
                rule.concl,
                bindings,
            );
            break :blk try validateHoleyAssertionAgainstCandidate(
                self,
                allocator,
                parser,
                theorem,
                env,
                registry,
                diag_scratch,
                assertion,
                line,
                holey,
                expected_line,
            );
        },
    };
}

fn requireConcreteBindingsWithDiagnostic(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ApplicationLine,
    partial_bindings: []const ?ExprId,
) ![]const ExprId {
    for (partial_bindings, 0..) |binding, idx| {
        if (binding != null) continue;
        CompilerDiag.setProof(
            self,
            try Inference.buildMissingBinderDiagnostic(
                allocator,
                env,
                theorem,
                assertion,
                rule,
                line,
                .strict_replay,
                partial_bindings,
                partial_bindings,
                idx,
            ),
        );
        return error.MissingBinderAssignment;
    }
    return try Inference.requireConcreteBindings(allocator, partial_bindings);
}

fn inferCandidateBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    theorem: *TheoremContext,
    assertion: AssertionStmt,
    rule_id: u32,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_assertion: LineAssertion,
    partial_bindings: []const ?ExprId,
    base_ref_exprs: []const ExprId,
    expected_conclusion_hint: ?ExprId,
    fresh_context: Inference.HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    had_omitted: bool,
    rule_has_advanced_inference: bool,
    use_advanced_inference: bool,
    has_omitted_structural: bool,
    prefer_structural_solver: bool,
    rule_unify_cache: *Inference.RuleUnifyCache,
) ![]const ExprId {
    return switch (line_assertion) {
        .holey => |holey| blk: {
            const has_structural_hole = try Holes.containsStructuralHole(
                env,
                registry,
                holey,
            );
            // Exact refs can identify a candidate before the visible holey
            // assertion is checked.  Keep this shortcut conservative: it must
            // solve every binder, and it must not bypass structural-hole
            // inference such as `_ctx` ACUI minimal-residual solving.
            if (had_omitted and
                !has_structural_hole and
                !prefer_structural_solver)
            {
                if (try Inference.inferBindingsFromRefsOnly(
                    allocator,
                    theorem,
                    rule,
                    partial_bindings,
                    base_ref_exprs,
                )) |refs_only_bindings| {
                    break :blk refs_only_bindings;
                }
            }

            const use_holey_advanced = had_omitted and
                (rule_has_advanced_inference or has_structural_hole);
            if (use_holey_advanced) {
                break :blk Inference.inferBindingsFromHoleyAdvanced(
                    self,
                    allocator,
                    env,
                    registry,
                    diag_scratch,
                    theorem,
                    assertion,
                    rule_id,
                    rule,
                    line,
                    partial_bindings,
                    base_ref_exprs,
                    holey,
                    maybe_view,
                    fresh_context,
                ) catch |err| {
                    if (getDiagnostic(self) == null) {
                        try setHoleyInferenceDiagnostic(
                            self,
                            allocator,
                            assertion,
                            line,
                            rule,
                            holey,
                            err,
                            .{},
                        );
                    }
                    return err;
                };
            }
            if (!had_omitted) {
                break :blk try Inference.requireConcreteBindings(
                    allocator,
                    partial_bindings,
                );
            }
            var hole_report = Holes.InferenceReport{};
            break :blk Holes.inferBindingsFromAssertionDetailed(
                allocator,
                theorem,
                rule,
                partial_bindings,
                base_ref_exprs,
                holey,
                &hole_report,
            ) catch |err| {
                // The lightweight hole matcher is deliberately exact.  If
                // the visible assertion is too holey, exact ref replay can
                // fail before it gets to the candidate conclusion, even when
                // transparent rule matching would identify a unique concrete
                // candidate from the refs.  Try that def-aware path before
                // reporting the exact matcher's failure.
                if (err == error.UnifyMismatch or
                    err == error.HoleyInferenceMismatch)
                {
                    if (Inference.inferBindingsFromHoleyAdvanced(
                        self,
                        allocator,
                        env,
                        registry,
                        diag_scratch,
                        theorem,
                        assertion,
                        rule_id,
                        rule,
                        line,
                        partial_bindings,
                        base_ref_exprs,
                        holey,
                        maybe_view,
                        fresh_context,
                    )) |bindings| {
                        restoreDiagnostic(self, null);
                        break :blk bindings;
                    } else |_| {
                        restoreDiagnostic(self, null);
                    }
                }
                try setHoleyInferenceDiagnostic(
                    self,
                    allocator,
                    assertion,
                    line,
                    rule,
                    holey,
                    err,
                    hole_report,
                );
                return err;
            };
        },
        .implicit_whole_conclusion => blk: {
            if (had_omitted) {
                if (expected_conclusion_hint) |hint| {
                    if (Inference.inferBindings(
                        self,
                        allocator,
                        env,
                        registry,
                        diag_scratch,
                        theorem,
                        assertion,
                        rule_id,
                        rule,
                        line,
                        partial_bindings,
                        base_ref_exprs,
                        hint,
                        fresh_context,
                        maybe_view,
                        use_advanced_inference,
                        rule_unify_cache,
                    )) |hint_bindings| {
                        restoreDiagnostic(self, null);
                        break :blk hint_bindings;
                    } else |err| {
                        if (err == error.OutOfMemory) return err;
                        restoreDiagnostic(self, null);
                    }
                }
                if (maybe_view) |view| {
                    const seeded = try allocator.dupe(
                        ?ExprId,
                        partial_bindings,
                    );
                    defer allocator.free(seeded);
                    const view_applied = if (CompilerViews.applyViewBindingsRefsOnly(
                        allocator,
                        theorem,
                        env,
                        registry,
                        &view,
                        base_ref_exprs,
                        seeded,
                        null,
                        null,
                        self.debug.views,
                    ))
                        true
                    else |err| blk_view: {
                        if (err == error.OutOfMemory) return err;
                        break :blk_view false;
                    };
                    if (view_applied) {
                        if (!Inference.hasOmittedBindings(seeded)) {
                            break :blk try Inference.requireConcreteBindings(
                                allocator,
                                seeded,
                            );
                        }
                        if (try Inference.inferBindingsFromRefsOnly(
                            allocator,
                            theorem,
                            rule,
                            seeded,
                            base_ref_exprs,
                        )) |refs_only_bindings| {
                            break :blk refs_only_bindings;
                        }
                    }
                }
                // For implicit chained applications, an exact refs-only
                // result can commit to a non-minimal structural residual
                // before the enclosing application can validate it. Let the
                // structural path see the whole constraint set instead.
                if (!has_omitted_structural or !use_advanced_inference) {
                    if (try Inference.inferBindingsFromRefsOnly(
                        allocator,
                        theorem,
                        rule,
                        partial_bindings,
                        base_ref_exprs,
                    )) |refs_only_bindings| {
                        break :blk refs_only_bindings;
                    }
                }
                // Keep the cheap exact path above for ordinary inline
                // applications. If normalized or view-backed rules remain
                // underdetermined, treat the implicit conclusion like a
                // whole-line hole so structural hypothesis constraints can
                // recover hidden binders, e.g. an ACUI context for `nd`.
                if (use_advanced_inference) {
                    const whole_hole = Expr{ .hole = .{
                        .sort = try templateSort(env, rule, rule.concl),
                        .token = "<implicit>",
                    } };
                    break :blk try Inference.inferBindingsFromHoleyAdvanced(
                        self,
                        allocator,
                        env,
                        registry,
                        diag_scratch,
                        theorem,
                        assertion,
                        rule_id,
                        rule,
                        line,
                        partial_bindings,
                        base_ref_exprs,
                        &whole_hole,
                        maybe_view,
                        fresh_context,
                    );
                }
            }
            break :blk try requireConcreteBindingsWithDiagnostic(
                self,
                allocator,
                env,
                theorem,
                assertion,
                rule,
                line,
                partial_bindings,
            );
        },
        .concrete => |line_expr| blk: {
            if (had_omitted) {
                break :blk try Inference.inferBindings(
                    self,
                    allocator,
                    env,
                    registry,
                    diag_scratch,
                    theorem,
                    assertion,
                    rule_id,
                    rule,
                    line,
                    partial_bindings,
                    base_ref_exprs,
                    line_expr,
                    fresh_context,
                    maybe_view,
                    use_advanced_inference,
                    rule_unify_cache,
                );
            }
            break :blk try Inference.requireConcreteBindings(
                allocator,
                partial_bindings,
            );
        },
    };
}

fn templateSort(
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    template: TemplateExpr,
) !u7 {
    const sort_name = switch (template) {
        .binder => |idx| rule.args[idx].sort_name,
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            break :blk env.terms.items[app.term_id].ret_sort_name;
        },
    };
    const sort_id = env.sort_names.get(sort_name) orelse {
        return error.UnknownSort;
    };
    return @intCast(sort_id);
}

fn elaborateCandidateLine(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ApplicationLine,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    resolved_bindings: []const ExprId,
) !CandidateElaboration {
    const raw_conclusion = try theorem.instantiateTemplate(
        rule.concl,
        resolved_bindings,
    );
    const displayed_conclusion = switch (line_assertion) {
        .concrete => |line_expr| line_expr,
        .implicit_whole_conclusion => raw_conclusion,
        .holey => |holey| try validateHoleyAssertionAgainstCandidate(
            self,
            allocator,
            parser,
            theorem,
            env,
            registry,
            diag_scratch,
            assertion,
            line,
            holey,
            raw_conclusion,
        ),
    };
    return .{
        .resolved_bindings = resolved_bindings,
        .raw_conclusion = raw_conclusion,
        .displayed_conclusion = displayed_conclusion,
    };
}

fn validateHoleyAssertionAgainstCandidate(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ApplicationLine,
    holey: *const Expr,
    expected_line: ExprId,
) !ExprId {
    // Prefer the raw instantiated conclusion when the holey surface permits
    // it. A whole-line hole such as `_wff` can match anything; returning the
    // normalized form there hides the rule's raw constructor from later
    // omitted-binder inference that uses this line as a ref. If the raw shape
    // does not match the visible surface, normalized and materialized checks
    // below still handle normalized conclusions.
    var hole_report = Holes.ConcreteMatchReport{};
    if (try holeyAssertionMatchesCandidate(
        allocator,
        parser,
        theorem,
        env,
        holey,
        expected_line,
        &hole_report,
    )) {
        return expected_line;
    }

    var scratch_checked = std.ArrayListUnmanaged(CheckedLine){};
    defer scratch_checked.deinit(allocator);
    const normalized_line = try Normalize.normalizeExprForSnapshot(
        allocator,
        theorem,
        registry,
        env,
        &scratch_checked,
        diag_scratch,
        expected_line,
    );
    if (normalized_line != expected_line) {
        var normalized_report = Holes.ConcreteMatchReport{};
        if (try holeyAssertionMatchesCandidate(
            allocator,
            parser,
            theorem,
            env,
            holey,
            normalized_line,
            &normalized_report,
        )) {
            return normalized_line;
        }
        hole_report = normalized_report;
    }

    const can_materialize = normalized_line != expected_line or
        try Holes.containsStructuralHole(env, registry, holey);
    if (can_materialize) {
        var materialized_report = Holes.ConcreteMatchReport{};
        if (try Holes.materializeSurfaceWithCandidate(
            parser,
            theorem,
            env,
            holey,
            expected_line,
            &materialized_report,
        )) |materialized_line| {
            return materialized_line;
        } else if (materialized_report.failure != null) {
            hole_report = materialized_report;
        }
    }

    var diag = CompilerDiag.withPhase(.{
        .kind = .conclusion_mismatch,
        .err = error.HoleConclusionMismatch,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .span = concreteMatchFailureSpan(line, hole_report) orelse
            line.assertion_span,
    }, .theorem_application);
    try addHoleConcreteMatchNotes(allocator, &diag, line, hole_report);
    CompilerDiag.setProof(self, diag);
    return error.HoleConclusionMismatch;
}

fn holeyAssertionMatchesCandidate(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    candidate: ExprId,
    report: *Holes.ConcreteMatchReport,
) !bool {
    var exact_report = Holes.ConcreteMatchReport{};
    if (try Holes.matchesConcreteDetailed(
        parser,
        theorem,
        env,
        holey,
        candidate,
        &exact_report,
    )) {
        return true;
    }

    var semantic_report = Holes.ConcreteMatchReport{};
    if (try Holes.matchesConcreteSemanticallyDetailed(
        allocator,
        parser,
        theorem,
        env,
        holey,
        candidate,
        &semantic_report,
    )) {
        return true;
    }

    report.* = semantic_report;
    return false;
}

fn applyFreshenedRuleLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    line_expr: ExprId,
    rule: *const RuleDecl,
    rule_id: u32,
    original_bindings: []const ExprId,
    freshened: CompilerFreshen.FreshenResult,
    refs: []const CheckedRef,
    base_ref_exprs: []const ExprId,
) !usize {
    const fresh_refs = try allocator.dupe(CheckedRef, refs);
    errdefer allocator.free(fresh_refs);

    for (base_ref_exprs, 0..) |actual, idx| {
        const expected_old = try theorem.instantiateTemplate(
            rule.hyps[idx],
            original_bindings,
        );
        const matched_old = (try Matching.tryMatchHypothesis(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            .none,
            idx,
            refs[idx],
            actual,
            expected_old,
        )) orelse return error.HypothesisMismatch;

        const expected_new = try theorem.instantiateTemplate(
            rule.hyps[idx],
            freshened.bindings,
        );
        if (expected_old == expected_new) {
            fresh_refs[idx] = matched_old;
            continue;
        }

        const conv_idx = (try CompilerFreshen.buildRelationProofFromTargetChange(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            expected_old,
            expected_new,
            freshened.old_target_expr,
            freshened.new_target_expr,
            freshened.target_conv_line_idx,
        )) orelse return error.FreshenTransportFailed;
        fresh_refs[idx] = try CompilerFreshen.transportRefAlongProof(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            expected_new,
            expected_old,
            conv_idx,
            matched_old,
        );
    }

    const expected_new_line = try theorem.instantiateTemplate(
        rule.concl,
        freshened.bindings,
    );
    const raw_idx = try CheckedIr.appendRuleLine(
        checked,
        allocator,
        expected_new_line,
        rule_id,
        freshened.bindings,
        fresh_refs,
    );

    var result_ref: CheckedRef = .{ .line = raw_idx };
    var result_expr = expected_new_line;
    const expected_old_line = try theorem.instantiateTemplate(
        rule.concl,
        original_bindings,
    );
    if (expected_old_line != expected_new_line) {
        const conv_idx = (try CompilerFreshen.buildRelationProofFromTargetChange(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            expected_old_line,
            expected_new_line,
            freshened.old_target_expr,
            freshened.new_target_expr,
            freshened.target_conv_line_idx,
        )) orelse return error.FreshenTransportFailed;
        result_ref = try CompilerFreshen.transportRefBackwardAlongProof(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            expected_old_line,
            expected_new_line,
            conv_idx,
            result_ref,
        );
        result_expr = expected_old_line;
    }

    if (result_expr != line_expr) {
        result_ref = (try Matching.tryMatchHypothesis(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            .none,
            0,
            result_ref,
            result_expr,
            line_expr,
        )) orelse return error.ConclusionMismatch;
    }

    return switch (result_ref) {
        .line => |line_idx| line_idx,
        .hyp => error.ConclusionMismatch,
    };
}

fn ensureConcreteCheckedIrRange(
    self: anytype,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_name: []const u8,
    lines: []const CheckedLine,
    line_label: ?[]const u8,
    span: ?Span,
    phase: CompilerDiag.DiagnosticPhase,
) !void {
    if (lines.len == 0) return;

    CheckedIr.validateLines(theorem, lines) catch |err| {
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = err,
            .theorem_name = theorem_name,
            .line_label = line_label,
            .span = span,
        }, phase));
        return err;
    };
    if (try CheckedIr.firstDepViolation(env, theorem, lines)) |failure| {
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = theorem_name,
            .line_label = line_label,
            .rule_name = if (failure.rule_id < env.rules.items.len)
                env.rules.items[failure.rule_id].name
            else
                null,
            .span = span,
            .detail = .{ .dep_violation = failure.detail },
        }, phase));
        return error.DepViolation;
    }
}

// Preserve any new checked-IR validation diagnostic on failure, but restore
// the caller's saved diagnostic on success so speculative attempts remain
// diagnostically transparent.
fn validateAttemptCheckedIrRange(
    self: anytype,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_name: []const u8,
    lines: []const CheckedLine,
    line_label: ?[]const u8,
    span: ?Span,
    phase: CompilerDiag.DiagnosticPhase,
    saved_diag: ?Diagnostic,
) !void {
    try ensureConcreteCheckedIrRange(
        self,
        env,
        theorem,
        theorem_name,
        lines,
        line_label,
        span,
        phase,
    );
    restoreDiagnostic(self, saved_diag);
}

test "checked ir leak diagnostics replace saved diagnostics" {
    const Sink = struct {
        last_diagnostic: ?Diagnostic = null,

        pub fn setDiagnostic(self: *@This(), diag: Diagnostic) void {
            self.last_diagnostic = diag;
        }
    };

    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const lines = [_]CheckedLine{.{
        .expr = placeholder,
        .data = .{ .rule = .{
            .rule_id = 0,
            .bindings = &.{theorem.theorem_vars.items[0]},
            .refs = &.{},
        } },
    }};

    var sink = Sink{};
    sink.last_diagnostic = CompilerDiag.withPhase(.{
        .kind = .generic,
        .err = error.UnknownRule,
        .theorem_name = "stale",
        .line_label = "old",
    }, .theorem_application);
    const saved_diag = getDiagnostic(&sink);
    const span: Span = .{ .start = 3, .end = 11 };
    var env = GlobalEnv.init(std.testing.allocator);
    defer {
        env.sort_names.deinit();
        env.term_names.deinit();
        env.rule_names.deinit();
        env.terms.deinit(std.testing.allocator);
        env.rules.deinit(std.testing.allocator);
    }

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateAttemptCheckedIrRange(
            &sink,
            &env,
            &theorem,
            "demo",
            &lines,
            "l2",
            span,
            .theorem_application,
            saved_diag,
        ),
    );

    const diag = sink.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.PlaceholderLeakage, diag.err);
    try std.testing.expectEqualStrings("demo", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l2", diag.line_label.?);
    try std.testing.expectEqual(span.start, diag.span.?.start);
    try std.testing.expectEqual(span.end, diag.span.?.end);
    try std.testing.expectEqual(
        CompilerDiag.DiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqual(.proof, diag.source);
}

fn lookupRuleApplicationId(
    self: anytype,
    env: *const GlobalEnv,
    rule_catalog: *const RuleCatalog.Catalog,
    diag_context: ApplicationDiagnosticContext,
    application: RuleApplication,
) !u32 {
    if (env.getRuleId(application.rule_name)) |rule_id| return rule_id;

    if (rule_catalog.get(application.rule_name)) |entry| {
        if (entry.ordinal >= env.rules.items.len) {
            var diag: Diagnostic = .{
                .kind = .rule_not_yet_available,
                .err = error.RuleNotYetAvailable,
                .theorem_name = diag_context.theorem_name,
                .line_label = diag_context.line_label,
                .rule_name = application.rule_name,
                .span = application.rule_span,
            };
            CompilerDiag.setPhase(&diag, .theorem_application);
            CompilerDiag.addNote(
                &diag,
                "rule is declared later in the mm0 file",
                .mm0,
                null,
            );
            CompilerDiag.addRelated(
                &diag,
                "rule declaration is here",
                .mm0,
                entry.name_span,
            );
            CompilerDiag.setProof(self, diag);
            return error.RuleNotYetAvailable;
        }
    }

    CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .theorem_name = diag_context.theorem_name,
        .line_label = diag_context.line_label,
        .rule_name = application.rule_name,
        .span = application.rule_span,
    }, .theorem_application));
    return error.UnknownRule;
}

fn inferExpectedRefsForInlineApplications(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    partial_bindings: []const ?ExprId,
) ![]?ExprId {
    const expected_refs = try allocator.alloc(?ExprId, rule.hyps.len);
    @memset(expected_refs, null);

    const line_expr = expected_conclusion_hint orelse switch (line_assertion) {
        .concrete => |expr| expr,
        .holey, .implicit_whole_conclusion => return expected_refs,
    };

    const contextual = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(contextual);
    if (!theorem.matchTemplate(rule.concl, line_expr, contextual)) {
        return expected_refs;
    }

    for (rule.hyps, 0..) |hyp, idx| {
        expected_refs[idx] = try instantiateTemplatePartial(
            theorem,
            hyp,
            contextual,
        );
    }
    return expected_refs;
}

fn instantiateTemplatePartial(
    theorem: *TheoremContext,
    template: TemplateExpr,
    binders: []const ?ExprId,
) !?ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= binders.len) return error.TemplateBinderOutOfRange;
            break :blk binders[idx];
        },
        .app => |app| blk: {
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            errdefer theorem.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try instantiateTemplatePartial(
                    theorem,
                    arg,
                    binders,
                )) orelse {
                    theorem.allocator.free(args);
                    break :blk null;
                };
            }
            break :blk try theorem.interner.internAppOwned(app.term_id, args);
        },
    };
}

fn elaborateRefs(
    self: anytype,
    context: *const RuleApplyContext,
    line: ApplicationLine,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    source_refs: []const Ref,
    expected_ref_exprs: []const ?ExprId,
    refs: []CheckedRef,
    ref_exprs: []ExprId,
) anyerror!void {
    const assertion = context.assertion;
    for (source_refs, 0..) |ref, idx| {
        ref_exprs[idx] = switch (ref) {
            .hyp => |hyp| blk: {
                if (hyp.index == 0 or
                    hyp.index > theorem.theorem_hyps.items.len)
                {
                    CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                        .kind = .unknown_hypothesis_ref,
                        .err = error.UnknownHypothesisRef,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .span = hyp.span,
                        .detail = .{
                            .hypothesis_ref = .{
                                .index = hyp.index,
                            },
                        },
                    }, .theorem_application));
                    return error.UnknownHypothesisRef;
                }
                refs[idx] = .{ .hyp = hyp.index - 1 };
                break :blk theorem.theorem_hyps.items[hyp.index - 1];
            },
            .line => |label| blk: {
                const line_idx = context.labels.get(label.label) orelse {
                    CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                        .kind = .unknown_label,
                        .err = error.UnknownLabel,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .name = label.label,
                        .span = label.span,
                    }, .theorem_application));
                    return error.UnknownLabel;
                };
                refs[idx] = .{ .line = line_idx };
                break :blk context.checked.items[line_idx].expr;
            },
            .application => |inline_app| blk: {
                const attempt = try applyRuleApplication(
                    self,
                    context,
                    inline_app,
                    .implicit_whole_conclusion,
                    expected_ref_exprs[idx],
                    .{
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .span = inline_app.span,
                    },
                    line.forInline(inline_app),
                    theorem,
                    theorem_vars,
                );
                refs[idx] = .{ .line = attempt.line_idx };
                break :blk context.checked.items[attempt.line_idx].expr;
            },
        };
    }
}

fn buildTheoremVarMap(
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
) !NameExprMap {
    var vars = NameExprMap.init(allocator);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try vars.put(actual_name, expr);
        }
    }
    return vars;
}

fn cloneNameExprMap(
    allocator: std.mem.Allocator,
    src: *const NameExprMap,
) !NameExprMap {
    var dst = NameExprMap.init(allocator);
    errdefer dst.deinit();

    try dst.ensureTotalCapacity(src.count());
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

fn getDiagnostic(self: anytype) ?Diagnostic {
    const T = @TypeOf(self);
    switch (@typeInfo(T)) {
        .pointer => |ptr| {
            if (@hasField(ptr.child, "last_diagnostic")) {
                return self.last_diagnostic;
            }
        },
        .@"struct" => {
            if (@hasField(T, "last_diagnostic")) {
                return self.last_diagnostic;
            }
        },
        else => {},
    }
    return null;
}

fn restoreDiagnostic(self: anytype, diag: ?Diagnostic) void {
    const T = @TypeOf(self);
    switch (@typeInfo(T)) {
        .pointer => |ptr| {
            if (@hasField(ptr.child, "last_diagnostic")) {
                self.last_diagnostic = diag;
            }
        },
        .@"struct" => {
            if (@hasField(T, "last_diagnostic")) {
                self.last_diagnostic = diag;
            }
        },
        else => {},
    }
}

fn parseBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    application: RuleApplication,
    line: ApplicationLine,
) ![]?ExprId {
    for (rule.arg_names) |arg_name| {
        if (arg_name == null) {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.UnnamedRuleBinder,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = application.rule_name,
                .span = application.ruleApplicationSpan(),
            }, .theorem_application));
            return error.UnnamedRuleBinder;
        }
    }

    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    for (application.arg_bindings) |binding| {
        const arg_index = findRuleArgIndex(rule, binding.name) orelse {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .unknown_binder_name,
                .err = error.UnknownBinderName,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = application.rule_name,
                .name = binding.name,
                .span = binding.span,
            }, .theorem_application));
            return error.UnknownBinderName;
        };
        if (bindings[arg_index] != null) {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .duplicate_binder_assignment,
                .err = error.DuplicateBinderAssignment,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = application.rule_name,
                .name = binding.name,
                .span = binding.span,
            }, .theorem_application));
            return error.DuplicateBinderAssignment;
        }

        const expr = blk: {
            try CompilerVars.ensureMathTextVars(
                parser,
                theorem,
                theorem_vars,
                sort_vars,
                binding.formula.text,
            );
            break :blk parser.parseArgText(
                binding.formula.text,
                theorem_vars,
                rule.args[arg_index],
            );
        } catch |err| {
            CompilerDiag.setProof(self, CompilerDiag.proofMathParseDiagnostic(
                parser,
                .parse_binding,
                err,
                theorem_name,
                line.label,
                application.rule_name,
                binding.name,
                binding.formula.span,
            ));
            return err;
        };
        bindings[arg_index] = try theorem.internParsedExpr(expr);
    }

    return bindings;
}

fn lineAssertionKnownDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    partial_bindings: []const ?ExprId,
) !u55 {
    return switch (line_assertion) {
        .concrete => |expr_id| (try Inference.exprInfo(
            env,
            theorem,
            theorem.arg_infos,
            expr_id,
        )).deps,
        .holey => |expr| expr.deps(),
        .implicit_whole_conclusion => try templateKnownDeps(
            env,
            theorem,
            rule.concl,
            partial_bindings,
        ),
    };
}

fn templateKnownDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    partial_bindings: []const ?ExprId,
) !u55 {
    return switch (template) {
        .binder => |idx| blk: {
            const expr_id = partial_bindings[idx] orelse break :blk 0;
            break :blk (try Inference.exprInfo(
                env,
                theorem,
                theorem.arg_infos,
                expr_id,
            )).deps;
        },
        .app => |app| blk: {
            var deps: u55 = 0;
            for (app.args) |arg| {
                deps |= try templateKnownDeps(
                    env,
                    theorem,
                    arg,
                    partial_bindings,
                );
            }
            break :blk deps;
        },
    };
}

fn validateFreshBindingsAgainstLine(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    partial_bindings: []const ?ExprId,
    resolved_bindings: []const ExprId,
    fresh_list: []const FreshDecl,
) !void {
    const optional_bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(optional_bindings);
    for (fresh_list) |fresh| {
        optional_bindings[fresh.target_arg_idx] = null;
    }

    const used_deps = try CompilerFresh.collectUsedDeps(
        env,
        theorem,
        line_expr,
        ref_exprs,
        optional_bindings,
        0,
    );
    for (fresh_list) |fresh| {
        if (partial_bindings[fresh.target_arg_idx] != null) continue;
        const selected = resolved_bindings[fresh.target_arg_idx];
        const selected_deps = (try Inference.exprInfo(
            env,
            theorem,
            theorem.arg_infos,
            selected,
        )).deps;
        if ((used_deps & selected_deps) == 0) continue;
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .parse_fresh,
            .err = error.FreshNoAvailableVar,
            .theorem_name = theorem_name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .name = rule.arg_names[fresh.target_arg_idx].?,
            .span = line.ruleApplicationSpan(),
        }, .theorem_application));
        return error.FreshNoAvailableVar;
    }
}

fn applyFreshBindings(
    self: anytype,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_deps: u55,
    ref_exprs: []const ExprId,
    bindings: []?ExprId,
    fresh_list: []const FreshDecl,
) !void {
    const used_deps = try CompilerFresh.collectUsedDepsFromLineDeps(
        env,
        theorem,
        line_deps,
        ref_exprs,
        bindings,
        0,
    );
    var reserved_deps: u55 = 0;

    for (fresh_list) |fresh| {
        if (bindings[fresh.target_arg_idx] != null) continue;

        const selection = CompilerFresh.chooseFreshBinding(
            parser,
            theorem,
            theorem_vars,
            sort_vars,
            rule.args[fresh.target_arg_idx].sort_name,
            used_deps,
            reserved_deps,
        ) catch |err| {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .parse_fresh,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = rule.arg_names[fresh.target_arg_idx].?,
                .span = line.ruleApplicationSpan(),
            }, .theorem_application));
            return err;
        };
        bindings[fresh.target_arg_idx] = selection.expr_id;
        reserved_deps |= selection.deps;
    }
}

fn addFallbackFailureNote(
    diag: *Diagnostic,
    line_assertion: LineAssertion,
    line: ApplicationLine,
) void {
    switch (line_assertion) {
        .concrete, .implicit_whole_conclusion => {},
        .holey => |holey| {
            addStaticProofNoteSpan(
                diag,
                "fallback chain exhausted for holey assertion; " ++
                    "showing first candidate failure",
                firstHoleProofSpan(line, holey),
            );
        },
    }
}

fn concreteMatchFailureSpan(
    line: ApplicationLine,
    report: Holes.ConcreteMatchReport,
) ?Span {
    const failure = report.failure orelse return null;
    return switch (failure) {
        .hole_sort_mismatch => |mismatch| proofSpanForSourceSpan(
            line,
            mismatch.token_span,
        ),
        .visible_structure_mismatch => null,
    };
}

fn firstHoleProofSpan(line: ApplicationLine, expr: *const Expr) ?Span {
    return proofSpanForSourceSpan(line, Holes.firstHoleSourceSpan(expr));
}

fn proofSpanForSourceSpan(
    line: ApplicationLine,
    maybe_span: ?SourceSpan,
) ?Span {
    const span = maybe_span orelse return null;
    const inner_start = line.assertion_span.start + 1;
    return .{
        .start = inner_start + span.start,
        .end = inner_start + span.end,
    };
}

fn setHoleyInferenceDiagnostic(
    self: anytype,
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
    line: ApplicationLine,
    rule: *const RuleDecl,
    holey: *const Expr,
    err: anyerror,
    report: Holes.InferenceReport,
) !void {
    const failure = report.failure;
    const missing = if (failure) |actual| switch (actual) {
        .missing_binder => |info| info,
        else => null,
    } else null;

    const kind: CompilerDiag.DiagnosticKind = if (missing != null)
        .missing_binder_assignment
    else
        .inference_failed;
    const hole_span = firstHoleProofSpan(line, holey);
    const span = if (err == error.HoleyInferenceMismatch)
        hole_span orelse line.assertion_span
    else if (missing != null)
        hole_span orelse line.assertion_span
    else
        line.ruleApplicationSpan();
    const binder_name = if (missing) |info|
        info.name orelse "_"
    else
        null;
    var diag = CompilerDiag.withPhase(.{
        .kind = kind,
        .err = err,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .name = binder_name,
        .span = span,
        .detail = if (missing) |info| .{ .missing_binder_assignment = .{
            .binder_name = info.name orelse "_",
            .path = .holey_surface_match,
        } } else .{ .inference_failure = .{
            .path = .holey_surface_match,
            .first_unsolved_binder_name = null,
        } },
    }, .inference);
    try addHoleyInferenceNotes(allocator, &diag, rule, line, holey, report);
    CompilerDiag.setProof(self, diag);
}

fn addHoleyInferenceNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    rule: *const RuleDecl,
    line: ApplicationLine,
    holey: *const Expr,
    report: Holes.InferenceReport,
) !void {
    try addFormattedProofNote(
        allocator,
        diag,
        "inference path: {s}",
        .{CompilerDiag.inferencePathName(.holey_surface_match)},
    );
    const failure = report.failure orelse return;
    const hole_span = firstHoleProofSpan(line, holey);
    switch (failure) {
        .hypothesis_mismatch => addStaticProofNote(
            diag,
            "referenced hypotheses did not match the candidate rule",
        ),
        .visible_structure_mismatch => addStaticProofNoteSpan(
            diag,
            "visible structure in the holey assertion did not match " ++
                "the candidate conclusion",
            hole_span,
        ),
        .missing_binder => |info| {
            const name = info.name orelse "_";
            try addFormattedProofNoteSpan(
                allocator,
                diag,
                "holey assertion left binder {s} unsolved",
                .{name},
                hole_span,
            );
            if (info.index < rule.arg_names.len and rule.arg_names[info.index] == null) {
                try addFormattedProofNote(
                    allocator,
                    diag,
                    "unsolved binder index: {d}",
                    .{info.index + 1},
                );
            }
        },
    }
}

fn addHoleConcreteMatchNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    line: ApplicationLine,
    report: Holes.ConcreteMatchReport,
) !void {
    const failure = report.failure orelse return;
    switch (failure) {
        .visible_structure_mismatch => addStaticProofNote(
            diag,
            "visible structure in the holey assertion did not match " ++
                "the candidate conclusion",
        ),
        .hole_sort_mismatch => |mismatch| {
            try addFormattedProofNoteSpan(
                allocator,
                diag,
                "hole {s} expected sort {s} but matched {s}",
                .{
                    mismatch.token,
                    mismatch.expected_sort_name,
                    mismatch.actual_sort_name,
                },
                proofSpanForSourceSpan(line, mismatch.token_span),
            );
        },
    }
}

fn addComparisonSnapshotNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    actual: ExprId,
    attempted_normalized: bool,
) !void {
    const expected_text = try ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        expected,
    );
    defer allocator.free(expected_text);
    try addFormattedProofNote(
        allocator,
        diag,
        "expected: {s}",
        .{truncateSnapshot(expected_text)},
    );

    const actual_text = try ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        actual,
    );
    defer allocator.free(actual_text);
    try addFormattedProofNote(
        allocator,
        diag,
        "actual: {s}",
        .{truncateSnapshot(actual_text)},
    );

    if (!attempted_normalized) return;

    const snapshot = Normalize.maybeBuildComparisonSnapshotWithDebug(
        allocator,
        @constCast(theorem),
        registry,
        env,
        scratch,
        expected,
        actual,
        .none,
    );
    if (snapshot.normalized_expected == null and
        snapshot.normalized_actual == null)
    {
        return;
    }

    addStaticProofNote(diag, "attempted normalized comparison");
    if (snapshot.normalized_expected) |normalized_expected| {
        const normalized_expected_text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            normalized_expected,
        );
        defer allocator.free(normalized_expected_text);
        try addFormattedProofNote(
            allocator,
            diag,
            "normalized expected: {s}",
            .{truncateSnapshot(normalized_expected_text)},
        );
    }
    if (snapshot.normalized_actual) |normalized_actual| {
        const normalized_actual_text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            normalized_actual,
        );
        defer allocator.free(normalized_actual_text);
        try addFormattedProofNote(
            allocator,
            diag,
            "normalized actual: {s}",
            .{truncateSnapshot(normalized_actual_text)},
        );
    }
}

fn truncateSnapshot(text: []const u8) []const u8 {
    const limit = 64;
    if (text.len <= limit) return text;
    return text[0..limit];
}

fn addFreshenAttemptNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    rule: *const RuleDecl,
    report: CompilerFreshen.FreshenAttemptReport,
) !void {
    if (!report.attempted) return;

    const target_name = rule.arg_names[report.target_arg_idx] orelse "_";
    const blocker_name = rule.arg_names[report.blocker_arg_idx] orelse "_";
    try addFormattedProofNote(
        allocator,
        diag,
        "attempted @freshen for target binder {s}",
        .{target_name},
    );
    try addFormattedProofNote(
        allocator,
        diag,
        "freshen blocker binder: {s}",
        .{blocker_name},
    );
    if (report.replacement_name) |replacement_name| {
        try addFormattedProofNote(
            allocator,
            diag,
            "chosen replacement binder: {s}",
            .{replacement_name},
        );
    }
    if (report.blocker_dependency_remaining) |remaining| {
        if (remaining) {
            try addFormattedProofNote(
                allocator,
                diag,
                "rewritten target still depends on blocker binder {s}",
                .{blocker_name},
            );
        } else {
            try addFormattedProofNote(
                allocator,
                diag,
                "rewritten target no longer depends on blocker binder {s}",
                .{blocker_name},
            );
        }
    }
}

fn addBoundaryAttemptNotes(
    diag: *Diagnostic,
    report: TheoremBoundary.ReconciliationReport,
) void {
    if (report.attempted_transparent) {
        addStaticProofNote(diag, "attempted transparent final reconciliation");
    }
    if (report.attempted_normalized) {
        addStaticProofNote(diag, "attempted normalized final reconciliation");
    }
    if (report.attempted_alpha_cleanup) {
        addStaticProofNote(diag, "attempted alpha-cleanup final reconciliation");
    }
}

fn addStaticProofNote(diag: *Diagnostic, message: []const u8) void {
    addStaticProofNoteSpan(diag, message, null);
}

fn addStaticProofNoteSpan(
    diag: *Diagnostic,
    message: []const u8,
    span: ?Span,
) void {
    CompilerDiag.addNote(diag, message, .proof, span);
}

fn addFormattedProofNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    try addFormattedProofNoteSpan(allocator, diag, fmt, args, null);
}

fn addFormattedProofNoteSpan(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
    span: ?Span,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    CompilerDiag.addNote(diag, message, .proof, span);
}

fn refSpan(ref: Ref) Span {
    return switch (ref) {
        .hyp => |hyp| hyp.span,
        .line => |line| line.span,
        .application => |application| application.span,
    };
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}
