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
const Span = @import("../proof_script.zig").Span;
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

        const base_refs = try allocator.alloc(CheckedRef, line.refs.len);
        defer allocator.free(base_refs);
        const base_ref_exprs = try allocator.alloc(ExprId, line.refs.len);
        defer allocator.free(base_ref_exprs);
        try resolveBaseRefs(
            self,
            theorem,
            assertion,
            line,
            &labels,
            checked.items,
            base_refs,
            base_ref_exprs,
        );

        const initial_rule_id = try lookupRuleId(
            self,
            env,
            rule_catalog,
            assertion,
            line,
        );

        const parsed_line = try parseProofLineAssertion(
            self,
            parser,
            theorem,
            &theorem_vars,
            sort_vars,
            assertion,
            line,
        );

        const saved_diag = getDiagnostic(self);

        if (registry.getFallbackRule(initial_rule_id) == null) {
            const checked_mark = checked.items.len;
            const attempt = try tryApplyLineWithCandidate(
                self,
                allocator,
                parser,
                env,
                registry,
                fresh_bindings,
                freshen_bindings,
                views,
                sort_vars,
                assertion,
                line,
                parsed_line,
                initial_rule_id,
                theorem,
                &theorem_vars,
                base_refs,
                base_ref_exprs,
                &checked,
                &diag_scratch,
                &rule_unify_cache,
            );

            try validateAttemptCheckedIrRange(
                self,
                env,
                theorem,
                assertion.name,
                checked.items[checked_mark..],
                line.label,
                line.span,
                .theorem_application,
                saved_diag,
            );

            restoreDiagnostic(self, saved_diag);
            try labels.put(line.label, attempt.line_idx);
            last_line = checked.items[attempt.line_idx].expr;
            last_line_idx = attempt.line_idx;
            last_label = line.label;
            last_span = line.span;
            continue;
        }

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
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = line.rule_name,
                    .span = line.rule_span,
                }, .theorem_application));
                return error.FallbackCycle;
            }

            restoreDiagnostic(self, null);
            const checked_mark = checked.items.len;
            var attempt_theorem = try theorem.clone();
            var attempt_theorem_vars = cloneNameExprMap(
                allocator,
                &theorem_vars,
            ) catch |err| {
                attempt_theorem.deinit();
                return err;
            };

            var attempt = tryApplyLineWithCandidate(
                self,
                allocator,
                parser,
                env,
                registry,
                fresh_bindings,
                freshen_bindings,
                views,
                sort_vars,
                assertion,
                line,
                parsed_line,
                candidate_rule_id,
                &attempt_theorem,
                &attempt_theorem_vars,
                base_refs,
                base_ref_exprs,
                &checked,
                &diag_scratch,
                &rule_unify_cache,
            ) catch |err| {
                CheckedIr.rollbackToMark(
                    allocator,
                    &checked,
                    checked_mark,
                );
                attempt_theorem_vars.deinit();
                attempt_theorem.deinit();
                if (first_err == null) {
                    first_err = err;
                    first_diag = getDiagnostic(self);
                }
                restoreDiagnostic(self, null);
                candidate_rule_id = registry.getFallbackRule(
                    candidate_rule_id,
                ) orelse {
                    var diag = first_diag orelse saved_diag;
                    if (first_diag != null) {
                        if (diag) |*actual_diag| {
                            try addFallbackFailureNote(
                                allocator,
                                actual_diag,
                                parsed_line,
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
                env,
                &attempt.theorem,
                assertion.name,
                checked.items[checked_mark..],
                line.label,
                line.span,
                .theorem_application,
                saved_diag,
            ) catch |err| {
                CheckedIr.rollbackToMark(
                    allocator,
                    &checked,
                    checked_mark,
                );
                attempt.theorem_vars.deinit();
                attempt.theorem.deinit();
                return err;
            };

            var old_theorem = theorem.*;
            theorem.* = attempt.theorem;
            old_theorem.deinit();
            theorem_vars.deinit();
            theorem_vars = attempt.theorem_vars;
            restoreDiagnostic(self, saved_diag);

            try labels.put(line.label, attempt.line_idx);
            last_line = checked.items[attempt.line_idx].expr;
            last_line_idx = attempt.line_idx;
            last_label = line.label;
            last_span = line.span;
            break;
        }
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
            line.rule_name,
            null,
            line.assertion.span,
        ));
        return err;
    };
}

fn tryApplyLineWithCandidate(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    line: ProofLine,
    parsed_line: Holes.ParsedAssertion,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    base_refs: []const CheckedRef,
    base_ref_exprs: []const ExprId,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
) !SuccessfulLineAttempt {
    const line_assertion = LineAssertion.fromParsed(parsed_line);

    const rule = &env.rules.items[rule_id];
    if (line.refs.len != rule.hyps.len) {
        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
            .kind = .ref_count_mismatch,
            .err = error.RefCountMismatch,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.refsOrRuleSpan(),
        }, .theorem_application));
        return error.RefCountMismatch;
    }

    const refs = try allocator.dupe(CheckedRef, base_refs);

    const partial_bindings = try parseBindings(
        self,
        allocator,
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        assertion.name,
        rule,
        line,
    );
    defer allocator.free(partial_bindings);

    // Keep the user's explicit bindings separate from @fresh selections.
    // applyFreshBindings mutates partial_bindings in-place, and later
    // hole-filled validation must still know which @fresh targets were
    // generated automatically rather than written by the user.
    const explicit_bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(explicit_bindings);

    if (fresh_bindings.get(rule_id)) |rule_fresh| {
        try applyFreshBindings(
            self,
            parser,
            env,
            theorem,
            theorem_vars,
            sort_vars,
            assertion.name,
            rule,
            line,
            try lineAssertionKnownDeps(env, theorem, line_assertion),
            base_ref_exprs,
            partial_bindings,
            rule_fresh,
        );
    }
    const maybe_view = views.get(rule_id);
    const had_omitted = Inference.hasOmittedBindings(partial_bindings);
    const rule_has_advanced_inference =
        Inference.shouldUseAdvancedInference(rule_id, maybe_view, registry);
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
                        base_ref_exprs,
                        partial_bindings,
                        null,
                        null,
                        self.debug.views,
                    ) catch |err| {
                        CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                            .kind = .generic,
                            .err = err,
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .rule_name = line.rule_name,
                            .span = line.ruleApplicationSpan(),
                        }, .theorem_application));
                        return err;
                    };
                },
                .holey => {},
            }
        }
    }

    const fresh_context: Inference.HiddenWitnessFreshContext = .{
        .parser = parser,
        .theorem_vars = theorem_vars,
        .sort_vars = sort_vars,
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
        line,
        line_assertion,
        partial_bindings,
        base_ref_exprs,
        fresh_context,
        maybe_view,
        had_omitted,
        rule_has_advanced_inference,
        use_advanced_inference,
        rule_unify_cache,
    );

    const norm_spec = registry.getNormalizeSpec(rule_id);

    var resolved_bindings = bindings;
    var freshened_bindings: ?CompilerFreshen.FreshenResult = null;
    Inference.validateResolvedBindingsWithDebug(
        self,
        self.debug,
        env,
        theorem,
        assertion,
        line,
        rule,
        resolved_bindings,
    ) catch |err| {
        if (err != error.DepViolation) return err;
        const rule_freshen = freshen_bindings.get(rule_id) orelse return err;
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
            sort_vars,
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
                line,
                norm_spec,
                rule,
                line_assertion,
                resolved_bindings,
            ),
            base_ref_exprs,
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
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
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
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
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
            line,
            rule,
            resolved_bindings,
        );
    };
    restoreDiagnostic(self, null);

    if (freshened_bindings) |freshened| {
        if (fresh_bindings.get(rule_id)) |rule_fresh| {
            try validateFreshBindingsAgainstLine(
                self,
                allocator,
                env,
                theorem,
                assertion.name,
                rule,
                line,
                try resolveLineAssertionForBindings(
                    self,
                    allocator,
                    parser,
                    theorem,
                    env,
                    registry,
                    diag_scratch,
                    assertion,
                    line,
                    norm_spec,
                    rule,
                    line_assertion,
                    bindings,
                ),
                base_ref_exprs,
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
            norm_spec,
            try resolveLineAssertionForBindings(
                self,
                allocator,
                parser,
                theorem,
                env,
                registry,
                diag_scratch,
                assertion,
                line,
                norm_spec,
                rule,
                line_assertion,
                bindings,
            ),
            rule,
            rule_id,
            bindings,
            freshened,
            refs,
            base_ref_exprs,
        ) catch |err| {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
            }, .theorem_application));
            return err;
        };
        return .{
            .line_idx = line_idx,
            .theorem = theorem.*,
            .theorem_vars = theorem_vars.*,
        };
    }

    for (base_ref_exprs, line.refs, 0..) |actual, ref, idx| {
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
            norm_spec,
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
                line.label,
                line.rule_name,
                refSpan(line.refs[idx]),
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
        };
        var diag = switch (ref) {
            .hyp => |hyp| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
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
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = label.label,
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
            if (norm_spec) |spec|
                Normalize.isHypMarkedForNormalize(spec, idx)
            else
                false,
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
        line,
        norm_spec,
        rule,
        line_assertion,
        resolved_bindings,
    );

    if (fresh_bindings.get(rule_id)) |rule_fresh| {
        try validateFreshBindingsAgainstLine(
            self,
            allocator,
            env,
            theorem,
            assertion.name,
            rule,
            line,
            candidate.displayed_conclusion,
            base_ref_exprs,
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
        norm_spec,
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
            line.label,
            line.rule_name,
            line.assertion.span,
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
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.assertion.span,
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
            if (norm_spec) |spec| spec.concl else false,
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
    line: ProofLine,
    norm_spec: ?@import("../rewrite_registry.zig").NormalizeSpec,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    bindings: []const ExprId,
) !ExprId {
    return switch (line_assertion) {
        .concrete => |line_expr| line_expr,
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
                norm_spec,
                holey,
                expected_line,
            );
        },
    };
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
    line: ProofLine,
    line_assertion: LineAssertion,
    partial_bindings: []const ?ExprId,
    base_ref_exprs: []const ExprId,
    fresh_context: Inference.HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    had_omitted: bool,
    rule_has_advanced_inference: bool,
    use_advanced_inference: bool,
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
            if (had_omitted and !has_structural_hole) {
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

fn elaborateCandidateLine(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ProofLine,
    norm_spec: ?@import("../rewrite_registry.zig").NormalizeSpec,
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
            norm_spec,
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
    line: ProofLine,
    norm_spec: ?@import("../rewrite_registry.zig").NormalizeSpec,
    holey: *const Expr,
    expected_line: ExprId,
) !ExprId {
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

    if (norm_spec) |spec| {
        if (spec.concl) {
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
    }

    var diag = CompilerDiag.withPhase(.{
        .kind = .conclusion_mismatch,
        .err = error.HoleConclusionMismatch,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.rule_name,
        .span = concreteMatchFailureSpan(line, hole_report) orelse
            line.assertion.span,
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
    norm_spec: ?@import("../rewrite_registry.zig").NormalizeSpec,
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
            norm_spec,
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
            norm_spec,
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

fn lookupRuleId(
    self: anytype,
    env: *const GlobalEnv,
    rule_catalog: *const RuleCatalog.Catalog,
    assertion: AssertionStmt,
    line: ProofLine,
) !u32 {
    if (env.getRuleId(line.rule_name)) |rule_id| return rule_id;

    if (rule_catalog.get(line.rule_name)) |entry| {
        if (entry.ordinal >= env.rules.items.len) {
            var diag: Diagnostic = .{
                .kind = .rule_not_yet_available,
                .err = error.RuleNotYetAvailable,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.rule_span,
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
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.rule_name,
        .span = line.rule_span,
    }, .theorem_application));
    return error.UnknownRule;
}

fn resolveBaseRefs(
    self: anytype,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: ProofLine,
    labels: *const LabelIndexMap,
    checked: []const CheckedLine,
    refs: []CheckedRef,
    ref_exprs: []ExprId,
) !void {
    for (line.refs, 0..) |ref, idx| {
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
                const line_idx = labels.get(label.label) orelse {
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
                break :blk checked[line_idx].expr;
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
    line: ProofLine,
) ![]?ExprId {
    for (rule.arg_names) |arg_name| {
        if (arg_name == null) {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.UnnamedRuleBinder,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
            }, .theorem_application));
            return error.UnnamedRuleBinder;
        }
    }

    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    for (line.arg_bindings) |binding| {
        const arg_index = findRuleArgIndex(rule, binding.name) orelse {
            CompilerDiag.setProof(self, CompilerDiag.withPhase(.{
                .kind = .unknown_binder_name,
                .err = error.UnknownBinderName,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
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
                .rule_name = line.rule_name,
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
                line.rule_name,
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
    line_assertion: LineAssertion,
) !u55 {
    return switch (line_assertion) {
        .concrete => |expr_id| (try Inference.exprInfo(
            env,
            theorem,
            theorem.arg_infos,
            expr_id,
        )).deps,
        .holey => |expr| expr.deps(),
    };
}

fn validateFreshBindingsAgainstLine(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ProofLine,
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
            .rule_name = line.rule_name,
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
    line: ProofLine,
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
                .rule_name = line.rule_name,
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
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    parsed_line: Holes.ParsedAssertion,
    line: ProofLine,
) !void {
    _ = allocator;
    switch (parsed_line) {
        .concrete => {},
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
    line: ProofLine,
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

fn firstHoleProofSpan(line: ProofLine, expr: *const Expr) ?Span {
    return proofSpanForSourceSpan(line, Holes.firstHoleSourceSpan(expr));
}

fn proofSpanForSourceSpan(
    line: ProofLine,
    maybe_span: ?SourceSpan,
) ?Span {
    const span = maybe_span orelse return null;
    const inner_start = line.assertion.span.start + 1;
    return .{
        .start = inner_start + span.start,
        .end = inner_start + span.end,
    };
}

fn setHoleyInferenceDiagnostic(
    self: anytype,
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
    line: ProofLine,
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
        hole_span orelse line.assertion.span
    else if (missing != null)
        hole_span orelse line.assertion.span
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
        .rule_name = line.rule_name,
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
    line: ProofLine,
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
    line: ProofLine,
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

    addStaticProofNote(diag, "attempted normalized comparison");
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
