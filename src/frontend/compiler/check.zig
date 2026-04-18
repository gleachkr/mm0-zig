const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const Expr = @import("../../trusted/expressions.zig").Expr;
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

const NameExprMap = std.StringHashMap(*const Expr);
const LabelIndexMap = std.StringHashMap(usize);

const SuccessfulLineAttempt = struct {
    line_idx: usize,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,
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

            const attempt = tryApplyLineWithCandidate(
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
                candidate_rule_id,
                &attempt_theorem,
                &attempt_theorem_vars,
                base_refs,
                base_ref_exprs,
                &checked,
                &diag_scratch,
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
                    restoreDiagnostic(self, first_diag orelse saved_diag);
                    return first_err.?;
                };
                continue;
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
            last_span = line.assertion.span;
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
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    base_refs: []const CheckedRef,
    base_ref_exprs: []const ExprId,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
) !SuccessfulLineAttempt {
    const line_expr = parseLineAssertion(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        line,
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
            line_expr,
            base_ref_exprs,
            partial_bindings,
            rule_fresh,
        );
    }
    const maybe_view = views.get(rule_id);
    const had_omitted = Inference.hasOmittedBindings(partial_bindings);
    const use_advanced_inference = had_omitted and
        Inference.shouldUseAdvancedInference(rule_id, maybe_view, registry);

    if (maybe_view) |view| {
        if (!use_advanced_inference) {
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
        }
    }

    const fresh_context: Inference.HiddenWitnessFreshContext = .{
        .parser = parser,
        .theorem_vars = theorem_vars,
        .sort_vars = sort_vars,
    };

    const bindings = if (had_omitted) blk: {
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
        );
    } else blk: {
        const b = try Inference.requireConcreteBindings(
            allocator,
            partial_bindings,
        );
        break :blk b;
    };

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
            line_expr,
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

    const norm_spec = registry.getNormalizeSpec(rule_id);

    if (freshened_bindings) |freshened| {
        const line_idx = applyFreshenedRuleLine(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            norm_spec,
            line_expr,
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

    const expected_line = try theorem.instantiateTemplate(
        rule.concl,
        resolved_bindings,
    );

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
        line_expr,
        expected_line,
        rule_id,
        resolved_bindings,
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
            expected_line,
            line_expr,
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

fn parseLineAssertion(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    line: ProofLine,
) !ExprId {
    try CompilerVars.ensureMathTextVars(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        line.assertion.text,
    );
    const expr = try parser.parseFormulaText(line.assertion.text, theorem_vars);
    return try theorem.internParsedExpr(expr);
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
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    bindings: []?ExprId,
    fresh_list: []const FreshDecl,
) !void {
    const used_deps = try CompilerFresh.collectUsedDeps(
        env,
        theorem,
        line_expr,
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
    CompilerDiag.addNote(diag, message, .proof, null);
}

fn addFormattedProofNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    CompilerDiag.addNote(diag, message, .proof, null);
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
