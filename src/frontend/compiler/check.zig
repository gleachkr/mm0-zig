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
const ViewDecl = CompilerViews.ViewDecl;
const FreshDecl = CompilerFresh.FreshDecl;
const CompilerDiag = @import("./diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Inference = @import("./inference.zig");
const Matching = @import("./check/matching.zig");
const Emit = @import("./emit.zig");
const CompilerVars = @import("./vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;

const NameExprMap = std.StringHashMap(*const Expr);
const LabelIndexMap = std.StringHashMap(usize);

pub fn checkTheoremBlock(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
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
        const line_expr = parseLineAssertion(
            parser,
            theorem,
            &theorem_vars,
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
        const rule_id = env.getRuleId(line.rule_name) orelse {
            CompilerDiag.setProof(self, .{
                .kind = .unknown_rule,
                .err = error.UnknownRule,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.rule_span,
            });
            return error.UnknownRule;
        };
        const rule = &env.rules.items[rule_id];
        if (line.refs.len != rule.hyps.len) {
            CompilerDiag.setProof(self, .{
                .kind = .ref_count_mismatch,
                .err = error.RefCountMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.refsOrRuleSpan(),
            });
            return error.RefCountMismatch;
        }

        const refs = try allocator.alloc(CheckedRef, line.refs.len);
        const ref_exprs = try allocator.alloc(ExprId, line.refs.len);
        for (line.refs, 0..) |ref, idx| {
            ref_exprs[idx] = switch (ref) {
                .hyp => |hyp| blk: {
                    if (hyp.index == 0 or
                        hyp.index > theorem.theorem_hyps.items.len)
                    {
                        CompilerDiag.setProof(self, .{
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
                        });
                        return error.UnknownHypothesisRef;
                    }
                    refs[idx] = .{ .hyp = hyp.index - 1 };
                    break :blk theorem.theorem_hyps.items[hyp.index - 1];
                },
                .line => |label| blk: {
                    const line_idx = labels.get(label.label) orelse {
                        CompilerDiag.setProof(self, .{
                            .kind = .unknown_label,
                            .err = error.UnknownLabel,
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .name = label.label,
                            .span = label.span,
                        });
                        return error.UnknownLabel;
                    };
                    refs[idx] = .{ .line = line_idx };
                    break :blk checked.items[line_idx].expr;
                },
            };
        }

        const partial_bindings = try parseBindings(
            self,
            allocator,
            parser,
            theorem,
            &theorem_vars,
            sort_vars,
            assertion.name,
            rule,
            line,
        );
        if (fresh_bindings.get(rule_id)) |rule_fresh| {
            try applyFreshBindings(
                self,
                parser,
                env,
                theorem,
                &theorem_vars,
                sort_vars,
                assertion.name,
                rule,
                line,
                line_expr,
                ref_exprs,
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
                    ref_exprs,
                    partial_bindings,
                    null,
                    null,
                    self.debug.views,
                ) catch |err| {
                    CompilerDiag.setProof(self, .{
                        .kind = .generic,
                        .err = err,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .rule_name = line.rule_name,
                        .span = line.ruleApplicationSpan(),
                    });
                    return err;
                };
            }
        }

        const fresh_context: Inference.HiddenWitnessFreshContext = .{
            .parser = parser,
            .theorem_vars = &theorem_vars,
            .sort_vars = sort_vars,
        };

        const bindings = if (had_omitted) blk: {
            break :blk try Inference.inferBindings(
                self,
                allocator,
                env,
                registry,
                &diag_scratch,
                theorem,
                assertion,
                rule,
                line,
                partial_bindings,
                ref_exprs,
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
        if (!had_omitted) {
            try Inference.validateResolvedBindings(
                self,
                env,
                theorem,
                assertion,
                line,
                rule,
                bindings,
            );
        }

        const norm_spec = registry.getNormalizeSpec(rule_id);

        for (ref_exprs, line.refs, 0..) |actual, ref, idx| {
            const expected = try theorem.instantiateTemplate(
                rule.hyps[idx],
                bindings,
            );
            const match_mark = diag_scratch.mark();
            if (Matching.tryMatchHypothesis(
                allocator,
                theorem,
                registry,
                env,
                &checked,
                &diag_scratch,
                norm_spec,
                idx,
                refs[idx],
                actual,
                expected,
            ) catch |err| {
                if (CompilerDiag.setProofScratchDiagnosticIfPresent(
                    self,
                    &diag_scratch,
                    match_mark,
                    env,
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
            CompilerDiag.setProof(self, switch (ref) {
                .hyp => |hyp| Diagnostic{
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
                },
                .line => |label| Diagnostic{
                    .kind = .hypothesis_mismatch,
                    .err = error.HypothesisMismatch,
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = line.rule_name,
                    .name = label.label,
                    .span = span,
                },
            });
            return error.HypothesisMismatch;
        }

        const expected_line = try theorem.instantiateTemplate(
            rule.concl,
            bindings,
        );

        const concl_mark = diag_scratch.mark();
        const line_idx = (Matching.tryBuildConclusionLine(
            allocator,
            theorem,
            registry,
            env,
            &checked,
            &diag_scratch,
            norm_spec,
            line_expr,
            expected_line,
            rule_id,
            bindings,
            refs,
        ) catch |err| {
            if (CompilerDiag.setProofScratchDiagnosticIfPresent(
                self,
                &diag_scratch,
                concl_mark,
                env,
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
            CompilerDiag.setProof(self, .{
                .kind = .conclusion_mismatch,
                .err = error.ConclusionMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.assertion.span,
            });
            return error.ConclusionMismatch;
        };
        diag_scratch.discard(concl_mark);

        const gop = try labels.getOrPut(line.label);
        if (gop.found_existing) {
            CompilerDiag.setProof(self, .{
                .kind = .duplicate_label,
                .err = error.DuplicateLabel,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .name = line.label,
                .span = line.label_span,
            });
            return error.DuplicateLabel;
        }
        gop.value_ptr.* = line_idx;
        last_line = checked.items[line_idx].expr;
        last_line_idx = line_idx;
        last_label = line.label;
        last_span = line.assertion.span;
    }

    const final_line = last_line orelse {
        CompilerDiag.setProof(self, .{
            .kind = .empty_proof_block,
            .err = error.EmptyProofBlock,
            .theorem_name = assertion.name,
            .block_name = block.name,
            .span = block.name_span,
        });
        return error.EmptyProofBlock;
    };
    if (final_line != theorem_concl) {
        if (last_line_idx) |line_idx| {
            const final_mark = diag_scratch.mark();
            if ((Matching.tryMatchFinalLine(
                allocator,
                theorem,
                registry,
                env,
                &checked,
                &diag_scratch,
                theorem_concl,
                final_line,
                line_idx,
            ) catch |err| {
                if (CompilerDiag.setProofScratchDiagnosticIfPresent(
                    self,
                    &diag_scratch,
                    final_mark,
                    env,
                    .generic,
                    err,
                    assertion.name,
                    last_label,
                    null,
                    last_span,
                )) {
                    return err;
                }
                diag_scratch.discard(final_mark);
                return err;
            })) {
                diag_scratch.discard(final_mark);
                return try checked.toOwnedSlice(allocator);
            }
            diag_scratch.discard(final_mark);
        }
        CompilerDiag.setProof(self, .{
            .kind = .final_line_mismatch,
            .err = error.FinalLineMismatch,
            .theorem_name = assertion.name,
            .line_label = last_label,
            .span = last_span,
        });
        return error.FinalLineMismatch;
    }
    return try checked.toOwnedSlice(allocator);
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
            CompilerDiag.setProof(self, .{
                .kind = .generic,
                .err = error.UnnamedRuleBinder,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.ruleApplicationSpan(),
            });
            return error.UnnamedRuleBinder;
        }
    }

    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    for (line.arg_bindings) |binding| {
        const arg_index = findRuleArgIndex(rule, binding.name) orelse {
            CompilerDiag.setProof(self, .{
                .kind = .unknown_binder_name,
                .err = error.UnknownBinderName,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = binding.name,
                .span = binding.span,
            });
            return error.UnknownBinderName;
        };
        if (bindings[arg_index] != null) {
            CompilerDiag.setProof(self, .{
                .kind = .duplicate_binder_assignment,
                .err = error.DuplicateBinderAssignment,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = binding.name,
                .span = binding.span,
            });
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
            CompilerDiag.setProof(self, .{
                .kind = .parse_fresh,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[fresh.target_arg_idx].?,
                .span = line.ruleApplicationSpan(),
            });
            return err;
        };
        bindings[fresh.target_arg_idx] = selection.expr_id;
        reserved_deps |= selection.deps;
    }
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
