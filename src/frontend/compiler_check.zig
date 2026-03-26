const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const Expr = @import("../trusted/expressions.zig").Expr;
const ProofLine = @import("./proof_script.zig").ProofLine;
const Span = @import("./proof_script.zig").Span;
const TheoremBlock = @import("./proof_script.zig").TheoremBlock;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const NormalizeSpec = @import("./rewrite_registry.zig").NormalizeSpec;
const CompilerViews = @import("./compiler_views.zig");
const CompilerDummies = @import("./compiler_dummies.zig");
const ViewDecl = CompilerViews.ViewDecl;
const DummyDecl = CompilerDummies.DummyDecl;
const CompilerDiag = @import("./compiler_diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedLine = @import("./compiler.zig").CheckedLine;
const CheckedRef = @import("./compiler.zig").CheckedRef;
const appendRuleLine = @import("./compiler.zig").appendRuleLine;
const appendTransportLine = @import("./compiler.zig").appendTransportLine;
const Inference = @import("./compiler_inference.zig");
const Normalize = @import("./compiler_normalize.zig");
const Emit = @import("./compiler_emit.zig");

const NameExprMap = std.StringHashMap(*const Expr);
const LabelIndexMap = std.StringHashMap(usize);

fn tryMatchHypothesis(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    norm_spec: ?NormalizeSpec,
    hyp_idx: usize,
    actual_ref: CheckedRef,
    actual: ExprId,
    expected: ExprId,
) !?CheckedRef {
    if (actual == expected) return actual_ref;

    if (try Inference.canConvertByDefOpening(
        allocator,
        theorem,
        env,
        expected,
        actual,
    )) {
        return .{ .line = try appendTransportLine(
            checked,
            allocator,
            expected,
            actual,
            actual_ref,
        ) };
    }

    _ = norm_spec;
    _ = hyp_idx;

    if (try Normalize.buildNormalizedConversion(
        allocator,
        theorem,
        registry,
        env,
        checked,
        actual,
        expected,
    )) |conversion| {
        var conversion_mut = conversion;
        if (conversion_mut.conv_line_idx) |conv_line_idx| {
            return .{ .line = try conversion_mut.normalizer.emitTransport(
                conversion_mut.relation,
                expected,
                actual,
                conv_line_idx,
                actual_ref,
            ) };
        }
        return actual_ref;
    }

    return try Normalize.buildDefAwareNormalizedHypRef(
        allocator,
        theorem,
        registry,
        env,
        checked,
        actual_ref,
        actual,
        expected,
    );
}

fn tryBuildConclusionLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    norm_spec: ?NormalizeSpec,
    line_expr: ExprId,
    expected_line: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !?usize {
    if (line_expr == expected_line) {
        return try appendRuleLine(
            checked,
            allocator,
            line_expr,
            rule_id,
            bindings,
            refs,
        );
    }

    if (try Inference.canConvertByDefOpening(
        allocator,
        theorem,
        env,
        line_expr,
        expected_line,
    )) {
        const raw_idx = try appendRuleLine(
            checked,
            allocator,
            expected_line,
            rule_id,
            bindings,
            refs,
        );
        return try appendTransportLine(
            checked,
            allocator,
            line_expr,
            expected_line,
            .{ .line = raw_idx },
        );
    }

    if (norm_spec) |spec| {
        if (spec.concl) {
            if (try Normalize.buildNormalizedConversion(
                allocator,
                theorem,
                registry,
                env,
                checked,
                expected_line,
                line_expr,
            )) |conversion| {
                var conversion_mut = conversion;
                const raw_idx = try appendRuleLine(
                    checked,
                    allocator,
                    expected_line,
                    rule_id,
                    bindings,
                    refs,
                );

                return if (conversion_mut.conv_line_idx) |conv_idx|
                    try conversion_mut.normalizer.emitTransport(
                        conversion_mut.relation,
                        line_expr,
                        expected_line,
                        conv_idx,
                        .{ .line = raw_idx },
                    )
                else
                    raw_idx;
            }
            return try Normalize.buildDefAwareNormalizedConclusionLine(
                allocator,
                theorem,
                registry,
                env,
                checked,
                line_expr,
                expected_line,
                rule_id,
                bindings,
                refs,
            );
        }
    }

    return null;
}

fn tryMatchFinalLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem_concl: ExprId,
    final_line: ExprId,
    line_idx: usize,
) !bool {
    if (try Inference.canConvertByDefOpening(
        allocator,
        theorem,
        env,
        theorem_concl,
        final_line,
    )) {
        _ = try appendTransportLine(
            checked,
            allocator,
            theorem_concl,
            final_line,
            .{ .line = line_idx },
        );
        return true;
    }

    if (try Normalize.buildNormalizedConversion(
        allocator,
        theorem,
        registry,
        env,
        checked,
        final_line,
        theorem_concl,
    )) |conversion| {
        var conversion_mut = conversion;
        if (conversion_mut.conv_line_idx) |conv_idx| {
            _ = try conversion_mut.normalizer.emitTransport(
                conversion_mut.relation,
                theorem_concl,
                final_line,
                conv_idx,
                .{ .line = line_idx },
            );
            return true;
        }
    }

    return false;
}

pub fn checkTheoremBlock(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    dummies: *const std.AutoHashMap(u32, []const DummyDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
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
    var last_line: ?ExprId = null;
    var last_line_idx: ?usize = null;
    var last_label: ?[]const u8 = null;
    var last_span: ?Span = null;

    for (block.lines) |line| {
        const line_expr = parseLineAssertion(
            parser,
            theorem,
            &theorem_vars,
            line,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .parse_assertion,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .span = line.assertion.span,
            });
            return err;
        };
        const rule_id = env.getRuleId(line.rule_name) orelse {
            self.setDiagnostic(.{
                .kind = .unknown_rule,
                .err = error.UnknownRule,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return error.UnknownRule;
        };
        const rule = &env.rules.items[rule_id];
        if (line.refs.len != rule.hyps.len) {
            self.setDiagnostic(.{
                .kind = .ref_count_mismatch,
                .err = error.RefCountMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
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
                        const hyp_name = try Emit.hypText(allocator, hyp.index);
                        self.setDiagnostic(.{
                            .kind = .unknown_hypothesis_ref,
                            .err = error.UnknownHypothesisRef,
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .name = hyp_name,
                            .span = hyp.span,
                        });
                        return error.UnknownHypothesisRef;
                    }
                    refs[idx] = .{ .hyp = hyp.index - 1 };
                    break :blk theorem.theorem_hyps.items[hyp.index - 1];
                },
                .line => |label| blk: {
                    const line_idx = labels.get(label.label) orelse {
                        self.setDiagnostic(.{
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
            assertion.name,
            rule,
            line,
        );
        if (dummies.get(rule_id)) |rule_dummies| {
            try applyDummyBindings(
                self,
                parser,
                theorem,
                assertion.name,
                rule,
                line,
                partial_bindings,
                rule_dummies,
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
                    &view,
                    line_expr,
                    ref_exprs,
                    partial_bindings,
                ) catch |err| {
                    self.setDiagnostic(.{
                        .kind = .generic,
                        .err = err,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .rule_name = line.rule_name,
                        .span = line.span,
                    });
                    return err;
                };
            }
        }

        const bindings = if (had_omitted)
            try Inference.inferBindings(
                self,
                allocator,
                env,
                registry,
                theorem,
                assertion,
                rule,
                line,
                partial_bindings,
                ref_exprs,
                line_expr,
                maybe_view,
                use_advanced_inference,
            )
        else
            try Inference.requireConcreteBindings(
                allocator,
                partial_bindings,
            );
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

        // Check hypotheses (with optional normalization)
        for (ref_exprs, line.refs, 0..) |actual, ref, idx| {
            const expected = try theorem.instantiateTemplate(
                rule.hyps[idx],
                bindings,
            );
            if (try tryMatchHypothesis(
                allocator,
                theorem,
                registry,
                env,
                &checked,
                norm_spec,
                idx,
                refs[idx],
                actual,
                expected,
            )) |matched_ref| {
                refs[idx] = matched_ref;
                continue;
            }

            const name = switch (ref) {
                .hyp => |hyp| try Emit.hypText(allocator, hyp.index),
                .line => |label| label.label,
            };
            const span = switch (ref) {
                .hyp => |hyp| hyp.span,
                .line => |label| label.span,
            };
            self.setDiagnostic(.{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = name,
                .span = span,
            });
            return error.HypothesisMismatch;
        }

        const expected_line = try theorem.instantiateTemplate(
            rule.concl,
            bindings,
        );

        const line_idx = try tryBuildConclusionLine(
            allocator,
            theorem,
            registry,
            env,
            &checked,
            norm_spec,
            line_expr,
            expected_line,
            rule_id,
            bindings,
            refs,
        ) orelse {
            self.setDiagnostic(.{
                .kind = .conclusion_mismatch,
                .err = error.ConclusionMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.assertion.span,
            });
            return error.ConclusionMismatch;
        };

        const gop = try labels.getOrPut(line.label);
        if (gop.found_existing) {
            self.setDiagnostic(.{
                .kind = .duplicate_label,
                .err = error.DuplicateLabel,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .name = line.label,
                .span = line.span,
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
        self.setDiagnostic(.{
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
            if (try tryMatchFinalLine(
                allocator,
                theorem,
                registry,
                env,
                &checked,
                theorem_concl,
                final_line,
                line_idx,
            )) {
                return try checked.toOwnedSlice(allocator);
            }
        }
        self.setDiagnostic(.{
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
    theorem_vars: *const NameExprMap,
    line: ProofLine,
) !ExprId {
    const expr = try parser.parseFormulaText(line.assertion.text, theorem_vars);
    return try theorem.internParsedExpr(expr);
}

fn parseBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ProofLine,
) ![]?ExprId {
    for (rule.arg_names) |arg_name| {
        if (arg_name == null) {
            self.setDiagnostic(.{
                .kind = .generic,
                .err = error.UnnamedRuleBinder,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return error.UnnamedRuleBinder;
        }
    }

    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    for (line.arg_bindings) |binding| {
        const arg_index = findRuleArgIndex(rule, binding.name) orelse {
            self.setDiagnostic(.{
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
            self.setDiagnostic(.{
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

        const expr = parser.parseArgText(
            binding.formula.text,
            theorem_vars,
            rule.args[arg_index],
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .parse_binding,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = binding.name,
                .span = binding.formula.span,
            });
            return err;
        };
        bindings[arg_index] = try theorem.internParsedExpr(expr);
    }

    return bindings;
}

fn applyDummyBindings(
    self: anytype,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ProofLine,
    bindings: []?ExprId,
    dummies_list: []const DummyDecl,
) !void {
    for (dummies_list) |dummy| {
        if (bindings[dummy.target_arg_idx] != null) continue;
        bindings[dummy.target_arg_idx] = theorem.addDummyVar(
            parser,
            rule.args[dummy.target_arg_idx],
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .parse_dummy,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[dummy.target_arg_idx].?,
                .span = line.span,
            });
            return err;
        };
    }
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}
