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
const CompilerViews = @import("./compiler_views.zig");
const CompilerFresh = @import("./compiler_fresh.zig");
const ViewDecl = CompilerViews.ViewDecl;
const FreshDecl = CompilerFresh.FreshDecl;
const CompilerDiag = @import("./compiler_diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedIr = @import("./compiler/checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Inference = @import("./compiler_inference.zig");
const Matching = @import("./compiler_check/matching.zig");
const Emit = @import("./compiler_emit.zig");
const CompilerVars = @import("./compiler_vars.zig");
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
                    self.debug.views,
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

        const bindings = if (had_omitted) blk: {
            break :blk try Inference.inferBindings(
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
            if (try Matching.tryMatchHypothesis(
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

        const line_idx = try Matching.tryBuildConclusionLine(
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
            if (try Matching.tryMatchFinalLine(
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
    const used_deps = try collectUsedDeps(
        env,
        theorem,
        line_expr,
        ref_exprs,
        bindings,
    );
    var reserved_deps: u55 = 0;

    for (fresh_list) |fresh| {
        if (bindings[fresh.target_arg_idx] != null) continue;

        const selection = chooseFreshBinding(
            parser,
            theorem,
            theorem_vars,
            sort_vars,
            rule.args[fresh.target_arg_idx].sort_name,
            used_deps,
            reserved_deps,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .parse_fresh,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[fresh.target_arg_idx].?,
                .span = line.span,
            });
            return err;
        };
        bindings[fresh.target_arg_idx] = selection.expr_id;
        reserved_deps |= selection.deps;
    }
}

const FreshSelection = struct {
    expr_id: ExprId,
    deps: u55,
};

fn chooseFreshBinding(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    sort_name: []const u8,
    used_deps: u55,
    reserved_deps: u55,
) !FreshSelection {
    const pool = sort_vars.getPool(sort_name) orelse {
        return error.FreshNoAvailableVar;
    };
    var first_unallocated: ?[]const u8 = null;

    for (pool.tokens.items) |token| {
        if (theorem_vars.get(token)) |parser_expr| {
            const var_id = theorem.parser_vars.get(parser_expr) orelse {
                return error.UnknownTheoremVariable;
            };
            switch (var_id) {
                .dummy_var => |dummy_id| {
                    const dummy_info = theorem.theorem_dummies.items[dummy_id];
                    if ((used_deps & dummy_info.deps) != 0) continue;
                    if ((reserved_deps & dummy_info.deps) != 0) continue;
                    return .{
                        .expr_id = try theorem.interner.internVar(var_id),
                        .deps = dummy_info.deps,
                    };
                },
                .theorem_var => continue,
            }
        } else if (first_unallocated == null) {
            first_unallocated = token;
        }
    }

    const token = first_unallocated orelse return error.FreshNoAvailableVar;
    try theorem.ensureNamedDummyParserVar(
        parser.allocator,
        theorem_vars,
        token,
        pool.sort_name,
        pool.sort_id,
    );
    const parser_expr = theorem_vars.get(token) orelse {
        return error.UnknownTheoremVariable;
    };
    const var_id = theorem.parser_vars.get(parser_expr) orelse {
        return error.UnknownTheoremVariable;
    };
    return switch (var_id) {
        .dummy_var => |dummy_id| .{
            .expr_id = try theorem.interner.internVar(var_id),
            .deps = theorem.theorem_dummies.items[dummy_id].deps,
        },
        .theorem_var => error.FreshNoAvailableVar,
    };
}

fn collectUsedDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    bindings: []const ?ExprId,
) !u55 {
    var deps = try exprDeps(env, theorem, line_expr);
    for (ref_exprs) |expr_id| {
        deps |= try exprDeps(env, theorem, expr_id);
    }
    for (bindings) |maybe_expr_id| {
        if (maybe_expr_id) |expr_id| {
            deps |= try exprDeps(env, theorem, expr_id);
        }
    }
    return deps;
}

fn exprDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !u55 {
    return (try Inference.exprInfo(
        env,
        theorem,
        theorem.arg_infos,
        expr_id,
    )).deps;
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}
