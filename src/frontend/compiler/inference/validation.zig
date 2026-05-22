const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const ParseRecovery = @import("../../parse_recovery.zig");
const ArgInfo = ParseRecovery.ArgInfo;
const AssertionStmt = ParseRecovery.AssertionStmt;
const BindingValidation = @import("../../binding_validation.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const DebugConfig = @import("../../debug.zig").DebugConfig;
const DebugTrace = @import("../../debug.zig");

const ExprInfo = BindingValidation.ExprInfo;
pub const DepViolationDetail = CompilerDiag.DepViolationDiagnosticDetail;

pub fn validateResolvedBindingsWithDebug(
    self: *CompilerContext,
    debug: DebugConfig,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: anytype,
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
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
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
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .span = line.ruleApplicationSpan(),
            .detail = .{ .dep_violation = detail },
        }, .theorem_application));
        return error.DepViolation;
    }
}

pub fn validateResolvedBindings(
    self: *CompilerContext,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: anytype,
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
    var infos: [56]ExprInfo = undefined;
    std.debug.assert(bindings.len <= infos.len);
    for (bindings, 0..) |binding, idx| {
        infos[idx] = try exprInfo(env, theorem, theorem_args, binding);
    }

    const violation = BindingValidation.firstDepViolation(
        rule_args,
        infos[0..bindings.len],
    ) orelse return null;
    return depViolationDetail(
        rule_arg_names,
        violation.first_idx,
        infos[violation.first_idx],
        violation.second_idx,
        infos[violation.second_idx],
    );
}

pub fn firstPartialDepViolation(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    bindings: []const ?ExprId,
) !?DepViolationDetail {
    var bound_deps: [56]u55 = undefined;
    var bound_arg_indices: [56]usize = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_arg_indices: [56]usize = undefined;
    var prev_len: usize = 0;

    for (rule_args, bindings, 0..) |expected, binding, idx| {
        const info = if (binding) |expr_id|
            try exprInfo(env, theorem, theorem_args, expr_id)
        else
            null;

        if (expected.bound) {
            if (info) |actual| {
                for (prev_deps[0..prev_len], prev_arg_indices[0..prev_len]) |
                    prev_dep,
                    prev_idx,
                | {
                    if (prev_dep & actual.deps != 0) {
                        return depViolationDetail(
                            rule_arg_names,
                            prev_idx,
                            try exprInfo(
                                env,
                                theorem,
                                theorem_args,
                                bindings[prev_idx].?,
                            ),
                            idx,
                            actual,
                        );
                    }
                }
                bound_deps[bound_len] = actual.deps;
            } else {
                bound_deps[bound_len] = 0;
            }
            bound_arg_indices[bound_len] = idx;
            bound_len += 1;
        } else if (info) |actual| {
            for (bound_deps[0..bound_len], bound_arg_indices[0..bound_len], 0..) |
                bound_dep,
                bound_idx,
                k,
            | {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0) {
                    continue;
                }
                if (bound_dep & actual.deps != 0) {
                    return depViolationDetail(
                        rule_arg_names,
                        bound_idx,
                        try exprInfo(
                            env,
                            theorem,
                            theorem_args,
                            bindings[bound_idx].?,
                        ),
                        idx,
                        actual,
                    );
                }
            }
        }

        if (info) |actual| {
            prev_deps[prev_len] = actual.deps;
            prev_arg_indices[prev_len] = idx;
            prev_len += 1;
        }
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
    return try BindingValidation.exprInfo(
        env,
        theorem,
        theorem_args,
        expr_id,
    );
}
