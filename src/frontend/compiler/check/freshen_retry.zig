const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("../diag.zig");
const AlphaRewrite = @import("../alpha_rewrite.zig");
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Matching = @import("./matching.zig");

pub fn applyFreshenedRuleLine(
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
    freshened: AlphaRewrite.FreshenResult,
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

        const conv_idx = (try AlphaRewrite.buildRelationProofFromTargetChange(
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
        fresh_refs[idx] = try AlphaRewrite.transportRefAlongProof(
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
        const conv_idx = (try AlphaRewrite.buildRelationProofFromTargetChange(
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
        result_ref = try AlphaRewrite.transportRefBackwardAlongProof(
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
