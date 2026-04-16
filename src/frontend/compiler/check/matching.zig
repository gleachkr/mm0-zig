const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const NormalizeSpec = @import("../../rewrite_registry.zig").NormalizeSpec;
const Inference = @import("../inference.zig");
const Normalize = @import("../normalize.zig");
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendRuleLine = CheckedIr.appendRuleLine;
const appendTransportLine = CheckedIr.appendTransportLine;
const CompilerDiag = @import("../diag.zig");

pub fn tryMatchHypothesis(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    norm_spec: ?NormalizeSpec,
    hyp_idx: usize,
    actual_ref: CheckedRef,
    actual: ExprId,
    expected: ExprId,
) !?CheckedRef {
    if (actual == expected) return actual_ref;

    if (try Inference.canConvertTransparent(
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
        scratch,
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

    return try Normalize.buildTransparentNormalizedHypRef(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        actual_ref,
        actual,
        expected,
    );
}

pub fn tryBuildConclusionLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
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

    if (try Inference.canConvertTransparent(
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
                scratch,
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
            return try Normalize.buildTransparentNormalizedConclusionLine(
                allocator,
                theorem,
                registry,
                env,
                checked,
                scratch,
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

