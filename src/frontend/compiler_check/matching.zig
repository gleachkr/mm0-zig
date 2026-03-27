const std = @import("std");
const ExprId = @import("../compiler_expr.zig").ExprId;
const TheoremContext = @import("../compiler_expr.zig").TheoremContext;
const GlobalEnv = @import("../compiler_env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const NormalizeSpec = @import("../rewrite_registry.zig").NormalizeSpec;
const Inference = @import("../compiler_inference.zig");
const Normalize = @import("../compiler_normalize.zig");
const CheckedIr = @import("../compiler/checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendRuleLine = CheckedIr.appendRuleLine;
const appendTransportLine = CheckedIr.appendTransportLine;

pub fn tryMatchHypothesis(
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

pub fn tryMatchFinalLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem_concl: ExprId,
    final_line: ExprId,
    line_idx: usize,
) !bool {
    if (try Inference.canConvertTransparent(
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
