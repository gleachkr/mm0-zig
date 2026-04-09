const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;
const NormalizeSpec = @import("../rewrite_registry.zig").NormalizeSpec;
const Normalizer = @import("../normalizer.zig").Normalizer;
const CommonTargetResult = @import("../normalizer.zig").CommonTargetResult;
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendTransportLine = CheckedIr.appendTransportLine;
const appendRuleLine = CheckedIr.appendRuleLine;
const Inference = @import("./inference.zig");

pub const NormalizedConversion = struct {
    relation: ResolvedRelation,
    conv_line_idx: ?usize,
    normalizer: Normalizer,
};

pub const ExpectedNormalization = struct {
    relation: ResolvedRelation,
    normalized_expr: ExprId,
    conv_line_idx: ?usize,
    normalizer: Normalizer,
};

pub fn buildNormalizedConversion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    actual: ExprId,
    expected: ExprId,
) !?NormalizedConversion {
    var normalizer = Normalizer.init(
        allocator,
        theorem,
        registry,
        env,
        checked,
    );
    const relation = normalizer.resolveRelationForExpr(actual) orelse return null;
    const norm_actual = try normalizer.normalize(actual);
    const norm_expected = try normalizer.normalize(expected);

    const common_target: CommonTargetResult = if (norm_actual.result_expr ==
        norm_expected.result_expr)
        .{
            .target_expr = norm_actual.result_expr,
            .lhs_conv_line_idx = null,
            .rhs_conv_line_idx = null,
        }
    else
        (try normalizer.buildCommonTarget(
            norm_actual.result_expr,
            norm_expected.result_expr,
        ) orelse return null);

    const actual_to_common = try normalizer.composeTransitivity(
        relation,
        actual,
        norm_actual.result_expr,
        common_target.target_expr,
        norm_actual.conv_line_idx,
        common_target.lhs_conv_line_idx,
    );
    const expected_to_common = try normalizer.composeTransitivity(
        relation,
        expected,
        norm_expected.result_expr,
        common_target.target_expr,
        norm_expected.conv_line_idx,
        common_target.rhs_conv_line_idx,
    );

    const conv_line_idx = if (actual_to_common) |actual_idx|
        if (expected_to_common) |expected_idx|
            try normalizer.composeTransitivity(
                relation,
                actual,
                common_target.target_expr,
                expected,
                actual_idx,
                try normalizer.emitSymm(
                    relation,
                    expected,
                    common_target.target_expr,
                    expected_idx,
                ),
            )
        else
            actual_idx
    else if (expected_to_common) |expected_idx|
        try normalizer.emitSymm(
            relation,
            expected,
            common_target.target_expr,
            expected_idx,
        )
    else
        null;

    return .{
        .relation = relation,
        .conv_line_idx = conv_line_idx,
        .normalizer = normalizer,
    };
}

pub fn buildExpectedNormalization(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    expected: ExprId,
) !?ExpectedNormalization {
    var normalizer = Normalizer.init(
        allocator,
        theorem,
        registry,
        env,
        checked,
    );
    const relation = normalizer.resolveRelationForExpr(expected) orelse {
        return null;
    };
    const normalized = try normalizer.normalize(expected);
    if (normalized.result_expr == expected and normalized.conv_line_idx == null) {
        return null;
    }
    return .{
        .relation = relation,
        .normalized_expr = normalized.result_expr,
        .conv_line_idx = normalized.conv_line_idx,
        .normalizer = normalizer,
    };
}

pub fn buildTransparentNormalizedHypRef(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    actual_ref: CheckedRef,
    actual: ExprId,
    expected: ExprId,
) !?CheckedRef {
    var normalization = try buildExpectedNormalization(
        allocator,
        theorem,
        registry,
        env,
        checked,
        expected,
    ) orelse return null;
    if (!try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        normalization.normalized_expr,
        actual,
    )) {
        return null;
    }

    const normalized_ref = if (actual == normalization.normalized_expr)
        actual_ref
    else
        CheckedRef{ .line = try appendTransportLine(
            checked,
            allocator,
            normalization.normalized_expr,
            actual,
            actual_ref,
        ) };

    if (normalization.conv_line_idx) |conv_line_idx| {
        const symm_idx = try normalization.normalizer.emitSymm(
            normalization.relation,
            expected,
            normalization.normalized_expr,
            conv_line_idx,
        );
        return .{ .line = try normalization.normalizer.emitTransport(
            normalization.relation,
            expected,
            normalization.normalized_expr,
            symm_idx,
            normalized_ref,
        ) };
    }
    return normalized_ref;
}

pub fn buildTransparentNormalizedConclusionLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    line_expr: ExprId,
    expected_line: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !?usize {
    var normalization = try buildExpectedNormalization(
        allocator,
        theorem,
        registry,
        env,
        checked,
        expected_line,
    ) orelse return null;

    var line_normalizer = Normalizer.init(
        allocator,
        theorem,
        registry,
        env,
        checked,
    );
    const normalized_line = try line_normalizer.normalize(line_expr);
    if (normalized_line.result_expr != normalization.normalized_expr and
        !try Inference.canConvertTransparent(
            allocator,
            theorem,
            env,
            line_expr,
            normalization.normalized_expr,
        ))
    {
        return null;
    }

    const raw_idx = try appendRuleLine(
        checked,
        allocator,
        expected_line,
        rule_id,
        bindings,
        refs,
    );
    const normalized_idx = if (normalization.conv_line_idx) |conv_line_idx|
        try normalization.normalizer.emitTransport(
            normalization.relation,
            normalization.normalized_expr,
            expected_line,
            conv_line_idx,
            .{ .line = raw_idx },
        )
    else
        raw_idx;

    if (line_expr == normalization.normalized_expr) {
        return normalized_idx;
    }
    return try appendTransportLine(
        checked,
        allocator,
        line_expr,
        normalization.normalized_expr,
        .{ .line = normalized_idx },
    );
}

pub fn isHypMarkedForNormalize(
    spec: NormalizeSpec,
    hyp_idx: usize,
) bool {
    for (spec.hyp_indices) |marked| {
        if (marked == hyp_idx) return true;
    }
    return false;
}
