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
const CompilerDiag = @import("./diag.zig");
const DebugConfig = @import("../debug.zig").DebugConfig;
const DebugTrace = @import("../debug.zig");
const ViewTrace = @import("../view_trace.zig");

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

pub const ComparisonSnapshot = struct {
    normalized_expected: ?ExprId = null,
    normalized_actual: ?ExprId = null,
};

pub fn maybeBuildComparisonSnapshot(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    actual: ExprId,
) ComparisonSnapshot {
    return maybeBuildComparisonSnapshotWithDebug(
        allocator,
        theorem,
        registry,
        env,
        scratch,
        expected,
        actual,
        .none,
    );
}

pub fn maybeBuildComparisonSnapshotWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    actual: ExprId,
    debug: DebugConfig,
) ComparisonSnapshot {
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);

    const normalized_expected = normalizeExprForSnapshot(
        allocator,
        theorem,
        registry,
        env,
        &checked,
        scratch,
        expected,
    ) catch return .{};
    const normalized_actual = normalizeExprForSnapshot(
        allocator,
        theorem,
        registry,
        env,
        &checked,
        scratch,
        actual,
    ) catch return .{};

    if (normalized_expected == expected and normalized_actual == actual) {
        DebugTrace.traceNormalization(
            debug,
            "comparison snapshot found no normalized change",
            .{},
        );
        return .{};
    }
    tryTraceComparison(
        debug,
        allocator,
        theorem,
        env,
        "comparison snapshot",
        expected,
        actual,
    );
    return .{
        .normalized_expected = normalized_expected,
        .normalized_actual = normalized_actual,
    };
}

pub fn normalizeExprForSnapshot(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    expr: ExprId,
) !ExprId {
    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    const mark = scratch.mark();
    const normalized = normalizer.normalize(expr) catch |err| {
        scratch.discard(mark);
        return err;
    };
    scratch.discard(mark);
    return normalized.result_expr;
}

pub fn buildNormalizedConversion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    actual: ExprId,
    expected: ExprId,
) !?NormalizedConversion {
    return buildNormalizedConversionWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        actual,
        expected,
        .none,
    );
}

pub fn buildNormalizedConversionWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    actual: ExprId,
    expected: ExprId,
    debug: DebugConfig,
) !?NormalizedConversion {
    tryTraceComparison(
        debug,
        allocator,
        theorem,
        env,
        "trying normalized comparison",
        expected,
        actual,
    );
    var normalizer = Normalizer.initWithDebugAndScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        debug,
    );
    const relation = normalizer.resolveRelationForExpr(actual) orelse {
        DebugTrace.traceNormalization(
            debug,
            "normalized comparison has no relation for the actual expr",
            .{},
        );
        return null;
    };
    const actual_mark = scratch.mark();
    const norm_actual = normalizer.normalize(actual) catch |err| {
        return err;
    };
    scratch.discard(actual_mark);
    const expected_mark = scratch.mark();
    const norm_expected = normalizer.normalize(expected) catch |err| {
        return err;
    };
    scratch.discard(expected_mark);

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
        ) orelse {
            DebugTrace.traceNormalization(
                debug,
                "normalized comparison could not build a common target",
                .{},
            );
            return null;
        });

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

    DebugTrace.traceNormalization(
        debug,
        "normalized comparison succeeded",
        .{},
    );
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
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
) !?ExpectedNormalization {
    return buildExpectedNormalizationWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        expected,
        .none,
    );
}

pub fn buildExpectedNormalizationWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    debug: DebugConfig,
) !?ExpectedNormalization {
    var normalizer = Normalizer.initWithDebugAndScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        debug,
    );
    const relation = normalizer.resolveRelationForExpr(expected) orelse {
        return null;
    };
    const mark = scratch.mark();
    const normalized = normalizer.normalize(expected) catch |err| {
        return err;
    };
    scratch.discard(mark);
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
    scratch: *CompilerDiag.Scratch,
    actual_ref: CheckedRef,
    actual: ExprId,
    expected: ExprId,
) !?CheckedRef {
    return buildTransparentNormalizedHypRefWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        actual_ref,
        actual,
        expected,
        .none,
    );
}

pub fn buildTransparentNormalizedHypRefWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    actual_ref: CheckedRef,
    actual: ExprId,
    expected: ExprId,
    debug: DebugConfig,
) !?CheckedRef {
    var normalization = try buildExpectedNormalizationWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        expected,
        debug,
    ) orelse return null;
    if (!try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        normalization.normalized_expr,
        actual,
    )) {
        DebugTrace.traceNormalization(
            debug,
            "transparent-normalized hypothesis comparison did not match",
            .{},
        );
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
    scratch: *CompilerDiag.Scratch,
    line_expr: ExprId,
    expected_line: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !?usize {
    return buildTransparentNormalizedConclusionLineWithDebug(
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
        .none,
    );
}

pub fn buildTransparentNormalizedConclusionLineWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    line_expr: ExprId,
    expected_line: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
    debug: DebugConfig,
) !?usize {
    var normalization = try buildExpectedNormalizationWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        expected_line,
        debug,
    ) orelse return null;

    var line_normalizer = Normalizer.initWithDebugAndScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        debug,
    );
    const mark = scratch.mark();
    const normalized_line = line_normalizer.normalize(line_expr) catch |err| {
        return err;
    };
    scratch.discard(mark);
    if (normalized_line.result_expr != normalization.normalized_expr and
        !try Inference.canConvertTransparent(
            allocator,
            theorem,
            env,
            line_expr,
            normalization.normalized_expr,
        ))
    {
        DebugTrace.traceNormalization(
            debug,
            "transparent-normalized conclusion comparison did not match",
            .{},
        );
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

fn tryTraceComparison(
    debug: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    label: []const u8,
    expected: ExprId,
    actual: ExprId,
) void {
    if (!debug.normalization) return;

    const expected_text = ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        expected,
    ) catch return;
    defer allocator.free(expected_text);
    const actual_text = ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        actual,
    ) catch return;
    defer allocator.free(actual_text);

    DebugTrace.traceNormalization(
        debug,
        "{s}: expected={s}",
        .{ label, expected_text },
    );
    DebugTrace.traceNormalization(
        debug,
        "{s}: actual={s}",
        .{ label, actual_text },
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
