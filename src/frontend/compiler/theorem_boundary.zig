const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation =
    @import("../rewrite_registry.zig").ResolvedRelation;
const Normalizer = @import("../normalizer.zig").Normalizer;
const Inference = @import("./inference.zig");
const Normalize = @import("./normalize.zig");
const BoundaryCleanup = @import("./theorem_boundary/cleanup.zig");
const CompilerDiag = @import("./diag.zig");
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendTransportLine = CheckedIr.appendTransportLine;

pub const ReconciliationReport = struct {
    attempted_transparent: bool = false,
    attempted_normalized: bool = false,
    attempted_alpha_cleanup: bool = false,
};

pub fn tryReconcileFinalConclusion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    theorem_concl: ExprId,
    final_line: ExprId,
    line_idx: usize,
    report: *ReconciliationReport,
) !bool {
    report.attempted_transparent = true;
    if (try buildTransparentReconciliation(
        allocator,
        theorem,
        env,
        checked,
        theorem_concl,
        final_line,
        line_idx,
    )) {
        return true;
    }

    report.attempted_normalized = true;
    if (try buildNormalizedReconciliation(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        theorem_concl,
        final_line,
        line_idx,
    )) {
        return true;
    }

    report.attempted_alpha_cleanup = true;
    if (try buildAlphaCleanupReconciliation(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        theorem_concl,
        final_line,
        line_idx,
    )) {
        return true;
    }

    return false;
}

fn buildTransparentReconciliation(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem_concl: ExprId,
    final_line: ExprId,
    line_idx: usize,
) !bool {
    if (!try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        theorem_concl,
        final_line,
    )) {
        return false;
    }

    _ = try appendTransportLine(
        checked,
        allocator,
        theorem_concl,
        final_line,
        .{ .line = line_idx },
    );
    return true;
}

fn buildNormalizedReconciliation(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    theorem_concl: ExprId,
    final_line: ExprId,
    line_idx: usize,
) !bool {
    const conversion = (try Normalize.buildNormalizedConversion(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        final_line,
        theorem_concl,
    )) orelse return false;
    var conversion_mut = conversion;
    const conv_idx = conversion_mut.conv_line_idx orelse return false;

    _ = try conversion_mut.normalizer.emitTransport(
        conversion_mut.relation,
        theorem_concl,
        final_line,
        conv_idx,
        .{ .line = line_idx },
    );
    return true;
}

fn buildAlphaCleanupReconciliation(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    theorem_concl: ExprId,
    final_line: ExprId,
    line_idx: usize,
) !bool {
    const cleanup = (try BoundaryCleanup.tryBuildFinalCleanupConversion(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        theorem_concl,
        final_line,
    )) orelse return false;

    const conversion = try buildBoundaryTransport(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        cleanup.relation,
        theorem_concl,
        final_line,
        cleanup.declared_to_cleaned_line_idx,
        .{ .line = line_idx },
    );
    _ = conversion;
    return true;
}

fn buildBoundaryTransport(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    relation: ResolvedRelation,
    theorem_concl: ExprId,
    final_line: ExprId,
    theorem_to_final_idx: usize,
    final_ref: CheckedRef,
) !usize {
    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    const final_to_theorem_idx = try normalizer.emitSymm(
        relation,
        theorem_concl,
        final_line,
        theorem_to_final_idx,
    );
    return try normalizer.emitTransport(
        relation,
        theorem_concl,
        final_line,
        final_to_theorem_idx,
        final_ref,
    );
}
