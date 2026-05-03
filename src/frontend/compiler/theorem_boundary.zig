const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const Inference = @import("./inference.zig");
const Normalize = @import("./normalize.zig");
const CompilerDiag = @import("./diag.zig");
const DebugConfig = @import("../debug.zig").DebugConfig;
const DebugTrace = @import("../debug.zig");
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const appendTransportLine = CheckedIr.appendTransportLine;

pub const ReconciliationReport = struct {
    attempted_transparent: bool = false,
    attempted_normalized: bool = false,
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
    debug: DebugConfig,
    report: *ReconciliationReport,
) !bool {
    DebugTrace.traceBoundary(
        debug,
        "reconciling final theorem line via transparent then normalized " ++
            "paths",
        .{},
    );
    report.attempted_transparent = true;
    if (try buildTransparentReconciliation(
        allocator,
        theorem,
        env,
        checked,
        theorem_concl,
        final_line,
        line_idx,
        debug,
    )) {
        DebugTrace.traceBoundary(
            debug,
            "transparent reconciliation succeeded",
            .{},
        );
        return true;
    }

    DebugTrace.traceBoundary(
        debug,
        "transparent reconciliation failed; trying normalization",
        .{},
    );
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
        debug,
    )) {
        DebugTrace.traceBoundary(
            debug,
            "normalized reconciliation succeeded",
            .{},
        );
        return true;
    }

    DebugTrace.traceBoundary(
        debug,
        "final reconciliation failed on transparent and normalized paths",
        .{},
    );
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
    debug: DebugConfig,
) !bool {
    if (!try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        theorem_concl,
        final_line,
    )) {
        DebugTrace.traceBoundary(
            debug,
            "transparent reconciliation could not match the final line",
            .{},
        );
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
    debug: DebugConfig,
) !bool {
    const conversion = (try Normalize.buildNormalizedConversionWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        final_line,
        theorem_concl,
        debug,
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
