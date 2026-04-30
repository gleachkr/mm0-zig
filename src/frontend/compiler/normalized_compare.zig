const std = @import("std");

const DefOps = @import("../def_ops.zig");
const Expr = @import("../../trusted/expressions.zig").Expr;
const ExprId = @import("../expr.zig").ExprId;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const Normalizer = @import("../normalizer.zig").Normalizer;
const Canonicalizer = @import("../canonicalizer.zig").Canonicalizer;
const CheckedLine = @import("./checked_ir.zig").CheckedLine;
const CompilerDiag = @import("./diag.zig");

/// Finish a normalized comparison by normalizing and canonicalizing both
/// mirrored expressions, then applying the resulting equality to the match
/// session. This produces inference evidence only; final validation is still
/// responsible for emitting any transport proof lines.
pub fn finish(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    comparison: *DefOps.NormalizedComparison,
) !bool {
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);

    var normalizer = Normalizer.initWithScratch(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
        &checked,
        scratch,
    );
    const expected_mark = scratch.mark();
    const normalized_expected =
        normalizer.normalize(comparison.expected_expr) catch |err| {
            return err;
        };
    scratch.discard(expected_mark);
    const actual_mark = scratch.mark();
    const normalized_actual =
        normalizer.normalize(comparison.actual_expr) catch |err| {
            return err;
        };
    scratch.discard(actual_mark);

    var canonicalizer = Canonicalizer.init(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
    );
    const canonical_expected = try canonicalizer.canonicalize(
        normalized_expected.result_expr,
    );
    const canonical_actual = try canonicalizer.canonicalize(
        normalized_actual.result_expr,
    );
    return try comparison.finish(
        canonical_expected,
        canonical_actual,
    );
}

pub fn matchTemplate(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: ExprId,
) !bool {
    var comparison = try session.beginNormalizedComparison(template, actual);
    defer comparison.deinit();
    return try finish(
        allocator,
        env,
        registry,
        scratch,
        &comparison,
    );
}

pub fn matchSurface(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: *const Expr,
) !bool {
    var comparison = try session.beginNormalizedSurfaceComparison(
        env,
        template,
        actual,
    );
    defer comparison.deinit();
    return try finish(
        allocator,
        env,
        registry,
        scratch,
        &comparison,
    );
}
