const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const Span = @import("../../proof_script.zig").Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const AlphaRewrite = @import("../alpha_rewrite.zig");
const Normalize = @import("../normalize.zig");
const Holes = @import("../holes.zig");
const TheoremBoundary = @import("../theorem_boundary.zig");
const ViewTrace = @import("../../view_trace.zig");
const Diagnostic = CompilerDiag.Diagnostic;

pub fn addFallbackFailureNote(
    diag: *Diagnostic,
    line_assertion: anytype,
    line: anytype,
) void {
    switch (line_assertion) {
        .concrete, .implicit_whole_conclusion => {},
        .holey => |holey| {
            addStaticProofNoteSpan(
                diag,
                "fallback chain exhausted for holey assertion; " ++
                    "showing first candidate failure",
                firstHoleProofSpan(line, holey),
            );
        },
    }
}

pub fn concreteMatchFailureSpan(
    line: anytype,
    report: Holes.ConcreteMatchReport,
) ?Span {
    const failure = report.failure orelse return null;
    return switch (failure) {
        .hole_sort_mismatch => |mismatch| proofSpanForSourceSpan(
            line,
            mismatch.token_span,
        ),
        .visible_structure_mismatch => null,
    };
}

fn firstHoleProofSpan(line: anytype, expr: *const Expr) ?Span {
    return proofSpanForSourceSpan(line, Holes.firstHoleSourceSpan(expr));
}

fn proofSpanForSourceSpan(
    line: anytype,
    maybe_span: ?SourceSpan,
) ?Span {
    const span = maybe_span orelse return null;
    const inner_start = line.assertion_span.start + 1;
    return .{
        .start = inner_start + span.start,
        .end = inner_start + span.end,
    };
}

pub fn setHoleyInferenceDiagnostic(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
    line: anytype,
    rule: *const RuleDecl,
    holey: *const Expr,
    err: anyerror,
    report: Holes.InferenceReport,
) !void {
    const failure = report.failure;
    const missing = if (failure) |actual| switch (actual) {
        .missing_binder => |info| info,
        else => null,
    } else null;

    const kind: CompilerDiag.DiagnosticKind = if (missing != null)
        .missing_binder_assignment
    else
        .inference_failed;
    const hole_span = firstHoleProofSpan(line, holey);
    const span = if (err == error.HoleyInferenceMismatch)
        hole_span orelse line.assertion_span
    else if (missing != null)
        hole_span orelse line.assertion_span
    else
        line.ruleApplicationSpan();
    const binder_name = if (missing) |info|
        info.name orelse "_"
    else
        null;
    var diag = CompilerDiag.withPhase(.{
        .kind = kind,
        .err = err,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .name = binder_name,
        .span = span,
        .detail = if (missing) |info| .{ .missing_binder_assignment = .{
            .binder_name = info.name orelse "_",
            .path = .holey_surface_match,
        } } else .{ .inference_failure = .{
            .path = .holey_surface_match,
            .first_unsolved_binder_name = null,
        } },
    }, .inference);
    try addHoleyInferenceNotes(allocator, &diag, rule, line, holey, report);
    self.setProof(diag);
}

fn addHoleyInferenceNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    rule: *const RuleDecl,
    line: anytype,
    holey: *const Expr,
    report: Holes.InferenceReport,
) !void {
    try addFormattedProofNote(
        allocator,
        diag,
        "inference path: {s}",
        .{CompilerDiag.inferencePathName(.holey_surface_match)},
    );
    const failure = report.failure orelse return;
    const hole_span = firstHoleProofSpan(line, holey);
    switch (failure) {
        .hypothesis_mismatch => addStaticProofNote(
            diag,
            "referenced hypotheses did not match the candidate rule",
        ),
        .visible_structure_mismatch => addStaticProofNoteSpan(
            diag,
            "visible structure in the holey assertion did not match " ++
                "the candidate conclusion",
            hole_span,
        ),
        .missing_binder => |info| {
            const name = info.name orelse "_";
            try addFormattedProofNoteSpan(
                allocator,
                diag,
                "holey assertion left binder {s} unsolved",
                .{name},
                hole_span,
            );
            if (info.index < rule.arg_names.len and rule.arg_names[info.index] == null) {
                try addFormattedProofNote(
                    allocator,
                    diag,
                    "unsolved binder index: {d}",
                    .{info.index + 1},
                );
            }
        },
    }
}

pub fn addHoleConcreteMatchNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    line: anytype,
    report: Holes.ConcreteMatchReport,
) !void {
    const failure = report.failure orelse return;
    switch (failure) {
        .visible_structure_mismatch => addStaticProofNote(
            diag,
            "visible structure in the holey assertion did not match " ++
                "the candidate conclusion",
        ),
        .hole_sort_mismatch => |mismatch| {
            try addFormattedProofNoteSpan(
                allocator,
                diag,
                "hole {s} expected sort {s} but matched {s}",
                .{
                    mismatch.token,
                    mismatch.expected_sort_name,
                    mismatch.actual_sort_name,
                },
                proofSpanForSourceSpan(line, mismatch.token_span),
            );
        },
    }
}

pub fn addComparisonSnapshotNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    actual: ExprId,
    attempted_normalized: bool,
) !void {
    const expected_text = try ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        expected,
    );
    defer allocator.free(expected_text);
    try addFormattedProofNote(
        allocator,
        diag,
        "expected: {s}",
        .{truncateSnapshot(expected_text)},
    );

    const actual_text = try ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        actual,
    );
    defer allocator.free(actual_text);
    try addFormattedProofNote(
        allocator,
        diag,
        "actual: {s}",
        .{truncateSnapshot(actual_text)},
    );

    if (!attempted_normalized) return;

    const snapshot = Normalize.maybeBuildComparisonSnapshotWithDebug(
        allocator,
        @constCast(theorem),
        registry,
        env,
        scratch,
        expected,
        actual,
        .none,
    );
    if (snapshot.normalized_expected == null and
        snapshot.normalized_actual == null)
    {
        return;
    }

    addStaticProofNote(diag, "attempted normalized comparison");
    if (snapshot.normalized_expected) |normalized_expected| {
        const normalized_expected_text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            normalized_expected,
        );
        defer allocator.free(normalized_expected_text);
        try addFormattedProofNote(
            allocator,
            diag,
            "normalized expected: {s}",
            .{truncateSnapshot(normalized_expected_text)},
        );
    }
    if (snapshot.normalized_actual) |normalized_actual| {
        const normalized_actual_text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            normalized_actual,
        );
        defer allocator.free(normalized_actual_text);
        try addFormattedProofNote(
            allocator,
            diag,
            "normalized actual: {s}",
            .{truncateSnapshot(normalized_actual_text)},
        );
    }
}

fn truncateSnapshot(text: []const u8) []const u8 {
    const limit = 64;
    if (text.len <= limit) return text;
    return text[0..limit];
}

pub fn addFreshenAttemptNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    rule: *const RuleDecl,
    report: AlphaRewrite.FreshenAttemptReport,
) !void {
    if (!report.attempted) return;

    const target_name = rule.arg_names[report.target_arg_idx] orelse "_";
    const blocker_name = rule.arg_names[report.blocker_arg_idx] orelse "_";
    try addFormattedProofNote(
        allocator,
        diag,
        "attempted @freshen for target binder {s}",
        .{target_name},
    );
    try addFormattedProofNote(
        allocator,
        diag,
        "freshen blocker binder: {s}",
        .{blocker_name},
    );
    if (report.replacement_name) |replacement_name| {
        try addFormattedProofNote(
            allocator,
            diag,
            "chosen replacement binder: {s}",
            .{replacement_name},
        );
    }
    if (report.blocker_dependency_remaining) |remaining| {
        if (remaining) {
            try addFormattedProofNote(
                allocator,
                diag,
                "rewritten target still depends on blocker binder {s}",
                .{blocker_name},
            );
        } else {
            try addFormattedProofNote(
                allocator,
                diag,
                "rewritten target no longer depends on blocker binder {s}",
                .{blocker_name},
            );
        }
    }
}

pub fn addBoundaryAttemptNotes(
    diag: *Diagnostic,
    report: TheoremBoundary.ReconciliationReport,
) void {
    if (report.attempted_transparent) {
        addStaticProofNote(diag, "attempted transparent final reconciliation");
    }
    if (report.attempted_normalized) {
        addStaticProofNote(diag, "attempted normalized final reconciliation");
    }
}

fn addStaticProofNote(diag: *Diagnostic, message: []const u8) void {
    addStaticProofNoteSpan(diag, message, null);
}

fn addStaticProofNoteSpan(
    diag: *Diagnostic,
    message: []const u8,
    span: ?Span,
) void {
    CompilerDiag.addNote(diag, message, .proof, span);
}

fn addFormattedProofNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    try addFormattedProofNoteSpan(allocator, diag, fmt, args, null);
}

fn addFormattedProofNoteSpan(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
    span: ?Span,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    CompilerDiag.addNote(diag, message, .proof, span);
}
