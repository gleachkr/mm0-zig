const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const CompilerDiag = @import("../diag.zig");
const ViewTrace = @import("../../view_trace.zig");
const DebugConfig = @import("../../debug.zig").DebugConfig;
const DebugTrace = @import("../../debug.zig");

const Diagnostic = CompilerDiag.Diagnostic;
const InferencePath = CompilerDiag.InferencePath;

const BindingSummaryMode = enum {
    explicit,
    inferred,
};

pub fn buildInferenceFailureDiagnostic(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: anytype,
    path: InferencePath,
    err: anyerror,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !Diagnostic {
    var diag = CompilerDiag.withPhase(.{
        .kind = .inference_failed,
        .err = err,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .span = line.ruleApplicationSpan(),
        .detail = .{ .inference_failure = .{
            .path = path,
            .first_unsolved_binder_name = firstUnsolvedNamedBinder(rule, current_bindings),
        } },
    }, .inference);
    try addInferenceNotes(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        path,
        explicit_bindings,
        current_bindings,
    );
    return diag;
}

pub fn buildMissingBinderDiagnostic(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: anytype,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    missing_idx: usize,
) !Diagnostic {
    const binder_name = rule.arg_names[missing_idx] orelse "_";
    var diag = CompilerDiag.withPhase(.{
        .kind = .missing_binder_assignment,
        .err = error.MissingBinderAssignment,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .name = rule.arg_names[missing_idx],
        .span = line.application.binding_list_span orelse line.application.rule_span,
        .detail = .{ .missing_binder_assignment = .{
            .binder_name = binder_name,
            .path = path,
        } },
    }, .inference);
    try addInferenceNotes(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        path,
        explicit_bindings,
        current_bindings,
    );
    return diag;
}

pub fn addInferenceNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    try addFormattedInferenceNote(
        allocator,
        diag,
        "inference path: {s}",
        .{CompilerDiag.inferencePathName(path)},
    );

    const explicit_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .explicit,
    );
    defer allocator.free(explicit_summary);
    try addFormattedInferenceNote(
        allocator,
        diag,
        "explicit bindings: {s}",
        .{explicit_summary},
    );

    const inferred_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .inferred,
    );
    defer allocator.free(inferred_summary);
    try addFormattedInferenceNote(
        allocator,
        diag,
        "inferred bindings before failure: {s}",
        .{inferred_summary},
    );

    if (firstUnsolvedBinderLabel(rule, current_bindings)) |label| {
        try addFormattedInferenceNote(
            allocator,
            diag,
            "first unsolved binder: {s}",
            .{label},
        );
    }
}

pub fn addAmbiguityWarningNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    report: @import("../../inference_solver.zig").AmbiguityReport,
) !void {
    if (report.chosen_bindings) |summary| {
        try addFormattedInferenceNote(
            allocator,
            diag,
            "chosen bindings: {s}",
            .{summary},
        );
    }
    if (report.alternative_bindings) |summary| {
        try addFormattedInferenceNote(
            allocator,
            diag,
            "alternative bindings: {s}",
            .{summary},
        );
    }
    try addFormattedInferenceNote(
        allocator,
        diag,
        "distinct solutions considered: {d}",
        .{report.distinct_solution_count},
    );
}

pub fn addFormattedInferenceNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    CompilerDiag.addNote(diag, message, .proof, null);
}

pub fn traceInferenceAttempt(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;
    DebugTrace.traceInference(
        config,
        "trying {s} for rule {s}",
        .{ CompilerDiag.inferencePathName(path), rule.name },
    );
    try traceInferenceBindingSummaries(
        config,
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
    );
}

pub fn traceInferenceFailure(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    path: InferencePath,
    err: anyerror,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;
    DebugTrace.traceInference(
        config,
        "{s} failed for rule {s}: {s}",
        .{
            CompilerDiag.inferencePathName(path),
            rule.name,
            @errorName(err),
        },
    );
    try traceInferenceBindingSummaries(
        config,
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
    );
}

fn traceInferenceBindingSummaries(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;

    const explicit_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .explicit,
    );
    defer allocator.free(explicit_summary);
    DebugTrace.traceInference(
        config,
        "  explicit bindings: {s}",
        .{explicit_summary},
    );

    const inferred_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .inferred,
    );
    defer allocator.free(inferred_summary);
    DebugTrace.traceInference(
        config,
        "  inferred bindings: {s}",
        .{inferred_summary},
    );

    if (firstUnsolvedBinderLabel(rule, current_bindings)) |label| {
        DebugTrace.traceInference(
            config,
            "  first unsolved binder: {s}",
            .{label},
        );
    }
}

fn buildBindingSummary(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    mode: BindingSummaryMode,
) ![]const u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    var emitted: usize = 0;
    var remaining: usize = 0;
    for (current_bindings, 0..) |binding, idx| {
        const is_explicit = idx < explicit_bindings.len and
            explicit_bindings[idx] != null;
        const include = switch (mode) {
            .explicit => is_explicit,
            .inferred => !is_explicit and binding != null,
        };
        if (!include) continue;

        if (emitted == 3) {
            remaining += 1;
            continue;
        }
        if (emitted != 0) {
            try out.appendSlice(allocator, "; ");
        }
        try appendBindingEntry(
            &out,
            allocator,
            theorem,
            env,
            rule,
            idx,
            binding,
        );
        emitted += 1;
    }

    if (emitted == 0) {
        try out.appendSlice(allocator, "none");
    } else if (remaining != 0) {
        try out.writer(allocator).print(
            "; +{d} more",
            .{remaining},
        );
    }
    return try out.toOwnedSlice(allocator);
}

fn appendBindingEntry(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    idx: usize,
    binding: ?ExprId,
) !void {
    try out.appendSlice(allocator, binderLabel(rule, idx));
    try out.appendSlice(allocator, " = ");
    if (binding) |expr_id| {
        const text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            expr_id,
        );
        defer allocator.free(text);
        try appendInferenceTruncatedText(out, allocator, text, 48);
        return;
    }
    try out.appendSlice(allocator, "<unsolved>");
}

fn appendInferenceTruncatedText(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    text: []const u8,
    limit: usize,
) !void {
    if (text.len <= limit) {
        try out.appendSlice(allocator, text);
        return;
    }
    if (limit <= 1) {
        try out.appendSlice(allocator, text[0..limit]);
        return;
    }
    try out.appendSlice(allocator, text[0 .. limit - 1]);
    try out.appendSlice(allocator, "...");
}

pub fn firstUnsolvedNamedBinder(
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) ?[]const u8 {
    for (bindings, 0..) |binding, idx| {
        if (binding != null) continue;
        if (idx < rule.arg_names.len) {
            if (rule.arg_names[idx]) |name| return name;
        }
        return null;
    }
    return null;
}

fn firstUnsolvedBinderLabel(
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) ?[]const u8 {
    return firstUnsolvedNamedBinder(rule, bindings);
}

fn binderLabel(rule: *const RuleDecl, idx: usize) []const u8 {
    if (idx < rule.arg_names.len) {
        if (rule.arg_names[idx]) |name| return name;
    }
    return "_";
}
