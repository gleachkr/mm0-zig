const std = @import("std");
const CompilerDiag = @import("./diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticDetail = CompilerDiag.DiagnosticDetail;
const DiagnosticPhase = CompilerDiag.DiagnosticPhase;
const DiagnosticSource = CompilerDiag.DiagnosticSource;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const Span = @import("../proof_script.zig").Span;

pub const DiagnosticSink = struct {
    pub const max_warnings = 32;
    pub const max_primary_diagnostics = 256;
    const diagnostic_storage_size = 32768;
    const truncated_diagnostic_string = "<diagnostic string truncated>";

    source: []const u8,
    proof_source: ?[]const u8,
    last_diagnostic: ?Diagnostic,
    primary_diagnostic_storage: [max_primary_diagnostics]Diagnostic =
        undefined,
    primary_diagnostic_count: usize = 0,
    dropped_primary_diagnostic_count: usize = 0,
    dropped_mm0_primary_diagnostic_count: usize = 0,
    dropped_proof_primary_diagnostic_count: usize = 0,
    warning_storage: [max_warnings]Diagnostic = undefined,
    warning_count: usize = 0,
    dropped_warning_count: usize = 0,
    warnings_as_errors: bool = false,
    diagnostic_storage: [diagnostic_storage_size]u8 = undefined,
    diagnostic_storage_len: usize = 0,

    pub fn init(
        source: []const u8,
        proof_source: ?[]const u8,
    ) DiagnosticSink {
        return .{
            .source = source,
            .proof_source = proof_source,
            .last_diagnostic = null,
            .primary_diagnostic_storage = undefined,
            .primary_diagnostic_count = 0,
            .dropped_primary_diagnostic_count = 0,
            .dropped_mm0_primary_diagnostic_count = 0,
            .dropped_proof_primary_diagnostic_count = 0,
            .warning_storage = undefined,
            .warning_count = 0,
            .dropped_warning_count = 0,
            .warnings_as_errors = false,
            .diagnostic_storage = undefined,
            .diagnostic_storage_len = 0,
        };
    }

    pub fn clear(self: *DiagnosticSink) void {
        self.diagnostic_storage_len = 0;
        self.last_diagnostic = null;
        self.primary_diagnostic_count = 0;
        self.dropped_primary_diagnostic_count = 0;
        self.dropped_mm0_primary_diagnostic_count = 0;
        self.dropped_proof_primary_diagnostic_count = 0;
        self.warning_count = 0;
        self.dropped_warning_count = 0;
    }

    pub fn primaryDiagnostics(
        self: *const DiagnosticSink,
    ) []const Diagnostic {
        return self.primary_diagnostic_storage[0..self.primary_diagnostic_count];
    }

    pub fn warningDiagnostics(
        self: *const DiagnosticSink,
    ) []const Diagnostic {
        return self.warning_storage[0..self.warning_count];
    }

    pub fn omittedPrimaryDiagnostic(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) ?Diagnostic {
        const count = self.droppedPrimaryDiagnosticCount(source);
        if (count == 0) return null;
        return .{
            .kind = .omitted_diagnostics,
            .err = error.DiagnosticsOmitted,
            .source = source,
            .detail = .{ .omitted_diagnostics = .{ .count = count } },
        };
    }

    pub fn addPrimaryDiagnostic(
        self: *DiagnosticSink,
        diag: Diagnostic,
    ) void {
        const primary = self.stableDiagnostic(diag);
        if (self.primary_diagnostic_count >=
            self.primary_diagnostic_storage.len)
        {
            self.dropped_primary_diagnostic_count += 1;
            switch (primary.source) {
                .mm0 => self.dropped_mm0_primary_diagnostic_count += 1,
                .proof => self.dropped_proof_primary_diagnostic_count += 1,
            }
            return;
        }
        self.primary_diagnostic_storage[self.primary_diagnostic_count] =
            primary;
        self.primary_diagnostic_count += 1;
    }

    pub fn addWarning(self: *DiagnosticSink, diag: Diagnostic) void {
        var warning = self.stableDiagnostic(diag);
        warning.severity = .warning;
        if (self.warning_count >= self.warning_storage.len) {
            self.dropped_warning_count += 1;
            return;
        }
        self.warning_storage[self.warning_count] = warning;
        self.warning_count += 1;
    }

    pub fn reportWarnings(self: *const DiagnosticSink) void {
        for (self.warningDiagnostics()) |diag| {
            self.reportDiagnostic(diag, "warning");
        }
        if (self.dropped_warning_count != 0) {
            std.debug.print(
                "warning: omitted {d} additional warning(s)\n",
                .{self.dropped_warning_count},
            );
        }
    }

    pub fn reportError(self: *const DiagnosticSink, err: anyerror) void {
        if (self.last_diagnostic) |diag| {
            if (diag.err == err) {
                self.reportDiagnostic(diag, "error");
                return;
            }
        }
        std.debug.print("error: {s}\n", .{@errorName(err)});
    }

    pub fn promoteWarningsToErrors(self: *DiagnosticSink) !void {
        if (!self.warnings_as_errors) return;
        const warnings = self.warningDiagnostics();
        if (warnings.len == 0) return;

        var diag = warnings[0];
        diag.severity = .@"error";
        self.setDiagnostic(diag);
        return diag.err;
    }

    pub fn reportDiagnostic(
        self: *const DiagnosticSink,
        diag: Diagnostic,
        label: []const u8,
    ) void {
        if (diag.kind == .omitted_diagnostics) {
            const detail = switch (diag.detail) {
                .omitted_diagnostics => |info| info,
                else => return,
            };
            std.debug.print("{s}: ", .{label});
            CompilerDiag.writeOmittedDiagnosticsSummary(
                std.fs.File.stderr().deprecatedWriter(),
                detail.count,
            ) catch return;
            std.debug.print("\n", .{});
            return;
        }
        std.debug.print(
            "{s}: {s}\n",
            .{ label, CompilerDiag.diagnosticSummary(diag) },
        );
        if (diag.theorem_name) |name| {
            std.debug.print("  theorem: {s}\n", .{name});
        }
        if (diag.block_name) |name| {
            std.debug.print("  proof block: {s}\n", .{name});
        }
        if (diag.line_label) |line_label| {
            std.debug.print("  line: {s}\n", .{line_label});
        }
        if (diag.rule_name) |rule_name| {
            std.debug.print("  rule: {s}\n", .{rule_name});
        }
        if (diag.name) |name| {
            std.debug.print("  name: {s}\n", .{name});
        }
        if (diag.expected_name) |name| {
            std.debug.print("  expected: {s}\n", .{name});
        }
        if (diag.phase) |phase| {
            std.debug.print(
                "  phase: {s}\n",
                .{CompilerDiag.diagnosticPhaseName(phase)},
            );
        }
        reportDiagnosticDetail(diag.detail);
        self.reportDiagnosticNotes(diag);
        self.reportDiagnosticRelated(diag);
        self.reportDiagnosticLocation(diag);
    }

    fn reportDiagnosticLocation(
        self: *const DiagnosticSink,
        diag: Diagnostic,
    ) void {
        const span = diag.span orelse return;
        const source_info = self.sourceInfo(diag.source) orelse return;
        reportSpanLocation("", source_info, span);
    }

    fn reportDiagnosticNotes(
        self: *const DiagnosticSink,
        diag: Diagnostic,
    ) void {
        for (diag.noteSlice()) |note| {
            std.debug.print("  note: {s}\n", .{note.message});
            const span = note.span orelse continue;
            const source_info = self.sourceInfo(note.source) orelse continue;
            reportSpanLocation("note", source_info, span);
        }
    }

    fn reportDiagnosticRelated(
        self: *const DiagnosticSink,
        diag: Diagnostic,
    ) void {
        for (diag.relatedSlice()) |related| {
            std.debug.print("  related: {s}\n", .{related.label});
            const source_info = self.sourceInfo(related.source) orelse continue;
            reportSpanLocation("related", source_info, related.span);
        }
    }

    fn sourceInfo(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) ?SourceInfo {
        return switch (source) {
            .mm0 => .{
                .label = "source",
                .text = self.source,
            },
            .proof => .{
                .label = "proof",
                .text = self.proof_source orelse return null,
            },
        };
    }

    pub fn setDiagnostic(self: *DiagnosticSink, diag: Diagnostic) void {
        self.last_diagnostic = self.stableDiagnostic(diag);
    }

    pub fn setIfMissing(self: *DiagnosticSink, diag: Diagnostic) void {
        if (self.getDiagnostic() != null) return;
        self.setDiagnostic(diag);
    }

    pub fn setProof(self: *DiagnosticSink, diag: Diagnostic) void {
        var proof_diag = diag;
        proof_diag.source = .proof;
        self.setDiagnostic(proof_diag);
    }

    pub fn maybeSetProof(self: *DiagnosticSink, diag: Diagnostic) void {
        self.setProof(diag);
    }

    pub fn setProofScratchDiagnosticIfPresent(
        self: *DiagnosticSink,
        scratch: *CompilerDiag.Scratch,
        mark: CompilerDiag.Scratch.Mark,
        env: *const GlobalEnv,
        phase: ?DiagnosticPhase,
        kind: CompilerDiag.DiagnosticKind,
        err: anyerror,
        theorem_name: []const u8,
        line_label: ?[]const u8,
        rule_name: ?[]const u8,
        span: ?Span,
    ) bool {
        const detail = CompilerDiag.takeScratchDetail(
            scratch,
            mark,
            env,
            err,
        ) orelse {
            return false;
        };
        var diag: Diagnostic = .{
            .kind = kind,
            .err = err,
            .theorem_name = theorem_name,
            .line_label = line_label,
            .rule_name = rule_name,
            .span = span,
            .detail = detail,
        };
        if (phase) |actual_phase| {
            CompilerDiag.setPhase(&diag, actual_phase);
        }
        self.maybeSetProof(diag);
        return true;
    }

    pub fn getDiagnostic(self: *const DiagnosticSink) ?Diagnostic {
        return self.last_diagnostic;
    }

    pub fn restoreDiagnostic(
        self: *DiagnosticSink,
        diag: ?Diagnostic,
    ) void {
        self.last_diagnostic = diag;
    }

    fn stableDiagnostic(self: *DiagnosticSink, diag: Diagnostic) Diagnostic {
        var stable = diag;
        stable.theorem_name = self.stableString(diag.theorem_name);
        stable.block_name = self.stableString(diag.block_name);
        stable.line_label = self.stableString(diag.line_label);
        stable.rule_name = self.stableString(diag.rule_name);
        stable.name = self.stableString(diag.name);
        stable.expected_name = self.stableString(diag.expected_name);
        stable.detail = self.stableDiagnosticDetail(diag.detail);
        for (diag.noteSlice(), 0..) |note, idx| {
            stable.notes[idx] = .{
                .message = self.stableRequiredString(note.message),
                .source = note.source,
                .span = note.span,
            };
        }
        for (diag.relatedSlice(), 0..) |related, idx| {
            stable.related[idx] = .{
                .label = self.stableRequiredString(related.label),
                .source = related.source,
                .span = related.span,
            };
        }
        return stable;
    }

    fn stableDiagnosticDetail(
        self: *DiagnosticSink,
        detail: DiagnosticDetail,
    ) DiagnosticDetail {
        return switch (detail) {
            .none => .none,
            .omitted_diagnostics => |info| .{ .omitted_diagnostics = info },
            .unknown_math_token => |info| .{ .unknown_math_token = .{
                .token = self.stableRequiredString(info.token),
            } },
            .missing_binder_assignment => |info| .{
                .missing_binder_assignment = .{
                    .binder_name = self.stableRequiredString(info.binder_name),
                    .path = info.path,
                },
            },
            .inference_failure => |info| .{ .inference_failure = .{
                .path = info.path,
                .first_unsolved_binder_name = self.stableString(
                    info.first_unsolved_binder_name,
                ),
            } },
            .dep_violation => |info| .{ .dep_violation = .{
                .first_arg_idx = info.first_arg_idx,
                .second_arg_idx = info.second_arg_idx,
                .first_arg_name = self.stableString(info.first_arg_name),
                .second_arg_name = self.stableString(info.second_arg_name),
                .first_deps = info.first_deps,
                .second_deps = info.second_deps,
                .first_bound = info.first_bound,
                .second_bound = info.second_bound,
            } },
            .definition_body => |info| .{ .definition_body = .{
                .declared_sort_name = self.stableRequiredString(
                    info.declared_sort_name,
                ),
                .actual_sort_name = self.stableRequiredString(
                    info.actual_sort_name,
                ),
                .body_deps = info.body_deps,
                .hidden_binder_count = info.hidden_binder_count,
            } },
            .missing_congruence_rule => |info| .{ .missing_congruence_rule = .{
                .reason = info.reason,
                .term_name = self.stableString(info.term_name),
                .sort_name = self.stableString(info.sort_name),
                .arg_index = info.arg_index,
            } },
            .hypothesis_ref => |info| .{ .hypothesis_ref = info },
            .unused_parameter => |info| .{ .unused_parameter = .{
                .parameter_name = self.stableRequiredString(
                    info.parameter_name,
                ),
            } },
        };
    }

    fn stableString(
        self: *DiagnosticSink,
        value: ?[]const u8,
    ) ?[]const u8 {
        const actual = value orelse return null;
        return self.stableRequiredString(actual);
    }

    fn stableRequiredString(
        self: *DiagnosticSink,
        value: []const u8,
    ) []const u8 {
        if (self.isStableSourceSlice(value)) return value;
        const remaining = diagnostic_storage_size - self.diagnostic_storage_len;
        if (value.len > remaining) return truncated_diagnostic_string;

        const start = self.diagnostic_storage_len;
        const end = start + value.len;
        @memcpy(self.diagnostic_storage[start..end], value);
        self.diagnostic_storage_len = end;
        return self.diagnostic_storage[start..end];
    }

    fn isStableSourceSlice(
        self: *const DiagnosticSink,
        value: []const u8,
    ) bool {
        if (isSubslice(self.source, value)) return true;
        if (self.proof_source) |proof_source| {
            if (isSubslice(proof_source, value)) return true;
        }
        return false;
    }

    fn droppedPrimaryDiagnosticCount(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) usize {
        return switch (source) {
            .mm0 => self.dropped_mm0_primary_diagnostic_count,
            .proof => self.dropped_proof_primary_diagnostic_count,
        };
    }
};

fn reportSpanLocation(
    prefix: []const u8,
    source_info: SourceInfo,
    span: Span,
) void {
    const info = lineCol(source_info.text, span.start);
    const line = source_info.text[info.line_start..info.line_end];

    if (prefix.len == 0) {
        std.debug.print(
            "  --> {s}:{d}:{d}\n",
            .{ source_info.label, info.line, info.column },
        );
    } else {
        std.debug.print(
            "  {s} --> {s}:{d}:{d}\n",
            .{ prefix, source_info.label, info.line, info.column },
        );
    }
    std.debug.print("  | {s}\n", .{line});
    std.debug.print("  | ", .{});

    const caret_start = span.start - info.line_start;
    const caret_end = if (span.end > span.start)
        @min(span.end, info.line_end)
    else
        @min(span.start + 1, info.line_end);
    const caret_len = @max(caret_end - span.start, 1);

    for (0..caret_start) |_| {
        std.debug.print(" ", .{});
    }
    for (0..caret_len) |_| {
        std.debug.print("^", .{});
    }
    std.debug.print("\n", .{});
}

fn reportDiagnosticDetail(detail: DiagnosticDetail) void {
    switch (detail) {
        .none => {},
        .omitted_diagnostics => {},
        .unknown_math_token => |info| {
            std.debug.print("  token: {s}\n", .{info.token});
        },
        .missing_binder_assignment => |info| {
            std.debug.print(
                "  missing binder: {s}\n",
                .{info.binder_name},
            );
            std.debug.print(
                "  inference path: {s}\n",
                .{CompilerDiag.inferencePathName(info.path)},
            );
        },
        .inference_failure => |info| {
            std.debug.print(
                "  inference path: {s}\n",
                .{CompilerDiag.inferencePathName(info.path)},
            );
            if (info.first_unsolved_binder_name) |binder_name| {
                std.debug.print(
                    "  first unsolved binder: {s}\n",
                    .{binder_name},
                );
            }
        },
        .dep_violation => |info| {
            var stderr = std.fs.File.stderr().deprecatedWriter();
            stderr.writeAll("  dependency violation: ") catch return;
            CompilerDiag.writeDepViolationSummary(stderr, info) catch return;
            stderr.writeByte('\n') catch return;
            std.debug.print(
                "  first binder: deps=0x{x} bound={}\n",
                .{ info.first_deps, info.first_bound },
            );
            std.debug.print(
                "  second binder: deps=0x{x} bound={}\n",
                .{ info.second_deps, info.second_bound },
            );
        },
        .definition_body => |info| {
            std.debug.print(
                "  declared sort: {s}\n",
                .{info.declared_sort_name},
            );
            std.debug.print(
                "  actual sort: {s}\n",
                .{info.actual_sort_name},
            );
            std.debug.print(
                "  body deps: 0x{x}\n",
                .{info.body_deps},
            );
            std.debug.print(
                "  hidden binders: {d}\n",
                .{info.hidden_binder_count},
            );
        },
        .missing_congruence_rule => |info| {
            var stderr = std.fs.File.stderr().deprecatedWriter();
            stderr.writeAll("  missing congruence: ") catch return;
            CompilerDiag.writeMissingCongruenceRuleSummary(
                stderr,
                info,
            ) catch return;
            stderr.writeByte('\n') catch return;
            if (info.sort_name) |sort_name| {
                std.debug.print("  sort: {s}\n", .{sort_name});
            }
        },
        .hypothesis_ref => |info| {
            std.debug.print("  hypothesis ref: #{d}\n", .{info.index});
        },
        .unused_parameter => |info| {
            std.debug.print("  parameter: {s}\n", .{info.parameter_name});
        },
    }
}

const SourceInfo = struct {
    label: []const u8,
    text: []const u8,
};

const LineCol = struct {
    line: usize,
    column: usize,
    line_start: usize,
    line_end: usize,
};

fn isSubslice(owner: []const u8, value: []const u8) bool {
    const owner_start = @intFromPtr(owner.ptr);
    const owner_end = owner_start + owner.len;
    const value_start = @intFromPtr(value.ptr);
    const value_end = value_start + value.len;
    return value_start >= owner_start and value_end <= owner_end;
}

fn lineCol(src: []const u8, pos_raw: usize) LineCol {
    const pos = @min(pos_raw, src.len);
    var line: usize = 1;
    var column: usize = 1;
    var line_start: usize = 0;
    var i: usize = 0;

    while (i < pos) : (i += 1) {
        if (src[i] == '\n') {
            line += 1;
            column = 1;
            line_start = i + 1;
        } else {
            column += 1;
        }
    }

    var line_end = line_start;
    while (line_end < src.len and src[line_end] != '\n') : (line_end += 1) {}

    return .{
        .line = line,
        .column = column,
        .line_start = line_start,
        .line_end = line_end,
    };
}
