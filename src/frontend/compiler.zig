const std = @import("std");
const MmbWriter = @import("./mmb_writer.zig");
const CompilerDiag = @import("./compiler/diag.zig");
const DiagnosticDetail = CompilerDiag.DiagnosticDetail;
const Span = @import("./proof_script.zig").Span;
const Metadata = @import("./compiler/metadata.zig");
const CompilerVars = @import("./compiler/vars.zig");
const CheckedIr = @import("./compiler/checked_ir.zig");
const Pipeline = @import("./compiler/pipeline.zig");
pub const DebugConfig = @import("./debug.zig").DebugConfig;

pub const ViewDecl = Metadata.ViewDecl;
pub const FreshDecl = Metadata.FreshDecl;
pub const SortVarDecl = CompilerVars.SortVarDecl;
pub const SortVarRegistry = CompilerVars.SortVarRegistry;
pub const Diagnostic = CompilerDiag.Diagnostic;
pub const DiagnosticSeverity = CompilerDiag.DiagnosticSeverity;
pub const DiagnosticSource = CompilerDiag.DiagnosticSource;
pub const DiagnosticPhase = CompilerDiag.DiagnosticPhase;
pub const DiagnosticNote = CompilerDiag.DiagnosticNote;
pub const DiagnosticRelated = CompilerDiag.DiagnosticRelated;
pub const CheckedRef = CheckedIr.CheckedRef;
pub const CheckedLine = CheckedIr.CheckedLine;
pub const appendRuleLine = CheckedIr.appendRuleLine;
pub const appendTransportLine = CheckedIr.appendTransportLine;

pub const Compiler = struct {
    pub const max_warnings = 32;
    const diagnostic_storage_size = 4096;
    const truncated_diagnostic_string = "<diagnostic string truncated>";

    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    last_diagnostic: ?Diagnostic,
    warning_storage: [max_warnings]Diagnostic = undefined,
    warning_count: usize = 0,
    dropped_warning_count: usize = 0,
    warnings_as_errors: bool = false,
    debug: DebugConfig,
    diagnostic_storage: [diagnostic_storage_size]u8 = undefined,
    diagnostic_storage_len: usize = 0,

    const PipelineOutput = Pipeline.Output;

    pub fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) Compiler {
        return initInternal(allocator, source, null);
    }

    pub fn initWithProof(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: []const u8,
    ) Compiler {
        return initInternal(allocator, source, proof_source);
    }

    fn initInternal(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: ?[]const u8,
    ) Compiler {
        const compiler: Compiler = .{
            .allocator = allocator,
            .source = source,
            .proof_source = proof_source,
            .last_diagnostic = null,
            .warning_storage = undefined,
            .warning_count = 0,
            .dropped_warning_count = 0,
            .warnings_as_errors = false,
            .debug = DebugConfig.none,
            .diagnostic_storage = undefined,
            .diagnostic_storage_len = 0,
        };
        return compiler;
    }

    pub fn check(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        try Pipeline.run(self, arena.allocator(), null);
        try self.promoteWarningsToErrors();
    }

    pub fn compileMmb(
        self: *Compiler,
        out_allocator: std.mem.Allocator,
    ) ![]u8 {
        self.clearDiagnostics();

        _ = self.proof_source orelse return error.MissingProofFile;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var emit = PipelineOutput{};
        try Pipeline.run(self, arena.allocator(), &emit);
        try self.promoteWarningsToErrors();

        return try MmbWriter.buildFile(
            out_allocator,
            emit.sort_names.items,
            emit.sorts.items,
            emit.terms.items,
            emit.theorems.items,
            emit.statements.items,
        );
    }

    pub fn writeMmb(self: *Compiler) !void {
        const bytes = try self.compileMmb(self.allocator);
        self.allocator.free(bytes);
    }

    pub fn warningDiagnostics(self: *const Compiler) []const Diagnostic {
        return self.warning_storage[0..self.warning_count];
    }

    pub fn addWarning(self: *Compiler, diag: Diagnostic) void {
        var warning = self.stableDiagnostic(diag);
        warning.severity = .warning;
        if (self.warning_count >= self.warning_storage.len) {
            self.dropped_warning_count += 1;
            return;
        }
        self.warning_storage[self.warning_count] = warning;
        self.warning_count += 1;
    }

    pub fn reportWarnings(self: *const Compiler) void {
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

    pub fn reportError(self: *const Compiler, err: anyerror) void {
        if (self.last_diagnostic) |diag| {
            if (diag.err == err) {
                self.reportDiagnostic(diag, "error");
                return;
            }
        }
        std.debug.print("error: {s}\n", .{@errorName(err)});
    }

    fn clearDiagnostics(self: *Compiler) void {
        self.diagnostic_storage_len = 0;
        self.last_diagnostic = null;
        self.warning_count = 0;
        self.dropped_warning_count = 0;
    }

    fn promoteWarningsToErrors(self: *Compiler) !void {
        if (!self.warnings_as_errors) return;
        const warnings = self.warningDiagnostics();
        if (warnings.len == 0) return;

        var diag = warnings[0];
        diag.severity = .@"error";
        self.setDiagnostic(diag);
        return diag.err;
    }

    fn reportDiagnostic(
        self: *const Compiler,
        diag: Diagnostic,
        label: []const u8,
    ) void {
        std.debug.print(
            "{s}: {s}\n",
            .{ label, diagnosticSummary(diag) },
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
        reportDiagnosticDetail(self, diag.detail);
        self.reportDiagnosticNotes(diag);
        self.reportDiagnosticRelated(diag);
        self.reportDiagnosticLocation(diag);
    }

    fn reportDiagnosticLocation(
        self: *const Compiler,
        diag: Diagnostic,
    ) void {
        const span = diag.span orelse return;
        const source_info = self.sourceInfo(diag.source) orelse return;
        self.reportSpanLocation("", source_info, span);
    }

    fn reportDiagnosticNotes(self: *const Compiler, diag: Diagnostic) void {
        for (diag.noteSlice()) |note| {
            std.debug.print("  note: {s}\n", .{note.message});
            const span = note.span orelse continue;
            const source_info = self.sourceInfo(note.source) orelse continue;
            self.reportSpanLocation("note", source_info, span);
        }
    }

    fn reportDiagnosticRelated(
        self: *const Compiler,
        diag: Diagnostic,
    ) void {
        for (diag.relatedSlice()) |related| {
            std.debug.print("  related: {s}\n", .{related.label});
            const source_info = self.sourceInfo(related.source) orelse continue;
            self.reportSpanLocation("related", source_info, related.span);
        }
    }

    fn reportSpanLocation(
        self: *const Compiler,
        prefix: []const u8,
        source_info: SourceInfo,
        span: Span,
    ) void {
        _ = self;
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

    fn sourceInfo(
        self: *const Compiler,
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

    pub fn setDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.last_diagnostic = self.stableDiagnostic(diag);
    }

    fn stableDiagnostic(self: *Compiler, diag: Diagnostic) Diagnostic {
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
        self: *Compiler,
        detail: DiagnosticDetail,
    ) DiagnosticDetail {
        return switch (detail) {
            .none => .none,
            .unknown_math_token => |info| .{ .unknown_math_token = .{
                .token = self.stableRequiredString(info.token),
            } },
            .missing_binder_assignment => |info| .{
                .missing_binder_assignment = .{
                    .binder_name = self.stableRequiredString(info.binder_name),
                },
            },
            .missing_congruence_rule => |info| .{ .missing_congruence_rule = .{
                .reason = info.reason,
                .term_name = self.stableString(info.term_name),
                .sort_name = self.stableString(info.sort_name),
                .arg_index = info.arg_index,
            } },
            .hypothesis_ref => |info| .{ .hypothesis_ref = info },
        };
    }

    fn stableString(
        self: *Compiler,
        value: ?[]const u8,
    ) ?[]const u8 {
        const actual = value orelse return null;
        return self.stableRequiredString(actual);
    }

    fn stableRequiredString(
        self: *Compiler,
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

    fn isStableSourceSlice(self: *const Compiler, value: []const u8) bool {
        if (isSubslice(self.source, value)) return true;
        if (self.proof_source) |proof_source| {
            if (isSubslice(proof_source, value)) return true;
        }
        return false;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;

fn reportDiagnosticDetail(
    _: *const Compiler,
    detail: DiagnosticDetail,
) void {
    switch (detail) {
        .none => {},
        .unknown_math_token => |info| {
            std.debug.print("  token: {s}\n", .{info.token});
        },
        .missing_binder_assignment => |info| {
            std.debug.print("  missing binder: {s}\n", .{info.binder_name});
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
