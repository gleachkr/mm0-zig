const std = @import("std");
const MmbWriter = @import("./mmb_writer.zig");
const CompilerDiag = @import("./compiler/diag.zig");
const DiagnosticDetail = CompilerDiag.DiagnosticDetail;
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
pub const CheckedRef = CheckedIr.CheckedRef;
pub const CheckedLine = CheckedIr.CheckedLine;
pub const appendRuleLine = CheckedIr.appendRuleLine;
pub const appendTransportLine = CheckedIr.appendTransportLine;

pub const Compiler = struct {
    pub const max_warnings = 32;

    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    last_diagnostic: ?Diagnostic,
    warning_storage: [max_warnings]Diagnostic = undefined,
    warning_count: usize = 0,
    dropped_warning_count: usize = 0,
    warnings_as_errors: bool = false,
    debug: DebugConfig,

    const PipelineOutput = Pipeline.Output;

    pub fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = null,
            .last_diagnostic = null,
            .warning_storage = undefined,
            .warning_count = 0,
            .dropped_warning_count = 0,
            .warnings_as_errors = false,
            .debug = DebugConfig.none,
        };
    }

    pub fn initWithProof(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: []const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = proof_source,
            .last_diagnostic = null,
            .warning_storage = undefined,
            .warning_count = 0,
            .dropped_warning_count = 0,
            .warnings_as_errors = false,
            .debug = DebugConfig.none,
        };
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
        var warning = diag;
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
        self.last_diagnostic = diag;
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
        reportDiagnosticDetail(diag.detail);
        self.reportDiagnosticLocation(diag);
    }

    fn reportDiagnosticLocation(
        self: *const Compiler,
        diag: Diagnostic,
    ) void {
        const span = diag.span orelse return;
        const source_info = switch (diag.source) {
            .mm0 => SourceInfo{
                .label = "source",
                .text = self.source,
            },
            .proof => SourceInfo{
                .label = "proof",
                .text = self.proof_source orelse return,
            },
        };
        const info = lineCol(source_info.text, span.start);
        const line = source_info.text[info.line_start..info.line_end];

        std.debug.print(
            "  --> {s}:{d}:{d}\n",
            .{ source_info.label, info.line, info.column },
        );
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

    pub fn setDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.last_diagnostic = diag;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;

fn reportDiagnosticDetail(detail: DiagnosticDetail) void {
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
