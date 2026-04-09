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
pub const CheckedRef = CheckedIr.CheckedRef;
pub const CheckedLine = CheckedIr.CheckedLine;
pub const appendRuleLine = CheckedIr.appendRuleLine;
pub const appendTransportLine = CheckedIr.appendTransportLine;

pub const Compiler = struct {
    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    last_diagnostic: ?Diagnostic,
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
            .debug = DebugConfig.none,
        };
    }

    pub fn check(self: *Compiler) !void {
        self.last_diagnostic = null;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        try Pipeline.run(self, arena.allocator(), null);
    }

    pub fn compileMmb(
        self: *Compiler,
        out_allocator: std.mem.Allocator,
    ) ![]u8 {
        self.last_diagnostic = null;

        _ = self.proof_source orelse return error.MissingProofFile;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var emit = PipelineOutput{};
        try Pipeline.run(self, arena.allocator(), &emit);

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

    pub fn reportError(self: *const Compiler, err: anyerror) void {
        if (self.last_diagnostic) |diag| {
            if (diag.err == err) {
                std.debug.print(
                    "error: {s}\n",
                    .{diagnosticSummary(diag)},
                );
                if (diag.theorem_name) |name| {
                    std.debug.print("  theorem: {s}\n", .{name});
                }
                if (diag.block_name) |name| {
                    std.debug.print("  proof block: {s}\n", .{name});
                }
                if (diag.line_label) |label| {
                    std.debug.print("  line: {s}\n", .{label});
                }
                if (diag.rule_name) |rule| {
                    std.debug.print("  rule: {s}\n", .{rule});
                }
                if (diag.name) |name| {
                    std.debug.print("  name: {s}\n", .{name});
                }
                if (diag.expected_name) |name| {
                    std.debug.print("  expected: {s}\n", .{name});
                }
                reportDiagnosticDetail(diag.detail);
                self.reportDiagnosticLocation(diag);
                return;
            }
        }
        std.debug.print("error: {s}\n", .{@errorName(err)});
    }

    fn reportDiagnosticLocation(
        self: *const Compiler,
        diag: Diagnostic,
    ) void {
        const span = diag.span orelse return;
        const src = self.proof_source orelse return;
        const info = lineCol(src, span.start);
        const line = src[info.line_start..info.line_end];

        std.debug.print(
            "  --> proof:{d}:{d}\n",
            .{ info.line, info.column },
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
