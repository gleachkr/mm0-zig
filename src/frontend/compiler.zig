const std = @import("std");
const MmbWriter = @import("./compiler/mmb_writer.zig");
const CompilerDiag = @import("./compiler/diag.zig");
const Pipeline = @import("./compiler/pipeline.zig");
const DiagnosticSink = @import("./compiler/diagnostic_sink.zig")
    .DiagnosticSink;
const CompilerContext = @import("./compiler/context.zig").CompilerContext;
const DebugConfig = @import("./debug.zig").DebugConfig;

const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticSource = CompilerDiag.DiagnosticSource;

pub const Compiler = struct {
    pub const max_warnings = DiagnosticSink.max_warnings;
    pub const max_primary_diagnostics =
        DiagnosticSink.max_primary_diagnostics;

    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    diagnostics: DiagnosticSink,
    debug: DebugConfig,
    allow_search_placeholders: bool,

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
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = proof_source,
            .diagnostics = DiagnosticSink.init(source, proof_source),
            .debug = DebugConfig.none,
            .allow_search_placeholders = false,
        };
    }

    pub fn check(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var compiler_context = self.context();
        try Pipeline.run(&compiler_context, arena.allocator(), null);
        try self.diagnostics.promoteWarningsToErrors();
    }

    pub fn analyze(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var compiler_context = self.context();
        if (self.proof_source != null) {
            try Pipeline.analyze(&compiler_context, arena.allocator());
            return;
        }
        try Pipeline.analyzeMm0(&compiler_context, arena.allocator());
    }

    pub fn analyzeMm0(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var compiler_context = self.context();
        try Pipeline.analyzeMm0(&compiler_context, arena.allocator());
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
        var compiler_context = self.context();
        try Pipeline.run(&compiler_context, arena.allocator(), &emit);
        try self.diagnostics.promoteWarningsToErrors();

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

    pub fn primaryDiagnostics(self: *const Compiler) []const Diagnostic {
        return self.diagnostics.primaryDiagnostics();
    }

    pub fn warningDiagnostics(self: *const Compiler) []const Diagnostic {
        return self.diagnostics.warningDiagnostics();
    }

    pub fn omittedPrimaryDiagnostic(
        self: *const Compiler,
        source: DiagnosticSource,
    ) ?Diagnostic {
        return self.diagnostics.omittedPrimaryDiagnostic(source);
    }

    pub fn addPrimaryDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.diagnostics.addPrimaryDiagnostic(diag);
    }

    pub fn addWarning(self: *Compiler, diag: Diagnostic) void {
        self.diagnostics.addWarning(diag);
    }

    pub fn reportWarnings(self: *const Compiler) void {
        self.diagnostics.reportWarnings();
    }

    pub fn reportError(self: *const Compiler, err: anyerror) void {
        self.diagnostics.reportError(err);
    }

    pub fn setDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.diagnostics.setDiagnostic(diag);
    }

    pub fn getDiagnostic(self: *const Compiler) ?Diagnostic {
        return self.diagnostics.getDiagnostic();
    }

    pub fn restoreDiagnostic(self: *Compiler, diag: ?Diagnostic) void {
        self.diagnostics.restoreDiagnostic(diag);
    }

    fn clearDiagnostics(self: *Compiler) void {
        self.diagnostics.clear();
    }

    fn context(self: *Compiler) CompilerContext {
        var result = CompilerContext.init(
            self.source,
            self.proof_source,
            self.debug,
            &self.diagnostics,
        );
        result.allow_search_placeholders = self.allow_search_placeholders;
        return result;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;
