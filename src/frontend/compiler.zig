const std = @import("std");
const MmbWriter = @import("./mmb_writer.zig");
const CompilerDiag = @import("./compiler/diag.zig");
const Metadata = @import("./compiler/metadata.zig");
const CompilerVars = @import("./compiler/vars.zig");
const CheckedIr = @import("./compiler/checked_ir.zig");
const Pipeline = @import("./compiler/pipeline.zig");
const DiagnosticSinkModule = @import("./compiler/diagnostic_sink.zig");
const CompilerContextModule = @import("./compiler/context.zig");
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
pub const DiagnosticSink = DiagnosticSinkModule.DiagnosticSink;
pub const CompilerContext = CompilerContextModule.CompilerContext;
pub const CheckedRef = CheckedIr.CheckedRef;
pub const CheckedLine = CheckedIr.CheckedLine;
pub const appendRuleLine = CheckedIr.appendRuleLine;
pub const appendTransportLine = CheckedIr.appendTransportLine;

pub const Compiler = struct {
    pub const max_warnings = DiagnosticSink.max_warnings;
    pub const max_primary_diagnostics =
        DiagnosticSink.max_primary_diagnostics;

    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    diagnostics: DiagnosticSink,
    debug: DebugConfig,

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
        return CompilerContext.init(
            self.source,
            self.proof_source,
            self.debug,
            &self.diagnostics,
        );
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;
