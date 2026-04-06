const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const MmbWriter = @import("./mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const CompilerDiag = @import("./compiler_diag.zig");
const Metadata = @import("./compiler/metadata.zig");
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const ProofScriptParser = @import("./proof_script.zig").Parser;
const TheoremBlock = @import("./proof_script.zig").TheoremBlock;
const Span = @import("./proof_script.zig").Span;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const CheckedIr = @import("./compiler/checked_ir.zig");
pub const DebugConfig = @import("./debug.zig").DebugConfig;

// Sub-modules
const Emit = @import("./compiler_emit.zig");
const Check = @import("./compiler_check.zig");
const CompilerVars = @import("./compiler_vars.zig");

pub const ViewDecl = Metadata.ViewDecl;
pub const FreshDecl = Metadata.FreshDecl;
pub const SortVarDecl = Metadata.SortVarDecl;
pub const SortVarRegistry = Metadata.SortVarRegistry;
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

        var parser = MM0Parser.init(self.source, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
        var fresh_bindings = std.AutoHashMap(u32, []const FreshDecl).init(
            arena.allocator(),
        );
        var views = std.AutoHashMap(u32, ViewDecl).init(arena.allocator());
        var sort_vars = SortVarRegistry.init(arena.allocator());
        var proof_parser = if (self.proof_source) |proof|
            ProofScriptParser.init(arena.allocator(), proof)
        else
            null;

        while (try parser.next()) |stmt| {
            try CompilerVars.validateSortVarCollisions(&parser, &sort_vars);
            switch (stmt) {
                .assertion => |assertion| {
                    if (assertion.kind != .theorem) {
                        try env.addStmt(stmt);
                        try Metadata.processAssertionMetadata(
                            arena.allocator(),
                            &parser,
                            &env,
                            &registry,
                            &fresh_bindings,
                            &views,
                            assertion,
                            parser.last_annotations,
                        );
                        continue;
                    }

                    var theorem = TheoremContext.init(arena.allocator());
                    defer theorem.deinit();

                    try theorem.seedAssertion(assertion);
                    const theorem_concl = try theorem.internParsedExpr(
                        assertion.concl,
                    );

                    if (proof_parser) |*proofs| {
                        const block = try self.expectProofBlock(
                            proofs,
                            assertion.name,
                        );
                        _ = Check.checkTheoremBlock(
                            self,
                            arena.allocator(),
                            &parser,
                            &env,
                            &registry,
                            &fresh_bindings,
                            &views,
                            &sort_vars,
                            assertion,
                            block,
                            &theorem,
                            theorem_concl,
                        ) catch |err| {
                            self.setTheoremDiagnosticIfMissing(
                                assertion.name,
                                block.name_span,
                                err,
                            );
                            return err;
                        };
                    }

                    try env.addStmt(stmt);
                    try Metadata.processAssertionMetadata(
                        arena.allocator(),
                        &parser,
                        &env,
                        &registry,
                        &fresh_bindings,
                        &views,
                        assertion,
                        parser.last_annotations,
                    );
                },
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try Metadata.processTermMetadata(
                        &env,
                        &registry,
                        term_stmt,
                        parser.last_annotations,
                    );
                },
                .sort => |sort_stmt| {
                    try env.addStmt(stmt);
                    try Metadata.processSortMetadata(
                        &parser,
                        sort_stmt,
                        parser.last_annotations,
                        &sort_vars,
                    );
                },
            }
        }

        try CompilerVars.validateSortVarCollisions(&parser, &sort_vars);

        if (proof_parser) |*proofs| {
            if (try proofs.nextBlock()) |block| {
                self.setDiagnostic(.{
                    .kind = .extra_proof_block,
                    .err = error.ExtraProofBlock,
                    .block_name = block.name,
                    .span = block.name_span,
                });
                return error.ExtraProofBlock;
            }
        }
    }

    pub fn compileMmb(
        self: *Compiler,
        out_allocator: std.mem.Allocator,
    ) ![]u8 {
        self.last_diagnostic = null;

        const proof_source = self.proof_source orelse return error.MissingProofFile;

        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();

        var parser = MM0Parser.init(self.source, allocator);
        var proof_parser = ProofScriptParser.init(allocator, proof_source);
        var env = GlobalEnv.init(allocator);
        var registry = RewriteRegistry.init(allocator);
        var fresh_bindings = std.AutoHashMap(u32, []const FreshDecl).init(
            allocator,
        );
        var views = std.AutoHashMap(u32, ViewDecl).init(allocator);
        var sort_vars = SortVarRegistry.init(allocator);

        var sort_names = std.ArrayListUnmanaged([]const u8){};
        var sorts = std.ArrayListUnmanaged(@import("../trusted/sorts.zig").Sort){};
        var terms = std.ArrayListUnmanaged(TermRecord){};
        var theorems = std.ArrayListUnmanaged(TheoremRecord){};
        var statements = std.ArrayListUnmanaged(Statement){};

        while (try parser.next()) |stmt| {
            try CompilerVars.validateSortVarCollisions(&parser, &sort_vars);
            switch (stmt) {
                .sort => |sort_stmt| {
                    try sort_names.append(allocator, sort_stmt.name);
                    try sorts.append(allocator, sort_stmt.modifiers);
                    try statements.append(allocator, .{
                        .cmd = .Sort,
                        .body = &.{},
                    });
                    try env.addStmt(stmt);
                    try Metadata.processSortMetadata(
                        &parser,
                        sort_stmt,
                        parser.last_annotations,
                        &sort_vars,
                    );
                },
                .term => |term_stmt| {
                    const term_record = try Emit.compileTermRecord(
                        allocator,
                        &parser,
                        term_stmt,
                    );
                    try terms.append(allocator, term_record);
                    try statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = if (term_stmt.is_def)
                            try Emit.buildDefProofBody(allocator, &parser, term_stmt)
                        else
                            &.{},
                    });
                    try env.addStmt(stmt);
                    try Metadata.processTermMetadata(
                        &env,
                        &registry,
                        term_stmt,
                        parser.last_annotations,
                    );
                },
                .assertion => |assertion| {
                    var theorem = TheoremContext.init(allocator);
                    defer theorem.deinit();
                    try theorem.seedAssertion(assertion);
                    const theorem_concl = try theorem.internParsedExpr(
                        assertion.concl,
                    );
                    const unify = try Emit.buildAssertionUnifyStream(
                        allocator,
                        &theorem,
                        theorem_concl,
                    );
                    const args = try Emit.buildArgArray(&parser, assertion.args);
                    const hyp_names = try Emit.buildHypNames(
                        allocator,
                        assertion.hyps.len,
                    );

                    switch (assertion.kind) {
                        .axiom => {
                            const body = try Emit.buildAxiomProofBody(
                                allocator,
                                &theorem,
                                theorem_concl,
                            );
                            try theorems.append(allocator, .{
                                .args = args,
                                .unify = unify,
                                .name = assertion.name,
                                .var_names = try Emit.buildTheoremVarNames(
                                    allocator,
                                    assertion.arg_names,
                                    theorem.theorem_dummies.items.len,
                                ),
                                .hyp_names = hyp_names,
                            });
                            try statements.append(allocator, .{
                                .cmd = .Axiom,
                                .body = body,
                            });
                            try env.addStmt(stmt);
                            try Metadata.processAssertionMetadata(
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &fresh_bindings,
                                &views,
                                assertion,
                                parser.last_annotations,
                            );
                        },
                        .theorem => {
                            const block = try self.expectProofBlock(
                                &proof_parser,
                                assertion.name,
                            );
                            const checked = Check.checkTheoremBlock(
                                self,
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &fresh_bindings,
                                &views,
                                &sort_vars,
                                assertion,
                                block,
                                &theorem,
                                theorem_concl,
                            ) catch |err| {
                                self.setTheoremDiagnosticIfMissing(
                                    assertion.name,
                                    block.name_span,
                                    err,
                                );
                                return err;
                            };
                            const body = Emit.buildTheoremProofBody(
                                allocator,
                                &theorem,
                                &env,
                                checked,
                            ) catch |err| {
                                self.setTheoremDiagnosticIfMissing(
                                    assertion.name,
                                    block.name_span,
                                    err,
                                );
                                return err;
                            };
                            try theorems.append(allocator, .{
                                .args = args,
                                .unify = unify,
                                .name = assertion.name,
                                .var_names = try Emit.buildTheoremVarNames(
                                    allocator,
                                    assertion.arg_names,
                                    theorem.theorem_dummies.items.len,
                                ),
                                .hyp_names = hyp_names,
                            });
                            try statements.append(allocator, .{
                                .cmd = .Thm,
                                .body = body,
                            });
                            try env.addStmt(stmt);
                            try Metadata.processAssertionMetadata(
                                allocator,
                                &parser,
                                &env,
                                &registry,
                                &fresh_bindings,
                                &views,
                                assertion,
                                parser.last_annotations,
                            );
                        },
                    }
                },
            }
        }

        try CompilerVars.validateSortVarCollisions(&parser, &sort_vars);

        if (try proof_parser.nextBlock()) |block| {
            self.setDiagnostic(.{
                .kind = .extra_proof_block,
                .err = error.ExtraProofBlock,
                .block_name = block.name,
                .span = block.name_span,
            });
            return error.ExtraProofBlock;
        }

        return try MmbWriter.buildFile(
            out_allocator,
            sort_names.items,
            sorts.items,
            terms.items,
            theorems.items,
            statements.items,
        );
    }

    pub fn writeMmb(self: *Compiler) !void {
        const bytes = try self.compileMmb(self.allocator);
        self.allocator.free(bytes);
    }

    pub fn writeMm0(self: *Compiler) !void {
        try self.check();
        return error.Unimplemented;
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

    fn setTheoremDiagnosticIfMissing(
        self: *Compiler,
        theorem_name: []const u8,
        span: Span,
        err: anyerror,
    ) void {
        if (self.last_diagnostic != null) return;
        self.setDiagnostic(.{
            .kind = .generic,
            .err = err,
            .theorem_name = theorem_name,
            .span = span,
        });
    }

    fn expectProofBlock(
        self: *Compiler,
        proof_parser: *ProofScriptParser,
        theorem_name: []const u8,
    ) !TheoremBlock {
        const block = try proof_parser.nextBlock() orelse {
            self.setDiagnostic(.{
                .kind = .missing_proof_block,
                .err = error.MissingProofBlock,
                .theorem_name = theorem_name,
            });
            return error.MissingProofBlock;
        };
        if (!std.mem.eql(u8, block.name, theorem_name)) {
            self.setDiagnostic(.{
                .kind = .theorem_name_mismatch,
                .err = error.TheoremNameMismatch,
                .theorem_name = theorem_name,
                .block_name = block.name,
                .expected_name = theorem_name,
                .span = block.name_span,
            });
            return error.TheoremNameMismatch;
        }
        return block;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;

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
