const builtin = @import("builtin");
const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

const types = lsp.types;

const UnsupportedUriScheme = error{UnsupportedUriScheme};
const UnsupportedUriHost = error{UnsupportedUriHost};
const UnsupportedDocument = error{UnsupportedDocument};

const OpenDocument = struct {
    text: []u8,
    version: i32,
};

const LoadedText = struct {
    uri: []const u8,
    text: []const u8,
    version: ?i32,
};

const Handler = struct {
    allocator: std.mem.Allocator,
    transport: *lsp.Transport,
    docs: std.StringHashMapUnmanaged(OpenDocument),
    offset_encoding: lsp.offsets.Encoding,

    fn init(
        allocator: std.mem.Allocator,
        transport: *lsp.Transport,
    ) Handler {
        return .{
            .allocator = allocator,
            .transport = transport,
            .docs = .empty,
            .offset_encoding = .@"utf-16",
        };
    }

    fn deinit(self: *Handler) void {
        var it = self.docs.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.text);
        }
        self.docs.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn initialize(
        self: *Handler,
        _: std.mem.Allocator,
        request: types.InitializeParams,
    ) types.InitializeResult {
        if (request.capabilities.general) |general| {
            for (general.positionEncodings orelse &.{}) |encoding| {
                self.offset_encoding = switch (encoding) {
                    .@"utf-8" => .@"utf-8",
                    .@"utf-16" => .@"utf-16",
                    .@"utf-32" => .@"utf-32",
                    .custom_value => continue,
                };
                break;
            }
        }

        const capabilities: types.ServerCapabilities = .{
            .positionEncoding = switch (self.offset_encoding) {
                .@"utf-8" => .@"utf-8",
                .@"utf-16" => .@"utf-16",
                .@"utf-32" => .@"utf-32",
            },
            .textDocumentSync = .{
                .TextDocumentSyncOptions = .{
                    .openClose = true,
                    .change = .Full,
                },
            },
        };

        if (builtin.mode == .Debug) {
            lsp.basic_server.validateServerCapabilities(Handler, capabilities);
        }

        return .{
            .serverInfo = .{
                .name = "abc",
                .version = "0.1.0",
            },
            .capabilities = capabilities,
        };
    }

    pub fn initialized(
        _: *Handler,
        _: std.mem.Allocator,
        _: types.InitializedParams,
    ) void {}

    pub fn shutdown(
        _: *Handler,
        _: std.mem.Allocator,
        _: void,
    ) ?void {
        return null;
    }

    pub fn exit(
        _: *Handler,
        _: std.mem.Allocator,
        _: void,
    ) void {}

    pub fn @"textDocument/didOpen"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidOpenTextDocumentParams,
    ) !void {
        try self.putDocument(
            params.textDocument.uri,
            params.textDocument.text,
            params.textDocument.version,
        );
        try self.analyzeUri(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didChange"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidChangeTextDocumentParams,
    ) !void {
        const doc = self.docs.getPtr(params.textDocument.uri) orelse return;

        var buffer = std.ArrayListUnmanaged(u8){};
        try buffer.appendSlice(arena, doc.text);

        for (params.contentChanges) |change| {
            switch (change) {
                .literal_0 => |partial| {
                    const loc = lsp.offsets.rangeToLoc(
                        buffer.items,
                        partial.range,
                        self.offset_encoding,
                    );
                    try buffer.replaceRange(
                        arena,
                        loc.start,
                        loc.end - loc.start,
                        partial.text,
                    );
                },
                .literal_1 => |whole| {
                    buffer.clearRetainingCapacity();
                    try buffer.appendSlice(arena, whole.text);
                },
            }
        }

        const new_text = try self.allocator.dupe(u8, buffer.items);
        self.allocator.free(doc.text);
        doc.text = new_text;
        doc.version = params.textDocument.version;

        try self.analyzeUri(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didClose"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidCloseTextDocumentParams,
    ) !void {
        const uri = params.textDocument.uri;
        const path = uriToPath(arena, uri) catch {
            try self.removeDocument(uri);
            try self.clearDiagnostics(arena, uri, null);
            return;
        };
        const kind = documentKind(path);

        try self.removeDocument(uri);
        try self.clearDiagnostics(arena, uri, null);

        switch (kind) {
            .mm0 => {
                const proof_path = siblingPathForMm0(arena, path) catch return;
                const proof_uri = try pathToUri(arena, proof_path);
                if (self.docs.contains(proof_uri)) {
                    try self.analyzeUri(arena, proof_uri);
                }
            },
            .proof => {
                const mm0_path = siblingPathForProof(arena, path) catch return;
                const mm0_uri = try pathToUri(arena, mm0_path);
                if (self.docs.contains(mm0_uri)) {
                    try self.analyzeUri(arena, mm0_uri);
                } else {
                    try self.clearDiagnostics(arena, mm0_uri, null);
                }
            },
            .other => {},
        }
    }

    pub fn onResponse(
        _: *Handler,
        _: std.mem.Allocator,
        _: lsp.JsonRPCMessage.Response,
    ) void {}

    fn putDocument(
        self: *Handler,
        uri: []const u8,
        text: []const u8,
        version: i32,
    ) !void {
        const new_text = try self.allocator.dupe(u8, text);
        errdefer self.allocator.free(new_text);

        const gop = try self.docs.getOrPut(self.allocator, uri);
        if (gop.found_existing) {
            self.allocator.free(gop.value_ptr.text);
        } else {
            errdefer _ = self.docs.remove(uri);
            gop.key_ptr.* = try self.allocator.dupe(u8, uri);
        }

        gop.value_ptr.* = .{
            .text = new_text,
            .version = version,
        };
    }

    fn removeDocument(self: *Handler, uri: []const u8) !void {
        const entry = self.docs.fetchRemove(uri) orelse return;
        self.allocator.free(entry.key);
        self.allocator.free(entry.value.text);
    }

    fn analyzeUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !void {
        const doc = self.docs.get(uri) orelse return;
        const path = uriToPath(arena, uri) catch |err| {
            try self.publishMessageDiagnostic(
                arena,
                uri,
                doc.version,
                doc.text,
                switch (err) {
                    error.InvalidFormat => "document URI is not a valid URI",
                    UnsupportedUriScheme.UnsupportedUriScheme => "document URI must use the file scheme",
                    UnsupportedUriHost.UnsupportedUriHost => "file URI host must be empty or localhost",
                    else => @errorName(err),
                },
            );
            return;
        };

        switch (documentKind(path)) {
            .mm0 => try self.analyzeMm0Document(
                arena,
                uri,
                doc.version,
                doc.text,
            ),
            .proof => try self.analyzeProofDocument(
                arena,
                uri,
                doc.version,
                doc.text,
                path,
            ),
            .other => try self.clearDiagnostics(arena, uri, doc.version),
        }
    }

    fn analyzeMm0Document(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: i32,
        text: []const u8,
    ) !void {
        var compiler = mm0.Compiler.init(arena, text);
        compiler.check() catch |err| {
            if (compiler.last_diagnostic) |diag| {
                try self.publishCompilerDiagnostic(
                    arena,
                    uri,
                    version,
                    text,
                    diag,
                );
            } else {
                try self.publishMessageDiagnostic(
                    arena,
                    uri,
                    version,
                    text,
                    @errorName(err),
                );
            }
            return;
        };
        try self.publishCompilerWarnings(
            arena,
            uri,
            version,
            text,
            compiler.warningDiagnostics(),
            .mm0,
        );
    }

    fn analyzeProofDocument(
        self: *Handler,
        arena: std.mem.Allocator,
        proof_uri: []const u8,
        proof_version: i32,
        proof_text: []const u8,
        proof_path: []const u8,
    ) !void {
        const mm0_path = siblingPathForProof(arena, proof_path) catch {
            try self.publishMessageDiagnostic(
                arena,
                proof_uri,
                proof_version,
                proof_text,
                "proof files must end in .auf",
            );
            return;
        };
        const mm0_loaded = self.loadTextPreferOpenDocument(arena, mm0_path) catch |err| {
            const message = switch (err) {
                error.FileNotFound => "could not find sibling .mm0 file for this proof",
                else => try std.fmt.allocPrint(
                    arena,
                    "could not read sibling .mm0 file: {s}",
                    .{@errorName(err)},
                ),
            };
            try self.publishMessageDiagnostic(
                arena,
                proof_uri,
                proof_version,
                proof_text,
                message,
            );
            const mm0_uri = try pathToUri(arena, mm0_path);
            try self.clearDiagnostics(arena, mm0_uri, null);
            return;
        };

        var compiler = mm0.Compiler.initWithProof(
            arena,
            mm0_loaded.text,
            proof_text,
        );
        compiler.writeMmb() catch |err| {
            if (compiler.last_diagnostic) |diag| {
                switch (diag.source) {
                    .mm0 => {
                        try self.publishCompilerDiagnostic(
                            arena,
                            mm0_loaded.uri,
                            mm0_loaded.version,
                            mm0_loaded.text,
                            diag,
                        );
                        try self.clearDiagnostics(
                            arena,
                            proof_uri,
                            proof_version,
                        );
                    },
                    .proof => {
                        try self.publishCompilerDiagnostic(
                            arena,
                            proof_uri,
                            proof_version,
                            proof_text,
                            diag,
                        );
                        try self.clearDiagnostics(
                            arena,
                            mm0_loaded.uri,
                            mm0_loaded.version,
                        );
                    },
                }
            } else {
                try self.publishMessageDiagnostic(
                    arena,
                    proof_uri,
                    proof_version,
                    proof_text,
                    @errorName(err),
                );
                try self.clearDiagnostics(
                    arena,
                    mm0_loaded.uri,
                    mm0_loaded.version,
                );
            }
            return;
        };

        try self.publishCompilerWarnings(
            arena,
            proof_uri,
            proof_version,
            proof_text,
            compiler.warningDiagnostics(),
            .proof,
        );
        try self.publishCompilerWarnings(
            arena,
            mm0_loaded.uri,
            mm0_loaded.version,
            mm0_loaded.text,
            compiler.warningDiagnostics(),
            .mm0,
        );
    }

    fn loadTextPreferOpenDocument(
        self: *Handler,
        arena: std.mem.Allocator,
        path: []const u8,
    ) !LoadedText {
        const uri = try pathToUri(arena, path);
        if (self.docs.get(uri)) |doc| {
            return .{
                .uri = uri,
                .text = doc.text,
                .version = doc.version,
            };
        }

        return .{
            .uri = uri,
            .text = try readFileAlloc(arena, path),
            .version = null,
        };
    }

    fn publishCompilerDiagnostic(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
        text: []const u8,
        diag: mm0.CompilerDiagnostic,
    ) !void {
        const diagnostics = try arena.alloc(types.Diagnostic, 1);
        diagnostics[0] = try compilerDiagnosticToLsp(
            arena,
            text,
            diag,
            self.offset_encoding,
        );
        try self.publishDiagnostics(arena, uri, version, diagnostics);
    }

    fn publishCompilerWarnings(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
        text: []const u8,
        diags: []const mm0.CompilerDiagnostic,
        source: mm0.CompilerDiagnosticSource,
    ) !void {
        const diagnostics = try compilerDiagnosticsToLsp(
            arena,
            text,
            diags,
            source,
            self.offset_encoding,
        );
        if (diagnostics.len == 0) {
            try self.clearDiagnostics(arena, uri, version);
            return;
        }
        try self.publishDiagnostics(arena, uri, version, diagnostics);
    }

    fn publishMessageDiagnostic(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
        text: []const u8,
        message: []const u8,
    ) !void {
        const diagnostics = try arena.alloc(types.Diagnostic, 1);
        diagnostics[0] = .{
            .range = zeroRange(text, self.offset_encoding),
            .severity = .Error,
            .source = "abc",
            .message = message,
        };
        try self.publishDiagnostics(arena, uri, version, diagnostics);
    }

    fn clearDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
    ) !void {
        try self.publishDiagnostics(arena, uri, version, &.{});
    }

    fn publishDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
        diagnostics: []const types.Diagnostic,
    ) !void {
        try self.transport.writeNotification(
            arena,
            "textDocument/publishDiagnostics",
            types.PublishDiagnosticsParams,
            .{
                .uri = uri,
                .version = version,
                .diagnostics = diagnostics,
            },
            .{ .emit_null_optional_fields = false },
        );
    }
};

const DocumentKind = enum {
    mm0,
    proof,
    other,
};

pub fn run(allocator: std.mem.Allocator) !void {
    var read_buffer: [4096]u8 = undefined;
    var stdio_transport = lsp.Transport.Stdio.init(
        &read_buffer,
        .stdin(),
        .stdout(),
    );
    const transport: *lsp.Transport = &stdio_transport.transport;

    var handler = Handler.init(allocator, transport);
    defer handler.deinit();

    try lsp.basic_server.run(
        allocator,
        transport,
        &handler,
        std.log.err,
    );
}

fn uriToPath(
    allocator: std.mem.Allocator,
    uri_text: []const u8,
) ![]const u8 {
    const uri = try std.Uri.parse(uri_text);
    if (!std.mem.eql(u8, uri.scheme, "file")) {
        return UnsupportedUriScheme.UnsupportedUriScheme;
    }
    if (uri.host) |host| {
        const host_text = try host.toRawMaybeAlloc(allocator);
        if (host_text.len != 0 and
            !std.mem.eql(u8, host_text, "localhost"))
        {
            return UnsupportedUriHost.UnsupportedUriHost;
        }
    }
    return try uri.path.toRawMaybeAlloc(allocator);
}

fn pathToUri(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "file://{f}",
        .{std.fmt.alt(std.Uri.Component{ .raw = path }, .formatPath)},
    );
}

fn siblingPathForProof(
    allocator: std.mem.Allocator,
    proof_path: []const u8,
) ![]const u8 {
    if (!std.mem.endsWith(u8, proof_path, ".auf")) {
        return UnsupportedDocument.UnsupportedDocument;
    }
    return try std.fmt.allocPrint(
        allocator,
        "{s}.mm0",
        .{proof_path[0 .. proof_path.len - 4]},
    );
}

fn siblingPathForMm0(
    allocator: std.mem.Allocator,
    mm0_path: []const u8,
) ![]const u8 {
    if (!std.mem.endsWith(u8, mm0_path, ".mm0")) {
        return UnsupportedDocument.UnsupportedDocument;
    }
    return try std.fmt.allocPrint(
        allocator,
        "{s}.auf",
        .{mm0_path[0 .. mm0_path.len - 4]},
    );
}

fn documentKind(path: []const u8) DocumentKind {
    if (std.mem.endsWith(u8, path, ".mm0")) return .mm0;
    if (std.mem.endsWith(u8, path, ".auf")) return .proof;
    return .other;
}

fn readFileAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    if (std.fs.path.isAbsolute(path)) {
        const file = try std.fs.openFileAbsolute(path, .{});
        defer file.close();
        return try file.readToEndAlloc(allocator, std.math.maxInt(usize));
    }

    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

fn compilerDiagnosticsToLsp(
    arena: std.mem.Allocator,
    text: []const u8,
    diags: []const mm0.CompilerDiagnostic,
    source: mm0.CompilerDiagnosticSource,
    encoding: lsp.offsets.Encoding,
) ![]types.Diagnostic {
    var count: usize = 0;
    for (diags) |diag| {
        if (diag.source == source) count += 1;
    }
    const result = try arena.alloc(types.Diagnostic, count);
    var out_idx: usize = 0;
    for (diags) |diag| {
        if (diag.source != source) continue;
        result[out_idx] = try compilerDiagnosticToLsp(
            arena,
            text,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    return result;
}

fn compilerDiagnosticToLsp(
    arena: std.mem.Allocator,
    text: []const u8,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) !types.Diagnostic {
    return .{
        .range = rangeForDiagnostic(text, diag, encoding),
        .severity = diagnosticSeverityToLsp(diag.severity),
        .source = "abc",
        .message = try compilerDiagnosticMessage(arena, diag),
    };
}

fn diagnosticSeverityToLsp(
    severity: mm0.CompilerDiagnosticSeverity,
) types.DiagnosticSeverity {
    return switch (severity) {
        .@"error" => .Error,
        .warning => .Warning,
    };
}

fn rangeForDiagnostic(
    text: []const u8,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) types.Range {
    const span = diag.span orelse return zeroRange(text, encoding);
    const start = @min(span.start, text.len);
    const end = @max(start, @min(span.end, text.len));
    return lsp.offsets.locToRange(
        text,
        .{ .start = start, .end = end },
        encoding,
    );
}

fn zeroRange(
    text: []const u8,
    encoding: lsp.offsets.Encoding,
) types.Range {
    return lsp.offsets.locToRange(
        text,
        .{ .start = 0, .end = 0 },
        encoding,
    );
}

fn compilerDiagnosticMessage(
    arena: std.mem.Allocator,
    diag: mm0.CompilerDiagnostic,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(arena);

    try writer.writeAll(mm0.compilerDiagnosticSummary(diag));
    try appendNamedLine(&writer, "theorem", diag.theorem_name);
    try appendNamedLine(&writer, "proof block", diag.block_name);
    try appendNamedLine(&writer, "line", diag.line_label);
    try appendNamedLine(&writer, "rule", diag.rule_name);
    try appendNamedLine(&writer, "name", diag.name);
    try appendNamedLine(&writer, "expected", diag.expected_name);

    switch (diag.detail) {
        .none => {},
        .unknown_math_token => |detail| {
            try writer.print("\ntoken: {s}", .{detail.token});
        },
        .missing_binder_assignment => |detail| {
            try writer.print(
                "\nmissing binder: {s}",
                .{detail.binder_name},
            );
        },
        .missing_congruence_rule => |detail| {
            try writer.writeAll("\nmissing congruence: ");
            try mm0.writeCompilerMissingCongruenceRuleSummary(&writer, detail);
            try appendNamedLine(&writer, "sort", detail.sort_name);
        },
        .related_rule => |detail| {
            try writer.print(
                "\ndeclared later in: {s}",
                .{@tagName(detail.source)},
            );
        },
        .hypothesis_ref => |detail| {
            try writer.print("\nhypothesis ref: #{d}", .{detail.index});
        },
    }

    return buf.items;
}

fn appendNamedLine(
    writer: anytype,
    label: []const u8,
    value: ?[]const u8,
) !void {
    if (value) |actual| {
        try writer.print("\n{s}: {s}", .{ label, actual });
    }
}

test "uri path roundtrip" {
    const allocator = std.testing.allocator;
    const path = "/tmp/a path/example.mm0";
    const uri = try pathToUri(allocator, path);
    defer allocator.free(uri);

    const roundtrip = try uriToPath(allocator, uri);
    defer allocator.free(roundtrip);
    try std.testing.expectEqualStrings(path, roundtrip);
}

test "proof sibling path" {
    const allocator = std.testing.allocator;
    const path = try siblingPathForProof(allocator, "/tmp/demo.auf");
    defer allocator.free(path);
    try std.testing.expectEqualStrings("/tmp/demo.mm0", path);
}

test "document kind" {
    try std.testing.expectEqual(DocumentKind.mm0, documentKind("/tmp/a.mm0"));
    try std.testing.expectEqual(DocumentKind.proof, documentKind("/tmp/a.auf"));
    try std.testing.expectEqual(DocumentKind.other, documentKind("/tmp/a.txt"));
}

test "compiler diagnostic severity maps to LSP severity" {
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diagnosticSeverityToLsp(mm0.CompilerDiagnosticSeverity.@"error"),
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        diagnosticSeverityToLsp(mm0.CompilerDiagnosticSeverity.warning),
    );
}

test "compiler diagnostics filter by source for LSP publishing" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();
    const diags = [_]mm0.CompilerDiagnostic{
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.AmbiguousAcuiMatch,
            .source = .proof,
        },
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const proof = try compilerDiagnosticsToLsp(
        allocator,
        "",
        &diags,
        .proof,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 1), proof.len);
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        proof[0].severity.?,
    );

    const mm0_diags = try compilerDiagnosticsToLsp(
        allocator,
        "",
        &diags,
        .mm0,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 1), mm0_diags.len);
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        mm0_diags[0].severity.?,
    );
}
