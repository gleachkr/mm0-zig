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

const DiagnosticDocument = struct {
    uri: []const u8,
    text: []const u8,
    version: ?i32,
};

const DiagnosticContext = struct {
    mm0: ?DiagnosticDocument = null,
    proof: ?DiagnosticDocument = null,

    fn sourceDocument(
        self: DiagnosticContext,
        source: mm0.CompilerDiagnosticSource,
    ) ?DiagnosticDocument {
        return switch (source) {
            .mm0 => self.mm0,
            .proof => self.proof,
        };
    }
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
                path,
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
        path: []const u8,
    ) !void {
        if (siblingPathForMm0(arena, path)) |proof_path| {
            const proof_uri = try pathToUri(arena, proof_path);
            if (self.docs.get(proof_uri)) |proof_doc| {
                try self.analyzeProofDocument(
                    arena,
                    proof_uri,
                    proof_doc.version,
                    proof_doc.text,
                    proof_path,
                );
                return;
            }
        } else |_| {}

        const diag_context: DiagnosticContext = .{
            .mm0 = .{
                .uri = uri,
                .text = text,
                .version = version,
            },
        };

        var compiler = mm0.Compiler.init(arena, text);
        compiler.analyzeMm0() catch |err| {
            if (compiler.last_diagnostic != null or
                compiler.primaryDiagnostics().len != 0 or
                compiler.warningDiagnostics().len != 0)
            {
                try self.publishCompilerSourceDiagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.last_diagnostic,
                    compiler.omittedPrimaryDiagnostic(.mm0),
                    .mm0,
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
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            null,
            compiler.omittedPrimaryDiagnostic(.mm0),
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

        const diag_context: DiagnosticContext = .{
            .mm0 = .{
                .uri = mm0_loaded.uri,
                .text = mm0_loaded.text,
                .version = mm0_loaded.version,
            },
            .proof = .{
                .uri = proof_uri,
                .text = proof_text,
                .version = proof_version,
            },
        };

        var compiler = mm0.Compiler.initWithProof(
            arena,
            mm0_loaded.text,
            proof_text,
        );
        compiler.analyze() catch |err| {
            if (compiler.last_diagnostic != null or
                compiler.primaryDiagnostics().len != 0 or
                compiler.warningDiagnostics().len != 0)
            {
                try self.publishCompilerSourceDiagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.last_diagnostic,
                    compiler.omittedPrimaryDiagnostic(.proof),
                    .proof,
                );
                try self.publishCompilerSourceDiagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.last_diagnostic,
                    compiler.omittedPrimaryDiagnostic(.mm0),
                    .mm0,
                );
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

        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            compiler.last_diagnostic,
            compiler.omittedPrimaryDiagnostic(.proof),
            .proof,
        );
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            compiler.last_diagnostic,
            compiler.omittedPrimaryDiagnostic(.mm0),
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
        diag_context: DiagnosticContext,
        diag: mm0.CompilerDiagnostic,
    ) !void {
        const doc = diag_context.sourceDocument(diag.source) orelse return;
        const diagnostics = try arena.alloc(types.Diagnostic, 1);
        diagnostics[0] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            self.offset_encoding,
        );
        try self.publishDiagnostics(
            arena,
            doc.uri,
            doc.version,
            diagnostics,
        );
    }

    fn publishCompilerWarnings(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        diags: []const mm0.CompilerDiagnostic,
        source: mm0.CompilerDiagnosticSource,
    ) !void {
        const doc = diag_context.sourceDocument(source) orelse return;
        const diagnostics = try compilerDiagnosticsToLsp(
            arena,
            diag_context,
            diags,
            source,
            self.offset_encoding,
        );
        if (diagnostics.len == 0) {
            try self.clearDiagnostics(arena, doc.uri, doc.version);
            return;
        }
        try self.publishDiagnostics(
            arena,
            doc.uri,
            doc.version,
            diagnostics,
        );
    }

    fn publishCompilerSourceDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        primary: []const mm0.CompilerDiagnostic,
        warnings: []const mm0.CompilerDiagnostic,
        extra: ?mm0.CompilerDiagnostic,
        omitted: ?mm0.CompilerDiagnostic,
        source: mm0.CompilerDiagnosticSource,
    ) !void {
        const doc = diag_context.sourceDocument(source) orelse return;
        const diagnostics = try compilerSourceDiagnosticsToLsp(
            arena,
            diag_context,
            primary,
            warnings,
            extra,
            omitted,
            source,
            self.offset_encoding,
        );
        if (diagnostics.len == 0) {
            try self.clearDiagnostics(arena, doc.uri, doc.version);
            return;
        }
        try self.publishDiagnostics(
            arena,
            doc.uri,
            doc.version,
            diagnostics,
        );
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
    diag_context: DiagnosticContext,
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
            diag_context,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    return result;
}

fn compilerSourceDiagnosticsToLsp(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    primary: []const mm0.CompilerDiagnostic,
    warnings: []const mm0.CompilerDiagnostic,
    extra: ?mm0.CompilerDiagnostic,
    omitted: ?mm0.CompilerDiagnostic,
    source: mm0.CompilerDiagnosticSource,
    encoding: lsp.offsets.Encoding,
) ![]types.Diagnostic {
    var count: usize = 0;
    if (extra) |diag| {
        if (diag.source == source) count += 1;
    }
    for (primary) |diag| {
        if (diag.source == source) count += 1;
    }
    for (warnings) |diag| {
        if (diag.source == source) count += 1;
    }
    if (omitted) |diag| {
        if (diag.source == source) count += 1;
    }

    const result = try arena.alloc(types.Diagnostic, count);
    var out_idx: usize = 0;
    if (extra) |diag| {
        if (diag.source == source) {
            result[out_idx] = try compilerDiagnosticToLsp(
                arena,
                diag_context,
                diag,
                encoding,
            );
            out_idx += 1;
        }
    }
    for (primary) |diag| {
        if (diag.source != source) continue;
        result[out_idx] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    if (omitted) |diag| {
        if (diag.source == source) {
            result[out_idx] = try compilerDiagnosticToLsp(
                arena,
                diag_context,
                diag,
                encoding,
            );
            out_idx += 1;
        }
    }
    for (warnings) |diag| {
        if (diag.source != source) continue;
        result[out_idx] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    return result;
}

fn compilerDiagnosticToLsp(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) !types.Diagnostic {
    const doc = diag_context.sourceDocument(diag.source) orelse {
        return error.MissingDiagnosticDocument;
    };
    return .{
        .range = rangeForDiagnostic(doc.text, diag, encoding),
        .severity = diagnosticSeverityToLsp(diag.severity),
        .source = "abc",
        .message = try compilerDiagnosticMessage(arena, diag),
        .relatedInformation = try compilerDiagnosticRelatedInformation(
            arena,
            diag_context,
            diag,
            encoding,
        ),
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

fn compilerDiagnosticRelatedInformation(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) !?[]const types.DiagnosticRelatedInformation {
    var count: usize = 0;
    for (diag.noteSlice()) |note| {
        if (note.span != null and
            diag_context.sourceDocument(note.source) != null)
        {
            count += 1;
        }
    }
    for (diag.relatedSlice()) |related| {
        if (diag_context.sourceDocument(related.source) != null) {
            count += 1;
        }
    }
    if (count == 0) return null;

    const result = try arena.alloc(types.DiagnosticRelatedInformation, count);
    var idx: usize = 0;
    for (diag.noteSlice()) |note| {
        const span = note.span orelse continue;
        const doc = diag_context.sourceDocument(note.source) orelse continue;
        result[idx] = .{
            .location = .{
                .uri = doc.uri,
                .range = lsp.offsets.locToRange(
                    doc.text,
                    .{ .start = span.start, .end = span.end },
                    encoding,
                ),
            },
            .message = note.message,
        };
        idx += 1;
    }
    for (diag.relatedSlice()) |related| {
        const doc = diag_context.sourceDocument(related.source) orelse continue;
        result[idx] = .{
            .location = .{
                .uri = doc.uri,
                .range = lsp.offsets.locToRange(
                    doc.text,
                    .{ .start = related.span.start, .end = related.span.end },
                    encoding,
                ),
            },
            .message = related.label,
        };
        idx += 1;
    }
    return result;
}

fn diagnosticPhaseName(phase: mm0.CompilerDiagnosticPhase) []const u8 {
    return switch (phase) {
        .parse => "parse",
        .inference => "inference",
        .theorem_application => "theorem application",
        .freshen => "freshen",
        .normalization => "normalization",
        .final_reconciliation => "final reconciliation",
    };
}

fn compilerDiagnosticMessage(
    arena: std.mem.Allocator,
    diag: mm0.CompilerDiagnostic,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(arena);

    if (diag.kind == .omitted_diagnostics) {
        switch (diag.detail) {
            .omitted_diagnostics => |detail| {
                try mm0.writeCompilerOmittedDiagnosticsSummary(
                    &writer,
                    detail.count,
                );
            },
            else => try writer.writeAll(mm0.compilerDiagnosticSummary(diag)),
        }
    } else {
        try writer.writeAll(mm0.compilerDiagnosticSummary(diag));
    }
    try appendNamedLine(&writer, "theorem", diag.theorem_name);
    try appendNamedLine(&writer, "proof block", diag.block_name);
    try appendNamedLine(&writer, "line", diag.line_label);
    try appendNamedLine(&writer, "rule", diag.rule_name);
    try appendNamedLine(&writer, "name", diag.name);
    try appendNamedLine(&writer, "expected", diag.expected_name);
    if (diag.phase) |phase| {
        try writer.print(
            "\nphase: {s}",
            .{diagnosticPhaseName(phase)},
        );
    }

    switch (diag.detail) {
        .none => {},
        .omitted_diagnostics => {},
        .unknown_math_token => |detail| {
            try writer.print("\ntoken: {s}", .{detail.token});
        },
        .missing_binder_assignment => |detail| {
            try writer.print(
                "\nmissing binder: {s}",
                .{detail.binder_name},
            );
            try writer.print(
                "\ninference path: {s}",
                .{mm0.compilerInferencePathName(detail.path)},
            );
        },
        .inference_failure => |detail| {
            try writer.print(
                "\ninference path: {s}",
                .{mm0.compilerInferencePathName(detail.path)},
            );
            if (detail.first_unsolved_binder_name) |binder_name| {
                try writer.print(
                    "\nfirst unsolved binder: {s}",
                    .{binder_name},
                );
            }
        },
        .dep_violation => |detail| {
            try writer.writeAll("\ndependency violation: ");
            try mm0.writeCompilerDepViolationSummary(&writer, detail);
            try writer.print(
                "\nfirst binder: deps=0x{x} bound={}",
                .{ detail.first_deps, detail.first_bound },
            );
            try writer.print(
                "\nsecond binder: deps=0x{x} bound={}",
                .{ detail.second_deps, detail.second_bound },
            );
        },
        .missing_congruence_rule => |detail| {
            try writer.writeAll("\nmissing congruence: ");
            try mm0.writeCompilerMissingCongruenceRuleSummary(&writer, detail);
            try appendNamedLine(&writer, "sort", detail.sort_name);
        },
        .hypothesis_ref => |detail| {
            try writer.print("\nhypothesis ref: #{d}", .{detail.index});
        },
        .unused_parameter => |detail| {
            try writer.print(
                "\nparameter: {s}",
                .{detail.parameter_name},
            );
        },
    }

    for (diag.noteSlice()) |note| {
        try writer.print("\nnote: {s}", .{note.message});
    }
    for (diag.relatedSlice()) |related| {
        try writer.print("\nrelated: {s}", .{related.label});
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
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = "",
            .version = 1,
        },
    };
    const proof = try compilerDiagnosticsToLsp(
        allocator,
        diag_context,
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
        diag_context,
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

test "compiler source diagnostics merge primaries and warnings" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const primary = [_]mm0.CompilerDiagnostic{
        .{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const warnings = [_]mm0.CompilerDiagnostic{
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.AmbiguousAcuiMatch,
            .source = .mm0,
        },
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.UnknownLabel,
            .source = .proof,
        },
    };
    const extra: mm0.CompilerDiagnostic = .{
        .kind = .generic,
        .err = error.ExpectedIdent,
        .source = .mm0,
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = "",
            .version = 1,
        },
    };

    const diags = try compilerSourceDiagnosticsToLsp(
        allocator,
        diag_context,
        &primary,
        &warnings,
        extra,
        null,
        .mm0,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 3), diags.len);
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diags[0].severity.?,
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diags[1].severity.?,
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        diags[2].severity.?,
    );
}

test "compiler source diagnostics append omitted summary" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const primary = [_]mm0.CompilerDiagnostic{
        .{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const omitted: mm0.CompilerDiagnostic = .{
        .kind = .omitted_diagnostics,
        .err = error.DiagnosticsOmitted,
        .source = .mm0,
        .detail = .{ .omitted_diagnostics = .{ .count = 17 } },
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
    };

    const diags = try compilerSourceDiagnosticsToLsp(
        allocator,
        diag_context,
        &primary,
        &.{},
        null,
        omitted,
        .mm0,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expectEqualStrings(
        "17 more diagnostics omitted",
        diags[1].message,
    );
}

test "compiler diagnostics publish related information" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_text =
        \\first
        \\-----
        \\l1: $ top $ by second []
    ;

    const rule_start = std.mem.indexOf(u8, mm0_text, "second") orelse {
        return error.MissingNeedle;
    };
    const use_start = std.mem.lastIndexOf(u8, proof_text, "second") orelse {
        return error.MissingNeedle;
    };

    var diag: mm0.CompilerDiagnostic = .{
        .kind = .rule_not_yet_available,
        .err = error.RuleNotYetAvailable,
        .source = .proof,
        .phase = .theorem_application,
        .theorem_name = "first",
        .line_label = "l1",
        .rule_name = "second",
        .span = .{
            .start = use_start,
            .end = use_start + "second".len,
        },
    };
    diag.note_count = 1;
    diag.notes[0] = .{
        .message = "rule is declared later in the mm0 file",
        .source = .mm0,
    };
    diag.related_count = 1;
    diag.related[0] = .{
        .label = "rule declaration is here",
        .source = .mm0,
        .span = .{
            .start = rule_start,
            .end = rule_start + "second".len,
        },
    };

    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = mm0_text,
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };

    const lsp_diag = try compilerDiagnosticToLsp(
        allocator,
        diag_context,
        diag,
        .@"utf-16",
    );
    const related = lsp_diag.relatedInformation orelse {
        return error.ExpectedRelatedInformation;
    };
    try std.testing.expectEqual(@as(usize, 1), related.len);
    try std.testing.expectEqualStrings(
        "file:///tmp/test.mm0",
        related[0].location.uri,
    );
    try std.testing.expectEqualStrings(
        "rule declaration is here",
        related[0].message,
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "phase: theorem application",
    ));
}

test "compiler dependency diagnostics render detail in LSP messages" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const proof_text =
        \\rel_bad
        \\-------
        \\l1: $ rel z z $ by rel_ax (x := $ z $, y := $ z $) []
    ;

    const diag_context: DiagnosticContext = .{
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };
    const lsp_diag = try compilerDiagnosticToLsp(
        allocator,
        diag_context,
        .{
            .kind = .generic,
            .err = error.DepViolation,
            .source = .proof,
            .phase = .theorem_application,
            .theorem_name = "rel_bad",
            .line_label = "l1",
            .rule_name = "rel_ax",
            .span = .{ .start = 17, .end = 23 },
            .detail = .{ .dep_violation = .{
                .first_arg_idx = 0,
                .second_arg_idx = 1,
                .first_arg_name = "x",
                .second_arg_name = "y",
                .first_deps = 1,
                .second_deps = 1,
                .first_bound = true,
                .second_bound = true,
            } },
        },
        .@"utf-16",
    );

    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "dependency violation: conflicting binders x and y",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "first binder: deps=0x1 bound=true",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "second binder: deps=0x1 bound=true",
    ));
}
