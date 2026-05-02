const builtin = @import("builtin");
const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

const types = lsp.types;
const LspIndex = mm0.Frontend.LspIndex;

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
    mtime: ?i128,
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

const NavigationDocumentState = struct {
    uri: []const u8,
    version: ?i32,
    mtime: ?i128,

    fn eql(
        self: NavigationDocumentState,
        other: NavigationDocumentState,
    ) bool {
        return std.mem.eql(u8, self.uri, other.uri) and
            self.version == other.version and
            self.mtime == other.mtime;
    }
};

const NavigationCacheKey = struct {
    mm0: NavigationDocumentState,
    proof: ?NavigationDocumentState,

    fn init(
        allocator: std.mem.Allocator,
        request: NavigationCacheRequest,
    ) !NavigationCacheKey {
        const mm0_uri = try allocator.dupe(u8, request.mm0.uri);
        errdefer allocator.free(mm0_uri);

        const proof = if (request.proof) |proof_state| blk: {
            const proof_uri = try allocator.dupe(u8, proof_state.uri);
            break :blk NavigationDocumentState{
                .uri = proof_uri,
                .version = proof_state.version,
                .mtime = proof_state.mtime,
            };
        } else null;
        errdefer if (proof) |proof_state| {
            allocator.free(proof_state.uri);
        };

        return .{
            .mm0 = .{
                .uri = mm0_uri,
                .version = request.mm0.version,
                .mtime = request.mm0.mtime,
            },
            .proof = proof,
        };
    }

    fn deinit(self: *NavigationCacheKey, allocator: std.mem.Allocator) void {
        allocator.free(self.mm0.uri);
        if (self.proof) |proof| {
            allocator.free(proof.uri);
        }
        self.* = undefined;
    }

    fn eql(
        self: NavigationCacheKey,
        request: NavigationCacheRequest,
    ) bool {
        if (!self.mm0.eql(request.mm0)) return false;
        if (self.proof == null and request.proof == null) return true;
        if (self.proof == null or request.proof == null) return false;
        return self.proof.?.eql(request.proof.?);
    }
};

const NavigationCacheRequest = struct {
    mm0: NavigationDocumentState,
    proof: ?NavigationDocumentState,
};

const NavigationCacheEntry = struct {
    key: NavigationCacheKey,
    snapshot: LspIndex.Snapshot,

    fn deinit(
        self: *NavigationCacheEntry,
        allocator: std.mem.Allocator,
    ) void {
        self.snapshot.deinit();
        self.key.deinit(allocator);
        self.* = undefined;
    }
};

const NavigationSnapshot = struct {
    snapshot: *const LspIndex.Snapshot,
    document: LspIndex.DocumentId,
};

pub const Handler = struct {
    allocator: std.mem.Allocator,
    transport: *lsp.Transport,
    docs: std.StringHashMapUnmanaged(OpenDocument),
    nav_cache: std.StringHashMapUnmanaged(NavigationCacheEntry),
    offset_encoding: lsp.offsets.Encoding,
    snippet_support: bool,

    pub fn init(
        allocator: std.mem.Allocator,
        transport: *lsp.Transport,
    ) Handler {
        return .{
            .allocator = allocator,
            .transport = transport,
            .docs = .empty,
            .nav_cache = .empty,
            .offset_encoding = .@"utf-16",
            .snippet_support = false,
        };
    }

    pub fn deinit(self: *Handler) void {
        var it = self.docs.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.text);
        }
        self.docs.deinit(self.allocator);

        var cache_it = self.nav_cache.iterator();
        while (cache_it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
        }
        self.nav_cache.deinit(self.allocator);
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

        self.snippet_support = clientSupportsSnippets(request.capabilities);

        const supports_hierarchical_document_symbols =
            clientSupportsHierarchicalDocumentSymbols(request.capabilities);

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
            .hoverProvider = .{ .bool = true },
            .definitionProvider = .{ .bool = true },
            .completionProvider = .{
                .resolveProvider = false,
            },
            .documentSymbolProvider = if (supports_hierarchical_document_symbols)
                .{ .bool = true }
            else
                null,
        };

        if (builtin.mode == .Debug) {
            // The validator only understands static capabilities. Validate
            // against the superset of implemented handlers while returning
            // the client-specific capabilities above.
            var validation_capabilities = capabilities;
            validation_capabilities.documentSymbolProvider = .{ .bool = true };
            lsp.basic_server.validateServerCapabilities(
                Handler,
                validation_capabilities,
            );
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
        self.invalidateNavigationForUri(arena, params.textDocument.uri);
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

        self.invalidateNavigationForUri(arena, params.textDocument.uri);
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

        self.invalidateNavigationForUri(arena, uri);
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

    pub fn @"textDocument/hover"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.HoverParams,
    ) !lsp.ResultType("textDocument/hover") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const hover = nav.snapshot.hoverAt(nav.document, offset) orelse return null;
        return .{
            .contents = .{
                .MarkupContent = .{
                    .kind = .markdown,
                    .value = hover.markdown,
                },
            },
            .range = sourceRangeToLsp(
                nav.snapshot,
                hover.range,
                self.offset_encoding,
            ),
        };
    }

    pub fn @"textDocument/completion"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.CompletionParams,
    ) !lsp.ResultType("textDocument/completion") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const completions = try nav.snapshot.completionsAt(
            arena,
            nav.document,
            offset,
            .{ .snippet_support = self.snippet_support },
        );
        const items = try completionsToLsp(
            arena,
            nav.snapshot,
            completions,
            self.offset_encoding,
        );
        return .{ .array_of_CompletionItem = items };
    }

    pub fn @"textDocument/documentSymbol"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DocumentSymbolParams,
    ) !lsp.ResultType("textDocument/documentSymbol") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const symbols = try outlineSymbolsToLsp(
            arena,
            nav.snapshot,
            nav.snapshot.outline(nav.document),
            self.offset_encoding,
        );
        return .{ .array_of_DocumentSymbol = symbols };
    }

    pub fn @"textDocument/definition"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DefinitionParams,
    ) !lsp.ResultType("textDocument/definition") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const definition = nav.snapshot.definitionAt(
            nav.document,
            offset,
        ) orelse return null;
        return .{
            .Definition = .{
                .Location = .{
                    .uri = definition.uri,
                    .range = sourceRangeToLsp(
                        nav.snapshot,
                        definition.selection_range,
                        self.offset_encoding,
                    ),
                },
            },
        };
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
        return try self.loadTextForUriPath(arena, uri, path);
    }

    fn loadTextForUriPath(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !LoadedText {
        if (self.docs.get(uri)) |doc| {
            return .{
                .uri = uri,
                .text = doc.text,
                .version = doc.version,
                .mtime = null,
            };
        }

        const disk = try readFileWithMtimeAlloc(arena, path);
        return .{
            .uri = uri,
            .text = disk.text,
            .version = null,
            .mtime = disk.mtime,
        };
    }

    fn navigationState(loaded: LoadedText) NavigationDocumentState {
        return .{
            .uri = loaded.uri,
            .version = loaded.version,
            .mtime = loaded.mtime,
        };
    }

    fn navigationSnapshotForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !?NavigationSnapshot {
        const path = uriToPath(arena, uri) catch return null;
        return switch (documentKind(path)) {
            .mm0 => try self.navigationSnapshotForMm0(arena, uri, path),
            .proof => try self.navigationSnapshotForProof(arena, uri, path),
            .other => null,
        };
    }

    fn navigationSnapshotForMm0(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !?NavigationSnapshot {
        const mm0_loaded = self.loadTextForUriPath(arena, uri, path) catch {
            return null;
        };
        var proof_state: ?NavigationDocumentState = null;
        var proof_uri: ?[]const u8 = null;
        var proof_text: ?[]const u8 = null;

        if (siblingPathForMm0(arena, path)) |proof_path| {
            const expected_uri = try pathToUri(arena, proof_path);
            proof_state = .{
                .uri = expected_uri,
                .version = null,
                .mtime = null,
            };
            if (self.loadTextForUriPath(
                arena,
                expected_uri,
                proof_path,
            )) |proof| {
                proof_state = navigationState(proof);
                proof_uri = proof.uri;
                proof_text = proof.text;
            } else |_| {}
        } else |_| {}

        return try self.navigationSnapshotForRequest(
            .{
                .mm0 = navigationState(mm0_loaded),
                .proof = proof_state,
            },
            .{
                .mm0_uri = mm0_loaded.uri,
                .mm0_text = mm0_loaded.text,
                .proof_uri = proof_uri,
                .proof_text = proof_text,
            },
            .mm0,
        );
    }

    fn navigationSnapshotForProof(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !?NavigationSnapshot {
        const proof_loaded = self.loadTextForUriPath(arena, uri, path) catch {
            return null;
        };
        const mm0_path = siblingPathForProof(arena, path) catch return null;
        const mm0_loaded = self.loadTextPreferOpenDocument(arena, mm0_path) catch {
            return null;
        };

        return try self.navigationSnapshotForRequest(
            .{
                .mm0 = navigationState(mm0_loaded),
                .proof = navigationState(proof_loaded),
            },
            .{
                .mm0_uri = mm0_loaded.uri,
                .mm0_text = mm0_loaded.text,
                .proof_uri = proof_loaded.uri,
                .proof_text = proof_loaded.text,
            },
            .proof,
        );
    }

    fn navigationSnapshotForRequest(
        self: *Handler,
        request: NavigationCacheRequest,
        input: LspIndex.SnapshotInput,
        document: LspIndex.DocumentId,
    ) !NavigationSnapshot {
        if (self.nav_cache.getPtr(request.mm0.uri)) |entry| {
            if (entry.key.eql(request)) {
                return .{
                    .snapshot = &entry.snapshot,
                    .document = document,
                };
            }
        }

        self.removeNavigationCacheByMm0Uri(request.mm0.uri);

        var snapshot = try LspIndex.Snapshot.build(self.allocator, input);
        errdefer snapshot.deinit();

        var key = try NavigationCacheKey.init(self.allocator, request);
        errdefer key.deinit(self.allocator);

        const cache_key = key.mm0.uri;
        try self.nav_cache.put(self.allocator, cache_key, .{
            .key = key,
            .snapshot = snapshot,
        });

        const entry = self.nav_cache.getPtr(cache_key).?;
        return .{
            .snapshot = &entry.snapshot,
            .document = document,
        };
    }

    fn removeNavigationCacheByMm0Uri(
        self: *Handler,
        mm0_uri: []const u8,
    ) void {
        if (self.nav_cache.fetchRemove(mm0_uri)) |removed| {
            var entry = removed.value;
            entry.deinit(self.allocator);
        }
    }

    fn invalidateNavigationForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) void {
        const path = uriToPath(arena, uri) catch {
            self.invalidateNavigationContainingUri(uri);
            return;
        };

        switch (documentKind(path)) {
            .mm0 => self.removeNavigationCacheByMm0Uri(uri),
            .proof => {
                if (siblingPathForProof(arena, path)) |mm0_path| {
                    if (pathToUri(arena, mm0_path)) |mm0_uri| {
                        self.removeNavigationCacheByMm0Uri(mm0_uri);
                    } else |_| {}
                } else |_| {}
            },
            .other => {},
        }
        self.invalidateNavigationContainingUri(uri);
    }

    fn invalidateNavigationContainingUri(
        self: *Handler,
        uri: []const u8,
    ) void {
        while (true) {
            var it = self.nav_cache.iterator();
            var found: ?[]const u8 = null;
            while (it.next()) |entry| {
                if (std.mem.eql(u8, entry.value_ptr.key.mm0.uri, uri)) {
                    found = entry.key_ptr.*;
                    break;
                }
                if (entry.value_ptr.key.proof) |proof| {
                    if (std.mem.eql(u8, proof.uri, uri)) {
                        found = entry.key_ptr.*;
                        break;
                    }
                }
            }
            const key = found orelse break;
            self.removeNavigationCacheByMm0Uri(key);
        }
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

const ReadFileWithMtime = struct {
    text: []u8,
    mtime: i128,
};

fn readFileWithMtimeAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
) !ReadFileWithMtime {
    if (builtin.os.tag == .freestanding) {
        return error.FileNotFound;
    } else {
        const file = if (std.fs.path.isAbsolute(path))
            try std.fs.openFileAbsolute(path, .{})
        else
            try std.fs.cwd().openFile(path, .{});
        defer file.close();

        const stat = try file.stat();
        return .{
            .text = try file.readToEndAlloc(
                allocator,
                std.math.maxInt(usize),
            ),
            .mtime = stat.mtime,
        };
    }
}

fn readFileAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    return (try readFileWithMtimeAlloc(allocator, path)).text;
}

fn clientSupportsSnippets(capabilities: types.ClientCapabilities) bool {
    const text_document = capabilities.textDocument orelse return false;
    const completion = text_document.completion orelse return false;
    const item = completion.completionItem orelse return false;
    return item.snippetSupport orelse false;
}

fn clientSupportsHierarchicalDocumentSymbols(
    capabilities: types.ClientCapabilities,
) bool {
    const text_document = capabilities.textDocument orelse return false;
    const document_symbol = text_document.documentSymbol orelse return false;
    return document_symbol.hierarchicalDocumentSymbolSupport orelse false;
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

fn sourceRangeToLsp(
    snapshot: *const LspIndex.Snapshot,
    range: LspIndex.SourceRange,
    encoding: lsp.offsets.Encoding,
) types.Range {
    const text = snapshot.textForDocument(range.document) orelse "";
    const start = @min(range.start, text.len);
    const end = @max(start, @min(range.end, text.len));
    return lsp.offsets.locToRange(
        text,
        .{ .start = start, .end = end },
        encoding,
    );
}

fn completionsToLsp(
    arena: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    completions: []const LspIndex.CompletionItem,
    encoding: lsp.offsets.Encoding,
) ![]const types.CompletionItem {
    const result = try arena.alloc(types.CompletionItem, completions.len);
    for (completions, 0..) |item, i| {
        result[i] = .{
            .label = item.label,
            .kind = completionKindToLsp(item.kind),
            .detail = item.detail,
            .documentation = if (item.documentation_markdown) |doc|
                .{ .MarkupContent = .{ .kind = .markdown, .value = doc } }
            else
                null,
            .sortText = item.sort_text,
            .filterText = item.filter_text,
            .insertTextFormat = if (item.snippet_replacement_text != null)
                .Snippet
            else
                .PlainText,
            .textEdit = .{ .TextEdit = .{
                .range = sourceRangeToLsp(
                    snapshot,
                    item.replacement,
                    encoding,
                ),
                .newText = item.snippet_replacement_text orelse
                    item.replacement_text,
            } },
        };
    }
    return result;
}

fn completionKindToLsp(
    kind: LspIndex.CompletionKind,
) types.CompletionItemKind {
    return switch (kind) {
        .keyword, .modifier, .annotation => .Keyword,
        .sort => .Class,
        .term, .def => .Function,
        .notation => .Operator,
        .snippet => .Snippet,
        .axiom, .theorem, .lemma => .Method,
        .proof_line => .Reference,
        .hypothesis => .Value,
        .binder => .Variable,
    };
}

fn outlineSymbolsToLsp(
    arena: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    symbols: []const LspIndex.OutlineSymbol,
    encoding: lsp.offsets.Encoding,
) ![]const types.DocumentSymbol {
    const result = try arena.alloc(types.DocumentSymbol, symbols.len);
    for (symbols, 0..) |symbol, i| {
        result[i] = .{
            .name = symbol.name,
            .detail = symbol.kind.label(),
            .kind = declarationSymbolKind(symbol.kind),
            .range = sourceRangeToLsp(snapshot, symbol.range, encoding),
            .selectionRange = sourceRangeToLsp(
                snapshot,
                symbol.selection_range,
                encoding,
            ),
            .children = if (symbol.children.len == 0)
                null
            else
                try outlineSymbolsToLsp(
                    arena,
                    snapshot,
                    symbol.children,
                    encoding,
                ),
        };
    }
    return result;
}

fn declarationSymbolKind(kind: LspIndex.DeclarationKind) types.SymbolKind {
    return switch (kind) {
        .sort => .Class,
        .term, .def => .Function,
        .axiom, .theorem, .lemma => .Method,
        .proof_line, .sort_var => .Variable,
    };
}

const TestTransport = struct {
    transport: lsp.Transport = .{ .vtable = &vtable },

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    fn readJsonMessage(
        _: *lsp.Transport,
        _: std.mem.Allocator,
    ) lsp.Transport.ReadError![]u8 {
        return error.EndOfStream;
    }

    fn writeJsonMessage(
        _: *lsp.Transport,
        _: []const u8,
    ) lsp.Transport.WriteError!void {}
};

fn testPosition(text: []const u8, needle: []const u8) !types.Position {
    const offset = std.mem.indexOf(u8, text, needle) orelse {
        return error.MissingNeedle;
    };
    return lsp.offsets.indexToPosition(text, offset, .@"utf-16");
}

fn testLastPosition(text: []const u8, needle: []const u8) !types.Position {
    const offset = std.mem.lastIndexOf(u8, text, needle) orelse {
        return error.MissingNeedle;
    };
    return lsp.offsets.indexToPosition(text, offset, .@"utf-16");
}

fn expectRangeText(
    text: []const u8,
    range: types.Range,
    expected: []const u8,
) !void {
    const loc = lsp.offsets.rangeToLoc(text, range, .@"utf-16");
    try std.testing.expectEqualStrings(expected, text[loc.start..loc.end]);
}

fn expectDefinitionLocation(
    result: lsp.ResultType("textDocument/definition"),
) !types.Location {
    const value = result orelse return error.ExpectedDefinition;
    return switch (value) {
        .Definition => |definition| switch (definition) {
            .Location => |location| location,
            else => error.ExpectedDefinitionLocation,
        },
        else => error.ExpectedDefinitionLocation,
    };
}

fn expectDocumentSymbols(
    result: lsp.ResultType("textDocument/documentSymbol"),
) ![]const types.DocumentSymbol {
    const value = result orelse return error.ExpectedDocumentSymbols;
    return switch (value) {
        .array_of_DocumentSymbol => |symbols| symbols,
        else => error.ExpectedDocumentSymbols,
    };
}

fn expectCompletionItems(
    result: lsp.ResultType("textDocument/completion"),
) ![]const types.CompletionItem {
    const value = result orelse return error.ExpectedCompletions;
    return switch (value) {
        .array_of_CompletionItem => |items| items,
        else => error.ExpectedCompletions,
    };
}

fn completionItemNamed(
    items: []const types.CompletionItem,
    label: []const u8,
) ?types.CompletionItem {
    for (items) |item| {
        if (std.mem.eql(u8, item.label, label)) return item;
    }
    return null;
}

fn expectCompletionEditText(
    text: []const u8,
    item: types.CompletionItem,
    expected_old: []const u8,
    expected_new: []const u8,
) !void {
    const edit = item.textEdit orelse return error.ExpectedTextEdit;
    const text_edit = switch (edit) {
        .TextEdit => |value| value,
        else => return error.ExpectedTextEdit,
    };
    try expectRangeText(text, text_edit.range, expected_old);
    try std.testing.expectEqualStrings(expected_new, text_edit.newText);
}

const lsp_navigation_mm0_text =
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
    \\axiom keep: $ top $ > $ top $;
    \\theorem main: $ top $ > $ top $;
;

const lsp_navigation_proof_text =
    \\main
    \\----
    \\l1: $ top $ by top_i []
    \\l2: $ top $ by keep [l1]
;

fn putLspNavigationDocuments(
    handler: *Handler,
    mm0_uri: []const u8,
    proof_uri: []const u8,
) !void {
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_navigation_proof_text, 1);
}

test "LSP initialize advertises navigation capabilities" {
    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    const result = handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{
                .documentSymbol = .{
                    .hierarchicalDocumentSymbolSupport = true,
                },
            },
        },
    });

    const hover = result.capabilities.hoverProvider orelse {
        return error.ExpectedHoverProvider;
    };
    switch (hover) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanHoverProvider,
    }

    const definition = result.capabilities.definitionProvider orelse {
        return error.ExpectedDefinitionProvider;
    };
    switch (definition) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDefinitionProvider,
    }

    const completion = result.capabilities.completionProvider orelse {
        return error.ExpectedCompletionProvider;
    };
    try std.testing.expectEqual(false, completion.resolveProvider.?);

    const document_symbol = result.capabilities.documentSymbolProvider orelse {
        return error.ExpectedDocumentSymbolProvider;
    };
    switch (document_symbol) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDocumentSymbolProvider,
    }
}

test "LSP initialize omits document symbols for non-hierarchical clients" {
    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    const result = handler.initialize(std.testing.allocator, .{
        .capabilities = .{},
    });

    try std.testing.expect(result.capabilities.documentSymbolProvider == null);
}

test "LSP proof hover accepts UTF-16 positions after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-utf16.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ 💡 top $ by top_i []
        \\l2: $ top $ by keep [l1]
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const hover_result = try handler.@"textDocument/hover"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testPosition(proof_text, "top_i"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(proof_text, range, "top_i");

    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "axiom top_i",
    ));
}

test "LSP proof hover resolves rule applications" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const hover_result = try handler.@"textDocument/hover"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(lsp_navigation_proof_text, range, "keep");

    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "axiom keep",
    ));
}

test "LSP completion returns explicit edits" {
    const mm0_uri = "file:///tmp/lsp-completion.mm0";
    const proof_uri = "file:///tmp/lsp-completion.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by ke
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                proof_text.len,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingKeepCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Method, keep.kind.?);
    try expectCompletionEditText(proof_text, keep, "ke", "keep");
}

test "LSP completion uses UTF-16 ranges after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-completion-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-completion-utf16.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ 💡 top $ by ke
    ;
    const offset = (std.mem.indexOf(u8, proof_text, "ke") orelse {
        return error.MissingUtf16CompletionContext;
    }) + "ke".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingKeepUtf16Completion;
    };
    try expectCompletionEditText(proof_text, keep, "ke", "keep");
}

test "LSP completion returns notation snippets for snippet clients" {
    const mm0_uri = "file:///tmp/lsp-snippet.mm0";
    const mm0_text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    const offset = (std.mem.indexOf(u8, mm0_text, "fo $") orelse {
        return error.MissingSnippetContext;
    }) + "fo".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    _ = handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{
                .completion = .{
                    .completionItem = .{
                        .snippetSupport = true,
                    },
                },
            },
        },
    });
    try handler.putDocument(mm0_uri, mm0_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = mm0_uri },
            .position = lsp.offsets.indexToPosition(
                mm0_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const snippet = completionItemNamed(items, "∀ …") orelse {
        return error.MissingSnippetCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Snippet, snippet.kind.?);
    try std.testing.expectEqual(
        types.InsertTextFormat.Snippet,
        snippet.insertTextFormat.?,
    );
    try expectCompletionEditText(mm0_text, snippet, "fo", "∀ ${1:p}$0");
    try std.testing.expectEqualStrings(
        "forall ∀",
        snippet.filterText orelse "",
    );
}

test "LSP completion avoids snippets for plain completion clients" {
    const mm0_uri = "file:///tmp/lsp-no-snippet.mm0";
    const mm0_text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    const offset = (std.mem.indexOf(u8, mm0_text, "fo $") orelse {
        return error.MissingSnippetContext;
    }) + "fo".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    _ = handler.initialize(std.testing.allocator, .{
        .capabilities = .{},
    });
    try handler.putDocument(mm0_uri, mm0_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = mm0_uri },
            .position = lsp.offsets.indexToPosition(
                mm0_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "∀ …") == null);
    for (items) |item| {
        if (item.insertTextFormat) |format| {
            try std.testing.expect(format != .Snippet);
        }
    }
}

test "LSP proof definition resolves rules and line references" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const rule_location = try expectDefinitionLocation(
        try handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
        }),
    );
    try std.testing.expectEqualStrings(mm0_uri, rule_location.uri);
    try expectRangeText(lsp_navigation_mm0_text, rule_location.range, "keep");

    const line_location = try expectDefinitionLocation(
        try handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "l1"),
        }),
    );
    try std.testing.expectEqualStrings(proof_uri, line_location.uri);
    try expectRangeText(lsp_navigation_proof_text, line_location.range, "l1");
}

test "LSP document symbols returns quiet proof outline" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const symbols = try expectDocumentSymbols(
        try handler.@"textDocument/documentSymbol"(arena, .{
            .textDocument = .{ .uri = proof_uri },
        }),
    );
    try std.testing.expectEqual(@as(usize, 1), symbols.len);
    try std.testing.expectEqualStrings("main", symbols[0].name);
    try std.testing.expectEqual(types.SymbolKind.Method, symbols[0].kind);
    try std.testing.expect(symbols[0].children == null);
}

test "LSP navigation cache invalidates changed mm0 sibling" {
    const mm0_uri = "file:///tmp/lsp-stage5.mm0";
    const proof_uri = "file:///tmp/lsp-stage5.auf";
    const changed_mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep2: $ top $ > $ top $;
        \\theorem main: $ top $ > $ top $;
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const first_hover = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    try std.testing.expect(first_hover != null);
    try std.testing.expectEqual(@as(usize, 1), handler.nav_cache.count());

    try handler.@"textDocument/didChange"(arena, .{
        .textDocument = .{ .uri = mm0_uri, .version = 2 },
        .contentChanges = &.{
            .{ .literal_1 = .{ .text = changed_mm0_text } },
        },
    });
    try std.testing.expectEqual(@as(usize, 0), handler.nav_cache.count());

    const hover_result = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    const hover = hover_result orelse return error.ExpectedHover;
    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "unknown rule `keep`",
    ));
}

test "LSP navigation cache invalidates closed proof sibling" {
    const mm0_uri = "file:///tmp/lsp-stage5-close.mm0";
    const proof_uri = "file:///tmp/lsp-stage5-close.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const hover_result = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    try std.testing.expect(hover_result != null);
    try std.testing.expectEqual(@as(usize, 1), handler.nav_cache.count());

    try handler.@"textDocument/didClose"(arena, .{
        .textDocument = .{ .uri = proof_uri },
    });
    try std.testing.expectEqual(@as(usize, 0), handler.nav_cache.count());
}

test "LSP proof unknown rule has hover but no definition" {
    const mm0_uri = "file:///tmp/lsp-stage2-unknown.mm0";
    const proof_uri = "file:///tmp/lsp-stage2-unknown.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by missing []
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const hover_result = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "missing"),
    });
    const hover = hover_result orelse return error.ExpectedHover;
    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "unknown rule `missing`",
    ));

    const definition = try handler.@"textDocument/definition"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "missing"),
    });
    try std.testing.expect(definition == null);
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
        .definition_body => |detail| {
            try writer.print(
                "\ndeclared sort: {s}",
                .{detail.declared_sort_name},
            );
            try writer.print(
                "\nactual sort: {s}",
                .{detail.actual_sort_name},
            );
            try writer.print(
                "\nbody deps: 0x{x}",
                .{detail.body_deps},
            );
            try writer.print(
                "\nhidden binders: {d}",
                .{detail.hidden_binder_count},
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
