const builtin = @import("builtin");
const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

const types = lsp.types;
const LspIndex = mm0.Frontend.LspIndex;
const lsp_diagnostics = @import("lsp_diagnostics");
const DiagnosticContext = lsp_diagnostics.DiagnosticContext;
const compilerDiagnosticsToLsp = lsp_diagnostics.compilerDiagnosticsToLsp;
const compilerSourceDiagnosticsToLsp =
    lsp_diagnostics.compilerSourceDiagnosticsToLsp;
const compilerDiagnosticToLsp = lsp_diagnostics.compilerDiagnosticToLsp;
const zeroRange = lsp_diagnostics.zeroRange;
const sourceRangeToLsp = lsp_diagnostics.sourceRangeToLsp;
const sourceRangesToLocations = lsp_diagnostics.sourceRangesToLocations;
const completionsToLsp = lsp_diagnostics.completionsToLsp;
const outlineSymbolsToLsp = lsp_diagnostics.outlineSymbolsToLsp;

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
            .implementationProvider = .{ .bool = true },
            .referencesProvider = .{ .bool = true },
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

    pub fn @"textDocument/implementation"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.ImplementationParams,
    ) !lsp.ResultType("textDocument/implementation") {
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
        const implementation = nav.snapshot.implementationAt(
            nav.document,
            offset,
        ) orelse return null;
        return .{
            .Definition = .{
                .Location = .{
                    .uri = implementation.uri,
                    .range = sourceRangeToLsp(
                        nav.snapshot,
                        implementation.selection_range,
                        self.offset_encoding,
                    ),
                },
            },
        };
    }

    pub fn @"textDocument/references"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.ReferenceParams,
    ) !lsp.ResultType("textDocument/references") {
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
        const ranges = try nav.snapshot.referencesAt(
            arena,
            nav.document,
            offset,
            params.context.includeDeclaration,
        );
        return try sourceRangesToLocations(
            arena,
            nav.snapshot,
            ranges,
            self.offset_encoding,
        );
    }

    pub fn onResponse(
        _: *Handler,
        _: std.mem.Allocator,
        _: lsp.JsonRPCMessage.Response,
    ) void {}

    pub fn putDocument(
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
            if (compiler.diagnostics.last_diagnostic != null or
                compiler.primaryDiagnostics().len != 0 or
                compiler.warningDiagnostics().len != 0)
            {
                try self.publishCompilerSourceDiagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.diagnostics.last_diagnostic,
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
            if (compiler.diagnostics.last_diagnostic != null or
                compiler.primaryDiagnostics().len != 0 or
                compiler.warningDiagnostics().len != 0)
            {
                try self.publishProofAndMm0Diagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.diagnostics.last_diagnostic,
                    compiler.omittedPrimaryDiagnostic(.proof),
                    compiler.omittedPrimaryDiagnostic(.mm0),
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

        try self.publishProofAndMm0Diagnostics(
            arena,
            diag_context,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            compiler.diagnostics.last_diagnostic,
            compiler.omittedPrimaryDiagnostic(.proof),
            compiler.omittedPrimaryDiagnostic(.mm0),
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

    fn publishProofAndMm0Diagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        primary: []const mm0.CompilerDiagnostic,
        warnings: []const mm0.CompilerDiagnostic,
        extra: ?mm0.CompilerDiagnostic,
        proof_omitted: ?mm0.CompilerDiagnostic,
        mm0_omitted: ?mm0.CompilerDiagnostic,
    ) !void {
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            primary,
            warnings,
            extra,
            proof_omitted,
            .proof,
        );
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            primary,
            warnings,
            extra,
            mm0_omitted,
            .mm0,
        );
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

pub const DocumentKind = enum {
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

pub fn uriToPath(
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

pub fn pathToUri(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "file://{f}",
        .{std.fmt.alt(std.Uri.Component{ .raw = path }, .formatPath)},
    );
}

pub fn siblingPathForProof(
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

pub fn siblingPathForMm0(
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

pub fn documentKind(path: []const u8) DocumentKind {
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
