const std = @import("std");

const completion = @import("completion.zig");
const Builder = @import("builder.zig").Builder;
const model = @import("model.zig");
const notation = @import("notation.zig");
const Types = @import("types.zig");

pub const DocumentId = Types.DocumentId;
pub const SnapshotInput = Types.SnapshotInput;
pub const SourceRange = Types.SourceRange;
pub const DefinitionResult = Types.DefinitionResult;
pub const HoverResult = Types.HoverResult;
pub const CompletionOptions = Types.CompletionOptions;
pub const CompletionKind = Types.CompletionKind;
pub const CompletionItem = Types.CompletionItem;
pub const OutlineSymbol = Types.OutlineSymbol;
pub const DeclarationKind = Types.DeclarationKind;
pub const BinderDecl = Types.BinderDecl;
pub const Declaration = Types.Declaration;
pub const escapeSnippetText = notation.escapeSnippetText;

const LookupHit = model.LookupHit;
const NavigationSymbol = model.NavigationSymbol;
const ProofBlockInfo = model.ProofBlockInfo;
const ProofRuleDecl = model.ProofRuleDecl;
const ProofLineDecl = model.ProofLineDecl;
const ProofApplicationInfo = model.ProofApplicationInfo;
const NotationCompletionDecl = notation.NotationCompletionDecl;

pub const Snapshot = struct {
    arena: std.heap.ArenaAllocator,
    mm0_uri: []const u8,
    mm0_text: []const u8,
    proof_uri: ?[]const u8,
    proof_text: ?[]const u8,
    declarations: []const Declaration,
    decl_by_name: std.StringHashMapUnmanaged(usize),
    symbols: []const NavigationSymbol,
    mm0_outline: []const OutlineSymbol,
    proof_outline: []const OutlineSymbol,
    proof_blocks: []const ProofBlockInfo,
    proof_rules: []const ProofRuleDecl,
    proof_lines: []const ProofLineDecl,
    proof_applications: []const ProofApplicationInfo,
    notations: []const NotationCompletionDecl,
    left_delims: [256]bool,
    right_delims: [256]bool,

    pub fn build(
        allocator: std.mem.Allocator,
        input: SnapshotInput,
    ) !Snapshot {
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        errdefer arena_state.deinit();

        const arena = arena_state.allocator();
        var builder = Builder.init(arena);

        const mm0_uri = try arena.dupe(u8, input.mm0_uri);
        const mm0_text = try arena.dupe(u8, input.mm0_text);
        const proof_uri = if (input.proof_uri) |uri|
            try arena.dupe(u8, uri)
        else
            null;
        const proof_text = if (input.proof_text) |text|
            try arena.dupe(u8, text)
        else
            null;

        try builder.indexMm0(mm0_text);
        if (proof_text) |text| {
            try builder.indexProof(text);
        }

        return .{
            .arena = arena_state,
            .mm0_uri = mm0_uri,
            .mm0_text = mm0_text,
            .proof_uri = proof_uri,
            .proof_text = proof_text,
            .declarations = try builder.declarations.toOwnedSlice(arena),
            .decl_by_name = builder.decl_by_name,
            .symbols = try builder.symbols.toOwnedSlice(arena),
            .mm0_outline = try builder.mm0_outline.toOwnedSlice(arena),
            .proof_outline = try builder.proof_outline.toOwnedSlice(arena),
            .proof_blocks = try builder.proof_blocks.toOwnedSlice(arena),
            .proof_rules = try builder.proof_rules.toOwnedSlice(arena),
            .proof_lines = try builder.proof_lines.toOwnedSlice(arena),
            .proof_applications = try builder.proof_applications.toOwnedSlice(arena),
            .notations = try builder.notations.toOwnedSlice(arena),
            .left_delims = builder.left_delims,
            .right_delims = builder.right_delims,
        };
    }

    pub fn deinit(self: *Snapshot) void {
        self.arena.deinit();
        self.* = undefined;
    }

    pub fn hoverAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?HoverResult {
        const hit = self.lookupAt(document, offset) orelse return null;
        return .{
            .range = hit.source_range,
            .markdown = hit.markdown,
        };
    }

    pub fn definitionAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?DefinitionResult {
        const hit = self.lookupAt(document, offset) orelse return null;
        const target_range = hit.target_range orelse return null;
        return .{
            .uri = self.uriForDocument(target_range.document) orelse {
                return null;
            },
            .range = target_range,
            .selection_range = target_range,
        };
    }

    pub fn textForDocument(
        self: *const Snapshot,
        document: DocumentId,
    ) ?[]const u8 {
        return switch (document) {
            .mm0 => self.mm0_text,
            .proof => self.proof_text,
        };
    }

    pub fn outline(
        self: *const Snapshot,
        document: DocumentId,
    ) []const OutlineSymbol {
        return switch (document) {
            .mm0 => self.mm0_outline,
            .proof => self.proof_outline,
        };
    }

    pub fn completionsAt(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        document: DocumentId,
        offset: usize,
        options: CompletionOptions,
    ) ![]const CompletionItem {
        return completion.completionsAt(
            self,
            allocator,
            document,
            offset,
            options,
        );
    }

    fn lookupAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?LookupHit {
        for (self.symbols) |symbol| {
            if (rangeContains(symbol.source_range, document, offset)) {
                return .{
                    .source_range = symbol.source_range,
                    .target_range = symbol.target_range,
                    .markdown = symbol.markdown,
                };
            }
        }
        return null;
    }

    fn uriForDocument(
        self: *const Snapshot,
        document: DocumentId,
    ) ?[]const u8 {
        return switch (document) {
            .mm0 => self.mm0_uri,
            .proof => self.proof_uri,
        };
    }
};

fn rangeContains(range: SourceRange, document: DocumentId, offset: usize) bool {
    return range.document == document and offset >= range.start and
        offset < range.end;
}
