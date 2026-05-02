const std = @import("std");
const parse = @import("../../trusted/parse.zig");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const markdown = @import("markdown.zig");
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

const SourceSpan = source.SourceSpan;
const MathStringSpan = source.MathStringSpan;
const StatementIterator = source.StatementIterator;
const MathTokenCursor = source.MathTokenCursor;
const nextAnnotationToken = source.nextAnnotationToken;
const statementHeader = source.statementHeader;
const firstMathStringIn = source.firstMathStringIn;
const nextMathStringIn = source.nextMathStringIn;
const findStatementByte = source.findStatementByte;
const trimMathWhitespace = source.trimMathWhitespace;
const containsMathWhitespace = source.containsMathWhitespace;
const isMathWhitespace = source.isMathWhitespace;
const sourceRangeFromSlice = source.sourceRangeFromSlice;
const findIdentIn = source.findIdentIn;
const startsLineComment = source.startsLineComment;
const isIdentChar = source.isIdentChar;

const sortMarkdown = markdown.sortMarkdown;
const termMarkdown = markdown.termMarkdown;
const assertionMarkdown = markdown.assertionMarkdown;
const lemmaMarkdown = markdown.lemmaMarkdown;
const proofLineMarkdown = markdown.proofLineMarkdown;
const hypRefMarkdown = markdown.hypRefMarkdown;
const sortVarMarkdown = markdown.sortVarMarkdown;
const binderMarkdown = markdown.binderMarkdown;
const unknownRuleMarkdown = markdown.unknownRuleMarkdown;
const unknownLineMarkdown = markdown.unknownLineMarkdown;
const unknownHypMarkdown = markdown.unknownHypMarkdown;
const unknownBindingMarkdown = markdown.unknownBindingMarkdown;
const unresolvedBindingMarkdown = markdown.unresolvedBindingMarkdown;

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
        const text = self.textForDocument(document) orelse return &.{};
        const safe_offset = @min(offset, text.len);
        var list = std.ArrayListUnmanaged(CompletionItem){};
        const replacement = self.completionReplacementRange(
            document,
            text,
            safe_offset,
        );

        switch (document) {
            .mm0 => try self.mm0CompletionsAt(
                allocator,
                &list,
                text,
                safe_offset,
                replacement,
                options,
            ),
            .proof => try self.proofCompletionsAt(
                allocator,
                &list,
                text,
                safe_offset,
                replacement,
                options,
            ),
        }
        return try list.toOwnedSlice(allocator);
    }

    fn completionReplacementRange(
        self: *const Snapshot,
        document: DocumentId,
        text: []const u8,
        offset: usize,
    ) SourceRange {
        if (mathStringAt(text, offset)) |math| {
            return mathCompletionReplacementRange(
                document,
                text,
                math,
                offset,
                self.left_delims,
                self.right_delims,
            );
        }
        return identifierCompletionReplacementRange(document, text, offset);
    }

    fn mm0CompletionsAt(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        list: *std.ArrayListUnmanaged(CompletionItem),
        text: []const u8,
        offset: usize,
        replacement: SourceRange,
        options: CompletionOptions,
    ) !void {
        if (annotationContextAt(text, offset)) {
            try appendAnnotationCompletions(list, allocator, replacement);
            return;
        }
        if (lineCommentContextAt(text, offset)) return;
        if (mathStringAt(text, offset) != null) {
            try self.appendCurrentDeclarationBinders(
                list,
                allocator,
                text,
                offset,
                replacement,
            );
            try self.appendTermCompletions(
                list,
                allocator,
                replacement,
                .mm0,
                offset,
                null,
                options,
            );
            return;
        }
        if (mm0SortContextAt(text, offset)) {
            try self.appendSortCompletions(list, allocator, replacement);
            return;
        }
        if (mm0ReferenceContextAt(text, offset)) {
            try self.appendGlobalDeclarationCompletions(
                list,
                allocator,
                replacement,
                &.{ .term, .def, .axiom, .theorem },
                .mm0,
                offset,
                null,
            );
            return;
        }
        if (mm0TopLevelContextAt(text, offset)) {
            try appendKeywordCompletions(list, allocator, replacement);
        }
    }

    fn proofCompletionsAt(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        list: *std.ArrayListUnmanaged(CompletionItem),
        text: []const u8,
        offset: usize,
        replacement: SourceRange,
        options: CompletionOptions,
    ) !void {
        const block = self.proofBlockNear(offset);
        if (lineCommentContextAt(text, offset)) return;
        if (mathStringAt(text, offset) != null) {
            if (block) |block_index| {
                try self.appendBlockBinders(
                    list,
                    allocator,
                    block_index,
                    replacement,
                );
                if (proofLineMathContextAt(text, offset)) {
                    try self.appendSortVarCompletions(
                        list,
                        allocator,
                        replacement,
                        self.proof_blocks[block_index].global_available_before,
                    );
                }
            }
            try self.appendTermCompletions(
                list,
                allocator,
                replacement,
                .proof,
                offset,
                if (block) |i| self.proof_blocks[i].global_available_before else null,
                options,
            );
            return;
        }
        if (proofHeaderContextAt(text, offset)) {
            try self.appendGlobalDeclarationCompletions(
                list,
                allocator,
                replacement,
                &.{.theorem},
                .proof,
                offset,
                null,
            );
            return;
        }
        if (self.proofRuleApplicationAt(offset)) |app| {
            try self.appendProofRuleCompletions(
                list,
                allocator,
                app.block_index,
                offset,
                replacement,
            );
            return;
        }
        if (self.proofBindingApplicationAt(offset)) |app| {
            try self.appendRuleBinderCompletions(
                list,
                allocator,
                app,
                replacement,
            );
            return;
        }
        if (self.proofReferenceApplicationAt(offset)) |app| {
            try self.appendProofReferenceCompletions(
                list,
                allocator,
                app.block_index,
                app.line_start,
                replacement,
            );
            return;
        }
        if (proofRuleContextAt(text, offset)) {
            if (block) |block_index| {
                try self.appendProofRuleCompletions(
                    list,
                    allocator,
                    block_index,
                    offset,
                    replacement,
                );
            }
        }
    }

    fn appendCurrentDeclarationBinders(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        text: []const u8,
        offset: usize,
        replacement: SourceRange,
    ) !void {
        const decl_index = self.mm0DeclarationIndexAt(text, offset) orelse return;
        try self.appendDeclarationBinders(list, allocator, decl_index, replacement);
    }

    fn appendBlockBinders(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        block_index: usize,
        replacement: SourceRange,
    ) !void {
        const decl_index = self.proof_blocks[block_index].decl_index orelse return;
        try self.appendDeclarationBinders(list, allocator, decl_index, replacement);
    }

    fn appendSortVarCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        replacement: SourceRange,
        available_before: ?usize,
    ) !void {
        for (self.declarations) |decl| {
            if (decl.kind != .sort_var) continue;
            if (!globalDeclarationAvailable(
                decl,
                .proof,
                replacement.start,
                available_before,
            )) continue;
            if (completionAlreadyInserts(
                list.items,
                replacement,
                decl.name,
            )) continue;
            try list.append(allocator, .{
                .label = decl.name,
                .kind = .binder,
                .detail = declarationKindName(decl.kind),
                .documentation_markdown = decl.markdown,
                .replacement = replacement,
                .replacement_text = decl.name,
                .sort_text = globalDeclarationSortText(decl),
            });
        }
    }

    fn appendRuleBinderCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        app: ProofApplicationInfo,
        replacement: SourceRange,
    ) !void {
        const rule = self.ruleResolutionAt(
            app.block_index,
            app.rule_name,
            app.use_start,
        ) orelse return;
        try self.appendDeclarationBinders(
            list,
            allocator,
            rule.decl_index,
            replacement,
        );
    }

    fn appendDeclarationBinders(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        decl_index: usize,
        replacement: SourceRange,
    ) !void {
        const decl = self.declarations[decl_index];
        for (decl.binders) |binder| {
            try list.append(allocator, .{
                .label = binder.name,
                .kind = .binder,
                .detail = binder.sort_name,
                .replacement = replacement,
                .replacement_text = binder.name,
                .sort_text = binder.sort_text,
            });
        }
    }

    fn appendSortCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        replacement: SourceRange,
    ) !void {
        try self.appendGlobalDeclarationCompletions(
            list,
            allocator,
            replacement,
            &.{.sort},
            .mm0,
            replacement.start,
            null,
        );
    }

    fn appendTermCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        replacement: SourceRange,
        document: DocumentId,
        use_start: usize,
        available_before: ?usize,
        options: CompletionOptions,
    ) !void {
        try self.appendGlobalDeclarationCompletions(
            list,
            allocator,
            replacement,
            &.{ .term, .def },
            document,
            use_start,
            available_before,
        );
        try self.appendNotationCompletions(
            list,
            allocator,
            replacement,
            document,
            use_start,
            available_before,
            options,
        );
    }

    fn appendNotationCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        replacement: SourceRange,
        document: DocumentId,
        use_start: usize,
        available_before: ?usize,
        options: CompletionOptions,
    ) !void {
        const replacement_fragment = replacementFragment(self, replacement);
        for (self.notations) |notation| {
            const decl = self.declarations[notation.decl_index];
            if (!globalDeclarationAvailable(
                decl,
                document,
                use_start,
                available_before,
            )) continue;
            if (!completionAlreadyInserts(
                list.items,
                replacement,
                notation.token,
            )) {
                try list.append(allocator, .{
                    .label = notation.token,
                    .kind = .notation,
                    .detail = notation.detail,
                    .documentation_markdown = decl.markdown,
                    .replacement = replacement,
                    .replacement_text = notation.token,
                    .filter_text = notationFilterText(
                        notation,
                        decl,
                        replacement_fragment,
                    ),
                    .sort_text = notationCompletionSortText(
                        notation,
                        decl,
                        replacement_fragment,
                    ),
                });
            }
            if (options.snippet_support) {
                try appendNotationSnippetCompletion(
                    list,
                    allocator,
                    replacement,
                    notation,
                    decl,
                    replacement_fragment,
                );
            }
        }
    }

    fn appendGlobalDeclarationCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        replacement: SourceRange,
        kinds: []const DeclarationKind,
        document: DocumentId,
        use_start: usize,
        available_before: ?usize,
    ) !void {
        for (self.declarations) |decl| {
            if (!declarationKindIn(decl.kind, kinds)) continue;
            if (!globalDeclarationAvailable(
                decl,
                document,
                use_start,
                available_before,
            )) continue;
            try list.append(allocator, .{
                .label = decl.name,
                .kind = completionKindForDeclaration(decl.kind),
                .detail = declarationKindName(decl.kind),
                .documentation_markdown = decl.markdown,
                .replacement = replacement,
                .replacement_text = decl.name,
                .sort_text = globalDeclarationSortText(decl),
            });
        }
    }

    fn appendProofRuleCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        block_index: usize,
        use_start: usize,
        replacement: SourceRange,
    ) !void {
        var seen = std.StringHashMapUnmanaged(void){};
        for (self.proof_rules) |rule| {
            if (rule.available_start > use_start) continue;
            if (seen.contains(rule.name)) continue;
            try seen.put(allocator, rule.name, {});
            const decl = self.declarations[rule.decl_index];
            try list.append(allocator, .{
                .label = rule.name,
                .kind = .lemma,
                .detail = "lemma",
                .documentation_markdown = decl.markdown,
                .replacement = replacement,
                .replacement_text = rule.name,
                .sort_text = rule.sort_text,
            });
        }
        for (self.declarations) |decl| {
            switch (decl.kind) {
                .axiom, .theorem => {},
                else => continue,
            }
            if (seen.contains(decl.name)) continue;
            if (!self.globalRuleAvailable(block_index, decl)) continue;
            try list.append(allocator, .{
                .label = decl.name,
                .kind = completionKindForDeclaration(decl.kind),
                .detail = declarationKindName(decl.kind),
                .documentation_markdown = decl.markdown,
                .replacement = replacement,
                .replacement_text = decl.name,
                .sort_text = globalDeclarationSortText(decl),
            });
        }
    }

    fn appendProofReferenceCompletions(
        self: *const Snapshot,
        list: *std.ArrayListUnmanaged(CompletionItem),
        allocator: std.mem.Allocator,
        block_index: usize,
        line_start: usize,
        replacement: SourceRange,
    ) !void {
        const block = self.proof_blocks[block_index];
        if (block.hyp_count_known) {
            var i: usize = 1;
            while (i <= block.hyp_count) : (i += 1) {
                const label = try std.fmt.allocPrint(allocator, "#{d}", .{i});
                try list.append(allocator, .{
                    .label = label,
                    .kind = .hypothesis,
                    .detail = "hypothesis",
                    .replacement = replacement,
                    .replacement_text = label,
                    .sort_text = try completionSortText(
                        allocator,
                        sort_group_proof_reference,
                        i,
                        label,
                    ),
                });
            }
        }
        for (self.proof_lines) |line| {
            if (line.block_index != block_index) continue;
            if (line.line_start >= line_start) continue;
            const decl = self.declarations[line.decl_index];
            try list.append(allocator, .{
                .label = line.name,
                .kind = .proof_line,
                .detail = "proof line",
                .documentation_markdown = decl.markdown,
                .replacement = replacement,
                .replacement_text = line.name,
                .sort_text = line.sort_text,
            });
        }
    }

    fn mm0DeclarationIndexAt(
        self: *const Snapshot,
        text: []const u8,
        offset: usize,
    ) ?usize {
        var iter = StatementIterator.init(text);
        while (iter.next()) |stmt| {
            if (offset < stmt.start or offset > stmt.end) continue;
            const header = statementHeader(text, stmt) orelse return null;
            const name = header.name orelse return null;
            return self.decl_by_name.get(name);
        }
        return null;
    }

    fn proofBlockNear(self: *const Snapshot, offset: usize) ?usize {
        var best: ?usize = null;
        for (self.proof_blocks, 0..) |block, i| {
            if (block.span.start > offset) continue;
            if (best == null or
                block.span.start > self.proof_blocks[best.?].span.start)
            {
                best = i;
            }
        }
        return best;
    }

    fn proofRuleApplicationAt(
        self: *const Snapshot,
        offset: usize,
    ) ?ProofApplicationInfo {
        for (self.proof_applications) |app| {
            if (offset >= app.rule_span.start and offset <= app.rule_span.end) {
                return app;
            }
        }
        return null;
    }

    fn proofBindingApplicationAt(
        self: *const Snapshot,
        offset: usize,
    ) ?ProofApplicationInfo {
        for (self.proof_applications) |app| {
            const range = app.binding_list_span orelse continue;
            if (offset >= range.start and offset <= range.end) return app;
        }
        return null;
    }

    fn proofReferenceApplicationAt(
        self: *const Snapshot,
        offset: usize,
    ) ?ProofApplicationInfo {
        for (self.proof_applications) |app| {
            const range = app.refs_span orelse continue;
            if (offset >= range.start and offset <= range.end) return app;
        }
        return null;
    }

    fn ruleResolutionAt(
        self: *const Snapshot,
        block_index: usize,
        name: []const u8,
        use_start: usize,
    ) ?RuleResolution {
        var best: ?ProofRuleDecl = null;
        for (self.proof_rules) |rule| {
            if (!std.mem.eql(u8, rule.name, name)) continue;
            if (rule.available_start > use_start) continue;
            if (best == null or rule.available_start > best.?.available_start) {
                best = rule;
            }
        }
        if (best) |rule| {
            return .{ .decl_index = rule.decl_index, .available = true };
        }
        const decl_index = self.decl_by_name.get(name) orelse return null;
        const decl = self.declarations[decl_index];
        switch (decl.kind) {
            .axiom, .theorem => {},
            else => return null,
        }
        return .{
            .decl_index = decl_index,
            .available = self.globalRuleAvailable(block_index, decl),
        };
    }

    fn globalRuleAvailable(
        self: *const Snapshot,
        block_index: usize,
        decl: Declaration,
    ) bool {
        const bound = self.proof_blocks[block_index].global_available_before;
        if (bound) |before| return decl.name_range.start < before;
        return true;
    }
};

const AnnotationDirective = struct {
    label: []const u8,
    detail: []const u8,
    sort_text: []const u8,
};

const annotation_directives = [_]AnnotationDirective{
    .{ .label = "@vars", .detail = "sort variable pool", .sort_text = "09 00" },
    .{ .label = "@relation", .detail = "rewrite relation", .sort_text = "09 01" },
    .{ .label = "@rewrite", .detail = "rewrite rule", .sort_text = "09 02" },
    .{ .label = "@congr", .detail = "congruence rule", .sort_text = "09 03" },
    .{ .label = "@acui", .detail = "ACUI metadata", .sort_text = "09 04" },
    .{ .label = "@view", .detail = "view theorem", .sort_text = "09 05" },
    .{ .label = "@recover", .detail = "recovery theorem", .sort_text = "09 06" },
    .{ .label = "@abstract", .detail = "abstract theorem", .sort_text = "09 07" },
    .{ .label = "@fresh", .detail = "freshness theorem", .sort_text = "09 08" },
    .{ .label = "@hole", .detail = "proof hole", .sort_text = "09 09" },
};

const CompletionItemSeed = struct {
    label: []const u8,
    kind: CompletionKind,
    detail: []const u8,
    sort_text: []const u8,
};

const top_level_keywords = [_]CompletionItemSeed{
    .{ .label = "sort", .kind = .keyword, .detail = "sort declaration", .sort_text = "09 00" },
    .{ .label = "term", .kind = .keyword, .detail = "term declaration", .sort_text = "09 01" },
    .{ .label = "def", .kind = .keyword, .detail = "definition", .sort_text = "09 02" },
    .{ .label = "axiom", .kind = .keyword, .detail = "axiom", .sort_text = "09 03" },
    .{ .label = "theorem", .kind = .keyword, .detail = "theorem", .sort_text = "09 04" },
    .{ .label = "notation", .kind = .keyword, .detail = "notation", .sort_text = "09 05" },
    .{ .label = "prefix", .kind = .keyword, .detail = "prefix notation", .sort_text = "09 06" },
    .{ .label = "infixl", .kind = .keyword, .detail = "left infix", .sort_text = "09 07" },
    .{ .label = "infixr", .kind = .keyword, .detail = "right infix", .sort_text = "09 08" },
    .{ .label = "delimiter", .kind = .keyword, .detail = "delimiter", .sort_text = "09 09" },
    .{ .label = "pub", .kind = .modifier, .detail = "public", .sort_text = "09 10" },
    .{ .label = "pure", .kind = .modifier, .detail = "pure", .sort_text = "09 11" },
    .{ .label = "strict", .kind = .modifier, .detail = "strict", .sort_text = "09 12" },
    .{ .label = "provable", .kind = .modifier, .detail = "provable", .sort_text = "09 13" },
    .{ .label = "free", .kind = .modifier, .detail = "free", .sort_text = "09 14" },
};

fn appendAnnotationCompletions(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
) !void {
    for (annotation_directives) |directive| {
        try list.append(allocator, .{
            .label = directive.label,
            .kind = .annotation,
            .detail = directive.detail,
            .replacement = replacement,
            .replacement_text = directive.label,
            .sort_text = directive.sort_text,
        });
    }
}

fn appendKeywordCompletions(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
) !void {
    for (top_level_keywords) |keyword| {
        try list.append(allocator, .{
            .label = keyword.label,
            .kind = keyword.kind,
            .detail = keyword.detail,
            .replacement = replacement,
            .replacement_text = keyword.label,
            .sort_text = keyword.sort_text,
        });
    }
}

const sort_group_local_binder = "00";
const sort_group_proof_reference = "01";
const sort_group_proof_lemma = "02";
const sort_group_global_rule = "03";
const sort_group_notation_alias = "04";
const sort_group_notation_token = "05";
const sort_group_notation_snippet = "06";
const sort_group_term = "07";
const sort_group_sort = "08";
const sort_group_keyword = "09";

fn completionSortText(
    allocator: std.mem.Allocator,
    group: []const u8,
    ordinal: usize,
    label: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "{s} {d:0>10} {s}",
        .{ group, ordinal, label },
    );
}

fn globalDeclarationSortText(decl: Declaration) []const u8 {
    return decl.sort_text;
}

fn notationCompletionSortText(
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) []const u8 {
    if (completionFragmentMatchesAlias(
        replacement_fragment,
        decl.name,
        notation.token,
    )) {
        return notation.alias_sort_text;
    }
    return notation.token_sort_text;
}

fn notationSnippetSortText(
    notation: NotationCompletionDecl,
    _: Declaration,
) []const u8 {
    return notation.snippet_sort_text orelse notation.token_sort_text;
}

fn notationFilterText(
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) []const u8 {
    if (completionFragmentMatchesAlias(
        replacement_fragment,
        decl.name,
        notation.token,
    )) {
        return notation.alias_filter_text;
    }
    return notation.filter_text;
}

fn notationSnippetFilterText(
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) []const u8 {
    if (completionFragmentMatchesAlias(
        replacement_fragment,
        decl.name,
        notation.token,
    )) {
        return notation.snippet_alias_filter_text orelse
            notation.alias_filter_text;
    }
    return notation.snippet_filter_text orelse notation.filter_text;
}

fn aliasFirstFilterText(
    allocator: std.mem.Allocator,
    text: []const u8,
    alias: []const u8,
) ![]const u8 {
    if (std.mem.endsWith(u8, text, alias)) {
        const prefix_end = text.len - alias.len;
        const prefix = std.mem.trimRight(u8, text[0..prefix_end], " ");
        if (prefix.len == 0) return alias;
        return try std.fmt.allocPrint(
            allocator,
            "{s} {s}",
            .{ alias, prefix },
        );
    }
    return try std.fmt.allocPrint(
        allocator,
        "{s} {s}",
        .{ alias, text },
    );
}

fn replacementFragment(
    self: *const Snapshot,
    replacement: SourceRange,
) []const u8 {
    const text = self.textForDocument(replacement.document) orelse return "";
    if (replacement.start > replacement.end or replacement.end > text.len) {
        return "";
    }
    return text[replacement.start..replacement.end];
}

fn completionFragmentMatchesAlias(
    fragment: []const u8,
    decl_name: []const u8,
    token: []const u8,
) bool {
    if (fragment.len == 0) return false;
    if (fragment.len > decl_name.len) return false;
    if (std.mem.eql(u8, fragment, token)) return false;
    return std.mem.startsWith(u8, decl_name, fragment);
}

fn sortGroupForDeclaration(kind: DeclarationKind) []const u8 {
    return switch (kind) {
        .sort => sort_group_sort,
        .term, .def => sort_group_term,
        .axiom, .theorem => sort_group_global_rule,
        .lemma => sort_group_proof_lemma,
        .proof_line => sort_group_proof_reference,
        .sort_var => sort_group_local_binder,
    };
}

fn identifierCompletionReplacementRange(
    document: DocumentId,
    text: []const u8,
    offset: usize,
) SourceRange {
    var start = offset;
    while (start > 0 and completionTokenChar(text[start - 1])) start -= 1;
    var end = offset;
    while (end < text.len and completionTokenChar(text[end])) end += 1;
    return .{ .document = document, .start = start, .end = end };
}

fn mathCompletionReplacementRange(
    document: DocumentId,
    text: []const u8,
    math: SourceSpan,
    offset: usize,
    left_delims: [256]bool,
    right_delims: [256]bool,
) SourceRange {
    const inner_start = @min(math.start + 1, text.len);
    const raw_inner_end = if (math.end > math.start and
        math.end <= text.len and text[math.end - 1] == '$')
        math.end - 1
    else
        math.end;
    const inner_end = @max(inner_start, @min(raw_inner_end, text.len));
    const safe_offset = @min(@max(offset, inner_start), inner_end);
    const inner = text[inner_start..inner_end];
    const rel_offset = safe_offset - inner_start;
    var cursor = MathTokenCursor{
        .src = inner,
        .left_delims = left_delims,
        .right_delims = right_delims,
    };
    while (cursor.next()) |token| {
        if (rel_offset >= token.start and rel_offset <= token.end) {
            return .{
                .document = document,
                .start = inner_start + token.start,
                .end = inner_start + token.end,
            };
        }
    }
    return .{
        .document = document,
        .start = safe_offset,
        .end = safe_offset,
    };
}

fn completionTokenChar(ch: u8) bool {
    return isIdentChar(ch) or ch == '@' or ch == '#';
}

fn annotationContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    if (!startsLineComment(text, start)) return false;
    var pos = start + 2;
    while (pos < offset and pos < text.len and text[pos] == ' ') pos += 1;
    return pos < text.len and text[pos] == '|';
}

fn lineCommentContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const safe_offset = @min(offset, text.len);
    var pos = start;
    while (pos < safe_offset and pos + 1 < text.len) : (pos += 1) {
        if (text[pos] == '\n') return false;
        if (startsLineComment(text, pos)) return true;
    }
    return false;
}

fn mathStringAt(text: []const u8, offset: usize) ?SourceSpan {
    var pos: usize = 0;
    while (pos < text.len) {
        if (startsLineComment(text, pos)) {
            pos = lineEnd(text, pos);
            continue;
        }
        if (text[pos] != '$') {
            pos += 1;
            continue;
        }
        const start = pos;
        pos += 1;
        const inner_start = pos;
        while (pos < text.len and text[pos] != '$') pos += 1;
        const inner_end = pos;
        if (offset >= inner_start and offset <= inner_end) {
            return .{
                .start = start,
                .end = if (pos < text.len) pos + 1 else pos,
            };
        }
        if (pos < text.len) pos += 1;
    }
    return null;
}

fn mm0SortContextAt(text: []const u8, offset: usize) bool {
    const start = statementStartBefore(text, offset);
    var token_start = @min(offset, text.len);
    while (token_start > start and completionTokenChar(text[token_start - 1])) {
        token_start -= 1;
    }
    const before = previousNonSpace(text, start, token_start) orelse return false;
    if (text[before] == ':') return true;
    return before > start and text[before] == ',' and
        hasColonSince(text, start, before);
}

fn mm0ReferenceContextAt(text: []const u8, offset: usize) bool {
    const start = statementStartBefore(text, offset);
    const prefix = text[start..offset];
    return std.mem.indexOf(u8, prefix, "notation") != null or
        std.mem.indexOf(u8, prefix, "prefix") != null or
        std.mem.indexOf(u8, prefix, "infixl") != null or
        std.mem.indexOf(u8, prefix, "infixr") != null;
}

fn mm0TopLevelContextAt(text: []const u8, offset: usize) bool {
    const start = statementStartBefore(text, offset);
    var pos = start;
    while (pos < offset) {
        if (isMathWhitespace(text[pos])) {
            pos += 1;
            continue;
        }
        if (startsLineComment(text, pos)) {
            pos = lineEnd(text, pos);
            continue;
        }
        if (isIdentChar(text[pos])) {
            var end = pos + 1;
            while (end < offset and isIdentChar(text[end])) end += 1;
            if (isTopLevelModifier(text[pos..end])) {
                pos = end;
                continue;
            }
        }
        return rangeTouchesCurrentToken(text, pos, offset);
    }
    return true;
}

fn proofLineMathContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const end = lineEnd(text, offset);
    const line = text[start..end];
    const colon = std.mem.indexOfScalar(u8, line, ':') orelse return false;
    const by = std.mem.indexOf(u8, line, " by") orelse return false;
    return colon < by;
}

fn proofHeaderContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const end = lineEnd(text, offset);
    const line = text[start..end];
    if (std.mem.indexOfScalar(u8, line, ':') != null) return false;
    if (std.mem.indexOf(u8, line, "by") != null) return false;
    if (lineLooksUnderline(line)) return false;
    const prev_end = if (start == 0) 0 else start - 1;
    const prev_start = lineStart(text, prev_end);
    if (prev_start < prev_end and lineLooksUnderline(text[prev_start..prev_end])) {
        return false;
    }
    return true;
}

fn proofRuleContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const prefix = text[start..offset];
    const by_pos = std.mem.lastIndexOf(u8, prefix, "by") orelse return false;
    if (by_pos > 0 and isIdentChar(prefix[by_pos - 1])) return false;
    const after = by_pos + 2;
    if (after < prefix.len and isIdentChar(prefix[after])) return false;
    const suffix = prefix[after..];
    if (std.mem.lastIndexOfScalar(u8, suffix, '[')) |open| {
        if (std.mem.lastIndexOfScalar(u8, suffix, ']')) |close| {
            if (close > open) return false;
        }
        return false;
    }
    if (std.mem.lastIndexOfScalar(u8, suffix, '(')) |open| {
        if (std.mem.lastIndexOfScalar(u8, suffix, ')')) |close| {
            if (close > open) return true;
        }
        return false;
    }
    return true;
}

fn appendNotationSnippetCompletion(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) !void {
    const snippet = notation.snippet_text orelse return;
    if (completionAlreadyHasSnippet(list.items, replacement, snippet)) return;
    try list.append(allocator, .{
        .label = notation.snippet_label orelse notation.token,
        .kind = .snippet,
        .detail = notation.detail,
        .documentation_markdown = decl.markdown,
        .replacement = replacement,
        .replacement_text = notation.token,
        .snippet_replacement_text = snippet,
        .filter_text = notationSnippetFilterText(
            notation,
            decl,
            replacement_fragment,
        ),
        .sort_text = notationSnippetSortText(notation, decl),
    });
}

fn completionAlreadyInserts(
    items: []const CompletionItem,
    replacement: SourceRange,
    replacement_text: []const u8,
) bool {
    for (items) |item| {
        if (item.replacement.document != replacement.document or
            item.replacement.start != replacement.start or
            item.replacement.end != replacement.end)
        {
            continue;
        }
        if (std.mem.eql(u8, item.replacement_text, replacement_text)) {
            return true;
        }
    }
    return false;
}

fn completionAlreadyHasSnippet(
    items: []const CompletionItem,
    replacement: SourceRange,
    snippet_text: []const u8,
) bool {
    for (items) |item| {
        if (item.replacement.document != replacement.document or
            item.replacement.start != replacement.start or
            item.replacement.end != replacement.end)
        {
            continue;
        }
        const other = item.snippet_replacement_text orelse continue;
        if (std.mem.eql(u8, other, snippet_text)) return true;
    }
    return false;
}

pub fn escapeSnippetText(
    allocator: std.mem.Allocator,
    text: []const u8,
) ![]const u8 {
    var out = std.ArrayListUnmanaged(u8){};
    try appendEscapedSnippetText(allocator, &out, text);
    return try out.toOwnedSlice(allocator);
}

fn appendEscapedSnippetText(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    text: []const u8,
) !void {
    for (text) |ch| {
        if (ch == '$' or ch == '}' or ch == '\\') {
            try out.append(allocator, '\\');
        }
        try out.append(allocator, ch);
    }
}

fn appendSnippetPlaceholder(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    index: usize,
    label: []const u8,
) !void {
    try out.writer(allocator).print("${{{d}:", .{index});
    try appendEscapedSnippetText(allocator, out, label);
    try out.append(allocator, '}');
}

fn buildPrefixSnippet(
    allocator: std.mem.Allocator,
    token: []const u8,
    args: []const BinderDecl,
    decl_name: []const u8,
) !?NotationSnippet {
    if (args.len == 0) return null;

    var label = std.ArrayListUnmanaged(u8){};
    try label.appendSlice(allocator, token);
    try label.appendSlice(allocator, " …");

    var text = std.ArrayListUnmanaged(u8){};
    try appendEscapedSnippetText(allocator, &text, token);
    for (args, 0..) |arg, i| {
        try text.append(allocator, ' ');
        try appendSnippetPlaceholder(allocator, &text, i + 1, arg.name);
    }
    try text.appendSlice(allocator, "$0");

    return .{
        .label = try label.toOwnedSlice(allocator),
        .text = try text.toOwnedSlice(allocator),
        .filter_text = try std.fmt.allocPrint(
            allocator,
            "{s} {s}",
            .{ token, decl_name },
        ),
    };
}

fn buildGeneralNotationSnippet(
    allocator: std.mem.Allocator,
    pieces: []const NotationPiece,
    decl_name: []const u8,
) !?NotationSnippet {
    if (pieces.len == 0) return null;

    var label = std.ArrayListUnmanaged(u8){};
    var text = std.ArrayListUnmanaged(u8){};
    var filter = std.ArrayListUnmanaged(u8){};
    var has_variable = false;

    for (pieces, 0..) |piece, i| {
        if (i != 0 and notationSnippetNeedsSpace(pieces[i - 1], piece)) {
            try text.append(allocator, ' ');
            if (label.items.len != 0) try label.append(allocator, ' ');
            if (filter.items.len != 0) try filter.append(allocator, ' ');
        }
        switch (piece) {
            .constant => |constant| {
                try appendEscapedSnippetText(allocator, &text, constant);
                try label.appendSlice(allocator, constant);
                try filter.appendSlice(allocator, constant);
            },
            .variable => |variable| {
                has_variable = true;
                try appendSnippetPlaceholder(
                    allocator,
                    &text,
                    variable.arg_index + 1,
                    variable.name,
                );
                try label.appendSlice(allocator, "…");
            },
        }
    }
    if (!has_variable) return null;
    try text.appendSlice(allocator, "$0");
    if (filter.items.len != 0) try filter.append(allocator, ' ');
    try filter.appendSlice(allocator, decl_name);

    return .{
        .label = try label.toOwnedSlice(allocator),
        .text = try text.toOwnedSlice(allocator),
        .filter_text = try filter.toOwnedSlice(allocator),
    };
}

fn notationSnippetNeedsSpace(prev: NotationPiece, next: NotationPiece) bool {
    if (std.meta.activeTag(prev) == .variable or
        std.meta.activeTag(next) == .variable)
        return true;
    return !isSnippetDelimiter(prev.constant) and
        !isSnippetDelimiter(next.constant);
}

fn isSnippetDelimiter(token: []const u8) bool {
    return std.mem.eql(u8, token, "(") or
        std.mem.eql(u8, token, ")") or
        std.mem.eql(u8, token, "[") or
        std.mem.eql(u8, token, "]") or
        std.mem.eql(u8, token, "{") or
        std.mem.eql(u8, token, "}");
}

fn collectNotationBinderVariables(
    allocator: std.mem.Allocator,
    variables: *std.StringHashMapUnmanaged(NotationVariable),
    text: []const u8,
    stmt: SourceSpan,
    end: usize,
    args: []const BinderDecl,
) !void {
    var pos = stmt.start;
    var arg_index: usize = 0;
    while (pos < end and pos < stmt.end) {
        const open = text[pos];
        if (open != '(' and open != '{') {
            pos += 1;
            continue;
        }
        const close: u8 = if (open == '(') ')' else '}';
        pos += 1;
        while (pos < end and pos < stmt.end) {
            skipNotationWhitespace(text, &pos, end);
            if (pos >= end or pos >= stmt.end or text[pos] == ':') break;
            if (text[pos] == '.') pos += 1;
            const name = readNotationIdent(text, &pos, end) orelse {
                pos += 1;
                continue;
            };
            const label = if (std.mem.eql(u8, name, "_"))
                try placeholderNameForArg(allocator, args, arg_index)
            else
                name;
            try variables.put(allocator, name, .{
                .arg_index = arg_index,
                .name = label,
            });
            arg_index += 1;
        }
        while (pos < end and pos < stmt.end and text[pos] != close) {
            pos += 1;
        }
        if (pos < end and pos < stmt.end) pos += 1;
    }
}

fn collectNotationPieces(
    allocator: std.mem.Allocator,
    pieces: *std.ArrayListUnmanaged(NotationPiece),
    constants: *std.ArrayListUnmanaged([]const u8),
    variables: std.StringHashMapUnmanaged(NotationVariable),
    text: []const u8,
    start: usize,
    end: usize,
) !void {
    var pos = start;
    while (pos < end) {
        skipNotationWhitespace(text, &pos, end);
        if (pos >= end or text[pos] == ';') break;
        if (text[pos] == '$') {
            const math_start = pos + 1;
            pos = math_start;
            while (pos < end and text[pos] != '$') pos += 1;
            const math_end = pos;
            if (pos < end) pos += 1;
            const token = trimMathWhitespace(text[math_start..math_end]);
            if (token.len != 0 and !containsMathWhitespace(token)) {
                try pieces.append(allocator, .{ .constant = token });
                try constants.append(allocator, token);
            }
            continue;
        }
        if (readNotationIdent(text, &pos, end)) |ident| {
            if (variables.get(ident)) |variable| {
                try pieces.append(allocator, .{ .variable = variable });
            }
            continue;
        }
        pos += 1;
    }
}

fn skipNotationWhitespace(text: []const u8, pos: *usize, end: usize) void {
    while (pos.* < end and isMathWhitespace(text[pos.*])) pos.* += 1;
}

fn readNotationIdent(
    text: []const u8,
    pos: *usize,
    end: usize,
) ?[]const u8 {
    if (pos.* >= end or !isIdentChar(text[pos.*])) return null;
    const start = pos.*;
    pos.* += 1;
    while (pos.* < end and isIdentChar(text[pos.*])) pos.* += 1;
    return text[start..pos.*];
}

fn placeholderNameForArg(
    allocator: std.mem.Allocator,
    args: []const BinderDecl,
    index: usize,
) ![]const u8 {
    if (index < args.len and args[index].name.len != 0) {
        return args[index].name;
    }
    return try std.fmt.allocPrint(allocator, "arg{d}", .{index + 1});
}

fn declarationKindIn(kind: DeclarationKind, kinds: []const DeclarationKind) bool {
    for (kinds) |allowed| {
        if (kind == allowed) return true;
    }
    return false;
}

fn globalDeclarationAvailable(
    decl: Declaration,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
) bool {
    return switch (document) {
        .mm0 => decl.name_range.start <= use_start,
        .proof => if (available_before) |before|
            decl.name_range.start < before
        else
            true,
    };
}

fn completionKindForDeclaration(kind: DeclarationKind) CompletionKind {
    return switch (kind) {
        .sort => .sort,
        .term => .term,
        .def => .def,
        .axiom => .axiom,
        .theorem => .theorem,
        .lemma => .lemma,
        .proof_line => .proof_line,
        .sort_var => .binder,
    };
}

fn simpleNotationKind(keyword: []const u8) NotationKind {
    if (std.mem.eql(u8, keyword, "prefix")) return .prefix;
    if (std.mem.eql(u8, keyword, "infixl")) return .infixl;
    return .infixr;
}

fn declarationKindName(kind: DeclarationKind) []const u8 {
    return switch (kind) {
        .sort => "sort",
        .term => "term",
        .def => "def",
        .axiom => "axiom",
        .theorem => "theorem",
        .lemma => "lemma",
        .proof_line => "proof line",
        .sort_var => "sort variable",
    };
}

fn isTopLevelModifier(word: []const u8) bool {
    return std.mem.eql(u8, word, "pub") or
        std.mem.eql(u8, word, "pure") or
        std.mem.eql(u8, word, "strict") or
        std.mem.eql(u8, word, "provable") or
        std.mem.eql(u8, word, "free");
}

fn rangeTouchesCurrentToken(text: []const u8, pos: usize, offset: usize) bool {
    if (pos >= text.len or offset > text.len) return false;
    const repl = identifierCompletionReplacementRange(.mm0, text, offset);
    return pos >= repl.start and pos <= repl.end;
}

fn hasColonSince(text: []const u8, start: usize, end: usize) bool {
    var pos = start;
    while (pos < end) : (pos += 1) {
        if (text[pos] == ':') return true;
        if (text[pos] == ';') return false;
    }
    return false;
}

fn previousNonSpace(text: []const u8, start: usize, offset: usize) ?usize {
    var pos = @min(offset, text.len);
    while (pos > start) {
        pos -= 1;
        if (!isMathWhitespace(text[pos])) return pos;
    }
    return null;
}

fn statementStartBefore(text: []const u8, offset: usize) usize {
    var pos = @min(offset, text.len);
    while (pos > 0) {
        pos -= 1;
        if (text[pos] == ';') return pos + 1;
    }
    return 0;
}

fn lineStart(text: []const u8, offset: usize) usize {
    var pos = @min(offset, text.len);
    while (pos > 0 and text[pos - 1] != '\n') pos -= 1;
    return pos;
}

fn lineEnd(text: []const u8, offset: usize) usize {
    var pos = @min(offset, text.len);
    while (pos < text.len and text[pos] != '\n') pos += 1;
    return pos;
}

fn lineLooksUnderline(line: []const u8) bool {
    const trimmed = std.mem.trim(u8, line, " \t\r\n");
    if (trimmed.len == 0) return false;
    for (trimmed) |ch| {
        if (ch != '-') return false;
    }
    return true;
}

const LookupHit = struct {
    source_range: SourceRange,
    target_range: ?SourceRange,
    markdown: []const u8,
};

const NavigationSymbol = struct {
    source_range: SourceRange,
    target_range: ?SourceRange,
    markdown: []const u8,
};

const ProofBlockInfo = struct {
    kind: proof_script.BlockKind,
    name: []const u8,
    name_range: SourceRange,
    span: SourceRange,
    global_available_before: ?usize = null,
    decl_index: ?usize = null,
    hyp_count: usize = 0,
    hyp_count_known: bool = false,
};

const ProofRuleDecl = struct {
    name: []const u8,
    decl_index: usize,
    available_start: usize,
    sort_text: []const u8,
};

const ProofLineDecl = struct {
    block_index: usize,
    name: []const u8,
    decl_index: usize,
    line_start: usize,
    sort_text: []const u8,
};

const ProofApplicationInfo = struct {
    block_index: usize,
    rule_name: []const u8,
    rule_span: SourceRange,
    binding_list_span: ?SourceRange = null,
    refs_span: ?SourceRange = null,
    span: SourceRange,
    use_start: usize,
    line_start: usize,
};

const RuleResolution = struct {
    decl_index: usize,
    available: bool,
};

const NotationKind = enum {
    prefix,
    infixl,
    infixr,
    general,

    fn detailPrefix(self: NotationKind) []const u8 {
        return switch (self) {
            .prefix => "prefix",
            .infixl => "infixl",
            .infixr => "infixr",
            .general => "notation",
        };
    }
};

const NotationCompletionDecl = struct {
    decl_index: usize,
    kind: NotationKind,
    token: []const u8,
    detail: []const u8,
    filter_text: []const u8,
    alias_filter_text: []const u8,
    alias_sort_text: []const u8,
    token_sort_text: []const u8,
    snippet_label: ?[]const u8 = null,
    snippet_text: ?[]const u8 = null,
    snippet_filter_text: ?[]const u8 = null,
    snippet_alias_filter_text: ?[]const u8 = null,
    snippet_sort_text: ?[]const u8 = null,
};

const NotationVariable = struct {
    arg_index: usize,
    name: []const u8,
};

const NotationPiece = union(enum) {
    constant: []const u8,
    variable: NotationVariable,
};

const NotationSnippet = struct {
    label: []const u8,
    text: []const u8,
    filter_text: []const u8,
};

const Builder = struct {
    allocator: std.mem.Allocator,
    declarations: std.ArrayListUnmanaged(Declaration) = .{},
    decl_by_name: std.StringHashMapUnmanaged(usize) = .empty,
    symbols: std.ArrayListUnmanaged(NavigationSymbol) = .{},
    mm0_outline: std.ArrayListUnmanaged(OutlineSymbol) = .{},
    proof_outline: std.ArrayListUnmanaged(OutlineSymbol) = .{},
    proof_blocks: std.ArrayListUnmanaged(ProofBlockInfo) = .{},
    proof_rules: std.ArrayListUnmanaged(ProofRuleDecl) = .{},
    proof_lines: std.ArrayListUnmanaged(ProofLineDecl) = .{},
    proof_applications: std.ArrayListUnmanaged(ProofApplicationInfo) = .{},
    notations: std.ArrayListUnmanaged(NotationCompletionDecl) = .{},
    notation_by_token: std.StringHashMapUnmanaged(usize) = .empty,
    sort_var_by_token: std.StringHashMapUnmanaged(usize) = .empty,
    sort_names: std.ArrayListUnmanaged([]const u8) = .{},
    left_delims: [256]bool = [_]bool{false} ** 256,
    right_delims: [256]bool = [_]bool{false} ** 256,
    mm0_parser: ?parse.MM0Parser = null,

    fn init(allocator: std.mem.Allocator) Builder {
        return .{ .allocator = allocator };
    }

    fn indexMm0(self: *Builder, text: []const u8) !void {
        var parser = parse.MM0Parser.init(text, self.allocator);
        var statements = StatementIterator.init(text);
        while (true) {
            const stmt = parser.next() catch |err| {
                if (isFatalIndexError(err)) return err;
                break;
            };
            const concrete = stmt orelse break;
            try self.addStatement(
                concrete,
                text,
                nextStatementRangeForMm0Stmt(&statements, concrete),
                parser.last_annotations,
                parser.last_annotation_spans,
            );
        }
        self.mm0_parser = parser;
        try self.collectMm0Notation(text);
        try self.indexMm0Math(text);
    }

    fn indexProof(self: *Builder, text: []const u8) !void {
        var parser = proof_script.Parser.init(self.allocator, text);
        var blocks = std.ArrayListUnmanaged(proof_script.ProofBlock){};
        while (true) {
            const next = parser.nextBlock() catch |err| {
                if (isFatalIndexError(err)) return err;
                if (!parser.recoverToNextBlockBoundary()) break;
                continue;
            };
            const block = next orelse break;
            try blocks.append(self.allocator, block);
        }

        for (blocks.items, 0..) |block, i| {
            try self.addProofBlock(
                block,
                self.globalAvailabilityForProofBlock(blocks.items, i),
            );
        }
    }

    fn globalAvailabilityForProofBlock(
        self: *const Builder,
        blocks: []const proof_script.ProofBlock,
        index: usize,
    ) ?usize {
        const block = blocks[index];
        if (block.kind == .theorem) {
            return self.theoremAvailabilityBound(block.name);
        }

        var i = index + 1;
        while (i < blocks.len) : (i += 1) {
            if (blocks[i].kind != .theorem) continue;
            return self.theoremAvailabilityBound(blocks[i].name);
        }
        return null;
    }

    fn theoremAvailabilityBound(
        self: *const Builder,
        name: []const u8,
    ) ?usize {
        const decl_index = self.theoremDeclIndex(name) orelse return null;
        return self.declarations.items[decl_index].name_range.start;
    }

    fn addStatement(
        self: *Builder,
        stmt: parse.MM0Stmt,
        text: []const u8,
        statement_range: SourceRange,
        annotations: []const []const u8,
        annotation_spans: []const parse.MathSpan,
    ) !void {
        switch (stmt) {
            .sort => |sort| {
                try self.sort_names.append(self.allocator, sort.name);
                _ = try self.addGlobalDeclaration(.{
                    .name = sort.name,
                    .kind = .sort,
                    .name_range = mathSpanRange(sort.name_span),
                    .markdown = try sortMarkdown(
                        self.allocator,
                        sort,
                        annotations,
                    ),
                });
                try self.addMm0Outline(.{
                    .name = sort.name,
                    .kind = .sort,
                    .range = statement_range,
                    .selection_range = mathSpanRange(sort.name_span),
                });
                try self.addSortVarAnnotations(
                    sort,
                    annotations,
                    annotation_spans,
                );
            },
            .term => |term| {
                const kind: DeclarationKind = if (term.is_def) .def else .term;
                _ = try self.addGlobalDeclaration(.{
                    .name = term.name,
                    .kind = kind,
                    .name_range = mathSpanRange(term.name_span),
                    .markdown = try termMarkdown(
                        self.allocator,
                        text,
                        term,
                        annotations,
                    ),
                    .binders = try bindersFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        term.arg_names,
                        term.args,
                    ),
                    .completion_args = try completionArgsFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        term.arg_names,
                        term.args,
                    ),
                });
                try self.addMm0Outline(.{
                    .name = term.name,
                    .kind = kind,
                    .range = statement_range,
                    .selection_range = mathSpanRange(term.name_span),
                });
                try self.addArgSortUses(.mm0, text, term.args);
                try self.addSortUse(.mm0, text, term.ret_sort_name);
            },
            .assertion => |assertion| {
                const kind: DeclarationKind = switch (assertion.kind) {
                    .axiom => .axiom,
                    .theorem => .theorem,
                };
                _ = try self.addGlobalDeclaration(.{
                    .name = assertion.name,
                    .kind = kind,
                    .name_range = mathSpanRange(assertion.name_span),
                    .markdown = try assertionMarkdown(
                        self.allocator,
                        text,
                        assertion,
                        self.sortNameForId(assertion.concl.sort()),
                        annotations,
                    ),
                    .binders = try bindersFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        assertion.arg_names,
                        assertion.args,
                    ),
                    .completion_args = try completionArgsFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        assertion.arg_names,
                        assertion.args,
                    ),
                    .hyp_count = assertion.hyps.len,
                });
                try self.addMm0Outline(.{
                    .name = assertion.name,
                    .kind = kind,
                    .range = statement_range,
                    .selection_range = mathSpanRange(assertion.name_span),
                });
                try self.addArgSortUses(.mm0, text, assertion.args);
            },
        }
    }

    fn addSortVarAnnotations(
        self: *Builder,
        sort: parse.SortStmt,
        annotations: []const []const u8,
        annotation_spans: []const parse.MathSpan,
    ) !void {
        for (annotations, 0..) |annotation, i| {
            if (i >= annotation_spans.len) continue;
            var pos: usize = 0;
            const directive = nextAnnotationToken(annotation, &pos) orelse {
                continue;
            };
            if (!std.mem.eql(u8, directive.text, "@vars")) continue;

            while (nextAnnotationToken(annotation, &pos)) |token| {
                const span = annotation_spans[i];
                try self.addSortVarDeclaration(
                    sort.name,
                    token.text,
                    .{
                        .document = .mm0,
                        .start = span.start + token.start,
                        .end = span.start + token.end,
                    },
                );
            }
        }
    }

    fn addSortVarDeclaration(
        self: *Builder,
        sort_name: []const u8,
        token: []const u8,
        range: SourceRange,
    ) !void {
        const decl_index = try self.addDeclaration(.{
            .name = token,
            .kind = .sort_var,
            .name_range = range,
            .markdown = try sortVarMarkdown(
                self.allocator,
                token,
                sort_name,
            ),
        });
        if (self.sort_var_by_token.get(token) == null) {
            try self.sort_var_by_token.put(
                self.allocator,
                token,
                decl_index,
            );
        }
    }

    fn addGlobalDeclaration(self: *Builder, decl: Declaration) !usize {
        const index = try self.addDeclaration(decl);
        try self.decl_by_name.put(self.allocator, decl.name, index);
        return index;
    }

    fn addDeclaration(self: *Builder, decl_arg: Declaration) !usize {
        var decl = decl_arg;
        if (decl.sort_text.len == 0) {
            decl.sort_text = try completionSortText(
                self.allocator,
                sortGroupForDeclaration(decl.kind),
                decl.name_range.start,
                decl.name,
            );
        }
        const index = self.declarations.items.len;
        try self.declarations.append(self.allocator, decl);
        try self.addSymbol(.{
            .source_range = decl.name_range,
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
        for (decl.binders) |binder| {
            const range = binder.range orelse continue;
            try self.addSymbol(.{
                .source_range = range,
                .target_range = range,
                .markdown = try binderMarkdown(
                    self.allocator,
                    decl,
                    binder,
                ),
            });
        }
        return index;
    }

    fn addArgSortUses(
        self: *Builder,
        document: DocumentId,
        text: []const u8,
        args: []const parse.ArgInfo,
    ) !void {
        for (args) |arg| {
            try self.addSortUse(document, text, arg.sort_name);
        }
    }

    fn addSortUse(
        self: *Builder,
        document: DocumentId,
        text: []const u8,
        sort_name: []const u8,
    ) !void {
        const range = sourceRangeFromSlice(document, text, sort_name) orelse {
            return;
        };
        const decl_index = self.sortDeclIndex(sort_name) orelse return;
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = range,
            .target_range = targetRangeIfAvailable(decl, range.start),
            .markdown = decl.markdown,
        });
    }

    fn addDeclarationNameUse(
        self: *Builder,
        text: []const u8,
        name: []const u8,
        decl_index: usize,
    ) !void {
        const range = sourceRangeFromSlice(.mm0, text, name) orelse return;
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = range,
            .target_range = targetRangeIfAvailable(decl, range.start),
            .markdown = decl.markdown,
        });
    }

    fn addSymbol(self: *Builder, symbol: NavigationSymbol) !void {
        try self.symbols.append(self.allocator, symbol);
    }

    fn addMm0Outline(self: *Builder, symbol: OutlineSymbol) !void {
        try self.mm0_outline.append(self.allocator, symbol);
    }

    fn addProofOutline(self: *Builder, symbol: OutlineSymbol) !void {
        try self.proof_outline.append(self.allocator, symbol);
    }

    fn addProofBlock(
        self: *Builder,
        block: proof_script.ProofBlock,
        global_available_before: ?usize,
    ) !void {
        const block_index = self.proof_blocks.items.len;
        try self.proof_blocks.append(self.allocator, .{
            .kind = block.kind,
            .name = block.name,
            .name_range = proofSpanRange(block.name_span),
            .span = proofSpanRange(block.span),
            .global_available_before = global_available_before,
        });
        try self.addProofOutline(.{
            .name = block.name,
            .kind = proofBlockDeclarationKind(block.kind),
            .range = proofSpanRange(block.span),
            .selection_range = proofSpanRange(block.name_span),
        });

        switch (block.kind) {
            .theorem => try self.addTheoremBlockHeader(block_index, block),
            .lemma => try self.addLemmaBlockHeader(block_index, block),
        }

        for (block.lines) |line| {
            try self.addProofLine(block_index, line);
        }

        const info = self.proof_blocks.items[block_index];
        if (block.kind == .lemma) {
            if (info.decl_index) |decl_index| {
                try self.proof_rules.append(self.allocator, .{
                    .name = block.name,
                    .decl_index = decl_index,
                    .available_start = block.span.end,
                    .sort_text = try completionSortText(
                        self.allocator,
                        sort_group_proof_lemma,
                        block.span.end,
                        block.name,
                    ),
                });
            }
        }
    }

    fn addTheoremBlockHeader(
        self: *Builder,
        block_index: usize,
        block: proof_script.ProofBlock,
    ) !void {
        const decl_index = self.theoremDeclIndex(block.name) orelse return;
        const decl = self.declarations.items[decl_index];
        self.proof_blocks.items[block_index].decl_index = decl_index;
        self.proof_blocks.items[block_index].hyp_count = decl.hyp_count;
        self.proof_blocks.items[block_index].hyp_count_known = true;
        try self.addSymbol(.{
            .source_range = proofSpanRange(block.name_span),
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
    }

    fn addLemmaBlockHeader(
        self: *Builder,
        block_index: usize,
        block: proof_script.ProofBlock,
    ) !void {
        const maybe_assertion = try self.parseLemmaAssertion(block);
        const hyp_count = if (maybe_assertion) |assertion|
            assertion.hyps.len
        else
            0;
        const binders = if (maybe_assertion) |assertion|
            try bindersFromLemma(
                self.allocator,
                block,
                assertion.arg_names,
                assertion.args,
            )
        else
            &.{};
        const decl: Declaration = .{
            .name = block.name,
            .kind = .lemma,
            .name_range = proofSpanRange(block.name_span),
            .markdown = try lemmaMarkdown(
                self.allocator,
                block,
                hyp_count,
                maybe_assertion != null,
            ),
            .binders = binders,
            .hyp_count = hyp_count,
        };
        const decl_index = try self.addDeclaration(decl);
        self.proof_blocks.items[block_index].decl_index = decl_index;
        self.proof_blocks.items[block_index].hyp_count = hyp_count;
        self.proof_blocks.items[block_index].hyp_count_known =
            maybe_assertion != null;
        try self.indexLemmaHeaderMath(
            block,
            decl_index,
            self.proof_blocks.items[block_index].global_available_before,
        );
    }

    fn parseLemmaAssertion(
        self: *Builder,
        block: proof_script.ProofBlock,
    ) !?parse.AssertionStmt {
        const parser = self.mm0_parser orelse return null;
        const src = try std.fmt.allocPrint(
            self.allocator,
            "theorem {s}{s};",
            .{ block.name, block.header_tail },
        );
        return parser.parseAssertionText(src, .theorem, true) catch |err| {
            if (isFatalIndexError(err)) return err;
            return null;
        };
    }

    fn addProofLine(
        self: *Builder,
        block_index: usize,
        line: proof_script.ProofLine,
    ) !void {
        const decl: Declaration = .{
            .name = line.label,
            .kind = .proof_line,
            .name_range = proofSpanRange(line.label_span),
            .markdown = try proofLineMarkdown(self.allocator, line),
        };
        const decl_index = try self.addDeclaration(decl);
        try self.indexRuleApplication(block_index, line.application, line.span.start);
        try self.indexProofMathString(block_index, line.assertion);
        try self.proof_lines.append(self.allocator, .{
            .block_index = block_index,
            .name = line.label,
            .decl_index = decl_index,
            .line_start = line.span.start,
            .sort_text = try completionSortText(
                self.allocator,
                sort_group_proof_reference,
                line.span.start,
                line.label,
            ),
        });
    }

    fn indexRuleApplication(
        self: *Builder,
        block_index: usize,
        app: proof_script.RuleApplication,
        line_start: usize,
    ) !void {
        try self.proof_applications.append(self.allocator, .{
            .block_index = block_index,
            .rule_name = app.rule_name,
            .rule_span = proofSpanRange(app.rule_span),
            .binding_list_span = if (app.binding_list_span) |span|
                proofSpanRange(span)
            else
                null,
            .refs_span = if (app.refs_span) |span| proofSpanRange(span) else null,
            .span = proofSpanRange(app.span),
            .use_start = app.rule_span.start,
            .line_start = line_start,
        });
        const maybe_rule = self.resolveRule(
            block_index,
            app.rule_name,
            app.rule_span.start,
        );
        if (maybe_rule) |rule| {
            const decl = self.declarations.items[rule.decl_index];
            try self.addSymbol(.{
                .source_range = proofSpanRange(app.rule_span),
                .target_range = if (rule.available) decl.name_range else null,
                .markdown = decl.markdown,
            });
            try self.indexArgBindings(app, rule.decl_index, rule.available);
        } else {
            try self.addSymbol(.{
                .source_range = proofSpanRange(app.rule_span),
                .target_range = null,
                .markdown = try unknownRuleMarkdown(
                    self.allocator,
                    app.rule_name,
                ),
            });
            try self.indexUnknownArgBindings(app);
        }

        try self.indexRuleApplicationMath(block_index, app);

        for (app.refs) |ref| {
            switch (ref) {
                .hyp => |hyp| try self.addHypRef(block_index, hyp),
                .line => |line| try self.addLineRef(block_index, line, line_start),
                .application => |child| {
                    try self.indexRuleApplication(block_index, child, line_start);
                },
            }
        }
    }

    fn indexArgBindings(
        self: *Builder,
        app: proof_script.RuleApplication,
        decl_index: usize,
        rule_available: bool,
    ) !void {
        const decl = self.declarations.items[decl_index];
        for (app.arg_bindings) |binding| {
            const binder = findBinder(decl, binding.name) orelse {
                try self.addSymbol(.{
                    .source_range = proofSpanRange(binding.name_span),
                    .target_range = null,
                    .markdown = try unknownBindingMarkdown(
                        self.allocator,
                        binding.name,
                        decl.name,
                    ),
                });
                continue;
            };
            try self.addSymbol(.{
                .source_range = proofSpanRange(binding.name_span),
                .target_range = if (rule_available)
                    binder.range orelse decl.name_range
                else
                    null,
                .markdown = try binderMarkdown(
                    self.allocator,
                    decl,
                    binder,
                ),
            });
        }
    }

    fn indexUnknownArgBindings(
        self: *Builder,
        app: proof_script.RuleApplication,
    ) !void {
        for (app.arg_bindings) |binding| {
            try self.addSymbol(.{
                .source_range = proofSpanRange(binding.name_span),
                .target_range = null,
                .markdown = try unresolvedBindingMarkdown(
                    self.allocator,
                    binding.name,
                    app.rule_name,
                ),
            });
        }
    }

    fn addHypRef(
        self: *Builder,
        block_index: usize,
        hyp: proof_script.HypRef,
    ) !void {
        const block = self.proof_blocks.items[block_index];
        if (hyp.index == 0 or
            (block.hyp_count_known and hyp.index > block.hyp_count))
        {
            try self.addSymbol(.{
                .source_range = proofSpanRange(hyp.span),
                .target_range = null,
                .markdown = try unknownHypMarkdown(
                    self.allocator,
                    block.name,
                    hyp.index,
                ),
            });
            return;
        }
        const decl_index = block.decl_index orelse {
            try self.addSymbol(.{
                .source_range = proofSpanRange(hyp.span),
                .target_range = null,
                .markdown = try unknownHypMarkdown(
                    self.allocator,
                    block.name,
                    hyp.index,
                ),
            });
            return;
        };
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = proofSpanRange(hyp.span),
            .target_range = decl.name_range,
            .markdown = try hypRefMarkdown(
                self.allocator,
                block.name,
                hyp.index,
                block.hyp_count,
                block.hyp_count_known,
            ),
        });
    }

    fn addLineRef(
        self: *Builder,
        block_index: usize,
        ref: proof_script.LineRef,
        line_start: usize,
    ) !void {
        const decl_index = self.resolveLine(block_index, ref.label, line_start) orelse {
            try self.addSymbol(.{
                .source_range = proofSpanRange(ref.span),
                .target_range = null,
                .markdown = try unknownLineMarkdown(self.allocator, ref.label),
            });
            return;
        };
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = proofSpanRange(ref.span),
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
    }

    fn collectMm0Notation(self: *Builder, text: []const u8) !void {
        var iter = StatementIterator.init(text);
        while (iter.next()) |stmt| {
            const header = statementHeader(text, stmt) orelse continue;
            if (std.mem.eql(u8, header.keyword, "delimiter")) {
                self.collectDelimiterStatement(text, stmt);
                continue;
            }
            if (std.mem.eql(u8, header.keyword, "prefix") or
                std.mem.eql(u8, header.keyword, "infixl") or
                std.mem.eql(u8, header.keyword, "infixr"))
            {
                const name = header.name orelse continue;
                const decl_index = self.decl_by_name.get(name) orelse continue;
                const decl = self.declarations.items[decl_index];
                const kind = simpleNotationKind(header.keyword);
                try self.addDeclarationNameUse(text, name, decl_index);
                if (firstMathStringIn(text, stmt)) |math| {
                    const snippet = if (kind == .prefix)
                        try buildPrefixSnippet(
                            self.allocator,
                            trimMathWhitespace(math.text),
                            decl.completion_args,
                            decl.name,
                        )
                    else
                        null;
                    try self.addNotationMathToken(
                        decl_index,
                        kind,
                        math,
                        snippet,
                    );
                }
                continue;
            }
            if (!std.mem.eql(u8, header.keyword, "notation")) continue;
            const name = header.name orelse continue;
            const decl_index = self.decl_by_name.get(name) orelse continue;
            try self.addDeclarationNameUse(text, name, decl_index);
            const eq = findStatementByte(text, stmt, '=') orelse continue;
            try self.collectGeneralNotation(text, stmt, decl_index, eq);
        }
    }

    fn collectDelimiterStatement(
        self: *Builder,
        text: []const u8,
        stmt: SourceSpan,
    ) void {
        var pos = stmt.start;
        while (nextMathStringIn(text, stmt.end, &pos)) |math| {
            self.registerDelimiterMath(math.text);
        }
    }

    fn registerDelimiterMath(self: *Builder, math: []const u8) void {
        var pos: usize = 0;
        while (pos < math.len) {
            while (pos < math.len and isMathWhitespace(math[pos])) {
                pos += 1;
            }
            if (pos >= math.len) break;
            const ch = math[pos];
            pos += 1;
            self.left_delims[ch] = true;
            self.right_delims[ch] = true;
        }
    }

    fn collectGeneralNotation(
        self: *Builder,
        text: []const u8,
        stmt: SourceSpan,
        decl_index: usize,
        eq: usize,
    ) !void {
        const decl = self.declarations.items[decl_index];
        var variables = std.StringHashMapUnmanaged(NotationVariable){};
        try collectNotationBinderVariables(
            self.allocator,
            &variables,
            text,
            stmt,
            eq,
            decl.completion_args,
        );

        var pieces = std.ArrayListUnmanaged(NotationPiece){};
        var constants = std.ArrayListUnmanaged([]const u8){};
        try collectNotationPieces(
            self.allocator,
            &pieces,
            &constants,
            variables,
            text,
            eq + 1,
            stmt.end,
        );
        const snippet = try buildGeneralNotationSnippet(
            self.allocator,
            pieces.items,
            decl.name,
        );
        for (constants.items) |constant| {
            try self.addNotationToken(
                decl_index,
                .general,
                constant,
                snippet,
            );
        }
    }

    fn addNotationMathToken(
        self: *Builder,
        decl_index: usize,
        kind: NotationKind,
        math: MathStringSpan,
        snippet: ?NotationSnippet,
    ) !void {
        const trimmed = trimMathWhitespace(math.text);
        if (trimmed.len == 0) return;
        if (containsMathWhitespace(trimmed)) return;
        try self.addNotationToken(decl_index, kind, trimmed, snippet);
    }

    fn addNotationToken(
        self: *Builder,
        decl_index: usize,
        kind: NotationKind,
        token: []const u8,
        snippet: ?NotationSnippet,
    ) !void {
        const decl = self.declarations.items[decl_index];
        try self.notations.append(self.allocator, .{
            .decl_index = decl_index,
            .kind = kind,
            .token = token,
            .detail = try std.fmt.allocPrint(
                self.allocator,
                "{s} {s}",
                .{ kind.detailPrefix(), decl.name },
            ),
            .filter_text = try std.fmt.allocPrint(
                self.allocator,
                "{s} {s}",
                .{ token, decl.name },
            ),
            .alias_filter_text = try std.fmt.allocPrint(
                self.allocator,
                "{s} {s}",
                .{ decl.name, token },
            ),
            .alias_sort_text = try completionSortText(
                self.allocator,
                sort_group_notation_alias,
                decl.name_range.start,
                token,
            ),
            .token_sort_text = try completionSortText(
                self.allocator,
                sort_group_notation_token,
                decl.name_range.start,
                token,
            ),
            .snippet_label = if (snippet) |snp| snp.label else null,
            .snippet_text = if (snippet) |snp| snp.text else null,
            .snippet_filter_text = if (snippet) |snp|
                snp.filter_text
            else
                null,
            .snippet_alias_filter_text = if (snippet) |snp|
                try aliasFirstFilterText(
                    self.allocator,
                    snp.filter_text,
                    decl.name,
                )
            else
                null,
            .snippet_sort_text = if (snippet) |snp|
                try completionSortText(
                    self.allocator,
                    sort_group_notation_snippet,
                    decl.name_range.start,
                    snp.label,
                )
            else
                null,
        });
        try self.notation_by_token.put(
            self.allocator,
            token,
            decl_index,
        );
    }

    fn indexMm0Math(self: *Builder, text: []const u8) !void {
        var iter = StatementIterator.init(text);
        while (iter.next()) |stmt| {
            const decl_index = self.declIndexForStatement(text, stmt);
            var pos = stmt.start;
            while (nextMathStringIn(text, stmt.end, &pos)) |math| {
                try self.indexMathString(
                    .mm0,
                    math.text,
                    math.inner_start,
                    decl_index,
                    false,
                    null,
                );
            }
        }
    }

    fn declIndexForStatement(
        self: *Builder,
        text: []const u8,
        stmt: SourceSpan,
    ) ?usize {
        const header = statementHeader(text, stmt) orelse return null;
        if (header.name == null) return null;
        if (std.mem.eql(u8, header.keyword, "sort") or
            std.mem.eql(u8, header.keyword, "term") or
            std.mem.eql(u8, header.keyword, "def") or
            std.mem.eql(u8, header.keyword, "axiom") or
            std.mem.eql(u8, header.keyword, "theorem"))
        {
            return self.decl_by_name.get(header.name.?);
        }
        return null;
    }

    fn indexLemmaHeaderMath(
        self: *Builder,
        block: proof_script.ProofBlock,
        decl_index: usize,
        available_before: ?usize,
    ) !void {
        var pos: usize = 0;
        while (nextMathStringIn(
            block.header_tail,
            block.header_tail.len,
            &pos,
        )) |math| {
            try self.indexMathString(
                .proof,
                math.text,
                block.header_tail_span.start + math.inner_start,
                decl_index,
                false,
                available_before,
            );
        }
    }

    fn indexProofMathString(
        self: *Builder,
        block_index: usize,
        math: proof_script.MathString,
    ) !void {
        const block = self.proof_blocks.items[block_index];
        try self.indexMathString(
            .proof,
            math.text,
            math.span.start + 1,
            block.decl_index,
            true,
            block.global_available_before,
        );
    }

    fn indexRuleApplicationMath(
        self: *Builder,
        block_index: usize,
        app: proof_script.RuleApplication,
    ) !void {
        for (app.arg_bindings) |binding| {
            try self.indexProofMathString(block_index, binding.formula);
        }
    }

    fn indexMathString(
        self: *Builder,
        document: DocumentId,
        math: []const u8,
        base: usize,
        decl_index: ?usize,
        allow_sort_vars: bool,
        available_before: ?usize,
    ) !void {
        var cursor = MathTokenCursor{
            .src = math,
            .left_delims = self.left_delims,
            .right_delims = self.right_delims,
        };
        while (cursor.next()) |token| {
            if (token.text.len == 0) continue;
            const range = SourceRange{
                .document = document,
                .start = base + token.start,
                .end = base + token.end,
            };
            if (decl_index) |idx| {
                const decl = self.declarations.items[idx];
                if (findBinder(decl, token.text)) |binder| {
                    try self.addSymbol(.{
                        .source_range = range,
                        .target_range = binder.range orelse decl.name_range,
                        .markdown = try binderMarkdown(
                            self.allocator,
                            decl,
                            binder,
                        ),
                    });
                    continue;
                }
            }
            if (self.notation_by_token.get(token.text)) |idx| {
                const decl = self.declarations.items[idx];
                try self.addSymbol(.{
                    .source_range = range,
                    .target_range = targetRangeForUse(
                        decl,
                        document,
                        range.start,
                        available_before,
                    ),
                    .markdown = decl.markdown,
                });
                continue;
            }
            if (self.decl_by_name.get(token.text)) |idx| {
                const decl = self.declarations.items[idx];
                if (decl.kind == .term or decl.kind == .def) {
                    try self.addSymbol(.{
                        .source_range = range,
                        .target_range = targetRangeForUse(
                            decl,
                            document,
                            range.start,
                            available_before,
                        ),
                        .markdown = decl.markdown,
                    });
                    continue;
                }
            }
            if (allow_sort_vars) {
                if (self.sort_var_by_token.get(token.text)) |idx| {
                    const decl = self.declarations.items[idx];
                    try self.addSymbol(.{
                        .source_range = range,
                        .target_range = targetRangeForUse(
                            decl,
                            document,
                            range.start,
                            available_before,
                        ),
                        .markdown = decl.markdown,
                    });
                }
            }
        }
    }

    fn resolveRule(
        self: *const Builder,
        block_index: usize,
        name: []const u8,
        use_start: usize,
    ) ?RuleResolution {
        var best: ?ProofRuleDecl = null;
        for (self.proof_rules.items) |rule| {
            if (!std.mem.eql(u8, rule.name, name)) continue;
            if (rule.available_start > use_start) continue;
            if (best == null or rule.available_start > best.?.available_start) {
                best = rule;
            }
        }
        if (best) |rule| {
            return .{ .decl_index = rule.decl_index, .available = true };
        }
        return self.globalRuleResolution(block_index, name);
    }

    fn globalRuleResolution(
        self: *const Builder,
        block_index: usize,
        name: []const u8,
    ) ?RuleResolution {
        const decl_index = self.decl_by_name.get(name) orelse return null;
        const decl = self.declarations.items[decl_index];
        switch (decl.kind) {
            .axiom, .theorem => {},
            else => return null,
        }
        const bound = self.proof_blocks.items[block_index].global_available_before;
        const available = if (bound) |before|
            decl.name_range.start < before
        else
            true;
        return .{ .decl_index = decl_index, .available = available };
    }

    fn sortNameForId(self: *const Builder, id: u7) ?[]const u8 {
        const idx: usize = id;
        if (idx >= self.sort_names.items.len) return null;
        return self.sort_names.items[idx];
    }

    fn theoremDeclIndex(self: *const Builder, name: []const u8) ?usize {
        const decl_index = self.decl_by_name.get(name) orelse return null;
        const decl = self.declarations.items[decl_index];
        if (decl.kind != .theorem) return null;
        return decl_index;
    }

    fn sortDeclIndex(self: *const Builder, name: []const u8) ?usize {
        const decl_index = self.decl_by_name.get(name) orelse return null;
        const decl = self.declarations.items[decl_index];
        if (decl.kind != .sort) return null;
        return decl_index;
    }

    fn resolveLine(
        self: *const Builder,
        block_index: usize,
        label: []const u8,
        line_start: usize,
    ) ?usize {
        var best: ?ProofLineDecl = null;
        for (self.proof_lines.items) |line| {
            if (line.block_index != block_index) continue;
            if (!std.mem.eql(u8, line.name, label)) continue;
            if (line.line_start >= line_start) continue;
            if (best == null or line.line_start > best.?.line_start) {
                best = line;
            }
        }
        if (best) |line| return line.decl_index;
        return null;
    }
};

fn nextStatementRangeForMm0Stmt(
    iter: *StatementIterator,
    parsed: parse.MM0Stmt,
) SourceRange {
    const name_range = mm0StmtNameRange(parsed);
    while (iter.next()) |stmt| {
        if (stmt.start <= name_range.start and stmt.end >= name_range.end) {
            return .{
                .document = .mm0,
                .start = stmt.start,
                .end = stmt.end,
            };
        }
    }
    return name_range;
}

fn mm0StmtNameRange(stmt: parse.MM0Stmt) SourceRange {
    return switch (stmt) {
        .sort => |sort| mathSpanRange(sort.name_span),
        .term => |term| mathSpanRange(term.name_span),
        .assertion => |assertion| mathSpanRange(assertion.name_span),
    };
}

fn proofBlockDeclarationKind(kind: proof_script.BlockKind) DeclarationKind {
    return switch (kind) {
        .theorem => .theorem,
        .lemma => .lemma,
    };
}

fn mathSpanRange(span: parse.MathSpan) SourceRange {
    return .{
        .document = .mm0,
        .start = span.start,
        .end = span.end,
    };
}

fn proofSpanRange(span: proof_script.Span) SourceRange {
    return .{
        .document = .proof,
        .start = span.start,
        .end = span.end,
    };
}

fn rangeContains(range: SourceRange, document: DocumentId, offset: usize) bool {
    return range.document == document and offset >= range.start and
        offset < range.end;
}

fn targetRangeIfAvailable(decl: Declaration, use_start: usize) ?SourceRange {
    if (decl.name_range.start <= use_start) return decl.name_range;
    return null;
}

fn targetRangeForUse(
    decl: Declaration,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
) ?SourceRange {
    return switch (document) {
        .mm0 => targetRangeIfAvailable(decl, use_start),
        .proof => {
            const before = available_before orelse return decl.name_range;
            if (decl.name_range.start < before) return decl.name_range;
            return null;
        },
    };
}

fn isFatalIndexError(err: anyerror) bool {
    return switch (err) {
        error.OutOfMemory => true,
        else => false,
    };
}

fn findBinder(decl: Declaration, name: []const u8) ?BinderDecl {
    for (decl.binders) |binder| {
        if (std.mem.eql(u8, binder.name, name)) return binder;
    }
    return null;
}

fn bindersFromArgs(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = sourceRangeFromSlice(document, text, name),
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                name,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}

fn completionArgsFromArgs(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    for (args, 0..) |arg, i| {
        const name = if (i < names.len) names[i] else null;
        const label = if (name) |actual|
            actual
        else
            try std.fmt.allocPrint(allocator, "arg{d}", .{i + 1});
        try binders.append(allocator, .{
            .name = label,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = if (name) |actual|
                sourceRangeFromSlice(document, text, actual)
            else
                null,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                label,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}

fn bindersFromLemma(
    allocator: std.mem.Allocator,
    block: proof_script.ProofBlock,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    var search_start: usize = 0;
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        const maybe_rel = findIdentIn(block.header_tail, name, search_start);
        const range = if (maybe_rel) |rel| blk: {
            search_start = rel + name.len;
            break :blk SourceRange{
                .document = .proof,
                .start = block.header_tail_span.start + rel,
                .end = block.header_tail_span.start + rel + name.len,
            };
        } else null;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = range,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                name,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}
