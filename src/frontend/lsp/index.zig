const std = @import("std");
const parse = @import("../../trusted/parse.zig");
const proof_script = @import("../proof_script.zig");

pub const DocumentId = enum {
    mm0,
    proof,
};

pub const SnapshotInput = struct {
    mm0_uri: []const u8,
    mm0_text: []const u8,
    proof_uri: ?[]const u8 = null,
    proof_text: ?[]const u8 = null,
};

pub const SourceRange = struct {
    document: DocumentId,
    start: usize,
    end: usize,
};

pub const DefinitionResult = struct {
    uri: []const u8,
    range: SourceRange,
    selection_range: SourceRange,
};

pub const HoverResult = struct {
    range: SourceRange,
    markdown: []const u8,
};

pub const DeclarationKind = enum {
    sort,
    term,
    def,
    axiom,
    theorem,
    lemma,
    proof_line,
    sort_var,

    fn label(self: DeclarationKind) []const u8 {
        return switch (self) {
            .sort => "sort",
            .term => "term",
            .def => "def",
            .axiom => "axiom",
            .theorem => "theorem",
            .lemma => "lemma",
            .proof_line => "proof line",
            .sort_var => "@vars token",
        };
    }
};

pub const BinderDecl = struct {
    name: []const u8,
    sort_name: []const u8,
    bound: bool,
    range: ?SourceRange = null,
};

pub const Declaration = struct {
    name: []const u8,
    kind: DeclarationKind,
    name_range: SourceRange,
    markdown: []const u8,
    binders: []const BinderDecl = &.{},
    hyp_count: usize = 0,
};

pub const Snapshot = struct {
    arena: std.heap.ArenaAllocator,
    mm0_uri: []const u8,
    mm0_text: []const u8,
    proof_uri: ?[]const u8,
    proof_text: ?[]const u8,
    declarations: []const Declaration,
    decl_by_name: std.StringHashMapUnmanaged(usize),
    symbols: []const NavigationSymbol,

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
};

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
};

const ProofLineDecl = struct {
    block_index: usize,
    name: []const u8,
    decl_index: usize,
    line_start: usize,
};

const RuleResolution = struct {
    decl_index: usize,
    available: bool,
};

const Token = struct {
    text: []const u8,
    start: usize,
    end: usize,
};

const Builder = struct {
    allocator: std.mem.Allocator,
    declarations: std.ArrayListUnmanaged(Declaration) = .{},
    decl_by_name: std.StringHashMapUnmanaged(usize) = .empty,
    symbols: std.ArrayListUnmanaged(NavigationSymbol) = .{},
    proof_blocks: std.ArrayListUnmanaged(ProofBlockInfo) = .{},
    proof_rules: std.ArrayListUnmanaged(ProofRuleDecl) = .{},
    proof_lines: std.ArrayListUnmanaged(ProofLineDecl) = .{},
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
        while (true) {
            const stmt = parser.next() catch |err| {
                if (isFatalIndexError(err)) return err;
                break;
            };
            const concrete = stmt orelse break;
            try self.addStatement(
                concrete,
                text,
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
                try self.addSortVarAnnotations(
                    sort,
                    annotations,
                    annotation_spans,
                );
            },
            .term => |term| {
                _ = try self.addGlobalDeclaration(.{
                    .name = term.name,
                    .kind = if (term.is_def) .def else .term,
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
                });
                try self.addArgSortUses(.mm0, text, term.args);
                try self.addSortUse(.mm0, text, term.ret_sort_name);
            },
            .assertion => |assertion| {
                _ = try self.addGlobalDeclaration(.{
                    .name = assertion.name,
                    .kind = switch (assertion.kind) {
                        .axiom => .axiom,
                        .theorem => .theorem,
                    },
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
                    .hyp_count = assertion.hyps.len,
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

    fn addDeclaration(self: *Builder, decl: Declaration) !usize {
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
        });
    }

    fn indexRuleApplication(
        self: *Builder,
        block_index: usize,
        app: proof_script.RuleApplication,
        line_start: usize,
    ) !void {
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
                try self.addDeclarationNameUse(text, name, decl_index);
                if (firstMathStringIn(text, stmt)) |math| {
                    try self.addNotationMathToken(decl_index, math);
                }
                continue;
            }
            if (!std.mem.eql(u8, header.keyword, "notation")) continue;
            const name = header.name orelse continue;
            const decl_index = self.decl_by_name.get(name) orelse continue;
            try self.addDeclarationNameUse(text, name, decl_index);
            const eq = findStatementByte(text, stmt, '=') orelse continue;
            var pos = eq + 1;
            while (nextMathStringIn(text, stmt.end, &pos)) |math| {
                try self.addNotationMathToken(decl_index, math);
            }
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

    fn addNotationMathToken(
        self: *Builder,
        decl_index: usize,
        math: MathStringSpan,
    ) !void {
        const trimmed = trimMathWhitespace(math.text);
        if (trimmed.len == 0) return;
        if (containsMathWhitespace(trimmed)) return;
        try self.notation_by_token.put(
            self.allocator,
            trimmed,
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

const SourceSpan = struct {
    start: usize,
    end: usize,
};

const MathStringSpan = struct {
    text: []const u8,
    inner_start: usize,
    inner_end: usize,
};

const StatementHeader = struct {
    keyword: []const u8,
    name: ?[]const u8 = null,
};

const StatementIterator = struct {
    text: []const u8,
    pos: usize = 0,

    fn init(text: []const u8) StatementIterator {
        return .{ .text = text };
    }

    fn next(self: *StatementIterator) ?SourceSpan {
        skipTopLevelSpaceAndComments(self.text, &self.pos, self.text.len);
        if (self.pos >= self.text.len) return null;

        const start = self.pos;
        while (self.pos < self.text.len) {
            if (self.text[self.pos] == '$') {
                skipMathString(self.text, &self.pos, self.text.len);
                continue;
            }
            if (startsLineComment(self.text, self.pos)) {
                skipLineComment(self.text, &self.pos, self.text.len);
                continue;
            }
            self.pos += 1;
            if (self.text[self.pos - 1] == ';') {
                return .{ .start = start, .end = self.pos };
            }
        }
        return .{ .start = start, .end = self.text.len };
    }
};

const HeaderToken = struct {
    text: []const u8,
    end: usize,
};

const MathTokenCursor = struct {
    src: []const u8,
    pos: usize = 0,
    left_delims: [256]bool,
    right_delims: [256]bool,

    fn next(self: *MathTokenCursor) ?Token {
        while (self.pos < self.src.len and
            isMathWhitespace(self.src[self.pos]))
        {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) return null;

        const start = self.pos;
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            self.pos += 1;
            if (self.left_delims[ch]) break;
            if (self.pos >= self.src.len) break;
            const next_ch = self.src[self.pos];
            if (isMathWhitespace(next_ch) or self.right_delims[next_ch]) {
                break;
            }
        }
        return .{
            .text = self.src[start..self.pos],
            .start = start,
            .end = self.pos,
        };
    }
};

fn nextAnnotationToken(text: []const u8, pos: *usize) ?Token {
    while (pos.* < text.len and isMathWhitespace(text[pos.*])) {
        pos.* += 1;
    }
    if (pos.* >= text.len) return null;

    const start = pos.*;
    while (pos.* < text.len and !isMathWhitespace(text[pos.*])) {
        pos.* += 1;
    }
    return .{
        .text = text[start..pos.*],
        .start = start,
        .end = pos.*,
    };
}

fn statementHeader(text: []const u8, stmt: SourceSpan) ?StatementHeader {
    var pos = stmt.start;
    while (true) {
        const token = nextHeaderIdent(text, &pos, stmt.end) orelse return null;
        if (std.mem.eql(u8, token.text, "pub")) continue;
        if (std.mem.eql(u8, token.text, "pure") or
            std.mem.eql(u8, token.text, "strict") or
            std.mem.eql(u8, token.text, "provable") or
            std.mem.eql(u8, token.text, "free"))
        {
            continue;
        }
        if (std.mem.eql(u8, token.text, "sort") or
            std.mem.eql(u8, token.text, "term") or
            std.mem.eql(u8, token.text, "def") or
            std.mem.eql(u8, token.text, "axiom") or
            std.mem.eql(u8, token.text, "theorem") or
            std.mem.eql(u8, token.text, "prefix") or
            std.mem.eql(u8, token.text, "infixl") or
            std.mem.eql(u8, token.text, "infixr"))
        {
            const name = nextHeaderIdent(text, &pos, stmt.end) orelse {
                return .{ .keyword = token.text };
            };
            return .{ .keyword = token.text, .name = name.text };
        }
        if (std.mem.eql(u8, token.text, "notation")) {
            skipTopLevelSpaceAndComments(text, &pos, stmt.end);
            if (pos < stmt.end and text[pos] == '"') {
                return .{ .keyword = token.text };
            }
            const name = nextHeaderIdent(text, &pos, stmt.end) orelse {
                return .{ .keyword = token.text };
            };
            return .{ .keyword = token.text, .name = name.text };
        }
        return .{ .keyword = token.text };
    }
}

fn nextHeaderIdent(
    text: []const u8,
    pos: *usize,
    end: usize,
) ?HeaderToken {
    skipTopLevelSpaceAndComments(text, pos, end);
    if (pos.* >= end or !isIdentStart(text[pos.*])) return null;
    const start = pos.*;
    pos.* += 1;
    while (pos.* < end and isIdentChar(text[pos.*])) pos.* += 1;
    return .{ .text = text[start..pos.*], .end = pos.* };
}

fn skipTopLevelSpaceAndComments(
    text: []const u8,
    pos: *usize,
    end: usize,
) void {
    while (pos.* < end) {
        if (isMathWhitespace(text[pos.*])) {
            pos.* += 1;
            continue;
        }
        if (startsLineComment(text, pos.*)) {
            skipLineComment(text, pos, end);
            continue;
        }
        break;
    }
}

fn skipLineComment(text: []const u8, pos: *usize, end: usize) void {
    pos.* += 2;
    while (pos.* < end and text[pos.*] != '\n') pos.* += 1;
}

fn startsLineComment(text: []const u8, pos: usize) bool {
    return pos + 1 < text.len and text[pos] == '-' and text[pos + 1] == '-';
}

fn skipMathString(text: []const u8, pos: *usize, end: usize) void {
    pos.* += 1;
    while (pos.* < end and text[pos.*] != '$') pos.* += 1;
    if (pos.* < end) pos.* += 1;
}

fn firstMathStringIn(text: []const u8, stmt: SourceSpan) ?MathStringSpan {
    var pos = stmt.start;
    return nextMathStringIn(text, stmt.end, &pos);
}

fn nextMathStringIn(
    text: []const u8,
    end: usize,
    pos: *usize,
) ?MathStringSpan {
    while (pos.* < end) {
        if (startsLineComment(text, pos.*)) {
            skipLineComment(text, pos, end);
            continue;
        }
        if (text[pos.*] != '$') {
            pos.* += 1;
            continue;
        }
        pos.* += 1;
        const inner_start = pos.*;
        while (pos.* < end and text[pos.*] != '$') pos.* += 1;
        if (pos.* >= end) return null;
        const inner_end = pos.*;
        pos.* += 1;
        return .{
            .text = text[inner_start..inner_end],
            .inner_start = inner_start,
            .inner_end = inner_end,
        };
    }
    return null;
}

fn findStatementByte(
    text: []const u8,
    stmt: SourceSpan,
    needle: u8,
) ?usize {
    var pos = stmt.start;
    while (pos < stmt.end) {
        if (text[pos] == '$') {
            skipMathString(text, &pos, stmt.end);
            continue;
        }
        if (startsLineComment(text, pos)) {
            skipLineComment(text, &pos, stmt.end);
            continue;
        }
        if (text[pos] == needle) return pos;
        pos += 1;
    }
    return null;
}

fn trimMathWhitespace(text: []const u8) []const u8 {
    return std.mem.trim(u8, text, " \n\t\r");
}

fn containsMathWhitespace(text: []const u8) bool {
    for (text) |ch| {
        if (isMathWhitespace(ch)) return true;
    }
    return false;
}

fn isMathWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\n' or ch == '\t' or ch == '\r';
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

fn sortMarkdown(
    allocator: std.mem.Allocator,
    sort: parse.SortStmt,
    annotations: []const []const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.writeAll("```mm0\n");
    try writeSortModifiers(&writer, sort.modifiers);
    try writer.print("sort {s};\n```", .{sort.name});
    try writer.print("\n\nSort `{s}`.", .{sort.name});
    try writeMetadataSummary(&writer, annotations);
    return try buf.toOwnedSlice(allocator);
}

fn termMarkdown(
    allocator: std.mem.Allocator,
    text: []const u8,
    term: parse.TermStmt,
    annotations: []const []const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.print("{s} `{s}`, returns `{s}`.\n\n", .{
        if (term.is_def) "Definition" else "Term",
        term.name,
        term.ret_sort_name,
    });
    try writer.writeAll("```mm0\n");
    try writeSignatureAnnotations(&writer, annotations);
    try writer.print("{s} {s}", .{
        if (term.is_def) "def" else "term",
        term.name,
    });
    try writeCompactArgList(&writer, term.arg_names, term.args);
    try writer.print(": {s}", .{term.ret_sort_name});
    if (term.is_def) {
        if (definitionBodySource(text, term.name_span)) |body| {
            try writer.writeAll(" =\n");
            try writeMathLine(&writer, "  ", body);
        } else {
            try writer.writeAll(" = …");
        }
    }
    try writer.writeAll(";\n```");
    try writeMetadataSummary(&writer, annotations);
    return try buf.toOwnedSlice(allocator);
}

fn assertionMarkdown(
    allocator: std.mem.Allocator,
    text: []const u8,
    assertion: parse.AssertionStmt,
    concl_sort_name: ?[]const u8,
    annotations: []const []const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    const kind: DeclarationKind = switch (assertion.kind) {
        .axiom => .axiom,
        .theorem => .theorem,
    };
    try writer.print("{s} `{s}`: {d} {s}", .{
        declarationTitle(kind),
        assertion.name,
        assertion.hyps.len,
        if (assertion.hyps.len == 1) "hypothesis" else "hypotheses",
    });
    if (concl_sort_name) |sort_name| {
        try writer.print(", conclusion sort `{s}`", .{sort_name});
    }
    try writer.writeAll(".");
    if (assertion.is_local) try writer.writeAll(" Local assertion.");
    try writer.writeAll("\n\n```mm0\n");
    try writeSignatureAnnotations(&writer, annotations);
    try writer.print("{s} {s}", .{ kind.label(), assertion.name });
    try writeCompactArgList(&writer, assertion.arg_names, assertion.args);
    try writer.writeAll(":\n");

    const math_strings = try assertionMathSources(
        allocator,
        text,
        assertion.name_span,
    );
    const expected = assertion.hyps.len + 1;
    if (math_strings.len >= expected) {
        for (math_strings[0..assertion.hyps.len]) |hyp| {
            try writeMathLine(&writer, "  ", hyp);
            try writer.writeAll(" >\n");
        }
        try writeMathLine(&writer, "  ", math_strings[assertion.hyps.len]);
        try writer.writeAll(";\n```");
    } else {
        try writer.writeAll("  …;\n```");
    }
    try writeMetadataSummary(&writer, annotations);
    return try buf.toOwnedSlice(allocator);
}

fn lemmaMarkdown(
    allocator: std.mem.Allocator,
    block: proof_script.ProofBlock,
    hyp_count: usize,
    hyp_count_known: bool,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.writeAll("```auf\n");
    try writer.print("lemma {s}", .{block.name});
    if (block.header_tail.len != 0) {
        try writer.print(" {s}", .{block.header_tail});
    }
    try writer.writeAll("\n```");
    try writer.print("\n\nLocal lemma `{s}`.", .{block.name});
    if (hyp_count_known) {
        try writer.print(" {d} {s}.", .{
            hyp_count,
            if (hyp_count == 1) "hypothesis" else "hypotheses",
        });
    }
    return try buf.toOwnedSlice(allocator);
}

fn proofLineMarkdown(
    allocator: std.mem.Allocator,
    line: proof_script.ProofLine,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.writeAll("```auf\n");
    try writer.print("{s}: ${s}$\n```", .{
        line.label,
        line.assertion.text,
    });
    try writer.print("\n\nProof line `{s}`.", .{line.label});
    return try buf.toOwnedSlice(allocator);
}

fn hypRefMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_index: usize,
    hyp_count: usize,
    hyp_count_known: bool,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.print("hypothesis #{d} of `{s}`.", .{ hyp_index, block_name });
    if (hyp_count_known) {
        try writer.print("\n\n{d} of {d} hypotheses.", .{
            hyp_index,
            hyp_count,
        });
    }
    return try buf.toOwnedSlice(allocator);
}

fn sortVarMarkdown(
    allocator: std.mem.Allocator,
    token: []const u8,
    sort_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "Theorem-local dummy `{s}` from the `@vars` pool.\n\n" ++
            "Sort: `{s}`. Available in proof-body math.",
        .{ token, sort_name },
    );
}

fn binderMarkdown(
    allocator: std.mem.Allocator,
    decl: Declaration,
    binder: BinderDecl,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "Binder `{s}` for {s} `{s}`.\n\n" ++
            "Expected sort: `{s}`. {s} variable.",
        .{
            binder.name,
            decl.kind.label(),
            decl.name,
            binder.sort_name,
            if (binder.bound) "Bound" else "Free",
        },
    );
}

fn unknownRuleMarkdown(
    allocator: std.mem.Allocator,
    name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "unknown rule `{s}`", .{name});
}

fn unknownLineMarkdown(
    allocator: std.mem.Allocator,
    label: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "unknown line `{s}`", .{label});
}

fn unknownHypMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_index: usize,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "unknown hypothesis #{d} of `{s}`",
        .{ hyp_index, block_name },
    );
}

fn unknownBindingMarkdown(
    allocator: std.mem.Allocator,
    binder_name: []const u8,
    rule_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "unknown binder `{s}` for rule `{s}`",
        .{ binder_name, rule_name },
    );
}

fn unresolvedBindingMarkdown(
    allocator: std.mem.Allocator,
    binder_name: []const u8,
    rule_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "binder `{s}` for unresolved rule `{s}`",
        .{ binder_name, rule_name },
    );
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
        });
    }
    return try binders.toOwnedSlice(allocator);
}

fn sourceRangeFromSlice(
    document: DocumentId,
    text: []const u8,
    slice: []const u8,
) ?SourceRange {
    if (slice.len == 0) return null;
    const base = @intFromPtr(text.ptr);
    const ptr = @intFromPtr(slice.ptr);
    if (ptr < base) return null;
    const offset = ptr - base;
    if (offset + slice.len > text.len) return null;
    return .{
        .document = document,
        .start = offset,
        .end = offset + slice.len,
    };
}

fn findIdentIn(
    text: []const u8,
    needle: []const u8,
    start: usize,
) ?usize {
    var pos = @min(start, text.len);
    while (pos <= text.len) {
        const rel = std.mem.indexOf(u8, text[pos..], needle) orelse return null;
        const found = pos + rel;
        const before_ok = found == 0 or !isIdentChar(text[found - 1]);
        const end = found + needle.len;
        const after_ok = end >= text.len or !isIdentChar(text[end]);
        if (before_ok and after_ok) return found;
        pos = found + needle.len;
    }
    return null;
}

fn writeSortModifiers(writer: anytype, modifiers: anytype) !void {
    if (modifiers.strict) try writer.writeAll("strict ");
    if (modifiers.provable) try writer.writeAll("provable ");
    if (modifiers.pure) try writer.writeAll("pure ");
    if (modifiers.free) try writer.writeAll("free ");
}

fn writeMetadataSummary(
    writer: anytype,
    annotations: []const []const u8,
) !void {
    var wrote_header = false;
    for (annotations) |annotation| {
        const directive = annotationDirective(annotation) orelse continue;
        if (!isSelectedMetadataDirective(directive)) continue;
        if (!wrote_header) {
            try writer.writeAll("\n\nMetadata:");
            wrote_header = true;
        }
        try writer.print(" `{s}`", .{directive});
    }
    if (wrote_header) try writer.writeAll(".");
}

fn annotationDirective(annotation: []const u8) ?[]const u8 {
    var it = std.mem.tokenizeAny(u8, annotation, " \t\r\n");
    return it.next();
}

fn isSelectedMetadataDirective(directive: []const u8) bool {
    const selected = [_][]const u8{
        "@relation",
        "@rewrite",
        "@congr",
        "@acui",
        "@view",
        "@recover",
        "@abstract",
        "@fresh",
        "@freshen",
        "@vars",
        "@hole",
        "@fallback",
    };
    for (selected) |tag| {
        if (std.mem.eql(u8, directive, tag)) return true;
    }
    return false;
}

fn declarationTitle(kind: DeclarationKind) []const u8 {
    return switch (kind) {
        .sort => "Sort",
        .term => "Term",
        .def => "Definition",
        .axiom => "Axiom",
        .theorem => "Theorem",
        .lemma => "Local lemma",
        .proof_line => "Proof line",
        .sort_var => "Theorem-local dummy",
    };
}

fn writeSignatureAnnotations(
    writer: anytype,
    annotations: []const []const u8,
) !void {
    for (annotations) |annotation| {
        const directive = annotationDirective(annotation) orelse continue;
        if (!std.mem.eql(u8, directive, "@view")) continue;
        try writer.print("--| {s}\n", .{annotation});
    }
}

fn definitionBodySource(
    text: []const u8,
    name_span: parse.MathSpan,
) ?[]const u8 {
    const stmt = statementSpanForName(text, name_span) orelse return null;
    const eq = findStatementByte(text, stmt, '=') orelse return null;
    var pos = eq + 1;
    const math = nextMathStringIn(text, stmt.end, &pos) orelse return null;
    return math.text;
}

fn assertionMathSources(
    allocator: std.mem.Allocator,
    text: []const u8,
    name_span: parse.MathSpan,
) ![]const []const u8 {
    const stmt = statementSpanForName(text, name_span) orelse return &.{};
    const end = findStatementByte(text, stmt, '=') orelse stmt.end;
    var pos = stmt.start;
    var result = std.ArrayListUnmanaged([]const u8){};
    while (nextMathStringIn(text, end, &pos)) |math| {
        try result.append(allocator, math.text);
    }
    return try result.toOwnedSlice(allocator);
}

fn statementSpanForName(
    text: []const u8,
    name_span: parse.MathSpan,
) ?SourceSpan {
    var iter = StatementIterator.init(text);
    while (iter.next()) |stmt| {
        if (name_span.start >= stmt.start and name_span.end <= stmt.end) {
            return stmt;
        }
    }
    return null;
}

fn writeMathLine(
    writer: anytype,
    indent: []const u8,
    math: []const u8,
) !void {
    const trimmed = trimMathWhitespace(math);
    try writer.print("{s}$ ", .{indent});
    var pos: usize = 0;
    while (pos < trimmed.len) {
        const nl = std.mem.indexOfScalar(u8, trimmed[pos..], '\n');
        const line_end = if (nl) |rel| pos + rel else trimmed.len;
        if (pos != 0) try writer.print("\n{s}  ", .{indent});
        try writer.writeAll(std.mem.trim(u8, trimmed[pos..line_end], " \t\r"));
        if (nl == null) break;
        pos = line_end + 1;
    }
    try writer.writeAll(" $");
}

fn writeCompactArgList(
    writer: anytype,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) !void {
    var i: usize = 0;
    while (i < args.len) {
        var end = i + 1;
        while (end < args.len and canGroupArgs(names, args, i, end)) {
            end += 1;
        }
        try writeArgGroup(writer, names, args, i, end);
        i = end;
    }
}

fn canGroupArgs(
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    first: usize,
    next: usize,
) bool {
    if (first >= names.len or next >= names.len) return false;
    if (names[first] == null or names[next] == null) return false;
    const a = args[first];
    const b = args[next];
    if (a.bound != b.bound) return false;
    if (!std.mem.eql(u8, a.sort_name, b.sort_name)) return false;
    if (a.bound) return true;
    return a.deps == b.deps;
}

fn writeArgGroup(
    writer: anytype,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    start: usize,
    end: usize,
) !void {
    const arg = args[start];
    const open: u8 = if (arg.bound) '{' else '(';
    const close: u8 = if (arg.bound) '}' else ')';
    try writer.print(" {c}", .{open});
    for (start..end) |idx| {
        if (idx != start) try writer.writeAll(" ");
        if (idx < names.len) {
            if (names[idx]) |name| {
                try writer.writeAll(name);
            } else {
                try writer.writeAll("_");
            }
        } else {
            try writer.writeAll("_");
        }
    }
    try writer.print(": {s}", .{arg.sort_name});
    if (!arg.bound) {
        try writeDeps(writer, arg.deps, names, args, start);
    }
    try writer.print("{c}", .{close});
}

fn writeDeps(
    writer: anytype,
    deps: u55,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    before: usize,
) !void {
    if (deps == 0) return;
    var bound_slot: usize = 0;
    var idx: usize = 0;
    while (idx < before) : (idx += 1) {
        if (!args[idx].bound) continue;
        const bit = @as(u55, 1) << @intCast(bound_slot);
        bound_slot += 1;
        if ((deps & bit) == 0) continue;
        if (idx >= names.len) continue;
        const name = names[idx] orelse continue;
        try writer.print(" {s}", .{name});
    }
}

fn tokenAt(text: []const u8, offset: usize) ?Token {
    if (offset >= text.len) return null;
    if (!isIdentChar(text[offset])) return null;

    var start = offset;
    while (start > 0 and isIdentChar(text[start - 1])) start -= 1;
    if (!isIdentStart(text[start])) return null;

    var end = offset + 1;
    while (end < text.len and isIdentChar(text[end])) end += 1;

    return .{
        .text = text[start..end],
        .start = start,
        .end = end,
    };
}

fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}

test "snapshot build propagates allocation failure" {
    var buffer: [1]u8 = undefined;
    var fixed = std.heap.FixedBufferAllocator.init(&buffer);
    try std.testing.expectError(error.OutOfMemory, Snapshot.build(
        fixed.allocator(),
        .{
            .mm0_uri = "file:///test.mm0",
            .mm0_text = "provable sort wff;",
        },
    ));
}

test "malformed sources still index parsed prefixes" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\not a valid statement
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\bad_block
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.indexOf(u8, proof_text, "top_i") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingPrefixDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "top_i",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "snapshot indexes global mm0 declarations" {
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
        \\theorem imp_refl (a: wff): $ imp a a $;
        ,
    });
    defer snapshot.deinit();

    try std.testing.expectEqual(@as(usize, 4), snapshot.declarations.len);
    try std.testing.expect(snapshot.decl_by_name.contains("wff"));
    try std.testing.expect(snapshot.decl_by_name.contains("imp"));
    try std.testing.expect(snapshot.decl_by_name.contains("ax_mp"));
    try std.testing.expect(snapshot.decl_by_name.contains("imp_refl"));
}

test "definition lookup resolves declaration and simple global use" {
    const text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\theorem imp_refl (a: wff): $ imp a a $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const decl_offset =
        (std.mem.indexOf(u8, text, "imp") orelse unreachable) + 1;
    const decl_def = snapshot.definitionAt(.mm0, decl_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", decl_def.uri);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[decl_def.range.start..decl_def.range.end],
    );

    const use_offset =
        (std.mem.lastIndexOf(u8, text, "imp") orelse unreachable) + 1;
    const use_def = snapshot.definitionAt(.mm0, use_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(decl_def.range.start, use_def.range.start);
    try std.testing.expectEqual(decl_def.range.end, use_def.range.end);
}

test "hover returns markdown and source token range" {
    const text =
        \\provable sort wff;
        \\term top: wff;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, text, "top") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[hover.range.start..hover.range.end],
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term top",
    ));
}

test "global hover shows definition bodies and assertion formulas" {
    const text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\def id (a: wff): wff = $ a -> a $;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const def_offset =
        (std.mem.indexOf(u8, text, "id") orelse unreachable) + 1;
    const def_hover = snapshot.hoverAt(.mm0, def_offset) orelse {
        return error.MissingDefinitionHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        def_hover.markdown,
        1,
        "$ a -> a $",
    ));
    try std.testing.expect(!std.mem.containsAtLeast(
        u8,
        def_hover.markdown,
        1,
        "Binders:",
    ));

    const ax_offset =
        (std.mem.indexOf(u8, text, "axiom mp") orelse unreachable) +
        "axiom ".len + 1;
    const ax_hover = snapshot.hoverAt(.mm0, ax_offset) orelse {
        return error.MissingAssertionHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "2 hypotheses, conclusion sort `wff`",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "axiom mp (a b: wff):",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "$ a -> b $ >",
    ));
}

test "global hover renders dependency masks as bound names" {
    const text =
        \\sort ctx;
        \\sort tm;
        \\sort ty;
        \\provable sort jdg;
        \\term ok: jdg;
        \\axiom dep_rule (g: ctx) {k ih: tm} (C: ty k)
        \\  (s: tm k ih): $ ok $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, text, "dep_rule") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingDependencyHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "(C: ty k)",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "(s: tm k ih)",
    ));
}

test "sort references in signatures resolve explicitly" {
    const text =
        \\provable sort wff;
        \\term top: wff;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, text, "wff") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingSortDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "wff",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingSortHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Sort `wff`.",
    ));
}

test "comments do not produce global hovers" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\-- top should not be a hover target here
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, text, "top") orelse unreachable) + 1;
    try std.testing.expect(snapshot.hoverAt(.mm0, offset) == null);
    try std.testing.expect(snapshot.definitionAt(.mm0, offset) == null);
}

test "proof block header resolves to matching theorem" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "main") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "main",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "proof block header ignores non-theorem globals" {
    const mm0_text =
        \\provable sort wff;
        \\term main: wff;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ main $ by main []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "main") orelse unreachable) + 1;
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
    try std.testing.expect(snapshot.hoverAt(.proof, offset) == null);
}

test "proof rule applications ignore non-rule globals" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, proof_text, "top") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingUnknownRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "unknown rule `top`",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
}

test "forward global proof rules hover but do not define" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
        \\axiom later: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by later []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "later") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingForwardRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "axiom later",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
}

test "current theorem is not available as a proof rule" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by main []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, proof_text, "main") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingSelfRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "theorem main",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
}

test "proof rule and line references resolve" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by keep [l1]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "keep") orelse unreachable) + 1;
    const rule_def = snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingRuleDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", rule_def.uri);
    try std.testing.expectEqualStrings(
        "keep",
        snapshot.mm0_text[rule_def.range.start..rule_def.range.end],
    );

    const ref_offset =
        (std.mem.lastIndexOf(u8, proof_text, "l1") orelse unreachable) + 1;
    const ref_def = snapshot.definitionAt(.proof, ref_offset) orelse {
        return error.MissingLineDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.auf", ref_def.uri);
    try std.testing.expectEqualStrings(
        "l1",
        snapshot.proof_text.?[ref_def.range.start..ref_def.range.end],
    );
}

test "local lemma rule resolves in later proof block" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\lemma helper: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
        \\
        \\main
        \\----
        \\l1: $ top $ by helper []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "helper") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.auf", def.uri);
    const decl_start = std.mem.indexOf(u8, proof_text, "helper") orelse {
        return error.MissingLemmaHeader;
    };
    try std.testing.expectEqual(decl_start, def.range.start);
}

test "hypothesis references hover and jump to owning rule" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $ > $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [#1]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "#1") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "hypothesis #1",
    ));
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "main",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "unresolved proof symbols still hover" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by missing [future, #1]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.indexOf(u8, proof_text, "missing") orelse unreachable) + 1;
    const rule_hover = snapshot.hoverAt(.proof, rule_offset) orelse {
        return error.MissingRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        rule_hover.markdown,
        1,
        "unknown rule `missing`",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, rule_offset) == null);

    const line_offset =
        (std.mem.indexOf(u8, proof_text, "future") orelse unreachable) + 1;
    const line_hover = snapshot.hoverAt(.proof, line_offset) orelse {
        return error.MissingLineHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        line_hover.markdown,
        1,
        "unknown line `future`",
    ));

    const hyp_offset =
        (std.mem.indexOf(u8, proof_text, "#1") orelse unreachable) + 1;
    const hyp_hover = snapshot.hoverAt(.proof, hyp_offset) orelse {
        return error.MissingHypHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hyp_hover.markdown,
        1,
        "unknown hypothesis #1",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, hyp_offset) == null);
}

test "explicit proof bindings resolve to rule binders" {
    const mm0_text =
        \\sort obj;
        \\provable sort wff;
        \\axiom use {x: obj} (p: wff x): $ p $;
        \\theorem main {x: obj} (p: wff x): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (x := $ x $, p := $ p $)
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const binding_offset =
        (std.mem.indexOf(u8, proof_text, "x :=") orelse unreachable);
    const hover = snapshot.hoverAt(.proof, binding_offset) orelse {
        return error.MissingBindingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Expected sort: `obj`. Bound variable.",
    ));

    const def = snapshot.definitionAt(.proof, binding_offset) orelse {
        return error.MissingBindingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const free_offset =
        (std.mem.indexOf(u8, proof_text, "p :=") orelse unreachable);
    const free_hover = snapshot.hoverAt(.proof, free_offset) orelse {
        return error.MissingFreeBindingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        free_hover.markdown,
        1,
        "Expected sort: `wff`. Free variable.",
    ));
}

test "math notation tokens resolve to defining terms" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, mm0_text, "->") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingNotationDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingNotationHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term imp",
    ));
}

test "general notation tokens resolve to defining terms" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\notation top: wff = ($⊤$:max);
        \\theorem main: $ ⊤ $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, mm0_text, "⊤") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingGeneralNotationDefinition;
    };
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "proof math term definitions use mm0 declaration scope" {
    const mm0_text =
        \\-- padding keeps the mm0 declaration after the proof token offset
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const proof_top = std.mem.indexOf(u8, proof_text, "$ top $") orelse {
        return error.MissingProofMath;
    };
    const offset = proof_top + 2;
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingProofTermDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "proof math notation definitions use mm0 declaration scope" {
    const mm0_text =
        \\-- padding keeps the mm0 declaration after the proof token offset
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax (p q: wff): $ p -> q $;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p -> q $ by ax []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "->") orelse {
        return error.MissingProofNotation;
    };
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingProofNotationDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "forward proof math globals hover without definition" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\term later: wff;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ later $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const proof_later = std.mem.indexOf(u8, proof_text, "later") orelse {
        return error.MissingForwardProofMath;
    };
    const hover = snapshot.hoverAt(.proof, proof_later) orelse {
        return error.MissingForwardProofMathHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term later",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, proof_later) == null);
}

test "proof math binder references resolve to theorem binders" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (p := $ p $) []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const line_assertion = std.mem.indexOf(u8, proof_text, "$ p $") orelse {
        return error.MissingProofMath;
    };
    const offset = line_assertion + 2;
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingBinderDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "p",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingBinderHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Expected sort: `wff`. Free variable.",
    ));
}

test "proof @vars dummies hover and jump to pool token" {
    const mm0_text =
        \\provable sort wff;
        \\--| @vars x y
        \\sort obj;
        \\term eq (a b: obj): wff;
        \\axiom eq_refl (a: obj): $ eq a a $;
        \\theorem main (t: obj): $ eq t t $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ eq x x $ by eq_refl []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const proof_token =
        std.mem.indexOf(u8, proof_text, "x x") orelse unreachable;
    const hover = snapshot.hoverAt(.proof, proof_token) orelse {
        return error.MissingVarsHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Theorem-local dummy `x`",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Sort: `obj`",
    ));

    const def = snapshot.definitionAt(.proof, proof_token) orelse {
        return error.MissingVarsDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    const vars_token = std.mem.indexOf(u8, mm0_text, "x y") orelse {
        return error.MissingVarsAnnotation;
    };
    try std.testing.expectEqual(vars_token, def.range.start);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const decl_hover = snapshot.hoverAt(.mm0, vars_token) orelse {
        return error.MissingVarsDeclHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        decl_hover.markdown,
        1,
        "Available in proof-body math.",
    ));
}

test "global hover includes selected metadata summaries" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\--| @rewrite
        \\axiom top_i: $ top $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, mm0_text, "top_i") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingMetadataHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Metadata: `@rewrite`.",
    ));
}
