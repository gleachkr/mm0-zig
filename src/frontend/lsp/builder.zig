const std = @import("std");
const parse = @import("../../trusted/parse.zig");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const model = @import("model.zig");
const completion = @import("completion.zig");
const notation = @import("notation.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const OutlineSymbol = Types.OutlineSymbol;
const DeclarationKind = Types.DeclarationKind;
const BinderDecl = Types.BinderDecl;
const Declaration = Types.Declaration;

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

const NavigationSymbol = model.NavigationSymbol;
const ProofBlockInfo = model.ProofBlockInfo;
const ProofRuleDecl = model.ProofRuleDecl;
const ProofLineDecl = model.ProofLineDecl;
const ProofApplicationInfo = model.ProofApplicationInfo;
const RuleResolution = model.RuleResolution;

const NotationKind = notation.NotationKind;
const NotationCompletionDecl = notation.NotationCompletionDecl;
const NotationVariable = notation.NotationVariable;
const NotationPiece = notation.NotationPiece;
const NotationSnippet = notation.NotationSnippet;

const aliasFirstFilterText = notation.aliasFirstFilterText;
const buildGeneralNotationSnippet = notation.buildGeneralNotationSnippet;
const buildPrefixSnippet = notation.buildPrefixSnippet;
const collectNotationBinderVariables = notation.collectNotationBinderVariables;
const collectNotationPieces = notation.collectNotationPieces;
const completionSortText = completion.completionSortText;
const simpleNotationKind = notation.simpleNotationKind;
const sortGroupForDeclaration = completion.sortGroupForDeclaration;
const sort_group_local_binder = completion.sort_group_local_binder;
const sort_group_proof_lemma = completion.sort_group_proof_lemma;
const sort_group_proof_reference = completion.sort_group_proof_reference;
const sort_group_notation_alias = completion.sort_group_notation_alias;
const sort_group_notation_snippet = completion.sort_group_notation_snippet;
const sort_group_notation_token = completion.sort_group_notation_token;

pub const Builder = struct {
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

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .allocator = allocator };
    }

    pub fn indexMm0(self: *Builder, text: []const u8) !void {
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

    pub fn indexProof(self: *Builder, text: []const u8) !void {
        var parser = proof_script.Parser.init(self.allocator, text);
        var items = std.ArrayListUnmanaged(proof_script.TopLevelItem){};
        while (true) {
            const next = parser.nextItem() catch |err| {
                if (isFatalIndexError(err)) return err;
                if (!parser.recoverToNextItemBoundary()) break;
                continue;
            };
            const item = next orelse break;
            try items.append(self.allocator, item);
        }

        for (items.items, 0..) |item, i| {
            switch (item) {
                .block => |block| try self.addProofBlock(
                    block,
                    self.globalAvailabilityForProofItem(items.items, i),
                ),
                .def => |def| try self.addProofDefItem(text, def),
            }
        }
    }

    fn globalAvailabilityForProofItem(
        self: *const Builder,
        items: []const proof_script.TopLevelItem,
        index: usize,
    ) ?usize {
        const item = items[index];
        switch (item) {
            .block => |block| {
                if (block.kind == .theorem) {
                    return self.theoremAvailabilityBound(block.name);
                }
            },
            .def => {},
        }

        var i = index + 1;
        while (i < items.len) : (i += 1) {
            const block = switch (items[i]) {
                .block => |block| block,
                .def => continue,
            };
            if (block.kind != .theorem) continue;
            return self.theoremAvailabilityBound(block.name);
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
                    .binders = try bindersFromTerm(
                        self.allocator,
                        .mm0,
                        text,
                        term,
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

    fn addProofDefItem(
        self: *Builder,
        text: []const u8,
        def: proof_script.DefItem,
    ) !void {
        if (def.header_tail) |header_tail| {
            try self.addLocalProofDef(text, def, header_tail);
        } else {
            try self.addPublicDefBodyItem(def);
        }
    }

    fn addPublicDefBodyItem(
        self: *Builder,
        def: proof_script.DefItem,
    ) !void {
        const decl_index = self.decl_by_name.get(def.name) orelse return;
        const decl = self.declarations.items[decl_index];
        if (decl.kind != .def) return;

        try self.addProofOutline(.{
            .name = def.name,
            .kind = .def,
            .range = proofSpanRange(def.span),
            .selection_range = proofSpanRange(def.name_span),
        });
        try self.addSymbol(.{
            .source_range = proofSpanRange(def.name_span),
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
        try self.indexMathString(
            .proof,
            def.body.text,
            def.body.span.start + 1,
            decl_index,
            false,
            decl.name_range.start,
        );
    }

    fn addLocalProofDef(
        self: *Builder,
        text: []const u8,
        def: proof_script.DefItem,
        header_tail: []const u8,
    ) !void {
        var parser = self.mm0_parser orelse return;
        const term = parser.parseLocalDefText(
            def.name,
            .{ .start = def.name_span.start, .end = def.name_span.end },
            header_tail,
            def.body.text,
            proofMathTextSpan(def.body.span),
        ) catch |err| {
            if (isFatalIndexError(err)) return err;
            return;
        };
        self.mm0_parser = parser;

        const decl_index = try self.addDeclaration(.{
            .name = def.name,
            .kind = .def,
            .name_range = proofSpanRange(def.name_span),
            .markdown = try termMarkdown(
                self.allocator,
                text,
                term,
                def.annotations,
            ),
            .binders = try bindersFromProofDef(
                self.allocator,
                def,
                term,
            ),
            .completion_args = try completionArgsFromArgs(
                self.allocator,
                .proof,
                text,
                term.arg_names,
                term.args,
            ),
        });
        try self.addProofOutline(.{
            .name = def.name,
            .kind = .def,
            .range = proofSpanRange(def.span),
            .selection_range = proofSpanRange(def.name_span),
        });
        try self.indexProofDefHeaderSorts(def, term);
        try self.indexMathString(
            .proof,
            def.body.text,
            def.body.span.start + 1,
            decl_index,
            false,
            null,
        );
        try self.decl_by_name.put(self.allocator, def.name, decl_index);
    }

    fn indexProofDefHeaderSorts(
        self: *Builder,
        def: proof_script.DefItem,
        term: parse.TermStmt,
    ) !void {
        const header_tail = def.header_tail orelse return;
        var pos: usize = 0;
        for (term.args) |arg| {
            try self.addProofHeaderSortUse(header_tail, def, &pos, arg.sort_name);
        }
        for (term.dummy_args) |arg| {
            try self.addProofHeaderSortUse(header_tail, def, &pos, arg.sort_name);
        }
        try self.addProofHeaderSortUse(header_tail, def, &pos, term.ret_sort_name);
    }

    fn addProofHeaderSortUse(
        self: *Builder,
        header_tail: []const u8,
        def: proof_script.DefItem,
        pos: *usize,
        sort_name: []const u8,
    ) !void {
        const rel = findIdentIn(header_tail, sort_name, pos.*) orelse return;
        pos.* = rel + sort_name.len;
        const span = def.header_tail_span orelse return;
        const range = SourceRange{
            .document = .proof,
            .start = span.start + rel,
            .end = span.start + rel + sort_name.len,
        };
        const decl_index = self.sortDeclIndex(sort_name) orelse return;
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = range,
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
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

fn proofMathTextSpan(span: proof_script.Span) parse.MathSpan {
    return .{
        .start = @min(span.start + 1, span.end),
        .end = if (span.end > span.start) span.end - 1 else span.end,
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
            if (decl.name_range.document == .proof) {
                if (decl.name_range.start <= use_start) return decl.name_range;
                return null;
            }
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

fn bindersFromTerm(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    term: parse.TermStmt,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    try appendBindersFromArgs(
        allocator,
        &binders,
        document,
        text,
        term.arg_names,
        term.args,
        0,
    );
    try appendBindersFromArgs(
        allocator,
        &binders,
        document,
        text,
        term.dummy_names,
        term.dummy_args,
        term.args.len,
    );
    return try binders.toOwnedSlice(allocator);
}

fn appendBindersFromArgs(
    allocator: std.mem.Allocator,
    binders: *std.ArrayListUnmanaged(BinderDecl),
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    ordinal_base: usize,
) !void {
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
                ordinal_base + i,
                name,
            ),
        });
    }
}

const ScannedProofBinder = struct {
    name: []const u8,
    range: SourceRange,
    is_dummy: bool,
};

fn bindersFromProofDef(
    allocator: std.mem.Allocator,
    def: proof_script.DefItem,
    term: parse.TermStmt,
) ![]const BinderDecl {
    const header_tail = def.header_tail orelse return &.{};
    const header_span = def.header_tail_span orelse return &.{};
    const scanned = try scanProofDefBinders(
        allocator,
        header_tail,
        header_span.start,
    );

    var binders = std.ArrayListUnmanaged(BinderDecl){};
    var arg_index: usize = 0;
    var dummy_index: usize = 0;
    var ordinal: usize = 0;
    for (scanned) |item| {
        const arg = if (item.is_dummy) blk: {
            if (dummy_index >= term.dummy_args.len) continue;
            const arg = term.dummy_args[dummy_index];
            dummy_index += 1;
            break :blk arg;
        } else blk: {
            if (arg_index >= term.args.len) continue;
            const arg = term.args[arg_index];
            arg_index += 1;
            break :blk arg;
        };
        const maybe_name = if (item.is_dummy)
            term.dummy_names[dummy_index - 1]
        else
            term.arg_names[arg_index - 1];
        const name = maybe_name orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = item.range,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                ordinal,
                name,
            ),
        });
        ordinal += 1;
    }
    return try binders.toOwnedSlice(allocator);
}

fn scanProofDefBinders(
    allocator: std.mem.Allocator,
    header_tail: []const u8,
    base: usize,
) ![]const ScannedProofBinder {
    var result = std.ArrayListUnmanaged(ScannedProofBinder){};
    var pos: usize = 0;
    while (pos < header_tail.len) : (pos += 1) {
        const open = header_tail[pos];
        if (open != '(' and open != '{') continue;
        pos += 1;
        while (pos < header_tail.len) {
            skipProofDefHeaderSpace(header_tail, &pos);
            if (pos >= header_tail.len or header_tail[pos] == ':') break;
            const is_dummy = header_tail[pos] == '.';
            if (is_dummy) pos += 1;
            if (pos >= header_tail.len or !isProofIdentStart(header_tail[pos])) {
                break;
            }
            const start = pos;
            pos += 1;
            while (pos < header_tail.len and isProofIdentChar(header_tail[pos])) {
                pos += 1;
            }
            try result.append(allocator, .{
                .name = header_tail[start..pos],
                .range = .{
                    .document = .proof,
                    .start = base + start,
                    .end = base + pos,
                },
                .is_dummy = is_dummy,
            });
        }
    }
    return try result.toOwnedSlice(allocator);
}

fn skipProofDefHeaderSpace(text: []const u8, pos: *usize) void {
    while (pos.* < text.len) {
        switch (text[pos.*]) {
            ' ', '\t', '\r', '\n' => pos.* += 1,
            else => return,
        }
    }
}

fn isProofIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isProofIdentChar(ch: u8) bool {
    return isProofIdentStart(ch) or std.ascii.isDigit(ch);
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
