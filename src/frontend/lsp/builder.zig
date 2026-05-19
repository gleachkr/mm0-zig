const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const model = @import("model.zig");
const completion = @import("completion.zig");
const notation = @import("notation.zig");
const support = @import("builder_support.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const OutlineSymbol = Types.OutlineSymbol;
const DeclarationKind = Types.DeclarationKind;
const Declaration = Types.Declaration;

const StatementIterator = source.StatementIterator;
const nextAnnotationToken = source.nextAnnotationToken;
const sourceRangeFromSlice = source.sourceRangeFromSlice;
const findIdentIn = source.findIdentIn;

const sortMarkdown = markdown.sortMarkdown;
const termMarkdown = markdown.termMarkdown;
const assertionMarkdown = markdown.assertionMarkdown;
const sortVarMarkdown = markdown.sortVarMarkdown;
const binderMarkdown = markdown.binderMarkdown;

const NavigationSymbol = model.NavigationSymbol;
const ProofBlockInfo = model.ProofBlockInfo;
const ProofRuleDecl = model.ProofRuleDecl;
const ProofLineDecl = model.ProofLineDecl;
const ProofApplicationInfo = model.ProofApplicationInfo;

const NotationCompletionDecl = notation.NotationCompletionDecl;

const completionSortText = completion.completionSortText;
const sortGroupForDeclaration = completion.sortGroupForDeclaration;

const nextStatementRangeForMm0Stmt = support.nextStatementRangeForMm0Stmt;
const mathSpanRange = support.mathSpanRange;
const proofSpanRange = support.proofSpanRange;
const proofMathTextSpan = support.proofMathTextSpan;
const targetRangeIfAvailable = support.targetRangeIfAvailable;
const isFatalIndexError = support.isFatalIndexError;
const hypothesesFromMm0Assertion = support.hypothesesFromMm0Assertion;
const bindersFromTerm = support.bindersFromTerm;
const bindersFromProofDef = support.bindersFromProofDef;
const bindersFromArgs = support.bindersFromArgs;
const completionArgsFromArgs = support.completionArgsFromArgs;
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

    const proof = @import("builder_proof.zig");
    const notation_builder = @import("builder_notation.zig");
    const math_builder = @import("builder_math.zig");

    pub const addProofBlock = proof.addProofBlock;
    pub const addTheoremBlockHeader = proof.addTheoremBlockHeader;
    pub const addLemmaBlockHeader = proof.addLemmaBlockHeader;
    pub const parseLemmaAssertion = proof.parseLemmaAssertion;
    pub const addProofLine = proof.addProofLine;
    pub const indexRuleApplication = proof.indexRuleApplication;
    pub const indexArgBindings = proof.indexArgBindings;
    pub const indexUnknownArgBindings = proof.indexUnknownArgBindings;
    pub const addHypRef = proof.addHypRef;
    pub const addLineRef = proof.addLineRef;
    pub const resolveRule = proof.resolveRule;
    pub const globalRuleResolution = proof.globalRuleResolution;
    pub const sortNameForId = proof.sortNameForId;
    pub const theoremDeclIndex = proof.theoremDeclIndex;
    pub const sortDeclIndex = proof.sortDeclIndex;
    pub const resolveLine = proof.resolveLine;

    pub const collectMm0Notation = notation_builder.collectMm0Notation;
    pub const collectDelimiterStatement =
        notation_builder.collectDelimiterStatement;
    pub const registerDelimiterMath = notation_builder.registerDelimiterMath;
    pub const collectGeneralNotation = notation_builder.collectGeneralNotation;
    pub const addNotationMathToken = notation_builder.addNotationMathToken;
    pub const addNotationToken = notation_builder.addNotationToken;

    pub const indexMm0Math = math_builder.indexMm0Math;
    pub const declIndexForStatement = math_builder.declIndexForStatement;
    pub const indexLemmaHeaderMath = math_builder.indexLemmaHeaderMath;
    pub const indexProofMathString = math_builder.indexProofMathString;
    pub const indexRuleApplicationMath = math_builder.indexRuleApplicationMath;
    pub const indexMathString = math_builder.indexMathString;

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
                    .hypotheses = try hypothesesFromMm0Assertion(
                        self.allocator,
                        text,
                        assertion,
                    ),
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

    pub fn addDeclaration(self: *Builder, decl_arg: Declaration) !usize {
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

    pub fn addDeclarationNameUse(
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

    pub fn addSymbol(self: *Builder, symbol: NavigationSymbol) !void {
        try self.symbols.append(self.allocator, symbol);
    }

    fn addMm0Outline(self: *Builder, symbol: OutlineSymbol) !void {
        try self.mm0_outline.append(self.allocator, symbol);
    }

    pub fn addProofOutline(self: *Builder, symbol: OutlineSymbol) !void {
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
};
