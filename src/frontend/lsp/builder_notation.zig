const std = @import("std");

const source = @import("source.zig");
const notation = @import("notation.zig");
const completion = @import("completion.zig");

const SourceSpan = source.SourceSpan;
const MathStringSpan = source.MathStringSpan;
const StatementIterator = source.StatementIterator;
const statementHeader = source.statementHeader;
const firstMathStringIn = source.firstMathStringIn;
const nextMathStringIn = source.nextMathStringIn;
const findStatementByte = source.findStatementByte;
const trimMathWhitespace = source.trimMathWhitespace;
const containsMathWhitespace = source.containsMathWhitespace;
const isMathWhitespace = source.isMathWhitespace;

const NotationKind = notation.NotationKind;
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
const sort_group_notation_alias = completion.sort_group_notation_alias;
const sort_group_notation_snippet = completion.sort_group_notation_snippet;
const sort_group_notation_token = completion.sort_group_notation_token;

pub fn collectMm0Notation(self: anytype, text: []const u8) !void {
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

pub fn collectDelimiterStatement(
    self: anytype,
    text: []const u8,
    stmt: SourceSpan,
) void {
    var pos = stmt.start;
    while (nextMathStringIn(text, stmt.end, &pos)) |math| {
        self.registerDelimiterMath(math.text);
    }
}

pub fn registerDelimiterMath(self: anytype, math: []const u8) void {
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

pub fn collectGeneralNotation(
    self: anytype,
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

pub fn addNotationMathToken(
    self: anytype,
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

pub fn addNotationToken(
    self: anytype,
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
