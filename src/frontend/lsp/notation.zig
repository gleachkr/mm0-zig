const std = @import("std");
const source = @import("source.zig");
const Types = @import("types.zig");

const BinderDecl = Types.BinderDecl;
const SourceSpan = source.SourceSpan;
const trimMathWhitespace = source.trimMathWhitespace;
const containsMathWhitespace = source.containsMathWhitespace;
const isMathWhitespace = source.isMathWhitespace;
const isIdentChar = source.isIdentChar;

pub const NotationKind = enum {
    prefix,
    infixl,
    infixr,
    general,

    pub fn detailPrefix(self: NotationKind) []const u8 {
        return switch (self) {
            .prefix => "prefix",
            .infixl => "infixl",
            .infixr => "infixr",
            .general => "notation",
        };
    }
};

pub const NotationCompletionDecl = struct {
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

pub const NotationVariable = struct {
    arg_index: usize,
    name: []const u8,
};

pub const NotationPiece = union(enum) {
    constant: []const u8,
    variable: NotationVariable,
};

pub const NotationSnippet = struct {
    label: []const u8,
    text: []const u8,
    filter_text: []const u8,
};

pub fn aliasFirstFilterText(
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

pub fn buildPrefixSnippet(
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

pub fn buildGeneralNotationSnippet(
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

pub fn collectNotationBinderVariables(
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

pub fn collectNotationPieces(
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

pub fn simpleNotationKind(keyword: []const u8) NotationKind {
    if (std.mem.eql(u8, keyword, "prefix")) return .prefix;
    if (std.mem.eql(u8, keyword, "infixl")) return .infixl;
    return .infixr;
}
