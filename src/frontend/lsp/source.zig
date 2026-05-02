const std = @import("std");
const Types = @import("types.zig");

pub const Token = struct {
    text: []const u8,
    start: usize,
    end: usize,
};

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;

pub const SourceSpan = struct {
    start: usize,
    end: usize,
};

pub const MathStringSpan = struct {
    text: []const u8,
    inner_start: usize,
    inner_end: usize,
};

pub const StatementHeader = struct {
    keyword: []const u8,
    name: ?[]const u8 = null,
};

pub const StatementIterator = struct {
    text: []const u8,
    pos: usize = 0,

    pub fn init(text: []const u8) StatementIterator {
        return .{ .text = text };
    }

    pub fn next(self: *StatementIterator) ?SourceSpan {
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

pub const MathTokenCursor = struct {
    src: []const u8,
    pos: usize = 0,
    left_delims: [256]bool,
    right_delims: [256]bool,

    pub fn next(self: *MathTokenCursor) ?Token {
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

pub fn nextAnnotationToken(text: []const u8, pos: *usize) ?Token {
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

pub fn statementHeader(text: []const u8, stmt: SourceSpan) ?StatementHeader {
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

pub fn startsLineComment(text: []const u8, pos: usize) bool {
    return pos + 1 < text.len and text[pos] == '-' and text[pos + 1] == '-';
}

fn skipMathString(text: []const u8, pos: *usize, end: usize) void {
    pos.* += 1;
    while (pos.* < end and text[pos.*] != '$') pos.* += 1;
    if (pos.* < end) pos.* += 1;
}

pub fn firstMathStringIn(text: []const u8, stmt: SourceSpan) ?MathStringSpan {
    var pos = stmt.start;
    return nextMathStringIn(text, stmt.end, &pos);
}

pub fn nextMathStringIn(
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

pub fn findStatementByte(
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

pub fn trimMathWhitespace(text: []const u8) []const u8 {
    return std.mem.trim(u8, text, " \n\t\r");
}

pub fn containsMathWhitespace(text: []const u8) bool {
    for (text) |ch| {
        if (isMathWhitespace(ch)) return true;
    }
    return false;
}

pub fn isMathWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\n' or ch == '\t' or ch == '\r';
}

pub fn sourceRangeFromSlice(
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

pub fn findIdentIn(
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

pub fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

pub fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
