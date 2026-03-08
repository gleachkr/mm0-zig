const std = @import("std");

pub const Span = struct {
    start: usize,
    end: usize,
};

pub const MathString = struct {
    text: []const u8,
    span: Span,
};

pub const ArgBinding = struct {
    name: []const u8,
    formula: MathString,
    span: Span,
};

pub const HypRef = struct {
    index: usize,
    span: Span,
};

pub const LineRef = struct {
    label: []const u8,
    span: Span,
};

pub const Ref = union(enum) {
    hyp: HypRef,
    line: LineRef,
};

pub const ProofLine = struct {
    label: []const u8,
    assertion: MathString,
    rule_name: []const u8,
    arg_bindings: []const ArgBinding,
    refs: []const Ref,
    span: Span,
};

pub const TheoremBlock = struct {
    name: []const u8,
    name_span: Span,
    underline_span: ?Span,
    lines: []const ProofLine,
    span: Span,
};

pub const Parser = struct {
    allocator: std.mem.Allocator,
    src: []const u8,
    pos: usize = 0,

    pub fn init(allocator: std.mem.Allocator, src: []const u8) Parser {
        return .{
            .allocator = allocator,
            .src = src,
        };
    }

    pub fn nextBlock(self: *Parser) !?TheoremBlock {
        self.skipBlankLines();
        if (self.pos >= self.src.len) return null;

        const block_start = self.pos;
        const name_start = self.pos;
        const name = try self.parseIdentifier();
        const name_span = Span{
            .start = name_start,
            .end = name_start + name.len,
        };
        try self.expectLineEnd();

        const underline_span = self.parseUnderlineLine();
        self.skipBlankLines();

        var lines = std.ArrayListUnmanaged(ProofLine){};
        while (true) {
            const line_start = self.skipBlankLinesFrom(self.pos);
            self.pos = line_start;
            if (self.pos >= self.src.len) break;
            if (!self.lineStartsProofLine()) break;
            try lines.append(self.allocator, try self.parseProofLine());
        }

        return .{
            .name = name,
            .name_span = name_span,
            .underline_span = underline_span,
            .lines = try lines.toOwnedSlice(self.allocator),
            .span = .{
                .start = block_start,
                .end = self.pos,
            },
        };
    }

    fn parseProofLine(self: *Parser) !ProofLine {
        const start = self.pos;
        self.skipHorizontalSpace();
        const label = try self.parseIdentifier();
        self.skipHorizontalSpace();
        try self.expect(':');
        const assertion = try self.parseMathString();
        try self.expectKeyword("by");
        const rule_name = try self.parseIdentifier();
        self.skipHorizontalSpace();
        try self.expect('(');
        const arg_bindings = try self.parseArgBindings();
        try self.expect(')');
        self.skipHorizontalSpace();
        try self.expect('[');
        const refs = try self.parseRefs();
        try self.expect(']');
        try self.expectLineEnd();
        return .{
            .label = label,
            .assertion = assertion,
            .rule_name = rule_name,
            .arg_bindings = arg_bindings,
            .refs = refs,
            .span = .{
                .start = start,
                .end = self.pos,
            },
        };
    }

    fn parseArgBindings(self: *Parser) ![]const ArgBinding {
        var bindings = std.ArrayListUnmanaged(ArgBinding){};
        self.skipHorizontalSpace();
        if (self.peek() == ')') {
            return try bindings.toOwnedSlice(self.allocator);
        }
        while (true) {
            const start = self.pos;
            const name = try self.parseIdentifier();
            self.skipHorizontalSpace();
            try self.expect(':');
            try self.expect('=');
            const formula = try self.parseMathString();
            try bindings.append(self.allocator, .{
                .name = name,
                .formula = formula,
                .span = .{
                    .start = start,
                    .end = formula.span.end,
                },
            });
            self.skipHorizontalSpace();
            if (self.peek() != ',') break;
            self.pos += 1;
            self.skipHorizontalSpace();
        }
        return try bindings.toOwnedSlice(self.allocator);
    }

    fn parseRefs(self: *Parser) ![]const Ref {
        var refs = std.ArrayListUnmanaged(Ref){};
        self.skipHorizontalSpace();
        if (self.peek() == ']') {
            return try refs.toOwnedSlice(self.allocator);
        }
        while (true) {
            try refs.append(self.allocator, try self.parseRef());
            self.skipHorizontalSpace();
            if (self.peek() != ',') break;
            self.pos += 1;
            self.skipHorizontalSpace();
        }
        return try refs.toOwnedSlice(self.allocator);
    }

    fn parseRef(self: *Parser) !Ref {
        self.skipHorizontalSpace();
        const start = self.pos;
        if (self.peek() == '#') {
            self.pos += 1;
            const index = try self.parseNumber();
            return .{ .hyp = .{
                .index = index,
                .span = .{
                    .start = start,
                    .end = self.pos,
                },
            } };
        }
        const label = try self.parseIdentifier();
        return .{ .line = .{
            .label = label,
            .span = .{
                .start = start,
                .end = self.pos,
            },
        } };
    }

    fn parseMathString(self: *Parser) !MathString {
        self.skipHorizontalSpace();
        if (self.peek() != '$') return error.ExpectedMathString;
        const start = self.pos;
        self.pos += 1;
        const math_start = self.pos;
        while (self.pos < self.src.len and self.src[self.pos] != '$') {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) return error.UnterminatedMathString;
        const text = self.src[math_start..self.pos];
        self.pos += 1;
        return .{
            .text = text,
            .span = .{
                .start = start,
                .end = self.pos,
            },
        };
    }

    fn parseUnderlineLine(self: *Parser) ?Span {
        const saved = self.pos;
        var line_start = saved;
        while (line_start < self.src.len and
            isHorizontalSpace(self.src[line_start]))
        {
            line_start += 1;
        }
        var line_end = line_start;
        while (line_end < self.src.len and self.src[line_end] != '\n') {
            line_end += 1;
        }
        const trimmed = std.mem.trimRight(
            u8,
            self.src[line_start..line_end],
            " \t\r",
        );
        if (trimmed.len < 2) return null;
        for (trimmed) |ch| {
            if (ch != '-') return null;
        }
        self.pos = line_end;
        self.consumeNewline();
        return .{
            .start = saved,
            .end = self.pos,
        };
    }

    fn lineStartsProofLine(self: *Parser) bool {
        var i = self.pos;
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        if (i >= self.src.len or !isIdentStart(self.src[i])) return false;
        i += 1;
        while (i < self.src.len and isIdentChar(self.src[i])) : (i += 1) {}
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        return i < self.src.len and self.src[i] == ':';
    }

    fn parseIdentifier(self: *Parser) ![]const u8 {
        self.skipHorizontalSpace();
        const start = self.pos;
        if (start >= self.src.len or !isIdentStart(self.src[start])) {
            return error.ExpectedIdentifier;
        }
        self.pos += 1;
        while (self.pos < self.src.len and isIdentChar(self.src[self.pos])) {
            self.pos += 1;
        }
        return self.src[start..self.pos];
    }

    fn parseNumber(self: *Parser) !usize {
        self.skipHorizontalSpace();
        if (self.pos >= self.src.len or
            !std.ascii.isDigit(self.src[self.pos]))
        {
            return error.ExpectedNumber;
        }
        var value: usize = 0;
        while (self.pos < self.src.len and
            std.ascii.isDigit(self.src[self.pos]))
        {
            value = try std.math.mul(usize, value, 10);
            value = try std.math.add(
                usize,
                value,
                self.src[self.pos] - '0',
            );
            self.pos += 1;
        }
        return value;
    }

    fn expectKeyword(self: *Parser, keyword: []const u8) !void {
        self.skipHorizontalSpace();
        const actual = try self.parseIdentifier();
        if (!std.mem.eql(u8, actual, keyword)) return error.ExpectedKeyword;
    }

    fn expect(self: *Parser, ch: u8) !void {
        self.skipHorizontalSpace();
        if (self.peek() != ch) return error.UnexpectedCharacter;
        self.pos += 1;
    }

    fn expectLineEnd(self: *Parser) !void {
        self.skipHorizontalSpace();
        if (self.pos >= self.src.len) return;
        if (self.src[self.pos] != '\n') return error.ExpectedLineEnd;
        self.consumeNewline();
    }

    fn consumeNewline(self: *Parser) void {
        if (self.pos < self.src.len and self.src[self.pos] == '\n') {
            self.pos += 1;
        }
    }

    fn peek(self: *Parser) u8 {
        if (self.pos >= self.src.len) return 0;
        return self.src[self.pos];
    }

    fn skipHorizontalSpace(self: *Parser) void {
        while (self.pos < self.src.len and
            isHorizontalSpace(self.src[self.pos]))
        {
            self.pos += 1;
        }
    }

    fn skipBlankLines(self: *Parser) void {
        self.pos = self.skipBlankLinesFrom(self.pos);
    }

    fn skipBlankLinesFrom(self: *Parser, start: usize) usize {
        var i = start;
        while (true) {
            const line_start = i;
            while (i < self.src.len and isHorizontalSpace(self.src[i])) {
                i += 1;
            }
            if (i >= self.src.len) return i;
            if (self.src[i] != '\n') return line_start;
            i += 1;
        }
    }
};

fn isHorizontalSpace(ch: u8) bool {
    return ch == ' ' or ch == '\t' or ch == '\r';
}

fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
