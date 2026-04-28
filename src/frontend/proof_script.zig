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

pub const RuleApplication = struct {
    rule_name: []const u8,
    rule_span: Span,
    binding_list_span: ?Span = null,
    arg_bindings: []const ArgBinding = &.{},
    refs_span: ?Span = null,
    refs: []const Ref = &.{},
    span: Span,

    pub fn ruleApplicationSpan(self: RuleApplication) Span {
        return self.binding_list_span orelse self.rule_span;
    }

    pub fn refsOrRuleSpan(self: RuleApplication) Span {
        return self.refs_span orelse self.rule_span;
    }

    pub fn bindingSpan(
        self: RuleApplication,
        binder_name: ?[]const u8,
    ) ?Span {
        const name = binder_name orelse return null;
        for (self.arg_bindings) |binding| {
            if (std.mem.eql(u8, binding.name, name)) {
                return binding.span;
            }
        }
        return null;
    }
};

pub const Ref = union(enum) {
    hyp: HypRef,
    line: LineRef,
    application: RuleApplication,
};

pub const ProofLine = struct {
    label: []const u8,
    label_span: Span,
    assertion: MathString,
    application: RuleApplication,
    span: Span,

    pub fn ruleApplicationSpan(self: ProofLine) Span {
        return self.application.ruleApplicationSpan();
    }

    pub fn refsOrRuleSpan(self: ProofLine) Span {
        return self.application.refsOrRuleSpan();
    }
};

pub const BlockKind = enum {
    theorem,
    lemma,
};

pub const ProofBlock = struct {
    kind: BlockKind,
    name: []const u8,
    name_span: Span,
    header_span: Span,
    header_tail: []const u8 = "",
    underline_span: ?Span,
    lines: []const ProofLine,
    span: Span,
};

pub const TheoremBlock = ProofBlock;

pub const Parser = struct {
    allocator: std.mem.Allocator,
    src: []const u8,
    pos: usize = 0,
    current_block_name: ?[]const u8 = null,
    current_block_name_span: ?Span = null,
    last_error_span: ?Span = null,

    pub fn init(allocator: std.mem.Allocator, src: []const u8) Parser {
        return .{
            .allocator = allocator,
            .src = src,
        };
    }

    pub fn nextBlock(self: *Parser) !?ProofBlock {
        self.current_block_name = null;
        self.current_block_name_span = null;
        self.last_error_span = null;
        self.skipBlankLines();
        if (self.pos >= self.src.len) return null;

        const block_start = self.pos;
        const ident_start = self.pos;
        const ident = try self.parseIdentifier();
        if (std.mem.eql(u8, ident, "lemma") and self.startsLemmaHeader()) {
            return try self.parseLemmaBlock(block_start);
        }
        return try self.parseTheoremBlock(block_start, ident, ident_start);
    }

    pub fn diagnosticSpan(self: *const Parser) ?Span {
        if (self.last_error_span) |span| {
            if (span.start < span.end or self.current_block_name_span == null) {
                return span;
            }
        }
        return self.current_block_name_span orelse self.last_error_span;
    }

    pub fn diagnosticBlockName(self: *const Parser) ?[]const u8 {
        return self.current_block_name;
    }

    pub fn recoverToNextBlockBoundary(self: *Parser) bool {
        self.current_block_name = null;
        self.current_block_name_span = null;
        if (self.pos < self.src.len) {
            self.pos = self.nextLineStart(self.pos);
        }
        while (self.pos < self.src.len) {
            const line_start = self.pos;
            if (self.lineLooksLikeBlockHeader(line_start)) {
                return true;
            }
            self.pos = self.nextLineStart(line_start);
        }
        return false;
    }

    fn startsLemmaHeader(self: *Parser) bool {
        var i = self.pos;
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        return i < self.src.len and isIdentStart(self.src[i]);
    }

    fn parseTheoremBlock(
        self: *Parser,
        block_start: usize,
        name: []const u8,
        name_start: usize,
    ) !ProofBlock {
        self.setCurrentBlockContext(name, name_start);
        try self.expectLineEnd();
        const header_span = Span{
            .start = block_start,
            .end = self.pos,
        };
        const underline_span = try self.parseRequiredUnderlineLine();
        const lines = try self.parseProofLines();
        return .{
            .kind = .theorem,
            .name = name,
            .name_span = .{
                .start = name_start,
                .end = name_start + name.len,
            },
            .header_span = header_span,
            .underline_span = underline_span,
            .lines = lines,
            .span = .{
                .start = block_start,
                .end = self.pos,
            },
        };
    }

    fn parseLemmaBlock(
        self: *Parser,
        block_start: usize,
    ) !ProofBlock {
        const name_start = self.pos;
        const name = try self.parseIdentifier();
        self.setCurrentBlockContext(name, name_start);
        const tail = try self.parseLemmaHeaderTail();
        try self.expectLineEnd();
        const header_span = Span{
            .start = block_start,
            .end = self.pos,
        };
        const underline_span = try self.parseRequiredUnderlineLine();
        const lines = try self.parseProofLines();
        return .{
            .kind = .lemma,
            .name = name,
            .name_span = .{
                .start = name_start,
                .end = name_start + name.len,
            },
            .header_span = header_span,
            .header_tail = tail,
            .underline_span = underline_span,
            .lines = lines,
            .span = .{
                .start = block_start,
                .end = self.pos,
            },
        };
    }

    fn parseProofLines(self: *Parser) ![]const ProofLine {
        self.skipBlankLines();
        var lines = std.ArrayListUnmanaged(ProofLine){};
        while (true) {
            const line_start = self.skipBlankLinesFrom(self.pos);
            self.pos = line_start;
            if (self.pos >= self.src.len) break;
            if (!self.lineStartsProofLine()) break;
            try lines.append(self.allocator, try self.parseProofLine());
        }
        return try lines.toOwnedSlice(self.allocator);
    }

    fn parseProofLine(self: *Parser) !ProofLine {
        const start = self.pos;
        self.skipHorizontalSpace();
        const label_start = self.pos;
        const label = try self.parseIdentifier();
        const label_span = Span{
            .start = label_start,
            .end = label_start + label.len,
        };
        self.skipHorizontalSpace();
        try self.expect(':');
        const assertion = try self.parseMathString();
        try self.expectProofKeyword("by");
        const application = try self.parseRuleApplication();
        try self.expectLineEnd();
        return .{
            .label = label,
            .label_span = label_span,
            .assertion = assertion,
            .application = application,
            .span = .{
                .start = start,
                .end = self.pos,
            },
        };
    }

    fn parseRuleApplication(self: *Parser) anyerror!RuleApplication {
        self.skipProofWhitespace();
        const rule_start = self.pos;
        const rule_name = try self.parseIdentifier();
        return try self.parseRuleApplicationAfterName(rule_start, rule_name);
    }

    fn parseRuleApplicationAfterName(
        self: *Parser,
        rule_start: usize,
        rule_name: []const u8,
    ) anyerror!RuleApplication {
        const rule_span = Span{
            .start = rule_start,
            .end = rule_start + rule_name.len,
        };

        var arg_bindings: []const ArgBinding = &.{};
        var binding_list_span: ?Span = null;
        if (self.consumeOptionalProofDelimiter('(')) |binding_start| {
            arg_bindings = try self.parseArgBindings();
            try self.expectProof(')');
            binding_list_span = .{
                .start = binding_start,
                .end = self.pos,
            };
        }

        var refs: []const Ref = &.{};
        var refs_span: ?Span = null;
        if (self.consumeOptionalProofDelimiter('[')) |refs_start| {
            refs = try self.parseRefs();
            try self.expectProof(']');
            refs_span = .{
                .start = refs_start,
                .end = self.pos,
            };
        }
        return .{
            .rule_name = rule_name,
            .rule_span = rule_span,
            .binding_list_span = binding_list_span,
            .arg_bindings = arg_bindings,
            .refs_span = refs_span,
            .refs = refs,
            .span = .{
                .start = rule_start,
                .end = if (refs_span) |span|
                    span.end
                else if (binding_list_span) |span|
                    span.end
                else
                    rule_span.end,
            },
        };
    }

    fn parseArgBindings(self: *Parser) ![]const ArgBinding {
        var bindings = std.ArrayListUnmanaged(ArgBinding){};
        self.skipProofWhitespace();
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
            self.skipProofWhitespace();
            if (self.peek() != ',') break;
            self.pos += 1;
            self.skipProofWhitespace();
        }
        return try bindings.toOwnedSlice(self.allocator);
    }

    fn parseRefs(self: *Parser) ![]const Ref {
        var refs = std.ArrayListUnmanaged(Ref){};
        self.skipProofWhitespace();
        if (self.peek() == ']') {
            return try refs.toOwnedSlice(self.allocator);
        }
        while (true) {
            try refs.append(self.allocator, try self.parseRef());
            self.skipProofWhitespace();
            if (self.peek() != ',') break;
            self.pos += 1;
            self.skipProofWhitespace();
        }
        return try refs.toOwnedSlice(self.allocator);
    }

    fn parseRef(self: *Parser) !Ref {
        self.skipProofWhitespace();
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
        const label_end = self.pos;
        if (self.nextProofTokenIsApplicationDelimiter()) {
            return .{
                .application = try self.parseRuleApplicationAfterName(
                    start,
                    label,
                ),
            };
        }
        return .{ .line = .{
            .label = label,
            .span = .{
                .start = start,
                .end = label_end,
            },
        } };
    }

    fn nextProofTokenIsApplicationDelimiter(self: *Parser) bool {
        const saved = self.pos;
        defer self.pos = saved;
        self.skipProofWhitespace();
        return self.peek() == '(' or self.peek() == '[';
    }

    fn parseMathString(self: *Parser) !MathString {
        self.skipProofWhitespace();
        if (self.peek() != '$') {
            return self.recordErrorAtPos(error.ExpectedMathString);
        }
        const start = self.pos;
        self.pos += 1;
        const math_start = self.pos;
        while (self.pos < self.src.len and self.src[self.pos] != '$') {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) {
            return self.recordErrorAtSpan(error.UnterminatedMathString, .{
                .start = start,
                .end = @min(start + 1, self.src.len),
            });
        }
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

    fn parseLemmaHeaderTail(self: *Parser) ![]const u8 {
        self.skipHorizontalSpace();
        const start = self.pos;
        while (self.pos < self.src.len and self.src[self.pos] != '\n') {
            if (self.src[self.pos] == '$') {
                const math_start = self.pos;
                self.pos += 1;
                while (self.pos < self.src.len and self.src[self.pos] != '$') {
                    self.pos += 1;
                }
                if (self.pos >= self.src.len) {
                    return self.recordErrorAtSpan(
                        error.UnterminatedMathString,
                        .{
                            .start = math_start,
                            .end = @min(math_start + 1, self.src.len),
                        },
                    );
                }
                self.pos += 1;
                continue;
            }
            if (self.pos + 1 < self.src.len and
                self.src[self.pos] == '-' and
                self.src[self.pos + 1] == '-')
            {
                break;
            }
            self.pos += 1;
        }
        var end = self.pos;
        while (end > start and isHorizontalSpace(self.src[end - 1])) {
            end -= 1;
        }
        return self.src[start..end];
    }

    fn parseRequiredUnderlineLine(self: *Parser) !Span {
        const start = self.pos;
        if (!self.lineIsUnderline(start)) {
            return self.recordErrorAtSpan(
                error.ExpectedBlockUnderline,
                self.underlineDiagnosticSpan(start),
            );
        }
        self.pos = self.lineEnd(start);
        self.consumeNewline();
        return .{
            .start = start,
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
            return self.recordErrorAtPos(error.ExpectedIdentifier);
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
            return self.recordErrorAtPos(error.ExpectedNumber);
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
        const start = self.pos;
        const actual = try self.parseIdentifier();
        if (!std.mem.eql(u8, actual, keyword)) {
            return self.recordErrorAtSpan(error.ExpectedKeyword, .{
                .start = start,
                .end = start + actual.len,
            });
        }
    }

    fn expectProofKeyword(self: *Parser, keyword: []const u8) !void {
        self.skipProofWhitespace();
        const start = self.pos;
        const actual = try self.parseIdentifier();
        if (!std.mem.eql(u8, actual, keyword)) {
            return self.recordErrorAtSpan(error.ExpectedKeyword, .{
                .start = start,
                .end = start + actual.len,
            });
        }
    }

    fn expect(self: *Parser, ch: u8) !void {
        self.skipHorizontalSpace();
        if (self.peek() != ch) {
            return self.recordErrorAtPos(error.UnexpectedCharacter);
        }
        self.pos += 1;
    }

    fn expectProof(self: *Parser, ch: u8) !void {
        self.skipProofWhitespace();
        if (self.peek() != ch) {
            return self.recordErrorAtPos(error.UnexpectedCharacter);
        }
        self.pos += 1;
    }

    fn expectLineEnd(self: *Parser) !void {
        self.skipHorizontalSpace();
        self.skipLineComment();
        if (self.pos >= self.src.len) return;
        if (self.src[self.pos] != '\n') {
            return self.recordErrorAtPos(error.ExpectedLineEnd);
        }
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

    fn skipLineComment(self: *Parser) void {
        if (self.pos + 1 < self.src.len and
            self.src[self.pos] == '-' and
            self.src[self.pos + 1] == '-')
        {
            while (self.pos < self.src.len and self.src[self.pos] != '\n') : (self.pos += 1) {}
        }
    }

    fn skipHorizontalSpace(self: *Parser) void {
        while (self.pos < self.src.len and
            isHorizontalSpace(self.src[self.pos]))
        {
            self.pos += 1;
        }
    }

    fn skipProofWhitespace(self: *Parser) void {
        while (true) {
            self.skipHorizontalSpace();
            if (self.pos + 1 < self.src.len and
                self.src[self.pos] == '-' and
                self.src[self.pos + 1] == '-')
            {
                while (self.pos < self.src.len and
                    self.src[self.pos] != '\n')
                {
                    self.pos += 1;
                }
                continue;
            }
            if (self.pos < self.src.len and self.src[self.pos] == '\n') {
                self.pos += 1;
                continue;
            }
            break;
        }
    }

    fn consumeOptionalProofDelimiter(
        self: *Parser,
        ch: u8,
    ) ?usize {
        const saved = self.pos;
        self.skipProofWhitespace();
        if (self.peek() == ch) {
            const start = self.pos;
            self.pos += 1;
            return start;
        }
        self.pos = saved;
        return null;
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
            if (i + 1 < self.src.len and
                self.src[i] == '-' and
                self.src[i + 1] == '-')
            {
                while (i < self.src.len and self.src[i] != '\n') : (i += 1) {}
                if (i < self.src.len) i += 1;
                continue;
            }
            if (self.src[i] != '\n') return line_start;
            i += 1;
        }
    }

    fn lineLooksLikeBlockHeader(
        self: *Parser,
        line_start: usize,
    ) bool {
        if (!self.lineStartsBlockHeaderLead(line_start)) return false;

        const next_start = self.nextLineStart(line_start);
        if (next_start >= self.src.len or !self.lineIsUnderline(next_start)) {
            return false;
        }
        self.pos = line_start;
        return true;
    }

    fn lineStartsBlockHeaderLead(
        self: *const Parser,
        line_start: usize,
    ) bool {
        var i = line_start;
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        if (i >= self.src.len or self.src[i] == '\n') return false;
        if (i + 1 < self.src.len and
            self.src[i] == '-' and
            self.src[i + 1] == '-')
        {
            return false;
        }
        const ident_start = i;
        if (!isIdentStart(self.src[ident_start])) return false;
        i += 1;
        while (i < self.src.len and isIdentChar(self.src[i])) : (i += 1) {}
        const ident = self.src[ident_start..i];
        if (std.mem.eql(u8, ident, "lemma")) {
            return self.lineLooksLikeLemmaHeader(i);
        }
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        return i >= self.src.len or
            self.src[i] == '\n' or
            (i + 1 < self.src.len and
                self.src[i] == '-' and
                self.src[i + 1] == '-');
    }

    fn lineLooksLikeLemmaHeader(
        self: *const Parser,
        after_keyword: usize,
    ) bool {
        var i = after_keyword;
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        if (i >= self.src.len or !isIdentStart(self.src[i])) return false;
        i += 1;
        while (i < self.src.len and isIdentChar(self.src[i])) : (i += 1) {}

        const line_end = self.lineEnd(i);
        while (i < line_end) {
            if (self.src[i] == '$') {
                i += 1;
                while (i < line_end and self.src[i] != '$') : (i += 1) {}
                if (i >= line_end) return false;
                i += 1;
                continue;
            }
            if (self.src[i] == ':') return true;
            if (i + 1 < line_end and
                self.src[i] == '-' and
                self.src[i + 1] == '-')
            {
                return false;
            }
            i += 1;
        }
        return false;
    }

    fn lineIsUnderline(self: *const Parser, line_start: usize) bool {
        var i = line_start;
        while (i < self.src.len and isHorizontalSpace(self.src[i])) : (i += 1) {}
        const line_end = self.lineEnd(i);
        const trimmed = std.mem.trimRight(
            u8,
            self.src[i..line_end],
            " \t\r",
        );
        if (trimmed.len < 3) return false;
        for (trimmed) |ch| {
            if (ch != '-') return false;
        }
        return true;
    }

    fn lineEnd(self: *const Parser, start: usize) usize {
        var i = start;
        while (i < self.src.len and self.src[i] != '\n') : (i += 1) {}
        return i;
    }

    fn nextLineStart(self: *const Parser, start: usize) usize {
        var i = self.lineEnd(start);
        if (i < self.src.len) i += 1;
        return i;
    }

    fn setCurrentBlockContext(
        self: *Parser,
        name: []const u8,
        name_start: usize,
    ) void {
        self.current_block_name = name;
        self.current_block_name_span = .{
            .start = name_start,
            .end = name_start + name.len,
        };
    }

    fn recordErrorAtPos(self: *Parser, err: anyerror) anyerror {
        self.last_error_span = self.tokenSpanAt(self.pos);
        return err;
    }

    fn recordErrorAtSpan(
        self: *Parser,
        err: anyerror,
        span: Span,
    ) anyerror {
        self.last_error_span = span;
        return err;
    }

    fn tokenSpanAt(self: *const Parser, pos_raw: usize) Span {
        const start = @min(pos_raw, self.src.len);
        const end = if (start < self.src.len) start + 1 else start;
        return .{
            .start = start,
            .end = end,
        };
    }

    fn underlineDiagnosticSpan(self: *const Parser, start: usize) Span {
        const clamped_start = @min(start, self.src.len);
        const line_end = self.lineEnd(clamped_start);
        if (line_end > clamped_start) {
            return .{
                .start = clamped_start,
                .end = line_end,
            };
        }
        return self.tokenSpanAt(clamped_start);
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
