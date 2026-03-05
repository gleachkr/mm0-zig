const std = @import("std");
const Arg = @import("./args.zig").Arg;
const Sort = @import("./sorts.zig").Sort;

pub const MM0Stmt = union(enum) {
    sort: SortStmt,
    term: TermStmt,
    assertion: AssertionStmt,
};

pub const SortStmt = struct {
    name: []const u8,
    modifiers: Sort,
};

pub const TermStmt = struct {
    name: []const u8,
    args: []const ArgInfo,
    ret_sort_name: []const u8,
    is_def: bool,
};

pub const AssertionStmt = struct {
    name: []const u8,
    args: []const ArgInfo,
    is_local: bool,
};

pub const ArgInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

pub const MM0Parser = struct {
    src: []const u8,
    pos: usize,
    allocator: std.mem.Allocator,

    pub fn init(src: []const u8, allocator: std.mem.Allocator) MM0Parser {
        return .{ .src = src, .pos = 0, .allocator = allocator };
    }

    // Returns next public statement, skipping local theorems/defs
    // and notation/inout statements entirely
    pub fn next(self: *MM0Parser) !?MM0Stmt {
        while (true) {
            self.skipWhitespaceAndComments();
            if (self.pos >= self.src.len) return null;

            const word = self.peekIdent() orelse {
                try self.skipToSemicolon();
                continue;
            };

            if (std.mem.eql(u8, word, "pure") or
                std.mem.eql(u8, word, "strict") or
                std.mem.eql(u8, word, "provable") or
                std.mem.eql(u8, word, "free") or
                std.mem.eql(u8, word, "sort"))
            {
                return MM0Stmt{ .sort = try self.parseSortStmt() };
            } else if (std.mem.eql(u8, word, "term")) {
                return MM0Stmt{ .term = try self.parseTermStmt(false) };
            } else if (std.mem.eql(u8, word, "def")) {
                return MM0Stmt{ .term = try self.parseTermStmt(true) };
            } else if (std.mem.eql(u8, word, "pub")) {
                _ = self.consumeIdent();
                self.skipWhitespaceAndComments();
                const next_word = self.peekIdent() orelse return error.ExpectedKeyword;
                if (std.mem.eql(u8, next_word, "def")) {
                    return MM0Stmt{ .term = try self.parseTermStmt(true) };
                } else if (std.mem.eql(u8, next_word, "theorem")) {
                    return MM0Stmt{ .assertion = try self.parseAssertionStmt(false) };
                } else return error.UnexpectedKeyword;
            } else if (std.mem.eql(u8, word, "axiom")) {
                return MM0Stmt{ .assertion = try self.parseAssertionStmt(false) };
            } else if (std.mem.eql(u8, word, "theorem")) {
                return MM0Stmt{ .assertion = try self.parseAssertionStmt(false) };
            } else if (std.mem.eql(u8, word, "local")) {
                try self.skipToSemicolon();
                continue;
            } else {
                // notation, delimiter, input, output - skip
                try self.skipToSemicolon();
                continue;
            }
        }
    }

    fn parseSortStmt(self: *MM0Parser) !SortStmt {
        var modifiers = Sort{};
        while (true) {
            self.skipWhitespaceAndComments();
            const word = self.peekIdent() orelse return error.ExpectedIdent;
            if (std.mem.eql(u8, word, "pure")) {
                _ = self.consumeIdent();
                modifiers.pure = true;
            } else if (std.mem.eql(u8, word, "strict")) {
                _ = self.consumeIdent();
                modifiers.strict = true;
            } else if (std.mem.eql(u8, word, "provable")) {
                _ = self.consumeIdent();
                modifiers.provable = true;
            } else if (std.mem.eql(u8, word, "free")) {
                _ = self.consumeIdent();
                modifiers.free = true;
            } else if (std.mem.eql(u8, word, "sort")) {
                _ = self.consumeIdent();
                self.skipWhitespaceAndComments();
                const name = self.consumeIdent() orelse return error.ExpectedIdent;
                self.skipWhitespaceAndComments();
                try self.expect(';');
                return .{ .name = name, .modifiers = modifiers };
            } else return error.UnexpectedKeyword;
        }
    }

    fn parseBinders(
        self: *MM0Parser,
        args: *std.ArrayListUnmanaged(ArgInfo),
        bv_names: *std.ArrayListUnmanaged([]const u8),
    ) !void {
        while (self.peek() == '(' or self.peek() == '{') {
            const is_bound = self.src[self.pos] == '{';
            self.pos += 1;
            self.skipWhitespaceAndComments();

            // Collect ident names until ':'
            var names: std.ArrayListUnmanaged([]const u8) = .{};
            var is_dummy_buf: std.ArrayListUnmanaged(bool) = .{};
            while (true) {
                self.skipWhitespaceAndComments();
                if (self.peek() == ':') break;
                const is_dummy = self.peek() == '.';
                if (is_dummy) self.pos += 1;
                const ident = self.consumeIdent() orelse return error.ExpectedIdent;
                try names.append(self.allocator, ident);
                try is_dummy_buf.append(self.allocator, is_dummy);
            }
            self.pos += 1; // consume ':'
            self.skipWhitespaceAndComments();
            const sort_name = self.consumeIdent() orelse return error.ExpectedIdent;

            if (is_bound) {
                // Bound vars have no dep annotations - they depend only on themselves
                // Register each name and assign the next bv index
                const close: u8 = '}';
                self.skipWhitespaceAndComments();
                try self.expect(close);
                for (names.items, is_dummy_buf.items) |n, is_dummy| {
                    const bv_idx = bv_names.items.len;
                    try bv_names.append(self.allocator, n);
                    if (!is_dummy) {
                        try args.append(self.allocator, .{
                            .sort_name = sort_name,
                            .bound = true,
                            .deps = @as(u55, 1) << @intCast(bv_idx),
                        });
                    }
                    // dummy vars are in bv_names for dep resolution but not in args
                }
            } else {
                // Consume optional dependency variable list e.g. (p: wff x y)
                var deps: u55 = 0;
                self.skipWhitespaceAndComments();
                while (self.peek() != ')' and self.peek() != 0) {
                    const dep_name = self.consumeIdent() orelse break;
                    for (bv_names.items, 0..) |bv_name, idx| {
                        if (std.mem.eql(u8, dep_name, bv_name)) {
                            deps |= @as(u55, 1) << @intCast(idx);
                            break;
                        }
                    }
                    self.skipWhitespaceAndComments();
                }
                try self.expect(')');
                for (names.items, is_dummy_buf.items) |_, is_dummy| {
                    if (!is_dummy) {
                        try args.append(self.allocator, .{
                            .sort_name = sort_name,
                            .bound = false,
                            .deps = deps,
                        });
                    }
                    // dummy regular vars are skipped entirely - not in bv_names either
                }
            }
            self.skipWhitespaceAndComments();
        }
    }

    fn parseSortExpr(
        self: *MM0Parser,
        bv_names: []const []const u8,
    ) !ArgInfo {
        self.skipWhitespaceAndComments();
        const sort_name = self.consumeIdent() orelse return error.ExpectedIdent;

        var deps: u55 = 0;
        while (true) {
            self.skipWhitespaceAndComments();
            const ch = self.peek();
            if (ch == '>' or ch == ';' or ch == '=' or ch == ')' or ch == 0)
                break;

            const dep_name = self.consumeIdent() orelse return error.ExpectedIdent;
            for (bv_names, 0..) |bv_name, idx| {
                if (std.mem.eql(u8, dep_name, bv_name)) {
                    deps |= @as(u55, 1) << @intCast(idx);
                    break;
                }
            }
        }

        return .{
            .sort_name = sort_name,
            .bound = false,
            .deps = deps,
        };
    }

    fn parseTermType(
        self: *MM0Parser,
        args: *std.ArrayListUnmanaged(ArgInfo),
        bv_names: []const []const u8,
    ) ![]const u8 {
        var current = try self.parseSortExpr(bv_names);

        while (true) {
            self.skipWhitespaceAndComments();
            if (self.peek() != '>') break;

            try args.append(self.allocator, current);
            self.pos += 1;
            current = try self.parseSortExpr(bv_names);
        }

        return current.sort_name;
    }

    fn parseTermStmt(self: *MM0Parser, is_def: bool) !TermStmt {
        _ = self.consumeIdent(); // consume 'term' or 'def'
        self.skipWhitespaceAndComments();
        const name = self.consumeIdent() orelse return error.ExpectedIdent;

        var args: std.ArrayListUnmanaged(ArgInfo) = .{};
        var bv_names: std.ArrayListUnmanaged([]const u8) = .{};
        defer bv_names.deinit(self.allocator);

        self.skipWhitespaceAndComments();
        try self.parseBinders(&args, &bv_names);

        // Parse ':' and then either `ret` or `a > b > ret`
        try self.expect(':');
        const ret_sort_name = try self.parseTermType(&args, bv_names.items);

        // Skip rest to semicolon (math string for def, nothing for term)
        try self.skipToSemicolon();

        return .{
            .name = name,
            .ret_sort_name = ret_sort_name,
            .args = try args.toOwnedSlice(self.allocator),
            .is_def = is_def,
        };
    }

    fn parseAssertionStmt(self: *MM0Parser, is_local: bool) !AssertionStmt {
        _ = self.consumeIdent(); // consume 'axiom' or 'theorem'
        self.skipWhitespaceAndComments();
        const name = self.consumeIdent() orelse return error.ExpectedIdent;

        var args: std.ArrayListUnmanaged(ArgInfo) = .{};
        var bv_names: std.ArrayListUnmanaged([]const u8) = .{};
        defer bv_names.deinit(self.allocator);

        self.skipWhitespaceAndComments();
        try self.parseBinders(&args, &bv_names);

        // Skip ':' math-str and optional '=' proof to semicolon
        try self.skipToSemicolon();

        return .{
            .name = name,
            .args = try args.toOwnedSlice(self.allocator),
            .is_local = is_local,
        };
    }

    // --- Primitives ---

    fn peek(self: *MM0Parser) u8 {
        if (self.pos >= self.src.len) return 0;
        return self.src[self.pos];
    }

    fn peekIdent(self: *MM0Parser) ?[]const u8 {
        const start = self.pos;
        var end = start;
        while (end < self.src.len and isIdentChar(self.src[end])) end += 1;
        if (end == start) return null;
        return self.src[start..end];
    }

    fn consumeIdent(self: *MM0Parser) ?[]const u8 {
        const ident = self.peekIdent() orelse return null;
        self.pos += ident.len;
        return ident;
    }

    fn expect(self: *MM0Parser, ch: u8) !void {
        if (self.peek() != ch) return error.UnexpectedChar;
        self.pos += 1;
    }

    fn skipWhitespaceAndComments(self: *MM0Parser) void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r') {
                self.pos += 1;
            } else if (ch == '-' and self.pos + 1 < self.src.len and self.src[self.pos + 1] == '-') {
                // Line comment
                while (self.pos < self.src.len and self.src[self.pos] != '\n') {
                    self.pos += 1;
                }
            } else break;
        }
    }

    fn skipToSemicolon(self: *MM0Parser) !void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            self.pos += 1;
            if (ch == '$') {
                // Skip math string
                while (self.pos < self.src.len and self.src[self.pos] != '$') {
                    self.pos += 1;
                }
                if (self.pos >= self.src.len) return error.UnterminatedMathStr;
                self.pos += 1; // consume closing '$'
            } else if (ch == ';') return;
        }
        return error.UnexpectedEOF;
    }

    fn isIdentChar(ch: u8) bool {
        return std.ascii.isAlphanumeric(ch) or ch == '_';
    }
};
