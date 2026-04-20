const std = @import("std");
const Arg = @import("../trusted/args.zig").Arg;
const Expr = @import("../trusted/expressions.zig").Expr;
const Sort = @import("../trusted/sorts.zig").Sort;

const MAX_PRECEDENCE = std.math.maxInt(u16);
const APP_PRECEDENCE: u16 = 1024;
const MAX_SORTS: usize = 128;
const PROV_COERCION_IDX: usize = MAX_SORTS;

pub const MM0Stmt = union(enum) {
    sort: SortStmt,
    term: TermStmt,
    assertion: AssertionStmt,
};

pub const SortStmt = struct {
    name: []const u8,
    name_span: MathSpan = .{ .start = 0, .end = 0 },
    modifiers: Sort,
};

pub const AssertionKind = enum {
    axiom,
    theorem,
};

pub const TermStmt = struct {
    name: []const u8,
    name_span: MathSpan = .{ .start = 0, .end = 0 },
    args: []const ArgInfo,
    arg_names: []const ?[]const u8,
    arg_exprs: []const *const Expr,
    dummy_args: []const ArgInfo = &.{},
    dummy_exprs: []const *const Expr = &.{},
    ret_sort_name: []const u8,
    is_def: bool,
    body: ?*const Expr,
};

pub const AssertionStmt = struct {
    name: []const u8,
    name_span: MathSpan = .{ .start = 0, .end = 0 },
    args: []const ArgInfo,
    arg_names: []const ?[]const u8,
    arg_exprs: []const *const Expr,
    hyps: []const *const Expr,
    concl: *const Expr,
    kind: AssertionKind,
    is_local: bool,
};

pub const ArgInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

const TermEnv = struct {
    args: []const Arg,
    ret_sort: u7,
};

const CoercionTag = enum(u8) {
    empty,
    one,
    trans,
    prov,
};

const CoercionRoute = struct {
    tag: CoercionTag = .empty,
    data: u32 = 0,
};

const PrefixLit = union(enum) {
    constant: []const u8,
    variable: PrefixVar,
};

const PrefixVar = struct {
    arg_index: usize,
    prec: u16,
};

const PrefixEnv = struct {
    term_id: u32,
    prec: u16,
    lits: []const PrefixLit,
};

const InfixEnv = struct {
    term_id: u32,
    prec: u16,
    right_assoc: bool,
};

const BinderKind = enum { term, assertion };

pub const MathSpan = struct {
    start: usize,
    end: usize,
};

pub const MathTokenInfo = struct {
    text: []const u8,
    span: MathSpan,
};

const IdentInfo = struct {
    text: []const u8,
    span: MathSpan,
};

pub const MathParseError = union(enum) {
    unknown_token: MathTokenInfo,
    unexpected_token: MathTokenInfo,
    unexpected_end: usize,
};

const BinderContext = struct {
    vars: std.StringHashMap(*const Expr),
    arg_infos: std.ArrayListUnmanaged(ArgInfo) = .{},
    arg_names: std.ArrayListUnmanaged(?[]const u8) = .{},
    arg_exprs: std.ArrayListUnmanaged(*const Expr) = .{},
    bound_names: std.ArrayListUnmanaged([]const u8) = .{},
    dummy_infos: std.ArrayListUnmanaged(ArgInfo) = .{},
    dummy_exprs: std.ArrayListUnmanaged(*const Expr) = .{},

    fn init(allocator: std.mem.Allocator) BinderContext {
        return .{ .vars = std.StringHashMap(*const Expr).init(allocator) };
    }
};

const MathCursor = struct {
    src: []const u8,
    pos: usize = 0,
    left_delims: [256]bool,
    right_delims: [256]bool,
    lookahead: ?MathTokenInfo = null,

    fn skipWhitespace(self: *MathCursor) void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == ' ' or ch == '\n' or ch == '\t' or ch == '\r') {
                self.pos += 1;
            } else break;
        }
    }

    fn readToken(self: *MathCursor) ?MathTokenInfo {
        self.skipWhitespace();
        if (self.pos >= self.src.len) return null;

        const start = self.pos;
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            self.pos += 1;
            if (self.left_delims[ch]) break;
            if (self.pos >= self.src.len) break;
            const next_ch = self.src[self.pos];
            if (next_ch == ' ' or next_ch == '\n' or next_ch == '\t' or
                next_ch == '\r')
            {
                break;
            }
            if (self.right_delims[next_ch]) break;
        }
        const end = self.pos;
        self.skipWhitespace();
        return .{
            .text = self.src[start..end],
            .span = .{
                .start = start,
                .end = end,
            },
        };
    }

    fn peek(self: *MathCursor) ?MathTokenInfo {
        if (self.lookahead == null) {
            self.lookahead = self.readToken();
        }
        return self.lookahead;
    }

    fn next(self: *MathCursor) ?MathTokenInfo {
        const token = self.peek();
        self.lookahead = null;
        return token;
    }
};

pub const MM0Parser = struct {
    src: []const u8,
    pos: usize,
    allocator: std.mem.Allocator,
    sort_names: std.StringHashMap(u8),
    term_names: std.StringHashMap(u32),
    sort_infos: std.ArrayListUnmanaged(Sort),
    terms: std.ArrayListUnmanaged(TermEnv),
    prefix_notations: std.StringHashMap(PrefixEnv),
    infix_notations: std.StringHashMap(InfixEnv),
    formula_markers: std.StringHashMap(void),
    // Global notation checks tracked as declarations are parsed.
    token_precs: std.StringHashMap(u16),
    infix_assoc: std.AutoHashMap(u16, bool),
    leading_tokens: std.StringHashMap(void),
    infixy_tokens: std.StringHashMap(void),
    // For each source sort, store either a direct coercion, a transitive
    // hop through another sort, or a route to the provable target slot.
    coercion_table: [MAX_SORTS][MAX_SORTS + 1]CoercionRoute,
    left_delims: [256]bool,
    right_delims: [256]bool,
    // Annotations captured from `--|` comment lines. Accumulated between
    // statements and moved to `last_annotations` when a statement is yielded.
    pending_annotations: std.ArrayListUnmanaged([]const u8) = .{},
    pending_annotation_spans: std.ArrayListUnmanaged(MathSpan) = .{},
    last_annotations: []const []const u8 = &.{},
    last_annotation_spans: []const MathSpan = &.{},
    last_math_error: ?MathParseError = null,
    last_math_span: ?MathSpan = null,
    current_decl_name: ?[]const u8 = null,
    current_decl_name_span: ?MathSpan = null,
    last_error_span: ?MathSpan = null,

    pub fn init(src: []const u8, allocator: std.mem.Allocator) MM0Parser {
        return .{
            .src = src,
            .pos = 0,
            .allocator = allocator,
            .sort_names = std.StringHashMap(u8).init(allocator),
            .term_names = std.StringHashMap(u32).init(allocator),
            .sort_infos = .{},
            .terms = .{},
            .prefix_notations = std.StringHashMap(PrefixEnv).init(allocator),
            .infix_notations = std.StringHashMap(InfixEnv).init(allocator),
            .formula_markers = std.StringHashMap(void).init(allocator),
            .token_precs = std.StringHashMap(u16).init(allocator),
            .infix_assoc = std.AutoHashMap(u16, bool).init(allocator),
            .leading_tokens = std.StringHashMap(void).init(allocator),
            .infixy_tokens = std.StringHashMap(void).init(allocator),
            .coercion_table = std.mem.zeroes(
                [MAX_SORTS][MAX_SORTS + 1]CoercionRoute,
            ),
            .left_delims = [_]bool{false} ** 256,
            .right_delims = [_]bool{false} ** 256,
        };
    }

    fn flushAnnotations(self: *MM0Parser) void {
        if (self.pending_annotations.items.len > 0) {
            self.last_annotations = self.pending_annotations.toOwnedSlice(
                self.allocator,
            ) catch &.{};
            self.last_annotation_spans =
                self.pending_annotation_spans.toOwnedSlice(
                    self.allocator,
                ) catch &.{};
        } else {
            self.last_annotations = &.{};
            self.last_annotation_spans = &.{};
        }
    }

    pub fn diagnosticName(self: *const MM0Parser) ?[]const u8 {
        return self.current_decl_name;
    }

    pub fn diagnosticSpan(self: *const MM0Parser) ?MathSpan {
        return self.last_error_span orelse self.current_decl_name_span;
    }

    fn resetDiagnosticContext(self: *MM0Parser) void {
        self.last_math_error = null;
        self.last_math_span = null;
        self.current_decl_name = null;
        self.current_decl_name_span = null;
        self.last_error_span = null;
    }

    fn currentTokenSpan(self: *const MM0Parser) ?MathSpan {
        const start = @min(self.pos, self.src.len);
        if (start >= self.src.len) return null;

        var end = start + 1;
        const ch = self.src[start];
        if (isIdentStart(ch)) {
            while (end < self.src.len and isIdentChar(self.src[end])) {
                end += 1;
            }
        } else if (std.ascii.isDigit(ch)) {
            while (end < self.src.len and std.ascii.isDigit(self.src[end])) {
                end += 1;
            }
        }
        return .{ .start = start, .end = end };
    }

    fn recordCurrentTokenError(self: *MM0Parser) void {
        self.last_error_span = self.currentTokenSpan();
    }

    fn consumeIdentInfo(self: *MM0Parser) ?IdentInfo {
        self.skipWhitespaceAndComments();
        const start = self.pos;
        const ident = self.peekIdent() orelse return null;
        self.pos += ident.len;
        const span = MathSpan{ .start = start, .end = self.pos };
        self.skipWhitespaceAndComments();
        return .{ .text = ident, .span = span };
    }

    fn consumeRequiredIdent(self: *MM0Parser) ![]const u8 {
        const info = try self.consumeRequiredIdentInfo();
        return info.text;
    }

    fn consumeRequiredIdentInfo(self: *MM0Parser) !IdentInfo {
        return self.consumeIdentInfo() orelse {
            self.recordCurrentTokenError();
            return error.ExpectedIdent;
        };
    }

    fn recordNameContext(self: *MM0Parser, info: IdentInfo) void {
        self.current_decl_name = info.text;
        self.current_decl_name_span = info.span;
    }

    fn lookupRecordedTermId(
        self: *MM0Parser,
        name_info: IdentInfo,
    ) !u32 {
        self.recordNameContext(name_info);
        return self.term_names.get(name_info.text) orelse {
            self.last_error_span = name_info.span;
            return error.UnknownTerm;
        };
    }

    fn lookupSortIdInfo(self: *MM0Parser, info: IdentInfo) !u7 {
        const sort_id = self.sort_names.get(info.text) orelse {
            self.last_error_span = info.span;
            return error.UnknownSort;
        };
        return @intCast(sort_id);
    }

    fn mathTokenSpanInSource(
        self: *const MM0Parser,
        token_span: MathSpan,
    ) ?MathSpan {
        const math_span = self.last_math_span orelse return null;
        return .{
            .start = math_span.start + token_span.start,
            .end = math_span.start + token_span.end,
        };
    }

    fn recordMathParseFailure(self: *MM0Parser) void {
        if (self.last_error_span != null) return;

        if (self.last_math_error) |math_err| {
            switch (math_err) {
                .unknown_token, .unexpected_token => |token| {
                    self.last_error_span = self.mathTokenSpanInSource(
                        token.span,
                    ) orelse self.last_math_span;
                    return;
                },
                .unexpected_end => |pos| {
                    const math_span = self.last_math_span orelse return;
                    const end = math_span.start + @min(
                        pos,
                        math_span.end - math_span.start,
                    );
                    self.last_error_span = .{
                        .start = end,
                        .end = end,
                    };
                    return;
                },
            }
        }

        self.last_error_span = self.last_math_span;
    }

    // Returns next public statement, while processing notation and coercion
    // declarations so later math strings are parsed with the correct grammar.
    pub fn next(self: *MM0Parser) !?MM0Stmt {
        while (true) {
            self.resetDiagnosticContext();
            self.skipWhitespaceAndComments();
            if (self.pos >= self.src.len) return null;

            const word = self.peekIdent() orelse {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                self.recordCurrentTokenError();
                return error.UnexpectedChar;
            };

            if (std.mem.eql(u8, word, "pure") or
                std.mem.eql(u8, word, "strict") or
                std.mem.eql(u8, word, "provable") or
                std.mem.eql(u8, word, "free") or
                std.mem.eql(u8, word, "sort"))
            {
                self.flushAnnotations();
                const stmt = try self.parseSortStmt();
                return MM0Stmt{ .sort = stmt };
            }
            if (std.mem.eql(u8, word, "term")) {
                self.flushAnnotations();
                const stmt = try self.parseTermStmt(false);
                return MM0Stmt{ .term = stmt };
            }
            if (std.mem.eql(u8, word, "def")) {
                self.flushAnnotations();
                const stmt = try self.parseTermStmt(true);
                return MM0Stmt{ .term = stmt };
            }
            if (std.mem.eql(u8, word, "axiom")) {
                self.flushAnnotations();
                const stmt = try self.parseAssertionStmt(.axiom, false);
                return MM0Stmt{ .assertion = stmt };
            }
            if (std.mem.eql(u8, word, "theorem")) {
                self.flushAnnotations();
                const stmt = try self.parseAssertionStmt(.theorem, false);
                return MM0Stmt{ .assertion = stmt };
            }
            if (std.mem.eql(u8, word, "pub")) {
                _ = self.consumeIdent();
                self.skipWhitespaceAndComments();
                const next_word = self.peekIdent() orelse {
                    self.recordCurrentTokenError();
                    return error.ExpectedKeyword;
                };
                if (std.mem.eql(u8, next_word, "def")) {
                    self.flushAnnotations();
                    const stmt = try self.parseTermStmt(true);
                    return MM0Stmt{ .term = stmt };
                }
                if (std.mem.eql(u8, next_word, "theorem")) {
                    self.flushAnnotations();
                    const stmt = try self.parseAssertionStmt(.theorem, false);
                    return MM0Stmt{ .assertion = stmt };
                }
                self.recordCurrentTokenError();
                return error.UnexpectedKeyword;
            }
            // Non-public declarations: annotations don't attach to these
            if (std.mem.eql(u8, word, "local") or
                std.mem.eql(u8, word, "input") or
                std.mem.eql(u8, word, "output"))
            {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                try self.skipToSemicolon();
                continue;
            }
            if (std.mem.eql(u8, word, "delimiter")) {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                try self.parseDelimiterStmt();
                continue;
            }
            if (std.mem.eql(u8, word, "prefix")) {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                try self.parseSimpleNotationStmt(.prefix);
                continue;
            }
            if (std.mem.eql(u8, word, "infixl")) {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                try self.parseSimpleNotationStmt(.infixl);
                continue;
            }
            if (std.mem.eql(u8, word, "infixr")) {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                try self.parseSimpleNotationStmt(.infixr);
                continue;
            }
            if (std.mem.eql(u8, word, "notation")) {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                if (try self.parseBareNotationMarker()) continue;
                try self.parseGeneralNotationStmt();
                continue;
            }
            if (std.mem.eql(u8, word, "coercion")) {
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                try self.parseCoercionStmt();
                continue;
            }

            self.pending_annotations.clearRetainingCapacity();
            self.pending_annotation_spans.clearRetainingCapacity();
            self.recordCurrentTokenError();
            return error.UnexpectedKeyword;
        }
    }

    fn parseSortStmt(self: *MM0Parser) !SortStmt {
        var modifiers = Sort{};
        while (true) {
            self.skipWhitespaceAndComments();
            const word = self.peekIdent() orelse {
                self.recordCurrentTokenError();
                return error.ExpectedIdent;
            };
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
                const name_info = try self.consumeRequiredIdentInfo();
                self.recordNameContext(name_info);
                try self.expect(';');
                if (self.sort_names.contains(name_info.text)) {
                    self.last_error_span = name_info.span;
                    return error.DuplicateSort;
                }
                const sort_id = try self.nextSortId();
                try self.sort_names.put(name_info.text, sort_id);
                try self.sort_infos.append(self.allocator, modifiers);
                if (modifiers.provable) {
                    try self.registerProvableSort(sort_id);
                }
                return .{
                    .name = name_info.text,
                    .name_span = name_info.span,
                    .modifiers = modifiers,
                };
            } else {
                self.recordCurrentTokenError();
                return error.UnexpectedKeyword;
            }
        }
    }

    fn parseTermStmt(self: *MM0Parser, is_def: bool) !TermStmt {
        _ = self.consumeIdent();
        const name_info = try self.consumeRequiredIdentInfo();
        self.recordNameContext(name_info);

        var ctx = BinderContext.init(self.allocator);
        self.skipWhitespaceAndComments();
        try self.parseBinders(&ctx, .term);

        try self.expect(':');
        const ret_sort_name = try self.parseTermType(&ctx);
        const ret_sort = try self.lookupSortId(ret_sort_name);

        var body: ?*const Expr = null;
        self.skipWhitespaceAndComments();
        if (is_def and self.peek() == '=') {
            self.pos += 1;
            const math = try self.readMathString();
            const expr = try self.parseMathString(math, &ctx.vars);
            body = try self.coerceExpr(expr, ret_sort);
        }

        self.skipWhitespaceAndComments();
        try self.expect(';');

        const arg_slice = try ctx.arg_infos.toOwnedSlice(self.allocator);
        const arg_names = try ctx.arg_names.toOwnedSlice(self.allocator);
        const arg_exprs = try ctx.arg_exprs.toOwnedSlice(self.allocator);
        const term_id = try self.nextTermId();
        const term_args = try self.buildTermArgs(arg_slice);
        try self.terms.append(self.allocator, .{
            .args = term_args,
            .ret_sort = ret_sort,
        });
        try self.term_names.put(name_info.text, term_id);

        return .{
            .name = name_info.text,
            .name_span = name_info.span,
            .args = arg_slice,
            .arg_names = arg_names,
            .arg_exprs = arg_exprs,
            .dummy_args = try ctx.dummy_infos.toOwnedSlice(self.allocator),
            .dummy_exprs = try ctx.dummy_exprs.toOwnedSlice(self.allocator),
            .ret_sort_name = ret_sort_name,
            .is_def = is_def,
            .body = body,
        };
    }

    fn parseAssertionStmt(
        self: *MM0Parser,
        kind: AssertionKind,
        is_local: bool,
    ) !AssertionStmt {
        _ = self.consumeIdent();
        const name_info = try self.consumeRequiredIdentInfo();
        self.recordNameContext(name_info);

        var ctx = BinderContext.init(self.allocator);
        var hyps_rev: std.ArrayListUnmanaged(*const Expr) = .{};
        self.skipWhitespaceAndComments();
        try self.parseBindersWithHyps(&ctx, &hyps_rev, .assertion);

        try self.expect(':');
        const concl = try self.parseAssertionTail(&ctx, &hyps_rev);

        self.skipWhitespaceAndComments();
        if (self.peek() == '=') {
            try self.skipToSemicolon();
        } else {
            try self.expect(';');
        }

        return .{
            .name = name_info.text,
            .name_span = name_info.span,
            .args = try ctx.arg_infos.toOwnedSlice(self.allocator),
            .arg_names = try ctx.arg_names.toOwnedSlice(self.allocator),
            .arg_exprs = try ctx.arg_exprs.toOwnedSlice(self.allocator),
            .hyps = try hyps_rev.toOwnedSlice(self.allocator),
            .concl = concl,
            .kind = kind,
            .is_local = is_local,
        };
    }

    fn parseAssertionTail(
        self: *MM0Parser,
        ctx: *BinderContext,
        hyps_rev: *std.ArrayListUnmanaged(*const Expr),
    ) !*const Expr {
        while (true) {
            self.skipWhitespaceAndComments();
            if (self.peek() == '$') {
                const formula = try self.parseFormulaMathString(&ctx.vars);
                self.skipWhitespaceAndComments();
                if (self.peek() == '>') {
                    self.pos += 1;
                    try hyps_rev.append(self.allocator, formula);
                    continue;
                }
                return formula;
            }

            const arg = try self.parseSortExpr(ctx.bound_names.items);
            const expr = try self.makeVariable(arg.sort_name, arg.bound, arg.deps);
            try ctx.arg_infos.append(self.allocator, arg);
            try ctx.arg_names.append(self.allocator, null);
            try ctx.arg_exprs.append(self.allocator, expr);
            self.skipWhitespaceAndComments();
            if (self.peek() != '>') return error.ExpectedFormula;
            self.pos += 1;
        }
    }

    fn parseBinders(
        self: *MM0Parser,
        ctx: *BinderContext,
        kind: BinderKind,
    ) !void {
        var ignore_hyps: std.ArrayListUnmanaged(*const Expr) = .{};
        try self.parseBindersWithHyps(ctx, &ignore_hyps, kind);
        if (ignore_hyps.items.len != 0) return error.UnexpectedHypothesisBinder;
    }

    fn parseBindersWithHyps(
        self: *MM0Parser,
        ctx: *BinderContext,
        hyps_rev: *std.ArrayListUnmanaged(*const Expr),
        kind: BinderKind,
    ) !void {
        while (self.peek() == '(' or self.peek() == '{') {
            const is_bound = self.src[self.pos] == '{';
            const close: u8 = if (is_bound) '}' else ')';
            self.pos += 1;
            self.skipWhitespaceAndComments();

            var names: std.ArrayListUnmanaged([]const u8) = .{};
            var is_dummy_buf: std.ArrayListUnmanaged(bool) = .{};
            while (true) {
                self.skipWhitespaceAndComments();
                if (self.peek() == ':') break;
                const is_dummy = self.peek() == '.';
                if (is_dummy) self.pos += 1;
                const ident = try self.consumeRequiredIdent();
                try names.append(self.allocator, ident);
                try is_dummy_buf.append(self.allocator, is_dummy);
            }
            self.pos += 1;
            self.skipWhitespaceAndComments();

            if (!is_bound and kind == .assertion and self.peek() == '$') {
                const hyp = try self.parseFormulaMathString(&ctx.vars);
                self.skipWhitespaceAndComments();
                try self.expect(close);
                for (names.items, is_dummy_buf.items) |_, is_dummy| {
                    if (is_dummy) return error.DummyHypothesisBinder;
                    try hyps_rev.append(self.allocator, hyp);
                }
                self.skipWhitespaceAndComments();
                continue;
            }

            const arg = try self.parseBinderType(ctx.bound_names.items, is_bound);
            self.skipWhitespaceAndComments();
            try self.expect(close);

            for (names.items, is_dummy_buf.items) |name, is_dummy| {
                const treat_as_bound = is_bound or is_dummy;
                const actual_arg = if (treat_as_bound)
                    ArgInfo{
                        .sort_name = arg.sort_name,
                        .bound = true,
                        .deps = @as(u55, 1) << @intCast(ctx.bound_names.items.len),
                    }
                else
                    arg;
                const expr = try self.makeVariable(
                    actual_arg.sort_name,
                    actual_arg.bound,
                    actual_arg.deps,
                );
                if (treat_as_bound) {
                    try ctx.bound_names.append(self.allocator, name);
                }
                if (!std.mem.eql(u8, name, "_")) {
                    try ctx.vars.put(name, expr);
                }
                if (!is_dummy) {
                    try ctx.arg_infos.append(self.allocator, actual_arg);
                    const arg_name = if (std.mem.eql(u8, name, "_"))
                        null
                    else
                        name;
                    try ctx.arg_names.append(self.allocator, arg_name);
                    try ctx.arg_exprs.append(self.allocator, expr);
                } else {
                    try ctx.dummy_infos.append(self.allocator, actual_arg);
                    try ctx.dummy_exprs.append(self.allocator, expr);
                }
            }
            self.skipWhitespaceAndComments();
        }
    }

    fn parseBinderType(
        self: *MM0Parser,
        bound_names: []const []const u8,
        is_bound: bool,
    ) !ArgInfo {
        self.skipWhitespaceAndComments();
        const sort_info = try self.consumeRequiredIdentInfo();
        _ = try self.lookupSortIdInfo(sort_info);
        if (is_bound) {
            const bv_index = bound_names.len;
            return .{
                .sort_name = sort_info.text,
                .bound = true,
                .deps = @as(u55, 1) << @intCast(bv_index),
            };
        }

        var deps: u55 = 0;
        while (true) {
            self.skipWhitespaceAndComments();
            const ch = self.peek();
            if (ch == ')' or ch == '}' or ch == 0) break;
            const dep_name = self.consumeIdent() orelse break;
            deps |= self.lookupBoundDep(bound_names, dep_name);
        }
        return .{ .sort_name = sort_info.text, .bound = false, .deps = deps };
    }

    fn parseSortExpr(
        self: *MM0Parser,
        bound_names: []const []const u8,
    ) !ArgInfo {
        self.skipWhitespaceAndComments();
        const sort_info = try self.consumeRequiredIdentInfo();
        _ = try self.lookupSortIdInfo(sort_info);

        var deps: u55 = 0;
        while (true) {
            self.skipWhitespaceAndComments();
            const ch = self.peek();
            if (ch == '>' or ch == ';' or ch == '=' or ch == ')' or
                ch == '}' or ch == 0)
                break;
            const dep_name = try self.consumeRequiredIdent();
            deps |= self.lookupBoundDep(bound_names, dep_name);
        }

        return .{ .sort_name = sort_info.text, .bound = false, .deps = deps };
    }

    fn parseTermType(self: *MM0Parser, ctx: *BinderContext) ![]const u8 {
        var current = try self.parseSortExpr(ctx.bound_names.items);
        while (true) {
            self.skipWhitespaceAndComments();
            if (self.peek() != '>') break;
            self.pos += 1;
            const expr = try self.makeVariable(current.sort_name, current.bound, current.deps);
            try ctx.arg_infos.append(self.allocator, current);
            try ctx.arg_names.append(self.allocator, null);
            try ctx.arg_exprs.append(self.allocator, expr);
            current = try self.parseSortExpr(ctx.bound_names.items);
        }
        return current.sort_name;
    }

    fn parseDelimiterStmt(self: *MM0Parser) !void {
        _ = self.consumeIdent();
        const left_or_both = try self.readMathString();
        self.skipWhitespaceAndComments();
        if (self.peek() == ';') {
            try self.registerDelimiters(left_or_both, true, true);
            self.pos += 1;
            return;
        }
        const right = try self.readMathString();
        try self.registerDelimiters(left_or_both, true, false);
        try self.registerDelimiters(right, false, true);
        self.skipWhitespaceAndComments();
        try self.expect(';');
    }

    fn parseSimpleNotationStmt(
        self: *MM0Parser,
        kind: enum { prefix, infixl, infixr },
    ) !void {
        _ = self.consumeIdent();
        self.skipWhitespaceAndComments();
        const name_info = try self.consumeRequiredIdentInfo();
        const term_id = try self.lookupRecordedTermId(name_info);
        const term = self.terms.items[term_id];

        self.skipWhitespaceAndComments();
        try self.expect(':');
        const token = try self.readConstantToken();
        self.skipWhitespaceAndComments();
        const kw_info = try self.consumeRequiredIdentInfo();
        if (!std.mem.eql(u8, kw_info.text, "prec")) {
            self.last_error_span = kw_info.span;
            return error.ExpectedKeyword;
        }
        const prec = try self.parsePrecedence();
        self.skipWhitespaceAndComments();
        try self.expect(';');

        try self.registerTokenPrec(token, prec);

        switch (kind) {
            .prefix => {
                try self.registerLeadingToken(token);
                var lits: std.ArrayListUnmanaged(PrefixLit) = .{};
                if (term.args.len > 0) {
                    for (term.args, 0..) |_, idx| {
                        try lits.append(self.allocator, .{ .variable = .{
                            .arg_index = idx,
                            .prec = if (idx + 1 == term.args.len) prec else MAX_PRECEDENCE,
                        } });
                    }
                }
                try self.prefix_notations.put(token, .{
                    .term_id = term_id,
                    .prec = prec,
                    .lits = try lits.toOwnedSlice(self.allocator),
                });
            },
            .infixl, .infixr => {
                try self.registerInfixyToken(token);
                if (term.args.len != 2) return error.ExpectedBinaryOperator;
                if (prec >= MAX_PRECEDENCE - 1) {
                    return error.InfixPrecOutOfRange;
                }
                try self.registerInfixAssoc(prec, kind == .infixr);
                try self.infix_notations.put(token, .{
                    .term_id = term_id,
                    .prec = prec,
                    .right_assoc = kind == .infixr,
                });
            },
        }
    }

    fn parseBareNotationMarker(self: *MM0Parser) !bool {
        const saved_pos = self.pos;
        _ = self.consumeIdent();
        self.skipWhitespaceAndComments();
        if (self.peek() != '"') {
            self.pos = saved_pos;
            return false;
        }
        const token = try self.readQuotedString();
        self.skipWhitespaceAndComments();
        try self.expect(';');
        try self.formula_markers.put(token, {});
        return true;
    }

    fn parseGeneralNotationStmt(self: *MM0Parser) !void {
        _ = self.consumeIdent();
        self.skipWhitespaceAndComments();
        const name_info = try self.consumeRequiredIdentInfo();
        const term_id = try self.lookupRecordedTermId(name_info);
        const term = self.terms.items[term_id];
        var var_names = std.StringHashMap(usize).init(self.allocator);
        var arg_index: usize = 0;
        while (self.peek() == '(' or self.peek() == '{') {
            const is_bound = self.src[self.pos] == '{';
            const close: u8 = if (is_bound) '}' else ')';
            self.pos += 1;
            self.skipWhitespaceAndComments();

            var names: std.ArrayListUnmanaged([]const u8) = .{};
            while (true) {
                self.skipWhitespaceAndComments();
                if (self.peek() == ':') break;
                const dummy_start = self.pos;
                const is_dummy = self.peek() == '.';
                if (is_dummy) self.pos += 1;
                const ident_info = try self.consumeRequiredIdentInfo();
                if (is_dummy) {
                    self.last_error_span = .{
                        .start = dummy_start,
                        .end = ident_info.span.end,
                    };
                    return error.DummyNotationBinder;
                }
                if (std.mem.eql(u8, ident_info.text, "_")) {
                    self.last_error_span = ident_info.span;
                    return error.AnonymousNotationBinder;
                }
                try names.append(self.allocator, ident_info.text);
            }
            self.pos += 1;
            _ = try self.parseSortExpr(&.{});
            self.skipWhitespaceAndComments();
            try self.expect(close);
            for (names.items) |binder_name| {
                if (!std.mem.eql(u8, binder_name, "_")) {
                    try var_names.put(binder_name, arg_index);
                }
                arg_index += 1;
            }
        }

        self.skipWhitespaceAndComments();
        try self.expect(':');
        _ = try self.parseSortExpr(&.{});
        self.skipWhitespaceAndComments();
        try self.expect('=');

        if (arg_index != term.args.len) {
            return error.InvalidNotationVariables;
        }
        const arg_coverage = try self.allocator.alloc(bool, term.args.len);
        defer self.allocator.free(arg_coverage);
        @memset(arg_coverage, false);

        const first = try self.parsePrecConstant();
        // Only the first constant is a leading token. Later constants become
        // infixy only when they immediately follow a variable.
        try self.registerTokenPrec(first.token, first.prec);
        try self.registerLeadingToken(first.token);
        var lits: std.ArrayListUnmanaged(PrefixLit) = .{};
        var pending_var_index: ?usize = null;
        while (true) {
            self.skipWhitespaceAndComments();
            if (self.peek() == ';') break;
            if (self.peek() == '(') {
                const cnst = try self.parsePrecConstant();
                try self.registerTokenPrec(cnst.token, cnst.prec);
                try lits.append(self.allocator, .{ .constant = cnst.token });
                if (pending_var_index) |idx| {
                    if (cnst.prec >= MAX_PRECEDENCE - 1) {
                        return error.InfixPrecOutOfRange;
                    }
                    try self.registerInfixyToken(cnst.token);
                    lits.items[idx].variable.prec = cnst.prec + 1;
                    pending_var_index = null;
                }
            } else {
                const ident_info = try self.consumeRequiredIdentInfo();
                const mapped = var_names.get(ident_info.text) orelse {
                    self.last_error_span = ident_info.span;
                    return error.UnknownVariable;
                };
                if (mapped >= arg_coverage.len or arg_coverage[mapped]) {
                    self.last_error_span = ident_info.span;
                    return error.InvalidNotationVariables;
                }
                arg_coverage[mapped] = true;
                try lits.append(self.allocator, .{ .variable = .{
                    .arg_index = mapped,
                    .prec = MAX_PRECEDENCE,
                } });
                pending_var_index = lits.items.len - 1;
            }
        }
        if (pending_var_index) |idx| {
            lits.items[idx].variable.prec = first.prec;
        }
        for (arg_coverage) |seen| {
            if (!seen) {
                self.last_error_span = name_info.span;
                return error.InvalidNotationVariables;
            }
        }

        try self.expect(';');
        try self.prefix_notations.put(first.token, .{
            .term_id = term_id,
            .prec = first.prec,
            .lits = try lits.toOwnedSlice(self.allocator),
        });
    }

    fn parseCoercionStmt(self: *MM0Parser) !void {
        _ = self.consumeIdent();
        self.skipWhitespaceAndComments();
        const name_info = try self.consumeRequiredIdentInfo();
        const term_id = try self.lookupRecordedTermId(name_info);
        const term = self.terms.items[term_id];
        if (term.args.len != 1) return error.ExpectedUnaryOperator;

        self.skipWhitespaceAndComments();
        try self.expect(':');
        self.skipWhitespaceAndComments();
        const src_info = try self.consumeRequiredIdentInfo();
        const src = try self.lookupSortIdInfo(src_info);
        self.skipWhitespaceAndComments();
        try self.expect('>');
        self.skipWhitespaceAndComments();
        const dst_info = try self.consumeRequiredIdentInfo();
        const dst = try self.lookupSortIdInfo(dst_info);
        self.skipWhitespaceAndComments();
        try self.expect(';');

        try self.registerCoercion(src, dst, term_id);
    }

    pub fn parseAssertionText(
        self: *const MM0Parser,
        src: []const u8,
        kind: AssertionKind,
        is_local: bool,
    ) !AssertionStmt {
        var parser = self.*;
        parser.src = src;
        parser.pos = 0;
        parser.pending_annotations = .{};
        parser.pending_annotation_spans = .{};
        parser.last_annotations = &.{};
        parser.last_annotation_spans = &.{};
        parser.resetDiagnosticContext();
        const stmt = try parser.parseAssertionStmt(kind, is_local);
        parser.skipWhitespaceAndComments();
        if (parser.pos != parser.src.len) {
            return error.UnexpectedTrailingInput;
        }
        return stmt;
    }

    pub fn parseFormulaText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
    ) anyerror!*const Expr {
        const expr = try self.parseMathText(math, vars);
        return try self.coerceExprToProvable(expr);
    }

    pub fn parseArgText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
        arg: ArgInfo,
    ) anyerror!*const Expr {
        const expr = try self.parseMathText(math, vars);
        const sort = try self.lookupSortId(arg.sort_name);
        const coerced = try self.coerceExpr(expr, sort);
        // Match verifier semantics: bound params require bound exprs,
        // but regular params accept any expression (including bound vars).
        if (arg.bound and !coerced.bound()) return error.BoundnessMismatch;
        // Note: dep checking is deferred to the verifier which checks deps
        // relative to the theorem's own bound variables. The expression's deps
        // here are relative to the calling theorem's context, not the callee's.
        return coerced;
    }

    fn parseFormulaMathString(
        self: *MM0Parser,
        vars: *const std.StringHashMap(*const Expr),
    ) anyerror!*const Expr {
        const math = try self.readMathString();
        return try self.parseFormulaText(math, vars);
    }

    pub fn parseMathText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
    ) anyerror!*const Expr {
        return try self.parseMathString(math, vars);
    }

    fn parseMathString(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
    ) anyerror!*const Expr {
        var cursor = MathCursor{
            .src = math,
            .left_delims = self.left_delims,
            .right_delims = self.right_delims,
        };
        self.last_math_error = null;
        self.last_error_span = null;
        const expr = self.parseExpr(&cursor, vars, 0) catch |err| {
            self.recordMathParseFailure();
            return err;
        };
        if (cursor.peek()) |token| {
            self.last_error_span = self.mathTokenSpanInSource(
                token.span,
            ) orelse self.last_math_span;
            return error.TrailingMathTokens;
        }
        return expr;
    }

    fn parseExpr(
        self: *MM0Parser,
        cursor: *MathCursor,
        vars: *const std.StringHashMap(*const Expr),
        min_prec: u16,
    ) anyerror!*const Expr {
        var lhs = try self.parsePrefixExpr(cursor, vars, min_prec);
        while (true) {
            const token = cursor.peek() orelse break;
            const infix = self.infix_notations.get(token.text) orelse break;
            if (infix.prec < min_prec) break;
            _ = cursor.next();
            const rhs_prec = if (infix.right_assoc)
                infix.prec
            else
                try std.math.add(u16, infix.prec, 1);
            const rhs = try self.parseExpr(cursor, vars, rhs_prec);
            lhs = try self.applyTerm(infix.term_id, &.{ lhs, rhs });
        }
        return lhs;
    }

    fn parsePrefixExpr(
        self: *MM0Parser,
        cursor: *MathCursor,
        vars: *const std.StringHashMap(*const Expr),
        min_prec: u16,
    ) anyerror!*const Expr {
        const token = cursor.next() orelse {
            self.last_math_error = .{
                .unexpected_end = cursor.pos,
            };
            return error.ExpectedMathToken;
        };
        if (std.mem.eql(u8, token.text, "(")) {
            const expr = try self.parseExpr(cursor, vars, 0);
            const close = cursor.next() orelse {
                self.last_math_error = .{
                    .unexpected_end = cursor.pos,
                };
                return error.ExpectedCloseParen;
            };
            if (!std.mem.eql(u8, close.text, ")")) {
                self.last_math_error = .{
                    .unexpected_token = close,
                };
                return error.ExpectedCloseParen;
            }
            return expr;
        }

        if (vars.get(token.text)) |expr| return expr;

        if (self.formula_markers.contains(token.text)) {
            return try self.parsePrefixExpr(cursor, vars, min_prec);
        }

        if (self.prefix_notations.get(token.text)) |prefix| {
            if (prefix.prec < min_prec) {
                self.last_math_error = .{
                    .unexpected_token = token,
                };
                return error.PrecMismatch;
            }
            return try self.parsePrefixNotation(cursor, vars, prefix);
        }

        if (self.term_names.get(token.text)) |term_id| {
            const term = self.terms.items[term_id];
            if (term.args.len == 0) return try self.applyTerm(term_id, &.{});
            if (APP_PRECEDENCE < min_prec) {
                self.last_math_error = .{
                    .unexpected_token = token,
                };
                return error.PrecMismatch;
            }
            var args: std.ArrayListUnmanaged(*const Expr) = .{};
            for (term.args) |_| {
                const arg = try self.parseExpr(cursor, vars, MAX_PRECEDENCE);
                try args.append(self.allocator, arg);
            }
            return try self.applyTerm(term_id, args.items);
        }

        self.last_math_error = .{
            .unknown_token = token,
        };
        return error.UnknownMathToken;
    }

    fn parsePrefixNotation(
        self: *MM0Parser,
        cursor: *MathCursor,
        vars: *const std.StringHashMap(*const Expr),
        prefix: PrefixEnv,
    ) anyerror!*const Expr {
        const term = self.terms.items[prefix.term_id];
        const args = try self.allocator.alloc(?*const Expr, term.args.len);
        defer self.allocator.free(args);
        @memset(args, null);
        for (prefix.lits) |lit| {
            switch (lit) {
                .constant => |expected| {
                    const actual = cursor.next() orelse {
                        self.last_math_error = .{
                            .unexpected_end = cursor.pos,
                        };
                        return error.ExpectedMathToken;
                    };
                    if (!std.mem.eql(u8, actual.text, expected)) {
                        self.last_math_error = .{
                            .unexpected_token = actual,
                        };
                        return error.NotationMismatch;
                    }
                },
                .variable => |info| {
                    const parsed = try self.parseExpr(cursor, vars, info.prec);
                    if (info.arg_index >= args.len or args[info.arg_index] != null) {
                        self.last_error_span = self.last_math_span;
                        return error.InvalidNotationVariables;
                    }
                    args[info.arg_index] = parsed;
                },
            }
        }
        const filled_args = try self.allocator.alloc(*const Expr, term.args.len);
        defer self.allocator.free(filled_args);
        for (args, 0..) |arg, idx| {
            filled_args[idx] = arg orelse {
                self.last_error_span = self.last_math_span;
                return error.InvalidNotationVariables;
            };
        }
        return try self.applyTerm(prefix.term_id, filled_args);
    }

    fn applyTerm(
        self: *MM0Parser,
        term_id: u32,
        raw_args: []const *const Expr,
    ) anyerror!*const Expr {
        const term = self.terms.items[term_id];
        if (raw_args.len != term.args.len) return error.ArgCountMismatch;

        var args = try self.allocator.alloc(*const Expr, raw_args.len);
        var deps: u55 = 0;
        for (raw_args, term.args, 0..) |expr, arg, idx| {
            const coerced = try self.coerceExpr(expr, arg.sort);
            if (arg.bound and !coerced.bound()) {
                return error.BoundnessMismatch;
            }
            args[idx] = coerced;
            deps |= coerced.deps();
        }

        const node = try self.allocator.create(Expr);
        node.* = .{ .term = .{
            .sort = term.ret_sort,
            .deps = deps,
            .id = term_id,
            .args = args,
        } };
        return node;
    }

    fn coerceExpr(
        self: *MM0Parser,
        expr: *const Expr,
        target: u7,
    ) anyerror!*const Expr {
        return try self.followCoercionRoute(expr, target, error.SortMismatch);
    }

    fn coerceExprToProvable(
        self: *MM0Parser,
        expr: *const Expr,
    ) anyerror!*const Expr {
        return try self.followCoercionRoute(
            expr,
            PROV_COERCION_IDX,
            error.NotProvable,
        );
    }

    fn followCoercionRoute(
        self: *MM0Parser,
        expr: *const Expr,
        target_idx: usize,
        empty_err: anyerror,
    ) anyerror!*const Expr {
        // The table stores either a direct term application, a transitive
        // hop via another sort, or the special provable target slot.
        if (target_idx < MAX_SORTS and expr.sort() == target_idx) return expr;

        const row = &self.coercion_table[expr.sort()];
        const route = row[target_idx];
        switch (route.tag) {
            .empty => return empty_err,
            .prov => return expr,
            .one => return try self.applyTerm(route.data, &.{expr}),
            .trans => {
                const via: u7 = @intCast(route.data);
                const mid = try self.followCoercionRoute(expr, via, empty_err);
                return try self.followCoercionRoute(mid, target_idx, empty_err);
            },
        }
    }

    fn makeVariable(
        self: *MM0Parser,
        sort_name: []const u8,
        bound: bool,
        deps: u55,
    ) anyerror!*const Expr {
        const sort = try self.lookupSortId(sort_name);
        const expr = try self.allocator.create(Expr);
        expr.* = .{ .variable = .{ .sort = sort, .bound = bound, .deps = deps } };
        return expr;
    }

    fn buildTermArgs(self: *MM0Parser, infos: []const ArgInfo) ![]const Arg {
        const args = try self.allocator.alloc(Arg, infos.len);
        for (infos, 0..) |info, idx| {
            const sort = try self.lookupSortId(info.sort_name);
            args[idx] = .{ .deps = info.deps, .reserved = 0, .sort = sort, .bound = info.bound };
        }
        return args;
    }

    fn registerDelimiters(
        self: *MM0Parser,
        math: []const u8,
        set_left: bool,
        set_right: bool,
    ) !void {
        var pos: usize = 0;
        while (pos < math.len) {
            while (pos < math.len) : (pos += 1) {
                const ch = math[pos];
                if (ch != ' ' and ch != '\n' and ch != '\t' and ch != '\r') break;
            }
            if (pos >= math.len) break;
            const ch = math[pos];
            pos += 1;
            if (pos < math.len) {
                const next_ch = math[pos];
                if (next_ch != ' ' and next_ch != '\n' and next_ch != '\t' and next_ch != '\r') {
                    return error.MultiCharacterDelimiter;
                }
            }
            if (set_left) self.left_delims[ch] = true;
            if (set_right) self.right_delims[ch] = true;
        }
    }

    fn parsePrecConstant(self: *MM0Parser) !struct { token: []const u8, prec: u16 } {
        self.skipWhitespaceAndComments();
        try self.expect('(');
        const token = try self.readConstantToken();
        self.skipWhitespaceAndComments();
        try self.expect(':');
        const prec = try self.parsePrecedence();
        self.skipWhitespaceAndComments();
        try self.expect(')');
        return .{ .token = token, .prec = prec };
    }

    fn readConstantToken(self: *MM0Parser) ![]const u8 {
        const math = try self.readMathString();
        const trimmed = std.mem.trim(u8, math, " \n\t\r");
        if (trimmed.len == 0) return error.ExpectedMathToken;
        for (trimmed) |ch| {
            if (ch == ' ' or ch == '\n' or ch == '\t' or ch == '\r') {
                return error.ExpectedMathToken;
            }
        }
        if (std.mem.eql(u8, trimmed, "(") or std.mem.eql(u8, trimmed, ")")) {
            return error.InvalidNotationToken;
        }
        return trimmed;
    }

    fn parsePrecedence(self: *MM0Parser) !u16 {
        self.skipWhitespaceAndComments();
        const word = self.peekIdent();
        if (word) |ident| {
            if (std.mem.eql(u8, ident, "max")) {
                _ = self.consumeIdent();
                return MAX_PRECEDENCE;
            }
        }
        return try self.consumeNumber();
    }

    fn nextSortId(self: *MM0Parser) !u8 {
        if (self.sort_infos.items.len >= MAX_SORTS) return error.TooManySorts;
        return @intCast(self.sort_infos.items.len);
    }

    fn registerTokenPrec(self: *MM0Parser, token: []const u8, prec: u16) !void {
        if (self.token_precs.get(token)) |old_prec| {
            if (old_prec != prec) return error.PrecedenceMismatch;
            return;
        }
        try self.token_precs.put(token, prec);
    }

    fn registerInfixAssoc(
        self: *MM0Parser,
        prec: u16,
        right_assoc: bool,
    ) !void {
        if (self.infix_assoc.get(prec)) |old_assoc| {
            if (old_assoc != right_assoc) {
                return error.PrecedenceAssocMismatch;
            }
            return;
        }
        try self.infix_assoc.put(prec, right_assoc);
    }

    fn registerLeadingToken(self: *MM0Parser, token: []const u8) !void {
        // Spec rule: a notation's first token cannot also be used as a
        // prefix token or any infixy token.
        if (self.leading_tokens.contains(token) or
            self.infixy_tokens.contains(token))
        {
            return error.NotationFirstTokenConflict;
        }
        try self.leading_tokens.put(token, {});
    }

    fn registerInfixyToken(self: *MM0Parser, token: []const u8) !void {
        // Infixy tokens may be reused as infixy, but never as a notation's
        // first token.
        if (self.leading_tokens.contains(token)) {
            return error.NotationFirstTokenConflict;
        }
        if (self.infixy_tokens.contains(token)) return;
        try self.infixy_tokens.put(token, {});
    }

    fn registerProvableSort(self: *MM0Parser, sort_id: u8) !void {
        const direct = &self.coercion_table[sort_id][PROV_COERCION_IDX];
        if (direct.tag == .empty) {
            direct.* = .{ .tag = .prov };
        }
    }

    fn registerCoercion(
        self: *MM0Parser,
        src: u7,
        dst: u7,
        term_id: u32,
    ) !void {
        // Maintain the transitive closure incrementally. Every filled slot in
        // coercion_table[s][t] represents the unique route from s to t.
        var lhs: usize = 0;
        while (lhs < self.sort_infos.items.len) : (lhs += 1) {
            if (self.coercion_table[lhs][src].tag == .empty) continue;
            if (lhs == dst) return error.CoercionCycle;
            const route = &self.coercion_table[lhs][dst];
            if (route.tag != .empty) return error.CoercionDiamond;
            route.* = .{ .tag = .trans, .data = src };
        }

        if (src == dst) return error.CoercionCycle;
        const direct = &self.coercion_table[src][dst];
        if (direct.tag != .empty) return error.CoercionDiamond;
        direct.* = .{ .tag = .one, .data = term_id };

        var rhs: usize = 0;
        while (rhs < self.sort_infos.items.len) : (rhs += 1) {
            if (self.coercion_table[dst][rhs].tag == .empty) continue;
            if (src == rhs) return error.CoercionCycle;
            const route = &self.coercion_table[src][rhs];
            if (route.tag != .empty) return error.CoercionDiamond;
            route.* = .{ .tag = .trans, .data = dst };
        }

        if (self.coercion_table[dst][PROV_COERCION_IDX].tag != .empty) {
            const prov = &self.coercion_table[src][PROV_COERCION_IDX];
            if (prov.tag != .empty) return error.CoercionDiamondToProvable;
            prov.* = .{ .tag = .trans, .data = dst };
        }
    }

    fn lookupSortId(self: *MM0Parser, sort_name: []const u8) !u7 {
        const sort_id = self.sort_names.get(sort_name) orelse {
            return error.UnknownSort;
        };
        return @intCast(sort_id);
    }

    fn nextTermId(self: *MM0Parser) !u32 {
        return std.math.cast(u32, self.terms.items.len) orelse error.TooManyTerms;
    }

    fn lookupBoundDep(self: *MM0Parser, bound_names: []const []const u8, name: []const u8) u55 {
        _ = self;
        for (bound_names, 0..) |bound_name, idx| {
            if (std.mem.eql(u8, bound_name, name)) {
                return @as(u55, 1) << @intCast(idx);
            }
        }
        return 0;
    }

    fn readQuotedString(self: *MM0Parser) ![]const u8 {
        self.skipWhitespaceAndComments();
        if (self.peek() != '"') {
            self.recordCurrentTokenError();
            return error.ExpectedString;
        }
        const quote_start = self.pos;
        self.pos += 1;
        const start = self.pos;
        while (self.pos < self.src.len and self.src[self.pos] != '"') {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) {
            self.last_error_span = .{
                .start = quote_start,
                .end = self.src.len,
            };
            return error.UnterminatedString;
        }
        const text = self.src[start..self.pos];
        self.pos += 1;
        self.skipWhitespaceAndComments();
        return text;
    }

    fn readMathString(self: *MM0Parser) ![]const u8 {
        self.skipWhitespaceAndComments();
        if (self.peek() != '$') {
            self.recordCurrentTokenError();
            return error.ExpectedMathStr;
        }
        const dollar_start = self.pos;
        self.pos += 1;
        const start = self.pos;
        while (self.pos < self.src.len and self.src[self.pos] != '$') {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) {
            self.last_error_span = .{
                .start = dollar_start,
                .end = self.src.len,
            };
            return error.UnterminatedMathStr;
        }
        const math = self.src[start..self.pos];
        self.last_math_span = .{
            .start = start,
            .end = self.pos,
        };
        self.pos += 1;
        self.skipWhitespaceAndComments();
        return math;
    }

    fn peek(self: *MM0Parser) u8 {
        if (self.pos >= self.src.len) return 0;
        return self.src[self.pos];
    }

    fn peekIdent(self: *MM0Parser) ?[]const u8 {
        const start = self.pos;
        var end = start;
        if (end >= self.src.len or !isIdentStart(self.src[end])) return null;
        end += 1;
        while (end < self.src.len and isIdentChar(self.src[end])) end += 1;
        return self.src[start..end];
    }

    fn consumeIdent(self: *MM0Parser) ?[]const u8 {
        const ident = self.peekIdent() orelse return null;
        self.pos += ident.len;
        self.skipWhitespaceAndComments();
        return ident;
    }

    fn consumeNumber(self: *MM0Parser) !u16 {
        self.skipWhitespaceAndComments();
        const start = self.pos;
        if (self.pos >= self.src.len or !std.ascii.isDigit(self.src[self.pos])) {
            self.recordCurrentTokenError();
            return error.ExpectedNumber;
        }
        var value: u32 = 0;
        while (self.pos < self.src.len and std.ascii.isDigit(self.src[self.pos])) {
            value = value * 10 + (self.src[self.pos] - '0');
            if (value > std.math.maxInt(u16)) {
                self.last_error_span = .{
                    .start = start,
                    .end = self.pos + 1,
                };
                return error.NumberOutOfRange;
            }
            self.pos += 1;
        }
        self.skipWhitespaceAndComments();
        return @intCast(value);
    }

    fn expect(self: *MM0Parser, ch: u8) !void {
        if (self.peek() != ch) {
            self.recordCurrentTokenError();
            return error.UnexpectedChar;
        }
        self.pos += 1;
        self.skipWhitespaceAndComments();
    }

    fn skipWhitespaceAndComments(self: *MM0Parser) void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r') {
                self.pos += 1;
            } else if (ch == '-' and
                self.pos + 1 < self.src.len and
                self.src[self.pos + 1] == '-')
            {
                self.pos += 2;
                // Check for annotation marker `--|`
                if (self.pos < self.src.len and self.src[self.pos] == '|') {
                    self.pos += 1;
                    // Skip leading whitespace after `--|`
                    while (self.pos < self.src.len and
                        (self.src[self.pos] == ' ' or
                            self.src[self.pos] == '\t'))
                    {
                        self.pos += 1;
                    }
                    const start = self.pos;
                    while (self.pos < self.src.len and
                        self.src[self.pos] != '\n')
                    {
                        self.pos += 1;
                    }
                    // Trim trailing whitespace
                    var end = self.pos;
                    while (end > start and
                        (self.src[end - 1] == ' ' or
                            self.src[end - 1] == '\t' or
                            self.src[end - 1] == '\r'))
                    {
                        end -= 1;
                    }
                    if (end > start) {
                        self.pending_annotations.append(
                            self.allocator,
                            self.src[start..end],
                        ) catch {};
                        self.pending_annotation_spans.append(
                            self.allocator,
                            .{ .start = start, .end = end },
                        ) catch {};
                    }
                } else {
                    while (self.pos < self.src.len and
                        self.src[self.pos] != '\n')
                    {
                        self.pos += 1;
                    }
                }
            } else break;
        }
    }

    fn skipToSemicolon(self: *MM0Parser) !void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            self.pos += 1;
            if (ch == '$') {
                const dollar_start = self.pos - 1;
                while (self.pos < self.src.len and self.src[self.pos] != '$') {
                    self.pos += 1;
                }
                if (self.pos >= self.src.len) {
                    self.last_error_span = .{
                        .start = dollar_start,
                        .end = self.src.len,
                    };
                    return error.UnterminatedMathStr;
                }
                self.pos += 1;
            } else if (ch == ';') {
                self.skipWhitespaceAndComments();
                return;
            }
        }
        self.last_error_span = self.currentTokenSpan();
        return error.UnexpectedEOF;
    }
};

fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
