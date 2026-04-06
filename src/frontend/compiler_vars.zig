const std = @import("std");
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const Expr = @import("../trusted/expressions.zig").Expr;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const Sort = @import("../trusted/sorts.zig").Sort;

const NameExprMap = std.StringHashMap(*const Expr);

pub const SortVarDecl = struct {
    sort_name: []const u8,
    sort_id: u8,
};

pub const SortVarPool = struct {
    sort_name: []const u8,
    sort_id: u8,
    tokens: std.ArrayListUnmanaged([]const u8) = .{},

    pub fn deinit(
        self: *SortVarPool,
        allocator: std.mem.Allocator,
    ) void {
        self.tokens.deinit(allocator);
    }
};

pub const SortVarRegistry = struct {
    allocator: std.mem.Allocator,
    tokens: std.StringHashMap(SortVarDecl),
    pools: std.StringHashMap(SortVarPool),

    pub fn init(allocator: std.mem.Allocator) SortVarRegistry {
        return .{
            .allocator = allocator,
            .tokens = std.StringHashMap(SortVarDecl).init(allocator),
            .pools = std.StringHashMap(SortVarPool).init(allocator),
        };
    }

    pub fn deinit(self: *SortVarRegistry) void {
        var pool_iter = self.pools.valueIterator();
        while (pool_iter.next()) |pool| {
            pool.deinit(self.allocator);
        }
        self.pools.deinit();
        self.tokens.deinit();
    }

    pub fn count(self: *const SortVarRegistry) usize {
        return self.tokens.count();
    }

    pub fn getTokenDecl(
        self: *const SortVarRegistry,
        token: []const u8,
    ) ?SortVarDecl {
        return self.tokens.get(token);
    }

    pub fn getPool(
        self: *const SortVarRegistry,
        sort_name: []const u8,
    ) ?SortVarPool {
        return self.pools.get(sort_name);
    }

    fn append(
        self: *SortVarRegistry,
        token: []const u8,
        decl: SortVarDecl,
    ) !void {
        try self.tokens.put(token, decl);
        const gop = try self.pools.getOrPut(decl.sort_name);
        if (!gop.found_existing) {
            gop.value_ptr.* = .{
                .sort_name = decl.sort_name,
                .sort_id = decl.sort_id,
            };
        }
        try gop.value_ptr.tokens.append(self.allocator, token);
    }
};

pub fn processSortVarAnnotations(
    parser: *const MM0Parser,
    sort_name: []const u8,
    sort_modifiers: Sort,
    annotations: []const []const u8,
    sort_vars: *SortVarRegistry,
) !void {
    const vars_tag = "@vars";

    for (annotations) |ann| {
        if (!annotationMatchesTag(ann, vars_tag)) continue;

        if (sort_modifiers.strict) return error.VarsStrictSort;
        if (sort_modifiers.free) return error.VarsFreeSort;

        const sort_id = parser.sort_names.get(sort_name) orelse {
            return error.UnknownSort;
        };

        const tail = std.mem.trim(u8, ann[vars_tag.len..], " \t\r\n");
        if (tail.len == 0) return error.InvalidVarsAnnotation;

        var iter = std.mem.tokenizeAny(u8, tail, " \t\r\n");
        while (iter.next()) |token| {
            try validateTokenHasNoSyntaxCollision(parser, token);
            if (sort_vars.getTokenDecl(token) != null) {
                return error.DuplicateVarsToken;
            }
            try sort_vars.append(token, .{
                .sort_name = sort_name,
                .sort_id = sort_id,
            });
        }
    }
}

pub fn validateSortVarCollisions(
    parser: *const MM0Parser,
    sort_vars: *const SortVarRegistry,
) !void {
    var iter = sort_vars.tokens.iterator();
    while (iter.next()) |entry| {
        try validateTokenHasNoSyntaxCollision(parser, entry.key_ptr.*);
    }
}

pub fn ensureMathTextVars(
    parser: *const MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    math: []const u8,
) !void {
    if (sort_vars.count() == 0) return;

    var pos: usize = 0;
    while (nextMathToken(
        math,
        &pos,
        parser.left_delims,
        parser.right_delims,
    )) |token| {
        if (theorem_vars.contains(token)) continue;
        if (hasSyntaxCollision(parser, token)) continue;

        if (sort_vars.getTokenDecl(token)) |decl| {
            try theorem.ensureNamedDummyParserVar(
                parser.allocator,
                theorem_vars,
                token,
                decl.sort_name,
                decl.sort_id,
            );
        }
    }
}

fn annotationMatchesTag(ann: []const u8, tag: []const u8) bool {
    if (!std.mem.startsWith(u8, ann, tag)) return false;
    if (ann.len == tag.len) return true;
    return isAsciiWhitespace(ann[tag.len]);
}

fn validateTokenHasNoSyntaxCollision(
    parser: *const MM0Parser,
    token: []const u8,
) !void {
    if (hasSyntaxCollision(parser, token)) return error.VarsTokenCollision;
}

fn hasSyntaxCollision(parser: *const MM0Parser, token: []const u8) bool {
    return parser.term_names.contains(token) or
        parser.formula_markers.contains(token) or
        parser.prefix_notations.contains(token) or
        parser.infix_notations.contains(token);
}

fn isAsciiWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r';
}

fn nextMathToken(
    src: []const u8,
    pos: *usize,
    left_delims: [256]bool,
    right_delims: [256]bool,
) ?[]const u8 {
    while (pos.* < src.len) {
        const ch = src[pos.*];
        if (isAsciiWhitespace(ch)) {
            pos.* += 1;
        } else break;
    }
    if (pos.* >= src.len) return null;

    const start = pos.*;
    while (pos.* < src.len) {
        const ch = src[pos.*];
        pos.* += 1;
        if (left_delims[ch]) break;
        if (pos.* >= src.len) break;

        const next_ch = src[pos.*];
        if (isAsciiWhitespace(next_ch) or right_delims[next_ch]) break;
    }

    return src[start..pos.*];
}
