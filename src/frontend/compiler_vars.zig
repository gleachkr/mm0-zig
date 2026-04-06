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

pub fn processSortVarAnnotations(
    parser: *const MM0Parser,
    sort_name: []const u8,
    sort_modifiers: Sort,
    annotations: []const []const u8,
    sort_vars: *std.StringHashMap(SortVarDecl),
) !void {
    const vars_tag = "@vars";

    for (annotations) |ann| {
        if (!std.mem.startsWith(u8, ann, vars_tag)) continue;
        if (ann.len > vars_tag.len and !isAsciiWhitespace(ann[vars_tag.len])) {
            continue;
        }

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
            if (sort_vars.contains(token)) return error.DuplicateVarsToken;
            try sort_vars.put(token, .{
                .sort_name = sort_name,
                .sort_id = sort_id,
            });
        }
    }
}

pub fn validateSortVarCollisions(
    parser: *const MM0Parser,
    sort_vars: *const std.StringHashMap(SortVarDecl),
) !void {
    var iter = sort_vars.iterator();
    while (iter.next()) |entry| {
        try validateTokenHasNoSyntaxCollision(parser, entry.key_ptr.*);
    }
}

pub fn ensureMathTextVars(
    parser: *const MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const std.StringHashMap(SortVarDecl),
    math: []const u8,
) !void {
    if (sort_vars.count() == 0) return;

    var pos: usize = 0;
    while (nextMathToken(math, &pos, parser.left_delims, parser.right_delims)) |token| {
        if (theorem_vars.contains(token)) continue;
        if (hasSyntaxCollision(parser, token)) continue;

        if (sort_vars.get(token)) |decl| {
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
