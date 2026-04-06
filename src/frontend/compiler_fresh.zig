const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;

pub const FreshDecl = struct {
    target_arg_idx: usize,
};

pub fn processFreshAnnotations(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    assertion: AssertionStmt,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    annotations: []const []const u8,
) !void {
    const rule_id = env.getRuleId(assertion.name) orelse return;
    const rule = &env.rules.items[rule_id];

    var decls = std.ArrayListUnmanaged(FreshDecl){};
    defer decls.deinit(allocator);

    for (annotations) |ann| {
        if (annotationMatchesTag(ann, "@dummy")) {
            return error.DummyAnnotationRemoved;
        }
        if (!annotationMatchesTag(ann, "@fresh")) continue;

        const decl = try parseFreshAnnotation(
            parser,
            rule,
            ann["@fresh".len..],
        );

        for (decls.items) |existing| {
            if (existing.target_arg_idx == decl.target_arg_idx) {
                return error.DuplicateFreshBinder;
            }
        }
        try decls.append(allocator, decl);
    }

    if (decls.items.len == 0) return;
    try fresh_bindings.put(rule_id, try decls.toOwnedSlice(allocator));
}

fn parseFreshAnnotation(
    parser: *const MM0Parser,
    rule: *const RuleDecl,
    text: []const u8,
) !FreshDecl {
    const trimmed = std.mem.trim(u8, text, " \t\r\n;");
    if (trimmed.len == 0) return error.InvalidFreshAnnotation;
    if (!isIdentStart(trimmed[0])) return error.InvalidFreshAnnotation;

    var name_end: usize = 1;
    while (name_end < trimmed.len and isIdentChar(trimmed[name_end])) {
        name_end += 1;
    }
    if (std.mem.trim(u8, trimmed[name_end..], " \t\r\n").len != 0) {
        return error.InvalidFreshAnnotation;
    }

    const name = trimmed[0..name_end];
    const target_arg_idx = findRuleArgIndex(rule, name) orelse {
        return error.UnknownFreshBinder;
    };
    if (!rule.args[target_arg_idx].bound) {
        return error.FreshRequiresBoundBinder;
    }

    const sort_name = rule.args[target_arg_idx].sort_name;
    const sort_id = parser.sort_names.get(sort_name) orelse {
        return error.UnknownSort;
    };
    const sort = parser.sort_infos.items[sort_id];
    if (sort.strict) return error.FreshStrictSort;
    if (sort.free) return error.FreshFreeSort;

    return .{
        .target_arg_idx = target_arg_idx,
    };
}

fn annotationMatchesTag(ann: []const u8, tag: []const u8) bool {
    if (!std.mem.startsWith(u8, ann, tag)) return false;
    if (ann.len == tag.len) return true;
    return isAsciiWhitespace(ann[tag.len]);
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}

fn isAsciiWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r';
}

fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
