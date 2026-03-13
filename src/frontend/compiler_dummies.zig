const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;

pub const DummyDecl = struct {
    target_arg_idx: usize,
};

pub fn processDummyAnnotations(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    assertion: AssertionStmt,
    annotations: []const []const u8,
    dummies: *std.AutoHashMap(u32, []const DummyDecl),
) !void {
    const rule_id = env.getRuleId(assertion.name) orelse return;
    const rule = &env.rules.items[rule_id];
    const dummy_prefix = "@dummy ";

    var decls = std.ArrayListUnmanaged(DummyDecl){};
    defer decls.deinit(allocator);

    for (annotations) |ann| {
        if (!std.mem.startsWith(u8, ann, dummy_prefix)) continue;
        const decl = try parseDummyAnnotation(
            parser,
            rule,
            ann[dummy_prefix.len..],
        );
        for (decls.items) |existing| {
            if (existing.target_arg_idx == decl.target_arg_idx) {
                return error.DuplicateDummyBinder;
            }
        }
        try decls.append(allocator, decl);
    }

    if (decls.items.len == 0) return;
    try dummies.put(rule_id, try decls.toOwnedSlice(allocator));
}

fn parseDummyAnnotation(
    parser: *const MM0Parser,
    rule: *const RuleDecl,
    text: []const u8,
) !DummyDecl {
    const trimmed = std.mem.trim(u8, text, " \t\r\n;");
    if (trimmed.len == 0) return error.InvalidDummyAnnotation;
    if (!isIdentStart(trimmed[0])) return error.InvalidDummyAnnotation;

    var name_end: usize = 1;
    while (name_end < trimmed.len and isIdentChar(trimmed[name_end])) {
        name_end += 1;
    }
    if (std.mem.trim(u8, trimmed[name_end..], " \t\r\n").len != 0) {
        return error.InvalidDummyAnnotation;
    }

    const name = trimmed[0..name_end];
    const target_arg_idx = findRuleArgIndex(rule, name) orelse {
        return error.UnknownDummyBinder;
    };
    if (!rule.args[target_arg_idx].bound) {
        return error.DummyRequiresBoundBinder;
    }

    const sort_name = rule.args[target_arg_idx].sort_name;
    const sort_id = parser.sort_names.get(sort_name) orelse {
        return error.UnknownSort;
    };
    const sort = parser.sort_infos.items[sort_id];
    if (sort.strict) return error.DummyStrictSort;
    if (sort.free) return error.DummyFreeSort;

    return .{ .target_arg_idx = target_arg_idx };
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}

fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
