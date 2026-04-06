const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;

pub const DummyMode = enum {
    dummy,
    fresh,
};

pub const DummyDecl = struct {
    target_arg_idx: usize,
    mode: DummyMode,
};

pub fn processDummyAnnotations(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    assertion: AssertionStmt,
    dummies: *std.AutoHashMap(u32, []const DummyDecl),
    annotations: []const []const u8,
) !void {
    const rule_id = env.getRuleId(assertion.name) orelse return;
    const rule = &env.rules.items[rule_id];

    var decls = std.ArrayListUnmanaged(DummyDecl){};
    defer decls.deinit(allocator);

    for (annotations) |ann| {
        const decl = if (annotationMatchesTag(ann, "@dummy"))
            try parseBinderAnnotation(
                parser,
                rule,
                ann["@dummy".len..],
                .dummy,
            )
        else if (annotationMatchesTag(ann, "@fresh"))
            try parseBinderAnnotation(
                parser,
                rule,
                ann["@fresh".len..],
                .fresh,
            )
        else
            continue;

        for (decls.items) |existing| {
            if (existing.target_arg_idx != decl.target_arg_idx) continue;
            if (existing.mode == decl.mode) {
                return switch (decl.mode) {
                    .dummy => error.DuplicateDummyBinder,
                    .fresh => error.DuplicateFreshBinder,
                };
            }
            return error.ConflictingDummyStrategy;
        }
        try decls.append(allocator, decl);
    }

    if (decls.items.len == 0) return;
    try dummies.put(rule_id, try decls.toOwnedSlice(allocator));
}

fn parseBinderAnnotation(
    parser: *const MM0Parser,
    rule: *const RuleDecl,
    text: []const u8,
    mode: DummyMode,
) !DummyDecl {
    const trimmed = std.mem.trim(u8, text, " \t\r\n;");
    if (trimmed.len == 0) return invalidAnnotation(mode);
    if (!isIdentStart(trimmed[0])) return invalidAnnotation(mode);

    var name_end: usize = 1;
    while (name_end < trimmed.len and isIdentChar(trimmed[name_end])) {
        name_end += 1;
    }
    if (std.mem.trim(u8, trimmed[name_end..], " \t\r\n").len != 0) {
        return invalidAnnotation(mode);
    }

    const name = trimmed[0..name_end];
    const target_arg_idx = findRuleArgIndex(rule, name) orelse {
        return unknownBinder(mode);
    };
    if (!rule.args[target_arg_idx].bound) {
        return requiresBoundBinder(mode);
    }

    const sort_name = rule.args[target_arg_idx].sort_name;
    const sort_id = parser.sort_names.get(sort_name) orelse {
        return error.UnknownSort;
    };
    const sort = parser.sort_infos.items[sort_id];
    if (sort.strict) return strictSort(mode);
    if (sort.free) return freeSort(mode);

    return .{
        .target_arg_idx = target_arg_idx,
        .mode = mode,
    };
}

fn annotationMatchesTag(ann: []const u8, tag: []const u8) bool {
    if (!std.mem.startsWith(u8, ann, tag)) return false;
    if (ann.len == tag.len) return true;
    return isAsciiWhitespace(ann[tag.len]);
}

fn invalidAnnotation(mode: DummyMode) anyerror {
    return switch (mode) {
        .dummy => error.InvalidDummyAnnotation,
        .fresh => error.InvalidFreshAnnotation,
    };
}

fn unknownBinder(mode: DummyMode) anyerror {
    return switch (mode) {
        .dummy => error.UnknownDummyBinder,
        .fresh => error.UnknownFreshBinder,
    };
}

fn requiresBoundBinder(mode: DummyMode) anyerror {
    return switch (mode) {
        .dummy => error.DummyRequiresBoundBinder,
        .fresh => error.FreshRequiresBoundBinder,
    };
}

fn strictSort(mode: DummyMode) anyerror {
    return switch (mode) {
        .dummy => error.DummyStrictSort,
        .fresh => error.FreshStrictSort,
    };
}

fn freeSort(mode: DummyMode) anyerror {
    return switch (mode) {
        .dummy => error.DummyFreeSort,
        .fresh => error.FreshFreeSort,
    };
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
