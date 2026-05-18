const std = @import("std");

const RuleDecl = @import("../env.zig").RuleDecl;

pub fn annotationMatchesTag(ann: []const u8, tag: []const u8) bool {
    if (!std.mem.startsWith(u8, ann, tag)) return false;
    if (ann.len == tag.len) return true;
    return isAsciiWhitespace(ann[tag.len]);
}

pub fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}

pub fn isAsciiWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r';
}

pub fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

pub fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
