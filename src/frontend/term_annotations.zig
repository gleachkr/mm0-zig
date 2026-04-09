const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const TermStmt = @import("../trusted/parse.zig").TermStmt;

pub fn processTermAnnotations(
    env: *GlobalEnv,
    stmt: TermStmt,
    annotations: []const []const u8,
) !void {
    _ = env;
    _ = stmt;

    for (annotations) |ann| {
        const directive = annotationDirective(ann) orelse continue;
        if (std.mem.eql(u8, directive, "@acui")) continue;
        return error.UnknownTermAnnotation;
    }
}

fn annotationDirective(ann: []const u8) ?[]const u8 {
    if (ann.len == 0 or ann[0] != '@') return null;

    var iter = std.mem.tokenizeAny(u8, ann, " \t\r\n");
    return iter.next();
}
