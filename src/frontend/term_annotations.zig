const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const TermStmt = @import("../trusted/parse.zig").TermStmt;

pub fn processTermAnnotations(
    env: *GlobalEnv,
    stmt: TermStmt,
    annotations: []const []const u8,
) !void {
    const term_id = env.term_names.get(stmt.name) orelse return;
    const term = &env.terms.items[term_id];

    for (annotations) |ann| {
        if (!std.mem.eql(u8, ann, "@abbrev")) continue;
        if (!stmt.is_def) return error.AbbrevOnNonDef;
        term.is_abbrev = true;
    }
}
