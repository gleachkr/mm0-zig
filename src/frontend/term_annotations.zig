const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const TermStmt = @import("../trusted/parse.zig").TermStmt;

pub fn processTermAnnotations(
    env: *GlobalEnv,
    stmt: TermStmt,
    annotations: []const []const u8,
) !void {
    _ = env;
    _ = stmt;
    _ = annotations;
}
