const std = @import("std");
const GlobalEnv = @import("../compiler_env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const CompilerFresh = @import("../compiler_fresh.zig");
const CompilerViews = @import("../compiler_views.zig");
const CompilerVars = @import("../compiler_vars.zig");
const TermAnnotations = @import("../term_annotations.zig");
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const SortStmt = @import("../../trusted/parse.zig").SortStmt;
const TermStmt = @import("../../trusted/parse.zig").TermStmt;

pub const ViewDecl = CompilerViews.ViewDecl;
pub const FreshDecl = CompilerFresh.FreshDecl;
pub const SortVarDecl = CompilerVars.SortVarDecl;
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

pub fn processSortMetadata(
    parser: *const MM0Parser,
    sort_stmt: SortStmt,
    annotations: []const []const u8,
    sort_vars: *SortVarRegistry,
) !void {
    try CompilerVars.processSortVarAnnotations(
        parser,
        sort_stmt.name,
        sort_stmt.modifiers,
        annotations,
        sort_vars,
    );
}

pub fn processTermMetadata(
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    term_stmt: TermStmt,
    annotations: []const []const u8,
) !void {
    try TermAnnotations.processTermAnnotations(
        env,
        term_stmt,
        annotations,
    );
    try registry.processAnnotations(env, term_stmt.name, annotations);
}

pub fn processAssertionMetadata(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    annotations: []const []const u8,
) !void {
    try registry.processAnnotations(env, assertion.name, annotations);
    try CompilerFresh.processFreshAnnotations(
        allocator,
        parser,
        env,
        assertion,
        fresh_bindings,
        annotations,
    );
    try CompilerViews.processViewAnnotations(
        allocator,
        parser,
        env,
        assertion,
        annotations,
        views,
    );
}
