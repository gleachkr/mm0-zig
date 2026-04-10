const std = @import("std");

const CompilerFresh = @import("../frontend/compiler/fresh.zig");
const CompilerVars = @import("../frontend/compiler/vars.zig");
const FrontendEnv = @import("../frontend/env.zig");
const FrontendExpr = @import("../frontend/expr.zig");
const DerivedBinding =
    @import("../frontend/derived_bindings.zig").DerivedBinding;
const DefOps = @import("../frontend/def_ops.zig");
const Expr = @import("../trusted/expressions.zig").Expr;
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;

const FreshFixture = struct {
    arena: std.heap.ArenaAllocator,
    parser: MM0Parser,
    env: FrontendEnv.GlobalEnv,
    theorem: FrontendExpr.TheoremContext,
    theorem_vars: std.StringHashMap(*const Expr),
    sort_vars: CompilerVars.SortVarRegistry,

    fn deinit(self: *FreshFixture) void {
        self.sort_vars.deinit();
        self.theorem_vars.deinit();
        self.theorem.deinit();
        self.arena.deinit();
    }

    fn ensureDummyToken(self: *FreshFixture, token: []const u8) !void {
        const decl = self.sort_vars.getTokenDecl(token) orelse {
            return error.MissingSortVarToken;
        };
        try self.theorem.ensureNamedDummyParserVar(
            self.parser.allocator,
            &self.theorem_vars,
            token,
            decl.sort_name,
            decl.sort_id,
        );
    }

    fn exprIdForToken(
        self: *FreshFixture,
        token: []const u8,
    ) !FrontendExpr.ExprId {
        const parser_expr = self.theorem_vars.get(token) orelse {
            return error.MissingTheoremVar;
        };
        const var_id = self.theorem.parser_vars.get(parser_expr) orelse {
            return error.UnknownTheoremVariable;
        };
        return self.theorem.interner.internVar(var_id);
    }

    fn depsForToken(self: *FreshFixture, token: []const u8) !u55 {
        const parser_expr = self.theorem_vars.get(token) orelse {
            return error.MissingTheoremVar;
        };
        const var_id = self.theorem.parser_vars.get(parser_expr) orelse {
            return error.UnknownTheoremVariable;
        };
        return switch (var_id) {
            .dummy_var => |dummy_id| self.theorem.theorem_dummies.items[
                dummy_id
            ].deps,
            .theorem_var => error.ExpectedDummyVar,
        };
    }

    fn internFormula(
        self: *FreshFixture,
        text: []const u8,
    ) !FrontendExpr.ExprId {
        const parsed = try self.parser.parseFormulaText(
            text,
            &self.theorem_vars,
        );
        return self.theorem.internParsedExpr(parsed);
    }
};

fn buildFreshFixture(src: []const u8) !FreshFixture {
    var fixture = FreshFixture{
        .arena = std.heap.ArenaAllocator.init(std.testing.allocator),
        .parser = undefined,
        .env = undefined,
        .theorem = undefined,
        .theorem_vars = undefined,
        .sort_vars = undefined,
    };
    errdefer fixture.deinit();

    fixture.parser = MM0Parser.init(src, fixture.arena.allocator());
    fixture.env = FrontendEnv.GlobalEnv.init(fixture.arena.allocator());
    fixture.theorem = FrontendExpr.TheoremContext.init(
        fixture.arena.allocator(),
    );
    fixture.theorem_vars = std.StringHashMap(*const Expr).init(
        fixture.arena.allocator(),
    );
    fixture.sort_vars = CompilerVars.SortVarRegistry.init(
        fixture.arena.allocator(),
    );

    var theorem_stmt: ?AssertionStmt = null;
    while (try fixture.parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| try CompilerVars.processSortVarAnnotations(
                &fixture.parser,
                sort_stmt.name,
                sort_stmt.modifiers,
                fixture.parser.last_annotations,
                &fixture.sort_vars,
            ),
            .assertion => |assertion| {
                if (assertion.kind == .theorem and
                    std.mem.eql(u8, assertion.name, "fresh_target"))
                {
                    theorem_stmt = assertion;
                }
            },
            else => {},
        }
        try fixture.env.addStmt(stmt);
    }

    const assertion = theorem_stmt orelse return error.MissingAssertion;
    try fixture.theorem.seedAssertion(assertion);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try fixture.theorem_vars.put(actual_name, expr);
        }
    }
    return fixture;
}

test "fresh helper reuses existing theorem-local vars" {
    const src =
        \\--| @vars x y
        \\provable sort wff;
        \\term top: wff;
        \\theorem fresh_target: $ top $;
    ;

    var fixture = try buildFreshFixture(src);
    defer fixture.deinit();

    try fixture.ensureDummyToken("x");
    const line_expr = try fixture.internFormula(" top ");
    const assignments = try CompilerFresh.assignHiddenRootsFromVarsPool(
        std.testing.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.theorem,
        &fixture.theorem_vars,
        &fixture.sort_vars,
        line_expr,
        &[_]FrontendExpr.ExprId{},
        &[_]?FrontendExpr.ExprId{},
        0,
        &[_]CompilerFresh.HiddenRootNeed{
            .{ .root_slot = 7, .sort_name = "wff" },
        },
    );
    defer std.testing.allocator.free(assignments);

    try std.testing.expectEqual(@as(usize, 1), assignments.len);
    try std.testing.expectEqual(@as(usize, 7), assignments[0].root_slot);
    try std.testing.expectEqual(
        try fixture.exprIdForToken("x"),
        assignments[0].expr_id,
    );
    try std.testing.expectEqual(
        try fixture.depsForToken("x"),
        assignments[0].deps,
    );
    try std.testing.expect(fixture.theorem_vars.get("y") == null);
}

test "fresh helper lazily allocates from the vars pool" {
    const src =
        \\--| @vars x y
        \\provable sort wff;
        \\term top: wff;
        \\theorem fresh_target: $ top $;
    ;

    var fixture = try buildFreshFixture(src);
    defer fixture.deinit();

    const line_expr = try fixture.internFormula(" top ");
    const assignments = try CompilerFresh.assignHiddenRootsFromVarsPool(
        std.testing.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.theorem,
        &fixture.theorem_vars,
        &fixture.sort_vars,
        line_expr,
        &[_]FrontendExpr.ExprId{},
        &[_]?FrontendExpr.ExprId{},
        0,
        &[_]CompilerFresh.HiddenRootNeed{
            .{ .root_slot = 3, .sort_name = "wff" },
        },
    );
    defer std.testing.allocator.free(assignments);

    try std.testing.expectEqual(@as(usize, 1), assignments.len);
    try std.testing.expectEqual(
        try fixture.exprIdForToken("x"),
        assignments[0].expr_id,
    );
    try std.testing.expect(fixture.theorem_vars.get("x") != null);
    try std.testing.expect(fixture.theorem_vars.get("y") == null);
}

test "fresh helper gives distinct vars to distinct hidden roots" {
    const src =
        \\--| @vars x y z
        \\provable sort wff;
        \\term top: wff;
        \\theorem fresh_target: $ top $;
    ;

    var fixture = try buildFreshFixture(src);
    defer fixture.deinit();

    const line_expr = try fixture.internFormula(" top ");
    const assignments = try CompilerFresh.assignHiddenRootsFromVarsPool(
        std.testing.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.theorem,
        &fixture.theorem_vars,
        &fixture.sort_vars,
        line_expr,
        &[_]FrontendExpr.ExprId{},
        &[_]?FrontendExpr.ExprId{},
        0,
        &[_]CompilerFresh.HiddenRootNeed{
            .{ .root_slot = 1, .sort_name = "wff" },
            .{ .root_slot = 2, .sort_name = "wff" },
        },
    );
    defer std.testing.allocator.free(assignments);

    try std.testing.expectEqual(@as(usize, 2), assignments.len);
    try std.testing.expectEqual(
        try fixture.exprIdForToken("x"),
        assignments[0].expr_id,
    );
    try std.testing.expectEqual(
        try fixture.exprIdForToken("y"),
        assignments[1].expr_id,
    );
    try std.testing.expect(assignments[0].expr_id != assignments[1].expr_id);
    try std.testing.expect(assignments[0].deps != assignments[1].deps);
}

test "fresh helper respects deps already visible on the line" {
    const src =
        \\--| @vars x y
        \\provable sort wff;
        \\term top: wff;
        \\theorem fresh_target: $ top $;
    ;

    var fixture = try buildFreshFixture(src);
    defer fixture.deinit();

    try fixture.ensureDummyToken("x");
    const line_expr = try fixture.internFormula(" x ");
    const assignments = try CompilerFresh.assignHiddenRootsFromVarsPool(
        std.testing.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.theorem,
        &fixture.theorem_vars,
        &fixture.sort_vars,
        line_expr,
        &[_]FrontendExpr.ExprId{},
        &[_]?FrontendExpr.ExprId{},
        0,
        &[_]CompilerFresh.HiddenRootNeed{
            .{ .root_slot = 9, .sort_name = "wff" },
        },
    );
    defer std.testing.allocator.free(assignments);

    try std.testing.expectEqual(@as(usize, 1), assignments.len);
    try std.testing.expectEqual(
        try fixture.exprIdForToken("y"),
        assignments[0].expr_id,
    );
    try std.testing.expectEqual(
        try fixture.depsForToken("y"),
        assignments[0].deps,
    );
}

test "recover-hole seeding allocates distinct vars per omitted hole" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @vars x y z
        \\sort obj;
        \\term pair (a b: obj): wff;
        \\theorem fresh_target {a b: obj}: $ pair a b $;
    ;

    var fixture = try buildFreshFixture(src);
    defer fixture.deinit();

    const line_expr = try fixture.internFormula(" pair a b ");
    const seeds = try CompilerFresh.seedRecoverHolesFromVarsPool(
        std.testing.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.theorem,
        &fixture.theorem_vars,
        &fixture.sort_vars,
        line_expr,
        &[_]FrontendExpr.ExprId{},
        &[_]?FrontendExpr.ExprId{ null, null },
        4,
        &[_]?usize{ null, 0, null, 1 },
        &[_]ArgInfo{
            .{ .sort_name = "obj", .bound = true, .deps = 1 },
            .{ .sort_name = "obj", .bound = true, .deps = 1 },
            .{ .sort_name = "wff", .bound = false, .deps = 0 },
            .{ .sort_name = "obj", .bound = true, .deps = 2 },
        },
        &[_]DerivedBinding{
            .{ .recover = .{
                .target_view_idx = 0,
                .source_view_idx = 2,
                .pattern_view_idx = 2,
                .hole_view_idx = 1,
            } },
            .{ .recover = .{
                .target_view_idx = 0,
                .source_view_idx = 2,
                .pattern_view_idx = 2,
                .hole_view_idx = 3,
            } },
        },
    );
    defer std.testing.allocator.free(seeds);

    try expectExactSeed(seeds[1], try fixture.exprIdForToken("x"));
    try expectExactSeed(seeds[3], try fixture.exprIdForToken("y"));
    try expectSeedNone(seeds[0]);
    try expectSeedNone(seeds[2]);
}

test "recover-hole seeding skips non-bound holes" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @vars x y
        \\sort obj;
        \\term hold (a: obj): wff;
        \\theorem fresh_target (a: obj): $ hold a $;
    ;

    var fixture = try buildFreshFixture(src);
    defer fixture.deinit();

    const line_expr = try fixture.internFormula(" hold a ");
    const seeds = try CompilerFresh.seedRecoverHolesFromVarsPool(
        std.testing.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.theorem,
        &fixture.theorem_vars,
        &fixture.sort_vars,
        line_expr,
        &[_]FrontendExpr.ExprId{},
        &[_]?FrontendExpr.ExprId{null},
        2,
        &[_]?usize{ null, 0 },
        &[_]ArgInfo{
            .{ .sort_name = "wff", .bound = false, .deps = 0 },
            .{ .sort_name = "obj", .bound = false, .deps = 0 },
        },
        &[_]DerivedBinding{.{ .recover = .{
            .target_view_idx = 0,
            .source_view_idx = 0,
            .pattern_view_idx = 0,
            .hole_view_idx = 1,
        } }},
    );
    defer std.testing.allocator.free(seeds);

    try expectSeedNone(seeds[0]);
    try expectSeedNone(seeds[1]);
    try std.testing.expect(fixture.theorem_vars.get("x") == null);
}

fn expectSeedNone(seed: DefOps.BindingSeed) !void {
    switch (seed) {
        .none => {},
        else => return error.ExpectedSeedNone,
    }
}

fn expectExactSeed(
    seed: DefOps.BindingSeed,
    expr_id: FrontendExpr.ExprId,
) !void {
    switch (seed) {
        .exact => |actual| try std.testing.expectEqual(expr_id, actual),
        else => return error.ExpectedExactSeed,
    }
}
