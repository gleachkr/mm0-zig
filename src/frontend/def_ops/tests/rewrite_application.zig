const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const ExprId = @import("../../expr.zig").ExprId;
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const MatchSession = Testing.MatchSession;
const SymbolicExpr = Testing.SymbolicExpr;
const SemanticStepCandidate = DefOps.SemanticStepCandidate;
const SemanticStepFixture = Fixtures.SemanticStepFixture;
const SemanticAcuiExposureFixture = Fixtures.SemanticAcuiExposureFixture;
const SemanticWrappedAcuiDefFixture =
    Fixtures.SemanticWrappedAcuiDefFixture;
const SemanticQuantifiedAcuiDefFixture =
    Fixtures.SemanticQuantifiedAcuiDefFixture;
const allocNoneSeeds = Fixtures.allocNoneSeeds;
const hasConcreteUnfold = Fixtures.hasConcreteUnfold;
const hasSymbolicUnfold = Fixtures.hasSymbolicUnfold;
const hasRewriteRule = Fixtures.hasRewriteRule;

test "rewrite application works on concrete roots" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const rule = fixture.registry.getRewriteRules(
        fixture.comp_term_id,
    )[0];
    const result = try Testing.applyRewriteRuleToExpr(
        &ctx,
        rule,
        fixture.comp_expr,
        &state,
    ) orelse return error.MissingRewriteResult;

    const f = fixture.theorem.theorem_vars.items[0];
    const g = fixture.theorem.theorem_vars.items[1];
    const alpha = fixture.theorem.theorem_vars.items[2];

    const rhs_inner_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    rhs_inner_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = f });
    rhs_inner_args[1] = try Testing.allocSymbolic(&ctx, .{ .fixed = alpha });
    const rhs_inner = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = rhs_inner_args,
    } });

    const expected_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    expected_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = g });
    expected_args[1] = rhs_inner;
    const expected = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = expected_args,
    } });

    try std.testing.expect(Testing.symbolicExprEql(&ctx, result, expected));
    try std.testing.expectEqual(@as(usize, 0), state.witnesses.count());
    try std.testing.expectEqual(
        @as(usize, 0),
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "rewrite application keeps hidden dummies symbolic" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());
    try state.symbolic_dummy_infos.append(
        fixture.arena.allocator(),
        .{ .sort_name = "mor", .bound = false },
    );
    try state.symbolic_dummy_infos.append(
        fixture.arena.allocator(),
        .{ .sort_name = "mor", .bound = false },
    );

    const f = fixture.theorem.theorem_vars.items[0];
    const dummy0 = try Testing.allocSymbolic(&ctx, .{ .dummy = 0 });
    const dummy1 = try Testing.allocSymbolic(&ctx, .{ .dummy = 1 });

    const lhs_inner_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    lhs_inner_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = f });
    lhs_inner_args[1] = dummy0;
    const lhs_inner = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = lhs_inner_args,
    } });

    const lhs_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    lhs_args[0] = lhs_inner;
    lhs_args[1] = dummy1;
    const lhs = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = lhs_args,
    } });

    const rule = fixture.registry.getRewriteRules(
        fixture.comp_term_id,
    )[0];
    const result = try Testing.applyRewriteRuleToSymbolic(
        &ctx,
        rule,
        lhs,
        &state,
    ) orelse return error.MissingRewriteResult;

    const rhs_inner_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    rhs_inner_args[0] = dummy0;
    rhs_inner_args[1] = dummy1;
    const rhs_inner = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = rhs_inner_args,
    } });

    const expected_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    expected_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = f });
    expected_args[1] = rhs_inner;
    const expected = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = expected_args,
    } });

    try std.testing.expect(Testing.symbolicExprEql(&ctx, result, expected));
    try std.testing.expectEqual(
        @as(usize, 2),
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(usize, 0), state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "failed rewrite application restores witness state" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const theorem_dummy = try fixture.theorem.addDummyVarResolved(
        "mor",
        fixture.mor_sort_id,
    );
    const f = fixture.theorem.theorem_vars.items[0];
    const dup_expr = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ theorem_dummy, f },
    );
    const start_dummy_info_len = state.symbolic_dummy_infos.items.len;
    const start_witness_count = state.witnesses.count();

    const rules = fixture.registry.getRewriteRules(fixture.comp_term_id);
    var dup_rule: ?RewriteRule = null;
    for (rules) |rule| {
        if (rule.rule_id == fixture.dup_left_rule_id) {
            dup_rule = rule;
            break;
        }
    }

    try std.testing.expectEqual(
        start_dummy_info_len,
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(start_witness_count, state.witnesses.count());
    try std.testing.expect(
        (try Testing.applyRewriteRuleToExpr(
            &ctx,
            dup_rule orelse return error.MissingRule,
            dup_expr,
            &state,
        )) == null,
    );
    try std.testing.expectEqual(
        start_dummy_info_len,
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(start_witness_count, state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 1), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 1), fixture.theorem.next_dummy_dep);
}
