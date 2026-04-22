const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../trusted/parse.zig").ArgInfo;
const AssertionKind = @import("../../../trusted/parse.zig").AssertionKind;
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
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

test "rewrite application ignores placeholder roots" {
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

    const placeholder = try fixture.theorem.addPlaceholderResolved(
        "mor",
    );
    const start_dummy_info_len = state.symbolic_dummy_infos.items.len;
    const start_witness_count = state.witnesses.count();
    const start_placeholder_count =
        fixture.theorem.theorem_placeholders.items.len;

    const rule = fixture.registry.getRewriteRules(
        fixture.comp_term_id,
    )[0];
    try std.testing.expect(
        (try Testing.applyRewriteRuleToExpr(
            &ctx,
            rule,
            placeholder,
            &state,
        )) == null,
    );
    try std.testing.expectEqual(
        start_dummy_info_len,
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(start_witness_count, state.witnesses.count());
    try std.testing.expectEqual(
        start_placeholder_count,
        fixture.theorem.theorem_placeholders.items.len,
    );
}

test "rewrite application rejects bindings with forbidden deps" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);

    const arr_term_id: u32 = 0;
    const sb_ty_term_id: u32 = 1;
    try env.term_names.put("arr", arr_term_id);
    try env.term_names.put("sb_ty", sb_ty_term_id);
    try env.terms.append(allocator, .{
        .name = "arr",
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .ret_sort_name = "ty",
        .is_def = false,
        .body = null,
    });
    try env.terms.append(allocator, .{
        .name = "sb_ty",
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .ret_sort_name = "ty",
        .is_def = false,
        .body = null,
    });

    const lhs: TemplateExpr = .{ .app = .{
        .term_id = sb_ty_term_id,
        .args = try allocator.dupe(TemplateExpr, &.{
            TemplateExpr{ .binder = 0 },
            TemplateExpr{ .binder = 1 },
            TemplateExpr{ .app = .{
                .term_id = arr_term_id,
                .args = try allocator.dupe(TemplateExpr, &.{
                    TemplateExpr{ .binder = 2 },
                    TemplateExpr{ .binder = 3 },
                }),
            } },
        }),
    } };
    const rhs: TemplateExpr = .{ .app = .{
        .term_id = arr_term_id,
        .args = try allocator.dupe(TemplateExpr, &.{
            TemplateExpr{ .binder = 2 },
            TemplateExpr{ .binder = 3 },
        }),
    } };

    const rule_args = try allocator.dupe(ArgInfo, &.{
        ArgInfo{ .sort_name = "tm", .bound = true, .deps = 0 },
        ArgInfo{ .sort_name = "tm", .bound = false, .deps = 1 },
        ArgInfo{ .sort_name = "ty", .bound = false, .deps = 0 },
        ArgInfo{ .sort_name = "ty", .bound = false, .deps = 0 },
    });
    try env.rule_names.put("sb_ty_arr", 0);
    try env.rules.append(allocator, .{
        .name = "sb_ty_arr",
        .args = rule_args,
        .arg_names = &.{},
        .hyps = &.{},
        .concl = lhs,
        .kind = AssertionKind.axiom,
        .is_local = false,
    });

    var rules = std.ArrayListUnmanaged(RewriteRule){};
    try rules.append(allocator, .{
        .rule_id = 0,
        .lhs = lhs,
        .rhs = rhs,
        .num_binders = rule_args.len,
        .head_term_id = sb_ty_term_id,
    });
    try registry.rewrites_by_head.put(sb_ty_term_id, rules);

    var theorem = TheoremContext.init(allocator);
    const theorem_args = [_]ArgInfo{
        .{ .sort_name = "tm", .bound = true, .deps = 1 },
        .{ .sort_name = "tm", .bound = false, .deps = 1 },
        .{ .sort_name = "ty", .bound = false, .deps = 1 },
        .{ .sort_name = "ty", .bound = false, .deps = 1 },
    };
    theorem.arg_infos = &theorem_args;
    try theorem.seedBinderCount(theorem_args.len);

    var ctx = Context.initWithRegistry(
        allocator,
        &theorem,
        &env,
        &registry,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(allocator, 0);
    defer state.deinit(allocator);

    const x = theorem.theorem_vars.items[0];
    const u = theorem.theorem_vars.items[1];
    const a = theorem.theorem_vars.items[2];
    const b = theorem.theorem_vars.items[3];
    const arr_expr = try theorem.interner.internApp(arr_term_id, &.{ a, b });
    const expr = try theorem.interner.internApp(
        sb_ty_term_id,
        &.{ x, u, arr_expr },
    );

    const rule = registry.getRewriteRules(sb_ty_term_id)[0];
    try std.testing.expect(
        (try Testing.applyRewriteRuleToExpr(
            &ctx,
            rule,
            expr,
            &state,
        )) == null,
    );
}
