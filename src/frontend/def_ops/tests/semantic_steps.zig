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
const hasAcuiHead = Fixtures.hasAcuiHead;

test "semantic step enumeration finds root def rewrite and acui moves" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    var mono_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer mono_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.mono_expr,
        &mono_steps,
    );
    try std.testing.expect(
        hasConcreteUnfold(
            mono_steps.items,
            fixture.mono_expr,
            fixture.mono_term_id,
        ),
    );
    try std.testing.expect(!hasRewriteRule(
        mono_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
    try std.testing.expect(!hasAcuiHead(
        mono_steps.items,
        fixture.join_term_id,
    ));

    var comp_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer comp_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.comp_expr,
        &comp_steps,
    );
    try std.testing.expect(hasRewriteRule(
        comp_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
    try std.testing.expect(!hasConcreteUnfold(
        comp_steps.items,
        fixture.comp_expr,
        fixture.comp_term_id,
    ));
    try std.testing.expect(!hasAcuiHead(
        comp_steps.items,
        fixture.join_term_id,
    ));

    var ctx_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer ctx_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.ctx_expr,
        &ctx_steps,
    );
    try std.testing.expect(hasAcuiHead(
        ctx_steps.items,
        fixture.join_term_id,
    ));
    try std.testing.expect(!hasRewriteRule(
        ctx_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
}

test "semantic step enumeration is registry-gated" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var mono_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer mono_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.mono_expr,
        &mono_steps,
    );
    try std.testing.expect(
        hasConcreteUnfold(
            mono_steps.items,
            fixture.mono_expr,
            fixture.mono_term_id,
        ),
    );

    var comp_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer comp_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.comp_expr,
        &comp_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), comp_steps.items.len);

    var ctx_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer ctx_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.ctx_expr,
        &ctx_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), ctx_steps.items.len);
}

test "semantic step enumeration handles symbolic roots" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const mono_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        1,
    );
    mono_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = fixture.comp_expr });
    const symbolic_mono = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer symbolic_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesSymbolic(
        &ctx,
        symbolic_mono,
        &symbolic_steps,
    );
    try std.testing.expect(
        hasSymbolicUnfold(symbolic_steps.items, fixture.mono_term_id),
    );

    const fixed_comp = try Testing.allocSymbolic(&ctx, .{ .fixed = fixture.comp_expr });
    var fixed_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer fixed_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesSymbolic(
        &ctx,
        fixed_comp,
        &fixed_steps,
    );
    try std.testing.expect(hasRewriteRule(
        fixed_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
}

test "semantic search matches def unfold then rewrite" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const mono_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        1,
    );
    mono_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = fixture.comp_expr });
    const symbolic_mono = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    try std.testing.expect(
        try Testing.matchSymbolicToExprSemantic(
            &ctx,
            symbolic_mono,
            fixture.semantic_target_expr,
            &state,
            1,
        ),
    );
    try std.testing.expectEqual(@as(usize, 0), state.witnesses.count());
    try std.testing.expectEqual(
        @as(usize, 2),
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic search budget failure restores state" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const mono_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        1,
    );
    mono_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = fixture.comp_expr });
    const symbolic_mono = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());
    const start_dummy_info_len = state.symbolic_dummy_infos.items.len;
    const start_witness_count = state.witnesses.count();

    try std.testing.expect(!try Testing.matchSymbolicToExprSemantic(
        &ctx,
        symbolic_mono,
        fixture.semantic_target_expr,
        &state,
        0,
    ));
    try std.testing.expectEqual(
        start_dummy_info_len,
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(start_witness_count, state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure materializes witness toward rewrite target" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.mono_expr,
        fixture.semantic_target_expr,
    ) orelse return error.MissingWitness;

    const f = fixture.theorem.theorem_vars.items[0];
    const g = fixture.theorem.theorem_vars.items[1];
    const alpha = fixture.theorem.theorem_vars.items[2];
    const gof = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ g, f },
    );
    const lhs_inner = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ gof, g },
    );
    const lhs = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ lhs_inner, alpha },
    );
    const rhs_inner = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ g, alpha },
    );
    const rhs = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ gof, rhs_inner },
    );
    const expected = try fixture.theorem.interner.internApp(
        fixture.env.term_names.get("mor_eq") orelse return error.MissingTerm,
        &[_]ExprId{ lhs, rhs },
    );

    try std.testing.expectEqual(expected, witness);
}

