const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const ExprId = @import("../../compiler_expr.zig").ExprId;
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

test "semantic ACUI leaf exposure rewrites before matching the leaf" {
    var fixture = try SemanticAcuiExposureFixture.init(true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.bound_item_expr,
        fixture.join_term_id,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_bound_witness, witness);
}

test "semantic ACUI exposure allows theorem args for non-bound hidden witnesses" {
    var fixture = try SemanticAcuiExposureFixture.init(false, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.free_item_expr,
        fixture.join_term_id,
    );

    try std.testing.expectEqual(fixture.expected_free_witness, witness);
}

test "semantic ACUI exposure keeps bound hidden witnesses strict" {
    var fixture = try SemanticAcuiExposureFixture.init(true, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.free_item_expr,
        fixture.join_term_id,
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
}

test "semantic def exposure matches wrapped ACUI witness" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(false, true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure matches wrapped full ACUI witness" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(true, true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure matches quantified wrapped ACUI witness" {
    var fixture = try SemanticQuantifiedAcuiDefFixture.init(false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure matches quantified wrapped full ACUI witness" {
    var fixture = try SemanticQuantifiedAcuiDefFixture.init(true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure keeps wrapped bound witnesses unresolved" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(false, true, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

