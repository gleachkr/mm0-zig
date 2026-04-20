const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const MatchSession = Testing.MatchSession;
const MaterializedDummyAssignment = DefOps.MaterializedDummyAssignment;
const SessionWitnessFixture = Fixtures.SessionWitnessFixture;
const allocNoneSeeds = Fixtures.allocNoneSeeds;

test "match sessions keep witness placeholders session-local" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "fresh match sessions start with fresh witness namespaces" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds1 = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session1 = try ctx.beginRuleMatch(fixture.rule_args, seeds1);
    defer session1.deinit();
    try std.testing.expect(
        try session1.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        session1.state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(usize, 0), session1.state.witnesses.count());

    const seeds2 = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session2 = try ctx.beginRuleMatch(fixture.rule_args, seeds2);
    defer session2.deinit();
    try std.testing.expect(
        try session2.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        session2.state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(usize, 0), session2.state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "representative selection treats placeholders distinctly from dummies" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const sort_id = fixture.env.sort_names.get("mor") orelse {
        return error.UnknownSort;
    };
    const placeholder = try fixture.theorem.addPlaceholderResolved(
        "mor",
    );
    const placeholder_repr = try Testing.chooseRepresentativeSymbolic(
        &ctx,
        placeholder,
        &state,
        .transparent,
    );
    try std.testing.expect(switch (placeholder_repr.*) {
        .dummy => |slot| slot == 0,
        else => false,
    });
    try std.testing.expectEqual(
        @as(usize, 1),
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(placeholder, state.witnesses.get(0).?);

    const dummy = try fixture.theorem.addDummyVarResolved("mor", sort_id);
    const dummy_repr = try Testing.chooseRepresentativeSymbolic(
        &ctx,
        dummy,
        &state,
        .transparent,
    );
    try std.testing.expect(switch (dummy_repr.*) {
        .fixed => |expr_id| expr_id == dummy,
        else => false,
    });
    try std.testing.expectEqual(
        @as(usize, 1),
        state.symbolic_dummy_infos.items.len,
    );
}

test "normalized comparison maps copied placeholders back to source" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var session = try ctx.beginRuleMatch(fixture.rule_args[0..1], &.{.none});
    defer session.deinit();

    _ = try fixture.theorem.addPlaceholderResolved("mor");
    _ = try fixture.theorem.addPlaceholderResolved("mor");
    _ = try fixture.theorem.addPlaceholderResolved("mor");
    const actual = try fixture.theorem.addPlaceholderResolved("mor");

    var comparison = try session.beginNormalizedComparison(
        .{ .binder = 0 },
        actual,
    );
    defer comparison.deinit();

    try std.testing.expect(switch (comparison.mirrorTheorem().interner.node(comparison.actual_expr).*) {
        .placeholder => true,
        else => false,
    });
    try std.testing.expect(actual != comparison.actual_expr);
    try std.testing.expect(
        try comparison.finish(
            comparison.expected_expr,
            comparison.actual_expr,
        ),
    );

    const binding = session.state.bindings[0] orelse {
        return error.MissingBinderAssignment;
    };
    try std.testing.expect(switch (binding) {
        .symbolic => |symbolic| switch (symbolic.expr.*) {
            .fixed => |expr_id| expr_id == actual,
            else => false,
        },
        .concrete => false,
    });
}

test "normalized comparison keeps mirrored dummies distinct from placeholders" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var session = try ctx.beginRuleMatch(fixture.rule_args[0..1], &.{.none});
    defer session.deinit();

    const sort_id = fixture.env.sort_names.get("mor") orelse {
        return error.UnknownSort;
    };
    const actual_dummy = try fixture.theorem.addDummyVarResolved(
        "mor",
        sort_id,
    );
    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;
    const start_placeholder_count =
        fixture.theorem.theorem_placeholders.items.len;

    var comparison = try session.beginNormalizedComparison(
        .{ .binder = 0 },
        actual_dummy,
    );
    defer comparison.deinit();

    try std.testing.expect(switch (comparison.mirrorTheorem().interner.node(comparison.expected_expr).*) {
        .placeholder => true,
        else => false,
    });
    try std.testing.expect(switch (comparison.mirrorTheorem().interner.node(comparison.actual_expr).*) {
        .variable => |var_id| switch (var_id) {
            .dummy_var => true,
            .theorem_var => false,
        },
        .placeholder, .app => false,
    });
    try std.testing.expect(
        try comparison.finish(
            comparison.expected_expr,
            comparison.actual_expr,
        ),
    );

    const binding = session.state.bindings[0] orelse {
        return error.MissingBinderAssignment;
    };
    try std.testing.expect(switch (binding) {
        .concrete => |concrete| concrete.raw == actual_dummy,
        .symbolic => false,
    });
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        start_placeholder_count,
        fixture.theorem.theorem_placeholders.items.len,
    );
}

test "normalized comparison maps symbolic-slot placeholders back to source" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var session = try ctx.beginRuleMatch(fixture.rule_args[0..1], &.{.none});
    defer session.deinit();

    try session.state.symbolic_dummy_infos.append(
        fixture.arena.allocator(),
        .{ .sort_name = "mor", .bound = true },
    );
    const symbolic_dummy = try Testing.allocSymbolic(
        &ctx,
        .{ .dummy = 0 },
    );
    session.state.bindings[0] = .{ .symbolic = .{
        .expr = symbolic_dummy,
        .mode = .normalized,
    } };

    const actual = try fixture.theorem.addPlaceholderResolved("mor");
    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;
    const start_placeholder_count =
        fixture.theorem.theorem_placeholders.items.len;

    var comparison = try session.beginNormalizedComparison(
        .{ .binder = 0 },
        actual,
    );
    defer comparison.deinit();

    try std.testing.expect(switch (comparison.mirrorTheorem().interner.node(comparison.expected_expr).*) {
        .placeholder => true,
        else => false,
    });
    try std.testing.expect(switch (comparison.mirrorTheorem().interner.node(comparison.actual_expr).*) {
        .placeholder => true,
        else => false,
    });
    try std.testing.expect(comparison.expected_expr != comparison.actual_expr);
    try std.testing.expect(
        try comparison.finish(
            comparison.expected_expr,
            comparison.actual_expr,
        ),
    );
    try std.testing.expectEqual(
        actual,
        session.state.witnesses.get(0) orelse return error.MissingWitness,
    );
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        start_placeholder_count,
        fixture.theorem.theorem_placeholders.items.len,
    );
}

test "transparent app matching ignores placeholder actuals" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    const placeholder = try fixture.theorem.addPlaceholderResolved(
        "mor",
    );
    const start_dummy_info_len = session.state.symbolic_dummy_infos.items.len;
    const start_witness_count = session.state.witnesses.count();

    try std.testing.expect(
        !(try session.matchTransparent(fixture.body, placeholder)),
    );
    try std.testing.expectEqual(
        start_dummy_info_len,
        session.state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(
        start_witness_count,
        session.state.witnesses.count(),
    );
}

test "representative computation stays symbolic inside one session" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const first = try Testing.chooseRepresentativeSymbolic(
        &ctx,
        fixture.raw,
        &state,
        .transparent,
    );
    try std.testing.expectEqual(
        fixture.actual,
        try ctx.chooseRepresentative(fixture.raw, .transparent),
    );

    const cache_count = state.transparent_representatives.count();
    const second = try Testing.chooseRepresentativeSymbolic(
        &ctx,
        fixture.raw,
        &state,
        .transparent,
    );

    try std.testing.expect(first == second);
    try std.testing.expectEqual(
        cache_count,
        state.transparent_representatives.count(),
    );
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "repeated transparent comparison through defs stays symbolic" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    for (0..32) |_| {
        try std.testing.expect(
            (try ctx.compareTransparent(fixture.raw, fixture.actual)) != null,
        );
    }

    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "finalization rejects unresolved hidden-dummy witnesses without allocating" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    // Finalization rejects unresolved hidden-dummy witnesses.
    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session.finalizeConcreteBindings(),
    );

    // No dummies should have been allocated.
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(start_dummy_dep, fixture.theorem.next_dummy_dep);
    try std.testing.expectEqual(
        @as(usize, 0),
        fixture.theorem.theorem_dummies.items.len,
    );
}

test "collectUnresolvedFinalizationRoots reports canonical roots" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );

    const roots = try session.collectUnresolvedFinalizationRoots();
    defer fixture.arena.allocator().free(roots);

    try std.testing.expectEqual(fixture.dummy_arg_count, roots.len);
    for (roots) |root| {
        try std.testing.expectEqualStrings("mor", root.sort_name);
        try std.testing.expect(root.bound);
    }

    try session.state.dummy_aliases.put(
        fixture.arena.allocator(),
        roots[1].root_slot,
        roots[0].root_slot,
    );

    const collapsed = try session.collectUnresolvedFinalizationRoots();
    defer fixture.arena.allocator().free(collapsed);

    try std.testing.expectEqual(@as(usize, 1), collapsed.len);
    try std.testing.expectEqual(roots[0].root_slot, collapsed[0].root_slot);
}

test "materialized dummy assignments finalize without mutating witnesses" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session.finalizeConcreteBindings(),
    );

    const roots = try session.collectUnresolvedFinalizationRoots();
    defer fixture.arena.allocator().free(roots);

    const sort_id = fixture.env.sort_names.get("mor") orelse {
        return error.UnknownSort;
    };
    const first = try fixture.theorem.addDummyVarResolved("mor", sort_id);
    const second = try fixture.theorem.addDummyVarResolved("mor", sort_id);
    const assignments = [_]MaterializedDummyAssignment{
        .{ .root_slot = roots[0].root_slot, .expr_id = first },
        .{ .root_slot = roots[1].root_slot, .expr_id = second },
    };
    const witness_count = session.state.witnesses.count();

    try session.applyMaterializedDummyAssignments(&assignments);

    try std.testing.expectEqual(witness_count, session.state.witnesses.count());
    try std.testing.expectEqual(roots.len, session.state.materialized_witnesses.count());

    const bindings = try session.finalizeConcreteBindings();
    defer fixture.arena.allocator().free(bindings);

    try std.testing.expectEqual(fixture.rule_args.len, bindings.len);
}

test "abandoning a matched session leaves theorem dummy state unchanged" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    {
        var ctx = Context.init(
            fixture.arena.allocator(),
            &fixture.theorem,
            &fixture.env,
        );
        defer ctx.deinit();

        const seeds = try allocNoneSeeds(
            fixture.arena.allocator(),
            fixture.rule_args.len,
        );
        var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
        defer session.deinit();

        try std.testing.expect(
            try session.matchTransparent(fixture.body, fixture.actual),
        );
    }

    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        @as(usize, 0),
        fixture.theorem.theorem_dummies.items.len,
    );
}

test "repeated sessions never allocate theorem dummies for hidden-dummy structure" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    for (0..40) |idx| {
        {
            const seeds = try allocNoneSeeds(
                fixture.arena.allocator(),
                fixture.rule_args.len,
            );
            var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
            defer session.deinit();

            try std.testing.expect(
                try session.matchTransparent(fixture.body, fixture.actual),
            );
            try std.testing.expect(
                (try ctx.compareTransparent(fixture.raw, fixture.actual)) != null,
            );

            if (idx % 3 == 0) {
                // Finalization rejects unresolved hidden-dummy witnesses.
                try std.testing.expectError(
                    error.UnresolvedDummyWitness,
                    session.finalizeConcreteBindings(),
                );
            }
        }

        // No dummies should ever be allocated.
        try std.testing.expectEqual(
            @as(usize, 0),
            fixture.theorem.theorem_dummies.items.len,
        );
        try std.testing.expectEqual(
            @as(u32, 0),
            fixture.theorem.next_dummy_id,
        );
        try std.testing.expectEqual(
            @as(u32, 0),
            fixture.theorem.next_dummy_dep,
        );
    }
}

test "hidden-dummy finalization never reaches dependency slot exhaustion" {
    // With the allocating escape removed, finalization rejects
    // unresolved dummies immediately, so the 55-slot dependency
    // limit is never reachable through this path.
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    for (0..60) |_| {
        const seeds = try allocNoneSeeds(
            fixture.arena.allocator(),
            fixture.rule_args.len,
        );
        var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
        defer session.deinit();
        try std.testing.expect(
            try session.matchTransparent(fixture.body, fixture.actual),
        );
        try std.testing.expectError(
            error.UnresolvedDummyWitness,
            session.finalizeConcreteBindings(),
        );
    }

    // No dummies allocated despite 60 finalization attempts.
    try std.testing.expectEqual(
        @as(usize, 0),
        fixture.theorem.theorem_dummies.items.len,
    );
}

test "transparent and normalized representative caches stay separate" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const transparent = try Testing.chooseRepresentativeSymbolic(
        &ctx,
        fixture.actual,
        &state,
        .transparent,
    );
    const normalized = try Testing.chooseRepresentativeSymbolic(
        &ctx,
        fixture.actual,
        &state,
        .normalized,
    );

    try std.testing.expect(transparent != normalized);
    try std.testing.expectEqual(
        transparent,
        state.transparent_representatives.get(fixture.actual).?,
    );
    try std.testing.expectEqual(
        normalized,
        state.normalized_representatives.get(fixture.actual).?,
    );
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}
