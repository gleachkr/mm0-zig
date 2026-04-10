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
