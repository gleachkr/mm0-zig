const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const Types = @import("./def_ops/types.zig");
const MatchState = @import("./def_ops/match_state.zig");
const SharedContext = @import("./def_ops/shared_context.zig").SharedContext;
const SymbolicEngine = @import("./def_ops/symbolic_engine.zig").SymbolicEngine;
const NormalizedMatch = @import("./def_ops/normalized_match.zig");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const Expr = @import("../trusted/expressions.zig").Expr;

pub const ConversionPlan = Types.ConversionPlan;
pub const BindingMode = Types.BindingMode;
pub const BindingSeed = Types.BindingSeed;
pub const RuleMatchSession = NormalizedMatch.RuleMatchSession;
pub const NormalizedComparison =
    NormalizedMatch.NormalizedComparison;
const BoundValue = Types.BoundValue;
const SymbolicExpr = Types.SymbolicExpr;
const MatchSession = MatchState.MatchSession;

pub const Context = struct {
    shared: SharedContext,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) Context {
        const shared = SharedContext.init(allocator, theorem, env);
        return .{
            .shared = shared,
        };
    }

    pub fn initWithRegistry(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
    ) Context {
        const shared = SharedContext.initWithRegistry(
            allocator,
            theorem,
            env,
            registry,
        );
        return .{
            .shared = shared,
        };
    }

    pub fn deinit(self: *Context) void {
        self.shared.deinit();
    }

    fn symbolicEngine(self: *Context) SymbolicEngine {
        return .{ .shared = &self.shared };
    }

    pub fn beginRuleMatch(
        self: *Context,
        rule_args: []const ArgInfo,
        seeds: []const BindingSeed,
    ) anyerror!RuleMatchSession {
        return try RuleMatchSession.init(
            &self.shared,
            rule_args,
            seeds,
        );
    }

    pub fn defCoversItem(
        self: *Context,
        def_expr: ExprId,
        item_expr: ExprId,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.defCoversItem(def_expr, item_expr);
    }

    pub fn planDefCoversItem(
        self: *Context,
        def_expr: ExprId,
        item_expr: ExprId,
    ) anyerror!?*const ConversionPlan {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.planDefCoversItem(def_expr, item_expr);
    }

    pub fn instantiateDefTowardAcuiItem(
        self: *Context,
        def_expr: ExprId,
        item_expr: ExprId,
        head_term_id: u32,
    ) anyerror!?ExprId {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.instantiateDefTowardAcuiItem(
            def_expr,
            item_expr,
            head_term_id,
        );
    }

    pub fn planDefToTarget(
        self: *Context,
        def_expr: ExprId,
        target_expr: ExprId,
        side: enum { lhs, rhs },
    ) anyerror!?*const ConversionPlan {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.planDefToTarget(def_expr, target_expr, side);
    }

    pub fn compareTransparent(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?*const ConversionPlan {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.compareTransparent(lhs, rhs);
    }

    pub fn matchTemplateTransparent(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchTemplateTransparent(
            template,
            actual,
            bindings,
        );
    }

    // These private forwards stay here so the local tests can exercise the
    // extracted symbolic engine and normalized matcher through the original
    // def_ops surface.
    fn matchTemplateRecState(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchTemplateRecState(template, actual, state);
    }

    fn boundValueFromSeed(
        self: *Context,
        seed: BindingSeed,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    ) anyerror!?BoundValue {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.boundValueFromSeed(seed, state, witness_slots);
    }

    fn chooseRepresentative(
        self: *Context,
        expr_id: ExprId,
        mode: BindingMode,
    ) anyerror!ExprId {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.chooseRepresentative(expr_id, mode);
    }

    fn chooseRepresentativeSymbolic(
        self: *Context,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!*const SymbolicExpr {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.chooseRepresentativeSymbolic(expr_id, state, mode);
    }

    fn symbolicExprEql(
        self: *Context,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
    ) bool {
        var symbolic_engine = self.symbolicEngine();
        return symbolic_engine.symbolicExprEql(lhs, rhs);
    }

    fn assignBinderValue(
        self: *Context,
        idx: usize,
        value: BoundValue,
        state: *MatchSession,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.assignBinderValue(idx, value, state);
    }

    fn finalizeBoundValue(
        self: *Context,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!ExprId {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.finalizeBoundValue(bound, state);
    }

    fn concreteBindingMatchExpr(
        self: *Context,
        concrete: Types.ConcreteBinding,
        state: *MatchSession,
    ) anyerror!?ExprId {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.concreteBindingMatchExpr(concrete, state);
    }

    fn currentWitnessExpr(
        self: *Context,
        slot: usize,
        state: *const MatchSession,
    ) ?ExprId {
        var symbolic_engine = self.symbolicEngine();
        return symbolic_engine.currentWitnessExpr(slot, state);
    }

    fn isProvisionalWitnessExpr(
        self: *Context,
        expr_id: ExprId,
        state: *const MatchSession,
    ) bool {
        var symbolic_engine = self.symbolicEngine();
        return symbolic_engine.isProvisionalWitnessExpr(expr_id, state);
    }

    fn makeConcreteBoundValue(
        self: *Context,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!BoundValue {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.makeConcreteBoundValue(expr_id, state, mode);
    }

    fn makeSymbolicBoundValue(
        self: *Context,
        symbolic: *const SymbolicExpr,
        mode: BindingMode,
    ) BoundValue {
        var symbolic_engine = self.symbolicEngine();
        return symbolic_engine.makeSymbolicBoundValue(symbolic, mode);
    }

    fn allocSymbolic(
        self: *Context,
        symbolic: SymbolicExpr,
    ) anyerror!*const SymbolicExpr {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.allocSymbolic(symbolic);
    }

    fn matchSymbolicDummyState(
        self: *Context,
        slot: usize,
        info: Types.SymbolicDummyInfo,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchSymbolicDummyState(
            slot,
            info,
            actual,
            state,
        );
    }

    fn matchDummyToSymbolic(
        self: *Context,
        slot: usize,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchDummyToSymbolic(slot, rhs, state);
    }
};

const SessionWitnessFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    theorem: TheoremContext,
    actual: ExprId,
    raw: ExprId,
    rule_args: []const ArgInfo,
    body: TemplateExpr,
    dummy_arg_count: usize,

    fn init() !SessionWitnessFixture {
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort mor;
            \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
            \\term all {x: mor} (p: wff x): wff; prefix all: $A.$ prec 41;
            \\term mor_eq (f g: mor): wff; infixl mor_eq: $~$ prec 15;
            \\term comp (f g: mor): mor; infixl comp: $o$ prec 35;
            \\def mono {.a .b: mor} (f: mor): wff =
            \\  $ A. a A. b ((f o a ~ f o b) -> (a ~ b)) $;
            \\theorem host (f: mor): $ mono f $;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        errdefer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var theorem = TheoremContext.init(arena.allocator());
        errdefer theorem.deinit();
        var theorem_vars = std.StringHashMap(*const Expr).init(
            arena.allocator(),
        );
        defer theorem_vars.deinit();

        var actual: ?ExprId = null;
        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |assertion| {
                    if (!std.mem.eql(u8, assertion.name, "host")) continue;
                    try theorem.seedAssertion(assertion);
                    actual = try theorem.internParsedExpr(assertion.concl);
                    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
                        if (name) |actual_name| {
                            try theorem_vars.put(actual_name, expr);
                        }
                    }
                },
                else => {},
            }
        }

        const raw_expr = try parser.parseFormulaText(
            " A. x A. y ((f o x ~ f o y) -> (x ~ y)) ",
            &theorem_vars,
        );
        const raw = try theorem.internParsedExpr(raw_expr);

        const mono_id = env.term_names.get("mono") orelse {
            return error.MissingTerm;
        };
        const mono = env.terms.items[mono_id];
        const body = mono.body orelse return error.MissingTermBody;
        const rule_args = try arena.allocator().alloc(
            ArgInfo,
            mono.args.len + mono.dummy_args.len,
        );
        @memcpy(rule_args[0..mono.args.len], mono.args);
        @memcpy(rule_args[mono.args.len..], mono.dummy_args);

        return .{
            .arena = arena,
            .env = env,
            .theorem = theorem,
            .actual = actual orelse return error.MissingAssertion,
            .raw = raw,
            .rule_args = rule_args,
            .body = body,
            .dummy_arg_count = mono.dummy_args.len,
        };
    }

    fn deinit(self: *SessionWitnessFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

fn allocNoneSeeds(
    allocator: std.mem.Allocator,
    len: usize,
) ![]BindingSeed {
    const seeds = try allocator.alloc(BindingSeed, len);
    for (seeds) |*seed| {
        seed.* = .none;
    }
    return seeds;
}

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

    const first = try ctx.chooseRepresentativeSymbolic(
        fixture.raw,
        &state,
        .transparent,
    );
    try std.testing.expectEqual(
        fixture.actual,
        try ctx.chooseRepresentative(fixture.raw, .transparent),
    );

    const cache_count = state.transparent_representatives.count();
    const second = try ctx.chooseRepresentativeSymbolic(
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

test "finalization materializes escaping witnesses exactly once" {
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

    const first = try session.finalizeConcreteBindings();
    try std.testing.expectEqual(
        start_dummy_id + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_id,
    );
    try std.testing.expectEqual(
        start_dummy_dep + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        fixture.theorem.theorem_dummies.items.len,
    );

    const second = try session.finalizeConcreteBindings();
    try std.testing.expectEqual(
        start_dummy_id + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_id,
    );
    try std.testing.expectEqual(
        start_dummy_dep + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        fixture.theorem.theorem_dummies.items.len,
    );
    try std.testing.expectEqual(first.len, second.len);
    for (first, second) |lhs, rhs| {
        try std.testing.expectEqual(lhs, rhs);
    }
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

test "many sessions only spend theorem dummies on escaped results" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var finalized_sessions: usize = 0;
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
                _ = try session.finalizeConcreteBindings();
                finalized_sessions += 1;
            }
        }

        const expected = finalized_sessions * fixture.dummy_arg_count;
        try std.testing.expectEqual(
            expected,
            fixture.theorem.theorem_dummies.items.len,
        );
        try std.testing.expectEqual(
            @as(u32, @intCast(expected)),
            fixture.theorem.next_dummy_id,
        );
        try std.testing.expectEqual(
            @as(u32, @intCast(expected)),
            fixture.theorem.next_dummy_dep,
        );
    }
}

test "real escape-point exhaustion stays explicit under repeated finalization" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const limit = @as(usize, @intCast(@import("./compiler_expr.zig")
        .tracked_bound_dep_limit));

    while (fixture.theorem.theorem_dummies.items.len +
        fixture.dummy_arg_count < limit)
    {
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
            _ = try session.finalizeConcreteBindings();
        }
    }

    try std.testing.expectEqual(limit - 1, fixture.theorem.next_dummy_dep);
    try std.testing.expectEqual(
        limit - 1,
        fixture.theorem.theorem_dummies.items.len,
    );

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
        error.DependencySlotExhausted,
        session.finalizeConcreteBindings(),
    );
    try std.testing.expectEqual(limit, fixture.theorem.next_dummy_dep);
    try std.testing.expectEqual(
        limit,
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

    const transparent = try ctx.chooseRepresentativeSymbolic(
        fixture.actual,
        &state,
        .transparent,
    );
    const normalized = try ctx.chooseRepresentativeSymbolic(
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
