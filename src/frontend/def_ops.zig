const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const RewriteRule = @import("./rewrite_registry.zig").RewriteRule;
const Types = @import("./def_ops/types.zig");
const MatchState = @import("./def_ops/match_state.zig");
const SharedContext = @import("./def_ops/shared_context.zig").SharedContext;
const SymbolicEngine = @import("./def_ops/symbolic_engine.zig").SymbolicEngine;
const NormalizedMatch = @import("./def_ops/normalized_match.zig");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;

pub const ConversionPlan = Types.ConversionPlan;
pub const BindingMode = Types.BindingMode;
pub const BindingSeed = Types.BindingSeed;
pub const MatchSeedState = Types.MatchSeedState;
pub const SemanticStepCandidate =
    @import("./def_ops/symbolic_engine.zig").SemanticStepCandidate;
pub const default_semantic_match_budget: usize = 3;
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

    pub fn beginRuleMatchFromSeedState(
        self: *Context,
        rule_args: []const ArgInfo,
        seed_state: *const MatchSeedState,
    ) anyerror!RuleMatchSession {
        return try RuleMatchSession.initFromSeedState(
            &self.shared,
            rule_args,
            seed_state,
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

    pub fn instantiateDefTowardExpr(
        self: *Context,
        def_expr: ExprId,
        target_expr: ExprId,
    ) anyerror!?ExprId {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.instantiateDefTowardExpr(
            def_expr,
            target_expr,
        );
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

    pub fn matchTemplateSemantic(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
        budget: usize,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchTemplateSemantic(
            template,
            actual,
            bindings,
            budget,
        );
    }

    fn collectSemanticStepCandidatesExpr(
        self: *Context,
        expr_id: ExprId,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.collectSemanticStepCandidatesExpr(
            expr_id,
            out,
        );
    }

    fn collectSemanticStepCandidatesSymbolic(
        self: *Context,
        symbolic: *const SymbolicExpr,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.collectSemanticStepCandidatesSymbolic(
            symbolic,
            out,
        );
    }

    fn applyRewriteRuleToExpr(
        self: *Context,
        rule: RewriteRule,
        expr_id: ExprId,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.applyRewriteRuleToExpr(
            rule,
            expr_id,
            state,
        );
    }

    fn applyRewriteRuleToSymbolic(
        self: *Context,
        rule: RewriteRule,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.applyRewriteRuleToSymbolic(
            rule,
            symbolic,
            state,
        );
    }

    fn matchTemplateSemanticState(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchTemplateSemanticState(
            template,
            actual,
            state,
            budget,
        );
    }

    fn matchSymbolicToExprSemantic(
        self: *Context,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchSymbolicToExprSemantic(
            symbolic,
            actual,
            state,
            budget,
        );
    }

    fn matchSymbolicToSymbolicSemantic(
        self: *Context,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var symbolic_engine = self.symbolicEngine();
        return try symbolic_engine.matchSymbolicToSymbolicSemantic(
            lhs,
            rhs,
            state,
            budget,
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

    pub fn chooseRepresentative(
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

pub const Testing = struct {
    pub const MatchSession = MatchState.MatchSession;
    pub const SymbolicExpr = Types.SymbolicExpr;

    pub fn collectSemanticStepCandidatesExpr(
        ctx: *Context,
        expr_id: ExprId,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        return try ctx.collectSemanticStepCandidatesExpr(expr_id, out);
    }

    pub fn collectSemanticStepCandidatesSymbolic(
        ctx: *Context,
        symbolic: *const Types.SymbolicExpr,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        return try ctx.collectSemanticStepCandidatesSymbolic(symbolic, out);
    }

    pub fn applyRewriteRuleToExpr(
        ctx: *Context,
        rule: RewriteRule,
        expr_id: ExprId,
        state: *MatchState.MatchSession,
    ) anyerror!?*const Types.SymbolicExpr {
        return try ctx.applyRewriteRuleToExpr(rule, expr_id, state);
    }

    pub fn applyRewriteRuleToSymbolic(
        ctx: *Context,
        rule: RewriteRule,
        symbolic: *const Types.SymbolicExpr,
        state: *MatchState.MatchSession,
    ) anyerror!?*const Types.SymbolicExpr {
        return try ctx.applyRewriteRuleToSymbolic(rule, symbolic, state);
    }

    pub fn matchSymbolicToExprSemantic(
        ctx: *Context,
        symbolic: *const Types.SymbolicExpr,
        actual: ExprId,
        state: *MatchState.MatchSession,
        budget: usize,
    ) anyerror!bool {
        return try ctx.matchSymbolicToExprSemantic(
            symbolic,
            actual,
            state,
            budget,
        );
    }

    pub fn chooseRepresentativeSymbolic(
        ctx: *Context,
        expr_id: ExprId,
        state: *MatchState.MatchSession,
        mode: BindingMode,
    ) anyerror!*const Types.SymbolicExpr {
        return try ctx.chooseRepresentativeSymbolic(expr_id, state, mode);
    }

    pub fn symbolicExprEql(
        ctx: *Context,
        lhs: *const Types.SymbolicExpr,
        rhs: *const Types.SymbolicExpr,
    ) bool {
        return ctx.symbolicExprEql(lhs, rhs);
    }

    pub fn allocSymbolic(
        ctx: *Context,
        symbolic: Types.SymbolicExpr,
    ) anyerror!*const Types.SymbolicExpr {
        return try ctx.allocSymbolic(symbolic);
    }
};
