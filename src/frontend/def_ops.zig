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
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const Expr = @import("../trusted/expressions.zig").Expr;

pub const ConversionPlan = Types.ConversionPlan;
pub const BindingMode = Types.BindingMode;
pub const BindingSeed = Types.BindingSeed;
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

const SemanticStepFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    mono_expr: ExprId,
    comp_expr: ExprId,
    ctx_expr: ExprId,
    semantic_target_expr: ExprId,
    mono_body: TemplateExpr,
    mono_term_id: u32,
    comp_term_id: u32,
    join_term_id: u32,
    comp_assoc_rule_id: u32,
    dup_left_rule_id: u32,
    mor_sort_id: u8,

    fn init() !SemanticStepFixture {
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort ctx;
            \\sort mor;
            \\
            \\term mor_eq (f g: mor): wff;
            \\infixl mor_eq: $~$ prec 15;
            \\term comp (f g: mor): mor;
            \\infixl comp: $o$ prec 35;
            \\
            \\term ctx_eq (g h: ctx): wff;
            \\term emp: ctx;
            \\notation emp: ctx = ($_$:max);
            \\--| @acui ctx_assoc ctx_comm emp ctx_idem
            \\term join (g h: ctx): ctx;
            \\infixl join: $,$ prec 5;
            \\term hyp (a: wff): ctx;
            \\
            \\--| @relation mor mor_eq mor_refl_raw mor_trans_raw mor_sym_raw _
            \\axiom mor_refl_raw (f: mor): $ f ~ f $;
            \\axiom mor_trans_raw (f g h: mor):
            \\  $ f ~ g $ > $ g ~ h $ > $ f ~ h $;
            \\axiom mor_sym_raw (f g: mor): $ f ~ g $ > $ g ~ f $;
            \\
            \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
            \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
            \\axiom ctx_trans (g h i: ctx):
            \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
            \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
            \\axiom ctx_assoc (g h i: ctx):
            \\  $ ctx_eq ((g , h) , i) (g , (h , i)) $;
            \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
            \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
            \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
            \\
            \\--| @rewrite
            \\axiom comp_assoc (f g h: mor): $ (f o g) o h ~ f o (g o h) $;
            \\--| @rewrite
            \\axiom dup_left (x y: mor): $ x o x ~ y $;
            \\
            \\def mono {.a .b: mor} (f: mor): wff =
            \\  $ (f o a) o b ~ f o (a o b) $;
            \\
            \\theorem host (f g alpha: mor) (p q: wff): $ g ~ g $;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        errdefer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
        var host_assertion: ?AssertionStmt = null;

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .sort => try env.addStmt(stmt),
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        term_stmt.name,
                        parser.last_annotations,
                    );
                },
                .assertion => |assertion| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        assertion.name,
                        parser.last_annotations,
                    );
                    if (std.mem.eql(u8, assertion.name, "host")) {
                        host_assertion = assertion;
                    }
                },
            }
        }

        var theorem = TheoremContext.init(arena.allocator());
        errdefer theorem.deinit();
        const host = host_assertion orelse return error.MissingAssertion;
        try theorem.seedAssertion(host);

        const comp_term_id = env.term_names.get("comp") orelse {
            return error.MissingTerm;
        };
        const mono_term_id = env.term_names.get("mono") orelse {
            return error.MissingTerm;
        };
        const join_term_id = env.term_names.get("join") orelse {
            return error.MissingTerm;
        };
        const hyp_term_id = env.term_names.get("hyp") orelse {
            return error.MissingTerm;
        };
        const comp_assoc_rule_id = env.getRuleId("comp_assoc") orelse {
            return error.MissingRule;
        };
        const dup_left_rule_id = env.getRuleId("dup_left") orelse {
            return error.MissingRule;
        };
        const mor_sort_id = env.sort_names.get("mor") orelse {
            return error.MissingSort;
        };

        const f = theorem.theorem_vars.items[0];
        const g = theorem.theorem_vars.items[1];
        const alpha = theorem.theorem_vars.items[2];
        const p = theorem.theorem_vars.items[3];
        const q = theorem.theorem_vars.items[4];

        const gof = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ g, f },
        );
        const comp_expr = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ gof, alpha },
        );
        const mono_expr = try theorem.interner.internApp(
            mono_term_id,
            &[_]ExprId{gof},
        );

        const semantic_lhs_inner = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ gof, g },
        );
        const semantic_lhs = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ semantic_lhs_inner, alpha },
        );
        const semantic_rhs_inner = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ g, alpha },
        );
        const semantic_rhs_mid = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ f, semantic_rhs_inner },
        );
        const semantic_rhs = try theorem.interner.internApp(
            comp_term_id,
            &[_]ExprId{ g, semantic_rhs_mid },
        );
        const semantic_target_expr = try theorem.interner.internApp(
            env.term_names.get("mor_eq") orelse return error.MissingTerm,
            &[_]ExprId{ semantic_lhs, semantic_rhs },
        );

        const hp = try theorem.interner.internApp(
            hyp_term_id,
            &[_]ExprId{p},
        );
        const hq = try theorem.interner.internApp(
            hyp_term_id,
            &[_]ExprId{q},
        );
        const ctx_expr = try theorem.interner.internApp(
            join_term_id,
            &[_]ExprId{ hp, hq },
        );

        return .{
            .arena = arena,
            .env = env,
            .registry = registry,
            .theorem = theorem,
            .mono_expr = mono_expr,
            .comp_expr = comp_expr,
            .ctx_expr = ctx_expr,
            .semantic_target_expr = semantic_target_expr,
            .mono_body = env.terms.items[mono_term_id].body orelse {
                return error.MissingTermBody;
            },
            .mono_term_id = mono_term_id,
            .comp_term_id = comp_term_id,
            .join_term_id = join_term_id,
            .comp_assoc_rule_id = comp_assoc_rule_id,
            .dup_left_rule_id = dup_left_rule_id,
            .mor_sort_id = mor_sort_id,
        };
    }

    fn deinit(self: *SemanticStepFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

const SemanticAcuiExposureFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    pre_ctx_expr: ExprId,
    bound_item_expr: ExprId,
    free_item_expr: ExprId,
    expected_bound_witness: ExprId,
    expected_free_witness: ExprId,
    join_term_id: u32,

    fn init(
        comptime hidden_bound: bool,
        comptime host_u_bound: bool,
    ) !SemanticAcuiExposureFixture {
        const hidden_binder = if (hidden_bound)
            "def pre_ctx (u: obj) {.x: obj}: ctx = $ box (hyp (u = x)) $;\n\n"
        else
            "def pre_ctx (u: obj) (.x: obj): ctx = $ box (hyp (u = x)) $;\n\n";
        const host_decl = if (host_u_bound)
            "theorem host {x u: obj}: $ ctx_eq emp emp $;\n"
        else
            "theorem host {x: obj} (u: obj): $ ctx_eq emp emp $;\n";
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort ctx;
            \\sort obj;
            \\
            \\term eq (a b: obj): wff;
            \\infixl eq: $=$ prec 35;
            \\term ctx_eq (g h: ctx): wff;
            \\term emp: ctx;
            \\--| @acui ctx_assoc ctx_comm emp ctx_idem
            \\term join (g h: ctx): ctx;
            \\infixl join: $,$ prec 5;
            \\term hyp (a: wff): ctx;
            \\term box (g: ctx): ctx;
            \\
            \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
            \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
            \\axiom ctx_trans (g h i: ctx):
            \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
            \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
            \\axiom ctx_assoc (g h i: ctx):
            \\  $ ctx_eq ((g , h) , i) (g , (h , i)) $;
            \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
            \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
            \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
            \\
            \\--| @rewrite
            \\axiom box_flat (g: ctx): $ ctx_eq (box g) (emp , g) $;
            \\
        ++ hidden_binder ++ host_decl;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        errdefer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
        var host_assertion: ?AssertionStmt = null;

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .sort => try env.addStmt(stmt),
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        term_stmt.name,
                        parser.last_annotations,
                    );
                },
                .assertion => |assertion| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        assertion.name,
                        parser.last_annotations,
                    );
                    if (std.mem.eql(u8, assertion.name, "host")) {
                        host_assertion = assertion;
                    }
                },
            }
        }

        var theorem = TheoremContext.init(arena.allocator());
        errdefer theorem.deinit();
        const host = host_assertion orelse return error.MissingAssertion;
        try theorem.seedAssertion(host);

        const x = theorem.theorem_vars.items[0];
        const u = theorem.theorem_vars.items[1];

        const eq_term_id = env.term_names.get("eq") orelse {
            return error.MissingTerm;
        };
        const hyp_term_id = env.term_names.get("hyp") orelse {
            return error.MissingTerm;
        };
        const box_term_id = env.term_names.get("box") orelse {
            return error.MissingTerm;
        };
        const pre_ctx_term_id = env.term_names.get("pre_ctx") orelse {
            return error.MissingTerm;
        };
        const join_term_id = env.term_names.get("join") orelse {
            return error.MissingTerm;
        };

        const bound_item_eq = try theorem.interner.internApp(
            eq_term_id,
            &[_]ExprId{ u, x },
        );
        const bound_item_expr = try theorem.interner.internApp(
            hyp_term_id,
            &[_]ExprId{bound_item_eq},
        );
        const free_item_eq = try theorem.interner.internApp(
            eq_term_id,
            &[_]ExprId{ u, u },
        );
        const free_item_expr = try theorem.interner.internApp(
            hyp_term_id,
            &[_]ExprId{free_item_eq},
        );
        const pre_ctx_expr = try theorem.interner.internApp(
            pre_ctx_term_id,
            &[_]ExprId{u},
        );
        const expected_bound_witness = try theorem.interner.internApp(
            box_term_id,
            &[_]ExprId{bound_item_expr},
        );
        const expected_free_witness = try theorem.interner.internApp(
            box_term_id,
            &[_]ExprId{free_item_expr},
        );

        return .{
            .arena = arena,
            .env = env,
            .registry = registry,
            .theorem = theorem,
            .pre_ctx_expr = pre_ctx_expr,
            .bound_item_expr = bound_item_expr,
            .free_item_expr = free_item_expr,
            .expected_bound_witness = expected_bound_witness,
            .expected_free_witness = expected_free_witness,
            .join_term_id = join_term_id,
        };
    }

    fn deinit(self: *SemanticAcuiExposureFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

const SemanticWrappedAcuiDefFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    pre_ctx_expr: ExprId,
    target_expr: ExprId,
    expected_witness: ExprId,

    fn init(
        comptime full_acui: bool,
        comptime hidden_bound: bool,
        comptime host_u_bound: bool,
    ) !SemanticWrappedAcuiDefFixture {
        const hidden_binder = if (hidden_bound) "{.x: obj}" else "(.x: obj)";
        const def_body = if (full_acui)
            "def pre_ctx (u: obj) (r: wff) " ++ hidden_binder ++ ": wff =\n" ++
                "  $ ((emp , hyp (u = x)) , (hyp r , " ++
                "(hyp (u = x) , emp))) |- (u = x) $;\n\n"
        else
            "def pre_ctx (u: obj) " ++ hidden_binder ++ ": wff =\n" ++
                "  $ (hyp (u = x) , emp) |- (u = x) $;\n\n";
        const host = if (full_acui)
            if (host_u_bound)
                "theorem host {u v: obj} (r: wff): $ u = v $;\n"
            else
                "theorem host (u: obj) (r: wff): $ u = u $;\n"
        else if (host_u_bound)
            "theorem host {u v: obj}: $ u = v $;\n"
        else
            "theorem host (u: obj): $ u = u $;\n";
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort ctx;
            \\sort obj;
            \\
            \\term iff (a b: wff): wff;
            \\infixr iff: $<->$ prec 20;
            \\term eq (a b: obj): wff;
            \\infixl eq: $=$ prec 35;
            \\
            \\term ctx_eq (g h: ctx): wff;
            \\term emp: ctx;
            \\--| @acui ctx_assoc ctx_comm emp ctx_idem
            \\term join (g h: ctx): ctx;
            \\infixl join: $,$ prec 5;
            \\term hyp (a: wff): ctx;
            \\coercion hyp: wff > ctx;
            \\term nd (g: ctx) (a: wff): wff;
            \\infixl nd: $|-$ prec 0;
            \\
            \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
            \\axiom iff_refl (a: wff): $ a <-> a $;
            \\axiom iff_trans (a b c: wff):
            \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
            \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
            \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
            \\
            \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
            \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
            \\axiom ctx_trans (g h i: ctx):
            \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
            \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
            \\axiom ctx_assoc (g h i: ctx):
            \\  $ ctx_eq ((g , h) , i) (g , (h , i)) $;
            \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
            \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
            \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
            \\
            \\--| @congr
            \\axiom join_congr (g1 g2 h1 h2: ctx):
            \\  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ >
            \\  $ ctx_eq (g1 , h1) (g2 , h2) $;
            \\
            \\--| @congr
            \\axiom nd_congr (g h: ctx) (a b: wff):
            \\  $ ctx_eq g h $ > $ a <-> b $ > $ (g |- a) <-> (h |- b) $;
            \\
        ++ def_body ++ host;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        errdefer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
        var host_assertion: ?AssertionStmt = null;

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .sort => try env.addStmt(stmt),
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        term_stmt.name,
                        parser.last_annotations,
                    );
                },
                .assertion => |assertion| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        assertion.name,
                        parser.last_annotations,
                    );
                    if (std.mem.eql(u8, assertion.name, "host")) {
                        host_assertion = assertion;
                    }
                },
            }
        }

        var theorem = TheoremContext.init(arena.allocator());
        errdefer theorem.deinit();
        const host_stmt = host_assertion orelse return error.MissingAssertion;
        try theorem.seedAssertion(host_stmt);

        const u = theorem.theorem_vars.items[0];
        const v: ExprId = if (host_u_bound)
            theorem.theorem_vars.items[1]
        else
            u;
        const r: ?ExprId = if (full_acui)
            theorem.theorem_vars.items[if (host_u_bound) 2 else 1]
        else
            null;
        const eq_term_id = env.term_names.get("eq") orelse {
            return error.MissingTerm;
        };
        const hyp_term_id = env.term_names.get("hyp") orelse {
            return error.MissingTerm;
        };
        const nd_term_id = env.term_names.get("nd") orelse {
            return error.MissingTerm;
        };
        const join_term_id = env.term_names.get("join") orelse {
            return error.MissingTerm;
        };
        const emp_term_id = env.term_names.get("emp") orelse {
            return error.MissingTerm;
        };
        const pre_ctx_term_id = env.term_names.get("pre_ctx") orelse {
            return error.MissingTerm;
        };

        const eq_uv = try theorem.interner.internApp(
            eq_term_id,
            &[_]ExprId{ u, v },
        );
        const hyp_uv = try theorem.interner.internApp(
            hyp_term_id,
            &[_]ExprId{eq_uv},
        );
        const target_ctx = if (full_acui)
            try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{
                    try theorem.interner.internApp(
                        hyp_term_id,
                        &[_]ExprId{r.?},
                    ),
                    hyp_uv,
                },
            )
        else
            hyp_uv;
        const target_expr = try theorem.interner.internApp(
            nd_term_id,
            &[_]ExprId{ target_ctx, eq_uv },
        );
        const emp_expr = try theorem.interner.internApp(emp_term_id, &.{});
        const expected_ctx = if (full_acui) blk: {
            const left = try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ emp_expr, hyp_uv },
            );
            const r_ctx = try theorem.interner.internApp(
                hyp_term_id,
                &[_]ExprId{r.?},
            );
            const right_tail = try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ hyp_uv, emp_expr },
            );
            const right = try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ r_ctx, right_tail },
            );
            break :blk try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ left, right },
            );
        } else try theorem.interner.internApp(
            join_term_id,
            &[_]ExprId{ hyp_uv, emp_expr },
        );
        const expected_witness = try theorem.interner.internApp(
            nd_term_id,
            &[_]ExprId{ expected_ctx, eq_uv },
        );
        const pre_ctx_expr = if (full_acui)
            try theorem.interner.internApp(
                pre_ctx_term_id,
                &[_]ExprId{ u, r.? },
            )
        else
            try theorem.interner.internApp(
                pre_ctx_term_id,
                &[_]ExprId{u},
            );

        return .{
            .arena = arena,
            .env = env,
            .registry = registry,
            .theorem = theorem,
            .pre_ctx_expr = pre_ctx_expr,
            .target_expr = target_expr,
            .expected_witness = expected_witness,
        };
    }

    fn deinit(self: *SemanticWrappedAcuiDefFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};


const SemanticQuantifiedAcuiDefFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    pre_ctx_expr: ExprId,
    target_expr: ExprId,
    expected_witness: ExprId,

    fn init(comptime full_acui: bool) !SemanticQuantifiedAcuiDefFixture {
        const def_body = if (full_acui)
            "def pre_ctx (u: obj) (r: wff) {.x: obj}: wff =\n" ++
                "  $ A. x (((emp , hyp (u = x)) , (hyp r , " ++
                "(hyp (u = x) , emp))) |- (u = x)) $;\n\n"
        else
            "def pre_ctx (u: obj) {.x: obj}: wff =\n" ++
                "  $ A. x ((hyp (u = x) , emp) |- (u = x)) $;\n\n";
        const host = if (full_acui)
            "theorem host {u v: obj} (r: wff): $ u = v $;\n"
        else
            "theorem host {u v: obj}: $ u = v $;\n";
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort ctx;
            \\sort obj;
            \\
            \\term all {x: obj} (p: wff x): wff;
            \\prefix all: $A.$ prec 41;
            \\term eq (a b: obj): wff;
            \\infixl eq: $=$ prec 35;
            \\term ctx_eq (g h: ctx): wff;
            \\term emp: ctx;
            \\--| @acui ctx_assoc ctx_comm emp ctx_idem
            \\term join (g h: ctx): ctx;
            \\infixl join: $,$ prec 5;
            \\term hyp (a: wff): ctx;
            \\coercion hyp: wff > ctx;
            \\term nd (g: ctx) (a: wff): wff;
            \\infixl nd: $|-$ prec 0;
            \\
            \\axiom ctx_assoc (g h i: ctx):
            \\  $ ctx_eq ((g , h) , i) (g , (h , i)) $;
            \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
            \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
            \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
            \\
        ++ def_body ++ host;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        errdefer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var registry = RewriteRegistry.init(arena.allocator());
        var host_assertion: ?AssertionStmt = null;

        while (try parser.next()) |stmt| {
            switch (stmt) {
                .sort => try env.addStmt(stmt),
                .term => |term_stmt| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        term_stmt.name,
                        parser.last_annotations,
                    );
                },
                .assertion => |assertion| {
                    try env.addStmt(stmt);
                    try registry.processAnnotations(
                        &env,
                        assertion.name,
                        parser.last_annotations,
                    );
                    if (std.mem.eql(u8, assertion.name, "host")) {
                        host_assertion = assertion;
                    }
                },
            }
        }

        var theorem = TheoremContext.init(arena.allocator());
        errdefer theorem.deinit();
        const host_stmt = host_assertion orelse return error.MissingAssertion;
        try theorem.seedAssertion(host_stmt);

        const u = theorem.theorem_vars.items[0];
        const v = theorem.theorem_vars.items[1];
        const r: ?ExprId = if (full_acui)
            theorem.theorem_vars.items[2]
        else
            null;
        const all_term_id = env.term_names.get("all") orelse {
            return error.MissingTerm;
        };
        const eq_term_id = env.term_names.get("eq") orelse {
            return error.MissingTerm;
        };
        const hyp_term_id = env.term_names.get("hyp") orelse {
            return error.MissingTerm;
        };
        const nd_term_id = env.term_names.get("nd") orelse {
            return error.MissingTerm;
        };
        const join_term_id = env.term_names.get("join") orelse {
            return error.MissingTerm;
        };
        const emp_term_id = env.term_names.get("emp") orelse {
            return error.MissingTerm;
        };
        const pre_ctx_term_id = env.term_names.get("pre_ctx") orelse {
            return error.MissingTerm;
        };

        const eq_uv = try theorem.interner.internApp(
            eq_term_id,
            &[_]ExprId{ u, v },
        );
        const hyp_uv = try theorem.interner.internApp(
            hyp_term_id,
            &[_]ExprId{eq_uv},
        );
        const target_ctx = if (full_acui)
            try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{
                    try theorem.interner.internApp(
                        hyp_term_id,
                        &[_]ExprId{r.?},
                    ),
                    hyp_uv,
                },
            )
        else
            hyp_uv;
        const target_nd = try theorem.interner.internApp(
            nd_term_id,
            &[_]ExprId{ target_ctx, eq_uv },
        );
        const target_expr = try theorem.interner.internApp(
            all_term_id,
            &[_]ExprId{ v, target_nd },
        );
        const emp_expr = try theorem.interner.internApp(emp_term_id, &.{});
        const expected_ctx = if (full_acui) blk: {
            const left = try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ emp_expr, hyp_uv },
            );
            const r_ctx = try theorem.interner.internApp(
                hyp_term_id,
                &[_]ExprId{r.?},
            );
            const right_tail = try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ hyp_uv, emp_expr },
            );
            const right = try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ r_ctx, right_tail },
            );
            break :blk try theorem.interner.internApp(
                join_term_id,
                &[_]ExprId{ left, right },
            );
        } else try theorem.interner.internApp(
            join_term_id,
            &[_]ExprId{ hyp_uv, emp_expr },
        );
        const expected_nd = try theorem.interner.internApp(
            nd_term_id,
            &[_]ExprId{ expected_ctx, eq_uv },
        );
        const expected_witness = try theorem.interner.internApp(
            all_term_id,
            &[_]ExprId{ v, expected_nd },
        );
        const pre_ctx_expr = if (full_acui)
            try theorem.interner.internApp(
                pre_ctx_term_id,
                &[_]ExprId{ u, r.? },
            )
        else
            try theorem.interner.internApp(
                pre_ctx_term_id,
                &[_]ExprId{u},
            );

        return .{
            .arena = arena,
            .env = env,
            .registry = registry,
            .theorem = theorem,
            .pre_ctx_expr = pre_ctx_expr,
            .target_expr = target_expr,
            .expected_witness = expected_witness,
        };
    }

    fn deinit(self: *SemanticQuantifiedAcuiDefFixture) void {
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

fn hasConcreteUnfold(
    steps: []const SemanticStepCandidate,
    expr_id: ExprId,
    term_id: u32,
) bool {
    for (steps) |step| {
        switch (step) {
            .unfold_concrete_def => |unfold| {
                if (unfold.expr_id == expr_id and unfold.term_id == term_id) {
                    return true;
                }
            },
            else => {},
        }
    }
    return false;
}

fn hasSymbolicUnfold(
    steps: []const SemanticStepCandidate,
    term_id: u32,
) bool {
    for (steps) |step| {
        switch (step) {
            .unfold_symbolic_def => |unfold| {
                if (unfold.term_id == term_id) return true;
            },
            else => {},
        }
    }
    return false;
}

fn hasRewriteRule(
    steps: []const SemanticStepCandidate,
    rule_id: u32,
    head_term_id: u32,
) bool {
    for (steps) |step| {
        switch (step) {
            .rewrite_rule => |rule| {
                if (rule.rule_id == rule_id and rule.head_term_id == head_term_id) {
                    return true;
                }
            },
            else => {},
        }
    }
    return false;
}

fn hasAcuiHead(
    steps: []const SemanticStepCandidate,
    head_term_id: u32,
) bool {
    for (steps) |step| {
        switch (step) {
            .acui => |acui| {
                if (acui.head_term_id == head_term_id) return true;
            },
            else => {},
        }
    }
    return false;
}

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
    try ctx.collectSemanticStepCandidatesExpr(
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
    try ctx.collectSemanticStepCandidatesExpr(
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
    try ctx.collectSemanticStepCandidatesExpr(
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
    try ctx.collectSemanticStepCandidatesExpr(
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
    try ctx.collectSemanticStepCandidatesExpr(
        fixture.comp_expr,
        &comp_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), comp_steps.items.len);

    var ctx_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer ctx_steps.deinit(fixture.arena.allocator());
    try ctx.collectSemanticStepCandidatesExpr(
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
    mono_args[0] = try ctx.allocSymbolic(.{ .fixed = fixture.comp_expr });
    const symbolic_mono = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer symbolic_steps.deinit(fixture.arena.allocator());
    try ctx.collectSemanticStepCandidatesSymbolic(
        symbolic_mono,
        &symbolic_steps,
    );
    try std.testing.expect(
        hasSymbolicUnfold(symbolic_steps.items, fixture.mono_term_id),
    );

    const fixed_comp = try ctx.allocSymbolic(.{ .fixed = fixture.comp_expr });
    var fixed_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer fixed_steps.deinit(fixture.arena.allocator());
    try ctx.collectSemanticStepCandidatesSymbolic(
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
    mono_args[0] = try ctx.allocSymbolic(.{ .fixed = fixture.comp_expr });
    const symbolic_mono = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    try std.testing.expect(
        try ctx.matchSymbolicToExprSemantic(
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
    mono_args[0] = try ctx.allocSymbolic(.{ .fixed = fixture.comp_expr });
    const symbolic_mono = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());
    const start_dummy_info_len = state.symbolic_dummy_infos.items.len;
    const start_witness_count = state.witnesses.count();

    try std.testing.expect(!try ctx.matchSymbolicToExprSemantic(
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
    const result = try ctx.applyRewriteRuleToExpr(
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
    rhs_inner_args[0] = try ctx.allocSymbolic(.{ .fixed = f });
    rhs_inner_args[1] = try ctx.allocSymbolic(.{ .fixed = alpha });
    const rhs_inner = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = rhs_inner_args,
    } });

    const expected_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    expected_args[0] = try ctx.allocSymbolic(.{ .fixed = g });
    expected_args[1] = rhs_inner;
    const expected = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = expected_args,
    } });

    try std.testing.expect(ctx.symbolicExprEql(result, expected));
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
    const dummy0 = try ctx.allocSymbolic(.{ .dummy = 0 });
    const dummy1 = try ctx.allocSymbolic(.{ .dummy = 1 });

    const lhs_inner_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    lhs_inner_args[0] = try ctx.allocSymbolic(.{ .fixed = f });
    lhs_inner_args[1] = dummy0;
    const lhs_inner = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = lhs_inner_args,
    } });

    const lhs_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    lhs_args[0] = lhs_inner;
    lhs_args[1] = dummy1;
    const lhs = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = lhs_args,
    } });

    const rule = fixture.registry.getRewriteRules(
        fixture.comp_term_id,
    )[0];
    const result = try ctx.applyRewriteRuleToSymbolic(
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
    const rhs_inner = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = rhs_inner_args,
    } });

    const expected_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    expected_args[0] = try ctx.allocSymbolic(.{ .fixed = f });
    expected_args[1] = rhs_inner;
    const expected = try ctx.allocSymbolic(.{ .app = .{
        .term_id = fixture.comp_term_id,
        .args = expected_args,
    } });

    try std.testing.expect(ctx.symbolicExprEql(result, expected));
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
        (try ctx.applyRewriteRuleToExpr(
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
