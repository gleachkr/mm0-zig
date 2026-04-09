const std = @import("std");
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const SemanticStepCandidate =
    @import("../symbolic_engine.zig").SemanticStepCandidate;
const BindingSeed = @import("../types.zig").BindingSeed;
const ArgInfo = @import("../../../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../../trusted/parse.zig").MM0Parser;
const Expr = @import("../../../trusted/expressions.zig").Expr;

pub const SessionWitnessFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    theorem: TheoremContext,
    actual: ExprId,
    raw: ExprId,
    rule_args: []const ArgInfo,
    body: TemplateExpr,
    dummy_arg_count: usize,

    pub fn init() !SessionWitnessFixture {
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

    pub fn deinit(self: *SessionWitnessFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

pub const SemanticStepFixture = struct {
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

    pub fn init() !SemanticStepFixture {
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

    pub fn deinit(self: *SemanticStepFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

pub const SemanticAcuiExposureFixture = struct {
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

    pub fn init(
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

    pub fn deinit(self: *SemanticAcuiExposureFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

pub const SemanticWrappedAcuiDefFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    pre_ctx_expr: ExprId,
    target_expr: ExprId,
    expected_witness: ExprId,

    pub fn init(
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

    pub fn deinit(self: *SemanticWrappedAcuiDefFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

pub const SemanticQuantifiedAcuiDefFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    pre_ctx_expr: ExprId,
    target_expr: ExprId,
    expected_witness: ExprId,

    pub fn init(comptime full_acui: bool) !SemanticQuantifiedAcuiDefFixture {
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

    pub fn deinit(self: *SemanticQuantifiedAcuiDefFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

pub fn allocNoneSeeds(
    allocator: std.mem.Allocator,
    len: usize,
) ![]BindingSeed {
    const seeds = try allocator.alloc(BindingSeed, len);
    for (seeds) |*seed| {
        seed.* = .none;
    }
    return seeds;
}

pub fn hasConcreteUnfold(
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

pub fn hasSymbolicUnfold(
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

pub fn hasRewriteRule(
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

pub fn hasAcuiHead(
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
