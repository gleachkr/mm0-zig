const std = @import("std");

const DefOps = @import("../../def_ops.zig");
const FrontendEnv = @import("../../env.zig");
const FrontendExpr = @import("../../expr.zig");
const Expr = @import("../../../trusted/expressions.zig").Expr;
const MM0Parser = @import("../../../trusted/parse.zig").MM0Parser;
const allocNoneSeeds = @import("./fixtures.zig").allocNoneSeeds;

fn readProofCaseFile(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

fn expectCompareTransparent(
    src: []const u8,
    lhs_text: []const u8,
    rhs_text: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const lhs_expr = try parser.parseFormulaText(lhs_text, &theorem_vars);
    const rhs_expr = try parser.parseFormulaText(rhs_text, &theorem_vars);
    const lhs = try theorem.internParsedExpr(lhs_expr);
    const rhs = try theorem.internParsedExpr(rhs_expr);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    try std.testing.expect((try def_ops.compareTransparent(lhs, rhs)) != null);
    try std.testing.expect((try def_ops.compareTransparent(rhs, lhs)) != null);
}

test "transparent comparison unfolds bic and allc under coercion" {
    const src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / ! $ $ . : ; ) ] $;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\sort term;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\term all: type > term;
        \\def allc {x: term} (A: type) (t: term x): term =
        \\  $ all A · (λ x: A. t) $;
        \\notation allc {x: term} (A: type) (t: term x): term =
        \\  ($!$:20) x ($:$:2) A ($.$:0) t;
        \\theorem host (A: type) {x: term} (t u: term x):
        \\  $ (!x: A. t) ⇔ (!x: A. u) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();
    var host_assertion: ?@import("../../../trusted/parse.zig").AssertionStmt = null;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem) continue;
                if (!std.mem.eql(u8, value.name, "host")) continue;
                try theorem.seedAssertion(value);
                host_assertion = value;
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                break;
            },
            else => {},
        }
    }

    const assertion = host_assertion orelse return error.MissingAssertion;
    const theorem_concl = try theorem.internParsedExpr(assertion.concl);
    const rhs_expr = try parser.parseFormulaText(
        " ≃[𝔹] all A · (λ x: A. t) = all A · (λ x: A. u) ",
        &theorem_vars,
    );
    const rhs = try theorem.internParsedExpr(rhs_expr);
    const rule_id = env.getRuleId("all_bic_raw") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const final_line = try theorem.instantiateTemplate(
        rule.concl,
        theorem.theorem_vars.items,
    );

    try std.testing.expectEqual(rhs, final_line);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    try std.testing.expect((try def_ops.compareTransparent(
        theorem_concl,
        final_line,
    )) != null);
    try std.testing.expect((try def_ops.compareTransparent(
        final_line,
        theorem_concl,
    )) != null);
}

test "targeted def module has no standalone opening API" {
    try std.testing.expect(!@hasDecl(DefOps.Context, "openConcreteDef"));
}

fn exprContainsExprId(
    theorem: *const FrontendExpr.TheoremContext,
    root: FrontendExpr.ExprId,
    needle: FrontendExpr.ExprId,
) bool {
    if (root == needle) return true;
    return switch (theorem.interner.node(root).*) {
        .variable => false,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (exprContainsExprId(theorem, arg, needle)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

test "def matcher binds quantified templates through hidden dummies" {
    const allocator = std.testing.allocator;
    const src = try readProofCaseFile(
        allocator,
        "pass_def_all_elim_free_param",
        "mm0",
    );
    defer allocator.free(src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const rule_id = env.getRuleId("all_elim") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    const parsed_actual = try parser.parseFormulaText(" mono f ", &theorem_vars);
    const actual = try theorem.internParsedExpr(parsed_actual);

    const bindings = try allocator.alloc(?FrontendExpr.ExprId, rule.args.len);
    defer allocator.free(bindings);
    @memset(bindings, null);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    try std.testing.expect(try def_ops.matchTemplateTransparent(
        rule.hyps[0],
        actual,
        bindings,
    ));

    // Public template matching now stays on the resolved, non-escaping path.
    // Hidden def dummies therefore remain unresolved here instead of being
    // materialized into fresh theorem-local dummy vars.
    try std.testing.expect(bindings[0] == null);
    try std.testing.expect(bindings[1] == null);
    try std.testing.expect(bindings[2] == null);
    try std.testing.expectEqual(@as(usize, 0), theorem.theorem_dummies.items.len);
}

test "def matcher opens nested user-side defs under matching heads" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ (a -> a) -> (a -> a) $;
    ;

    try expectCompareTransparent(
        src,
        " (a -> double a) -> (a -> a) ",
        " (a -> (a -> a)) -> (a -> a) ",
    );
}

test "def matcher opens nested user-side defs on both sides" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\def alias (a: wff): wff = $ double a $;
        \\def wrap (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ (a -> a) -> (a -> a) $;
    ;

    try expectCompareTransparent(
        src,
        " (a -> alias a) -> (a -> a) ",
        " (a -> wrap a) -> (a -> a) ",
    );
}

test "def matcher opens nested user-side defs through repeated heads" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\def alias (a: wff): wff = $ double a $;
        \\def wrap (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ ((a -> a) -> (a -> a)) -> (a -> a) $;
    ;

    try expectCompareTransparent(
        src,
        " ((a -> alias a) -> (a -> a)) -> (a -> a) ",
        " ((a -> wrap a) -> (a -> a)) -> (a -> a) ",
    );
}

test "def conversion plan unfolds to an exact target" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ a -> a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const lhs_expr = try parser.parseFormulaText(" double a ", &theorem_vars);
    const rhs_expr = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const lhs = try theorem.internParsedExpr(lhs_expr);
    const rhs = try theorem.internParsedExpr(rhs_expr);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    const plan = try def_ops.compareTransparent(lhs, rhs);
    const step = plan orelse return error.ExpectedConversionPlan;
    switch (step.*) {
        .unfold_lhs => |unfold| {
            try std.testing.expectEqual(rhs, unfold.witness);
            try std.testing.expect(unfold.next.* == .refl);
        },
        else => return error.UnexpectedConversionPlan,
    }
}

test "semantic seeds finalize to representatives while exact seeds stay raw" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\axiom keep (p: wff): $ p $;
        \\theorem host (a: wff): $ double a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const rule_id = env.getRuleId("keep") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const raw_expr = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const raw = try theorem.internParsedExpr(raw_expr);
    const folded_expr = try parser.parseFormulaText(" double a ", &theorem_vars);
    const folded = try theorem.internParsedExpr(folded_expr);

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var semantic_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .semantic = .{
            .expr_id = raw,
            .mode = .transparent,
        } }},
    );
    defer semantic_session.deinit();
    const semantic_bindings = try semantic_session.finalizeConcreteBindings();
    try std.testing.expectEqual(@as(usize, 1), semantic_bindings.len);
    try std.testing.expectEqual(folded, semantic_bindings[0]);

    var exact_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .exact = raw }},
    );
    defer exact_session.deinit();
    const exact_bindings = try exact_session.finalizeConcreteBindings();
    try std.testing.expectEqual(@as(usize, 1), exact_bindings.len);
    try std.testing.expectEqual(raw, exact_bindings[0]);
}

test "semantic seeds reuse representative-aware matches" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\axiom dup (p: wff): $ p -> p $;
        \\theorem host (a: wff): $ double a -> double a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const rule_id = env.getRuleId("dup") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const raw_expr = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const raw = try theorem.internParsedExpr(raw_expr);
    const folded_expr = try parser.parseFormulaText(" double a ", &theorem_vars);
    const folded = try theorem.internParsedExpr(folded_expr);
    const actual_expr =
        try parser.parseFormulaText(" double a -> double a ", &theorem_vars);
    const actual = try theorem.internParsedExpr(actual_expr);

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var semantic_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .semantic = .{
            .expr_id = raw,
            .mode = .transparent,
        } }},
    );
    defer semantic_session.deinit();
    try std.testing.expect(
        try semantic_session.matchTransparent(rule.concl, actual),
    );
    const semantic_bindings = try semantic_session.finalizeConcreteBindings();
    try std.testing.expectEqual(@as(usize, 1), semantic_bindings.len);
    try std.testing.expectEqual(folded, semantic_bindings[0]);

    var exact_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .exact = raw }},
    );
    defer exact_session.deinit();
    try std.testing.expect(
        !(try exact_session.matchTransparent(rule.concl, actual)),
    );
}

test "finalization rejects unresolved hidden-dummy witnesses" {
    // When matching through a def with hidden dummies produces symbolic
    // bindings containing unresolved dummy structure, finalization
    // returns error.UnresolvedDummyWitness. The user must provide
    // explicit bindings that cover the hidden def structure.
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const parsed_actual = try parser.parseFormulaText(" mono f ", &theorem_vars);
    const actual = try theorem.internParsedExpr(parsed_actual);

    // keep_all has binders {x: obj} (p: wff x), hyp = $ ∀ x p $.
    // Matching hyp against "mono f" forces unfolding of mono and
    // produces symbolic bindings with hidden-dummy structure.
    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, &.{ .none, .none });
    defer session.deinit();

    // Match hyp (∀ x p) against "mono f". The symbolic engine unfolds mono
    // and binds x → hidden dummy .a, p → ∀ b (...) symbolically.
    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));

    const dummies_before = theorem.theorem_dummies.items.len;

    // Finalization rejects unresolved hidden-dummy witnesses.
    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session.finalizeConcreteBindings(),
    );

    // No dummies should have been allocated.
    try std.testing.expectEqual(dummies_before, theorem.theorem_dummies.items.len);
}

test "materialized dummy assignments can finalize hidden def bindings" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const actual = try theorem.internParsedExpr(
        try parser.parseFormulaText(" mono f ", &theorem_vars),
    );

    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, &.{ .none, .none });
    defer session.deinit();

    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));
    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session.finalizeConcreteBindings(),
    );

    const roots = try session.collectUnresolvedFinalizationRoots();
    defer arena.allocator().free(roots);
    try std.testing.expect(roots.len != 0);

    const sort_id = env.sort_names.get("obj") orelse return error.UnknownSort;
    const assignments = try arena.allocator().alloc(
        DefOps.MaterializedDummyAssignment,
        roots.len,
    );
    for (roots, assignments) |root, *assignment| {
        assignment.* = .{
            .root_slot = root.root_slot,
            .expr_id = try theorem.addDummyVarResolved("obj", sort_id),
        };
    }
    const witness_count = session.state.witnesses.count();

    try session.applyMaterializedDummyAssignments(assignments);

    try std.testing.expectEqual(witness_count, session.state.witnesses.count());
    try std.testing.expectEqual(
        roots.len,
        session.state.materialized_witnesses.count(),
    );

    const bindings = try session.finalizeConcreteBindings();
    defer arena.allocator().free(bindings);
    try std.testing.expectEqual(rule.args.len, bindings.len);
}

test "exact hidden-binder seeds match repeated def expansions" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const actual = try theorem.internParsedExpr(
        try parser.parseFormulaText(" mono f ", &theorem_vars),
    );
    const exact_x = try theorem.addDummyVarResolved("obj", 0);

    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(
        rule.args,
        &.{ .{ .exact = exact_x }, .none },
    );
    defer session.deinit();

    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));
}

test "collectConcreteDepsForPendingFinalization sees exact dummy seeds" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const actual = try theorem.internParsedExpr(
        try parser.parseFormulaText(" mono f ", &theorem_vars),
    );
    const sort_id = env.sort_names.get("obj") orelse return error.UnknownSort;
    const exact_x = try theorem.addDummyVarResolved("obj", sort_id);
    const dummy_id = switch (theorem.interner.node(exact_x).*.variable) {
        .dummy_var => |idx| idx,
        else => unreachable,
    };
    const exact_dep = theorem.theorem_dummies.items[dummy_id].deps;

    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(
        rule.args,
        &.{ .{ .exact = exact_x }, .none },
    );
    defer session.deinit();

    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));

    const deps = try session.collectConcreteDepsForPendingFinalization();
    try std.testing.expect((deps & exact_dep) != 0);
}

test "symbolic transparent bindings fall back to representatives" {
    const allocator = std.testing.allocator;
    const src = try readProofCaseFile(
        allocator,
        "pass_alleq_transparent_inference",
        "mm0",
    );
    defer allocator.free(src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const hyp_text =
        " G ∧ ≃[𝔹] p = a ∧ q: 𝔹 ∧ r: 𝔹 ⊢" ++
        " ≃[𝔹] imp · (imp · p · r) ·" ++
        " (imp · (imp · q · r) · r) =" ++
        " imp · (imp · a · r) ·" ++
        " (imp · (imp · q · r) · r) ";
    const concl_text =
        " G ∧ ≃[𝔹] p = a ∧ q: 𝔹 ⊢" ++
        " all 𝔹 · (λ r: 𝔹. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r) ⇔" ++
        " (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r)) ";
    const ref_expr = try theorem.internParsedExpr(
        try parser.parseFormulaText(hyp_text, &theorem_vars),
    );
    const line_expr = try theorem.internParsedExpr(
        try parser.parseFormulaText(concl_text, &theorem_vars),
    );

    const rule_id = env.getRuleId("alleq") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const seeds = try allocNoneSeeds(allocator, rule.args.len);
    defer allocator.free(seeds);

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, seeds);
    defer session.deinit();

    try std.testing.expect(
        try session.matchTransparent(rule.hyps[0], ref_expr),
    );
    try std.testing.expect(
        try session.matchTransparent(rule.concl, line_expr),
    );
}

test "transparent matching reuses resolved allc representatives" {
    const allocator = std.testing.allocator;
    const src =
        \\strict provable sort wff;
        \\
        \\delimiter $ ( @ [ / ! $ $ . : ; ) ] $;
        \\
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\
        \\term an: wff > wff > wff;
        \\infixl an: $∧$ prec 1;
        \\
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\
        \\sort term;
        \\term ty: term > type > wff;
        \\infixl ty: $:$ prec 2;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\term imp: term;
        \\def impc (p q: term): term = $ imp · p · q $;
        \\infixr impc: $⇒$ prec 30;
        \\term all: type > term;
        \\def allc {x: term} (A: type) (t: term x): term =
        \\  $ all A · (λ x: A. t) $;
        \\notation allc {x: term} (A: type) (t: term x): term =
        \\  ($!$:20) x ($:$:2) A ($.$:0) t;
        \\
        \\axiom betacv (G: wff) (A B: type) {x: term} (t u v: term x):
        \\  $ G ∧ x: A ⊢ u: B $ >
        \\  $ G ⊢ t: A $ >
        \\  $ G ⊢ v: B $ >
        \\  $ G ∧ ≃[A] x = t ⊢ ≃[B] u = v $ >
        \\  $ G ⊢ ≃[B] (λ x: A. u) · t = v $;
        \\
        \\theorem orc_betacv_probe (G: wff) (a b: term) {q r: term}:
        \\  $ G ∧ q: 𝔹 ⊢ !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r: 𝔹 $ >
        \\  $ G ⊢ b: 𝔹 $ >
        \\  $ G ⊢ all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r): 𝔹 $ >
        \\  $ G ∧ ≃[𝔹] q = b ⊢
        \\      (!r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) ⇔
        \\      (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $ >
        \\  $ G ⊢ ≃[𝔹]
        \\      ((λ q: 𝔹. !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) · b) =
        \\      (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $;
    ;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();

    const assertion = blk: {
        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |value| {
                    if (value.kind != .theorem) continue;
                    if (!std.mem.eql(
                        u8,
                        value.name,
                        "orc_betacv_probe",
                    )) continue;
                    try theorem.seedAssertion(value);
                    for (value.arg_names, value.arg_exprs) |name, expr| {
                        if (name) |actual_name| {
                            try theorem_vars.put(actual_name, expr);
                        }
                    }
                    break :blk value;
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };

    const rule_id = env.getRuleId("betacv") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const seeds = try allocNoneSeeds(allocator, rule.args.len);
    defer allocator.free(seeds);

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, seeds);
    defer session.deinit();

    try std.testing.expect(
        try session.matchTransparent(rule.hyps[0], theorem.theorem_hyps.items[0]),
    );
    try std.testing.expect(
        try session.matchTransparent(rule.hyps[1], theorem.theorem_hyps.items[1]),
    );
    try std.testing.expect(
        try session.matchTransparent(rule.hyps[2], theorem.theorem_hyps.items[2]),
    );
    try std.testing.expect(
        try session.matchTransparent(rule.hyps[3], theorem.theorem_hyps.items[3]),
    );

    const concl = try theorem.internParsedExpr(assertion.concl);
    try std.testing.expect(
        try session.matchTransparent(rule.concl, concl),
    );
}

test "resolveBindingSeeds preserves symbolic state through view reuse" {
    // Same setup as the strict finalization test: matching "mono f" against
    // keep_all's ∀ x p produces symbolic bindings with hidden-dummy structure.
    // resolveBindingSeeds should return .bound seeds (preserving symbolic
    // BoundValues) where resolveOptionalBindings would lose the info.
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const parsed_actual = try parser.parseFormulaText(" mono f ", &theorem_vars);
    const actual = try theorem.internParsedExpr(parsed_actual);

    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, &.{ .none, .none });
    defer session.deinit();

    // Match hyp (∀ x p) against "mono f" — produces symbolic bindings.
    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));

    // materializeOptionalBindings collapses symbolic bindings to null where
    // the symbolic structure contains unresolved hidden dummies.
    const optional = try session.materializeOptionalBindings();
    defer arena.allocator().free(optional);

    // resolveBindingSeeds should preserve symbolic state as .bound seeds.
    const binding_seeds = try session.resolveBindingSeeds();

    // At least one seed should be .bound (symbolic), not .none.
    var has_bound_seed = false;
    for (binding_seeds) |seed| {
        switch (seed) {
            .bound => {
                has_bound_seed = true;
            },
            else => {},
        }
    }
    try std.testing.expect(has_bound_seed);

    var seed_state = try session.exportMatchSeedState(binding_seeds);
    defer seed_state.deinit(arena.allocator());

    // The exported state should be usable in a new session without any
    // side-channel import step, and without allocating theorem dummies.
    const dummies_before = theorem.theorem_dummies.items.len;

    var session2 = try def_ops.beginRuleMatchFromSeedState(
        rule.args,
        &seed_state,
    );
    defer session2.deinit();

    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session2.finalizeConcreteBindings(),
    );
    try std.testing.expectEqual(
        dummies_before,
        theorem.theorem_dummies.items.len,
    );
}
