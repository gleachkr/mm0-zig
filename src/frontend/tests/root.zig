const std = @import("std");
const mm0 = @import("mm0");

const FrontendEnv = mm0.Frontend.Env;
const FrontendExpr = mm0.Frontend.Expr;
const Expr = mm0.Expr;
const MM0Parser = mm0.MM0Parser;
const ProofScript = mm0.ProofScript;

test "proof script parser reads theorem blocks and proof lines" {
    const src =
        \\id
        \\--
        \\l1: $ a -> a $ by ax_1 (a := $ a $, b := $ a $) []
        \\l2: $ a $ by ax_mp (a := $ a $, b := $ a $) [#1, l1]
        \\
        \\other
        \\l1: $ b $ by ax_b []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const first = (try parser.nextBlock()).?;
    try std.testing.expect(first.kind == .theorem);
    try std.testing.expectEqualStrings("id", first.name);
    try std.testing.expect(first.underline_span != null);
    try std.testing.expectEqual(@as(usize, 2), first.lines.len);
    try std.testing.expectEqualStrings("l1", first.lines[0].label);
    try std.testing.expectEqualStrings(" a -> a ", first.lines[0].assertion.text);
    try std.testing.expectEqualStrings("ax_mp", first.lines[1].rule_name);
    try std.testing.expectEqual(@as(usize, 2), first.lines[1].arg_bindings.len);
    try std.testing.expectEqualStrings(
        "a",
        first.lines[1].arg_bindings[0].name,
    );
    try std.testing.expectEqual(@as(usize, 2), first.lines[1].refs.len);
    switch (first.lines[1].refs[0]) {
        .hyp => |hyp| try std.testing.expectEqual(@as(usize, 1), hyp.index),
        else => return error.UnexpectedRefKind,
    }
    switch (first.lines[1].refs[1]) {
        .line => |line| try std.testing.expectEqualStrings("l1", line.label),
        else => return error.UnexpectedRefKind,
    }

    const second = (try parser.nextBlock()).?;
    try std.testing.expect(second.kind == .theorem);
    try std.testing.expectEqualStrings("other", second.name);
    try std.testing.expect(second.underline_span == null);
    try std.testing.expectEqual(@as(usize, 1), second.lines.len);
    try std.testing.expectEqual(
        @as(usize, 0),
        second.lines[0].arg_bindings.len,
    );
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser reads lemma blocks" {
    const src =
        \\lemma id (a: wff): $ a -> a $
        \\---------------------------
        \\l1: $ a -> a $ by ax_id (a := $ a $) []
        \\
        \\main
        \\----
        \\l1: $ a -> a $ by id (a := $ a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const lemma = (try parser.nextBlock()).?;
    try std.testing.expect(lemma.kind == .lemma);
    try std.testing.expectEqualStrings("id", lemma.name);
    try std.testing.expectEqualStrings(
        "(a: wff): $ a -> a $",
        lemma.header_tail,
    );
    try std.testing.expectEqual(@as(usize, 1), lemma.lines.len);

    const theorem = (try parser.nextBlock()).?;
    try std.testing.expect(theorem.kind == .theorem);
    try std.testing.expectEqualStrings("main", theorem.name);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser allows newlines inside math strings" {
    const src =
        \\demo
        \\----
        \\l1: $ a ->
        \\  a $ by ax_id (a := $ a ->
        \\  a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expectEqualStrings(
        " a ->\n  a ",
        block.lines[0].assertion.text,
    );
    try std.testing.expectEqual(@as(usize, 1), block.lines[0].arg_bindings.len);
    try std.testing.expectEqualStrings(
        " a ->\n  a ",
        block.lines[0].arg_bindings[0].formula.text,
    );
}

test "proof script parser allows continuation newlines and comments" {
    const src =
        \\demo
        \\----
        \\l1:
        \\  $ a $
        \\  -- explain the rule choice
        \\  by
        \\  ax_keep
        \\  (
        \\    a := $ a $,
        \\    -- reuse the same witness
        \\    b := $ a $
        \\  )
        \\  [
        \\    #1,
        \\    l0
        \\  ]
        \\l2: $ b $ by ax_b []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqual(@as(usize, 2), block.lines.len);
    try std.testing.expectEqualStrings(" a ", block.lines[0].assertion.text);
    try std.testing.expectEqualStrings("ax_keep", block.lines[0].rule_name);
    try std.testing.expectEqual(@as(usize, 2), block.lines[0].arg_bindings.len);
    try std.testing.expectEqual(@as(usize, 2), block.lines[0].refs.len);
    switch (block.lines[0].refs[0]) {
        .hyp => |hyp| try std.testing.expectEqual(@as(usize, 1), hyp.index),
        else => return error.UnexpectedRefKind,
    }
    switch (block.lines[0].refs[1]) {
        .line => |line| try std.testing.expectEqualStrings("l0", line.label),
        else => return error.UnexpectedRefKind,
    }
    try std.testing.expectEqualStrings("l2", block.lines[1].label);
}

test "theorem context preserves theorem var identity" {
    const src =
        \\provable sort wff;
        \\theorem thm (a b: wff): $ a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(assertion);
    try std.testing.expectEqual(@as(usize, 2), ctx.theorem_vars.items.len);

    const first = ctx.theorem_vars.items[0];
    const second = ctx.theorem_vars.items[1];
    try std.testing.expect(first != second);

    const first_node = ctx.interner.node(first);
    const first_value = first_node.*;
    switch (first_value) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try std.testing.expectEqual(@as(u32, 0), idx);
            },
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }

    const second_node = ctx.interner.node(second);
    const second_value = second_node.*;
    switch (second_value) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try std.testing.expectEqual(@as(u32, 1), idx);
            },
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }
}

test "theorem context rejects dummy dependency slot overflow" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const limit = FrontendExpr.tracked_bound_dep_limit;
    try ctx.seedBinderCount(limit - 1);
    ctx.next_dummy_dep = limit - 1;

    const last_dummy = try ctx.addDummyVarResolved("wff", 0);
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_dummies.items.len);
    try std.testing.expectEqual(
        @as(u55, 1) << @intCast(limit - 1),
        ctx.theorem_dummies.items[0].deps,
    );
    try std.testing.expectEqual(limit, ctx.next_dummy_dep);

    const node = ctx.interner.node(last_dummy);
    switch (node.*) {
        .variable => |var_id| switch (var_id) {
            .dummy_var => |idx| try std.testing.expectEqual(@as(u32, 0), idx),
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }

    try std.testing.expectError(
        error.DependencySlotExhausted,
        ctx.addDummyVarResolved("wff", 0),
    );
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_dummies.items.len);
    try std.testing.expectEqual(limit, ctx.next_dummy_dep);
}

test "theorem context interns parsed expressions with sharing" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\theorem thm (a b: wff): $ imp a b $ > $ imp a b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(assertion);
    const concl_id = try ctx.internParsedExpr(assertion.concl);

    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_hyps.items.len);
    try std.testing.expectEqual(ctx.theorem_hyps.items[0], concl_id);
    try std.testing.expectEqual(@as(usize, 3), ctx.interner.count());
}

test "template instantiation shares repeated substitutions" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom dup (a: wff): $ imp a a $;
        \\theorem host (p q: wff): $ imp p q $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());

    const sort_stmt = (try parser.next()).?;
    try env.addStmt(sort_stmt);
    const term_stmt = (try parser.next()).?;
    try env.addStmt(term_stmt);
    const axiom_stmt = (try parser.next()).?;
    try env.addStmt(axiom_stmt);
    const host_stmt = (try parser.next()).?;
    try env.addStmt(host_stmt);

    const host = switch (host_stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };
    const rule = env.rules.items[0];

    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(host);
    const subst = try ctx.internParsedExpr(host.concl);
    const inst = try ctx.instantiateTemplate(rule.concl, &.{subst});

    const inst_node = ctx.interner.node(inst);
    const inst_value = inst_node.*;
    switch (inst_value) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 0), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            try std.testing.expectEqual(subst, app.args[0]);
            try std.testing.expectEqual(subst, app.args[1]);
        },
        else => return error.UnexpectedExprNode,
    }
}

test "explicit source dummy allocation is allowed and tracks dependency slots" {
    // Explicit user/source dummies (seedTerm, applyDummyBindings) are
    // legitimate and must keep working. This test verifies the low-level
    // addDummyVarResolved API that those paths use.
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    // Allocate two explicit dummies — simulates what seedTerm does for
    // dummies declared in .mm0 source.
    const d0 = try ctx.addDummyVarResolved("wff", 0);
    const d1 = try ctx.addDummyVarResolved("wff", 0);

    // Each allocation should produce a distinct ExprId.
    try std.testing.expect(d0 != d1);

    // Both should be tracked in theorem_dummies.
    try std.testing.expectEqual(@as(usize, 2), ctx.theorem_dummies.items.len);

    // Each should consume a distinct dependency slot (one-hot bit).
    try std.testing.expect(ctx.theorem_dummies.items[0].deps != ctx.theorem_dummies.items[1].deps);

    // The dependency counter should advance by 2.
    try std.testing.expectEqual(@as(u32, 2), ctx.next_dummy_dep);
}

test "placeholder allocation leaves real dummy bookkeeping unchanged" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    _ = try ctx.addDummyVarResolved("wff", 0);
    const start_dummy_id = ctx.next_dummy_id;
    const start_dummy_dep = ctx.next_dummy_dep;

    _ = try ctx.addPlaceholderResolved("wff");
    _ = try ctx.addPlaceholderResolved("wff");

    try std.testing.expectEqual(start_dummy_id, ctx.next_dummy_id);
    try std.testing.expectEqual(start_dummy_dep, ctx.next_dummy_dep);
    try std.testing.expectEqual(
        @as(usize, 1),
        ctx.theorem_dummies.items.len,
    );
    try std.testing.expectEqual(
        @as(usize, 2),
        ctx.theorem_placeholders.items.len,
    );
    try std.testing.expect(
        ctx.theorem_placeholders.items[0].deps !=
            ctx.theorem_placeholders.items[1].deps,
    );
    try std.testing.expect(
        (ctx.theorem_placeholders.items[0].deps &
            ctx.theorem_dummies.items[0].deps) == 0,
    );
}

test "placeholder deps share the global u55 mask budget" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const limit = FrontendExpr.tracked_bound_dep_limit;
    ctx.next_dummy_dep = limit - 1;

    const placeholder = try ctx.addPlaceholderResolved("wff");
    try std.testing.expectEqual(
        @as(u55, 1) << @intCast(limit - 1),
        ctx.theorem_placeholders.items[0].deps,
    );
    try std.testing.expectEqual(@as(u32, 0), ctx.next_dummy_id);
    try std.testing.expectEqual(limit - 1, ctx.next_dummy_dep);
    switch (ctx.interner.node(placeholder).*) {
        .placeholder => |idx| try std.testing.expectEqual(@as(u32, 0), idx),
        else => return error.UnexpectedExprNode,
    }

    try std.testing.expectError(
        error.DependencySlotExhausted,
        ctx.addPlaceholderResolved("wff"),
    );
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_placeholders.items.len);
}

test "placeholder info lookup reports placeholder-specific errors" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try std.testing.expectError(
        error.UnknownPlaceholder,
        ctx.requirePlaceholderInfo(0),
    );
}

test "leaf info helpers cover theorem vars dummies and placeholders" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const ArgInfo = @typeInfo(@TypeOf(ctx.arg_infos)).pointer.child;
    const args = [_]ArgInfo{
        .{ .sort_name = "wff", .bound = false, .deps = 0 },
        .{ .sort_name = "obj", .bound = true, .deps = 1 },
    };
    const arg_exprs = [_]*const Expr{
        &.{ .variable = .{ .sort = 0, .bound = false, .deps = 0 } },
        &.{ .variable = .{ .sort = 0, .bound = true, .deps = 1 } },
    };
    try ctx.seedArgs(args[0..], arg_exprs[0..]);

    const theorem_leaf = (try ctx.currentLeafInfo(ctx.theorem_vars.items[1])) orelse {
        return error.MissingLeafInfo;
    };
    try std.testing.expectEqualStrings("obj", theorem_leaf.sort_name);
    try std.testing.expect(theorem_leaf.bound);
    try std.testing.expectEqual(@as(u55, 1), theorem_leaf.deps);

    const dummy = try ctx.addDummyVarResolved("wff", 0);
    const dummy_leaf = (try ctx.currentLeafInfo(dummy)) orelse {
        return error.MissingLeafInfo;
    };
    try std.testing.expectEqualStrings("wff", dummy_leaf.sort_name);
    try std.testing.expect(dummy_leaf.bound);

    const placeholder = try ctx.addPlaceholderResolved("obj");
    const placeholder_leaf = (try ctx.currentLeafInfo(placeholder)) orelse {
        return error.MissingLeafInfo;
    };
    try std.testing.expectEqualStrings(
        "obj",
        placeholder_leaf.sort_name,
    );
    try std.testing.expect(placeholder_leaf.bound);
    try std.testing.expectEqual(
        placeholder_leaf.sort_name,
        ctx.currentLeafSortName(placeholder).?,
    );
}

test "mirror-only dummy allocation does not affect source theorem context" {
    // Mirror-only allocations (mirror_support.zig, normalized_match.zig)
    // create dummies in a temporary TheoremContext. This test verifies that
    // allocating dummies in a separate mirror context leaves the original
    // source context's dummy count untouched.
    var source = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer source.deinit();

    // Allocate one explicit dummy in the source context.
    _ = try source.addDummyVarResolved("wff", 0);
    try std.testing.expectEqual(@as(usize, 1), source.theorem_dummies.items.len);
    const source_dep_after = source.next_dummy_dep;

    // Create a separate mirror context (simulates MirroredTheoremContext).
    var mirror = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer mirror.deinit();

    // Allocate several dummies in the mirror context.
    _ = try mirror.addDummyVarResolved("wff", 0);
    _ = try mirror.addDummyVarResolved("wff", 0);
    _ = try mirror.addDummyVarResolved("wff", 0);

    // Mirror allocations should not have touched the source context.
    try std.testing.expectEqual(@as(usize, 1), source.theorem_dummies.items.len);
    try std.testing.expectEqual(source_dep_after, source.next_dummy_dep);

    // Mirror context should have its own independent count.
    try std.testing.expectEqual(@as(usize, 3), mirror.theorem_dummies.items.len);
}
