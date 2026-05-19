const std = @import("std");
const Index = @import("index.zig");

const Snapshot = Index.Snapshot;

fn completionNamed(
    items: []const Index.CompletionItem,
    label: []const u8,
) ?Index.CompletionItem {
    for (items) |item| {
        if (std.mem.eql(u8, item.label, label)) return item;
    }
    return null;
}

fn expectSortPrefix(
    item: Index.CompletionItem,
    prefix: []const u8,
) !void {
    try std.testing.expect(std.mem.startsWith(u8, item.sort_text, prefix));
}

test "snapshot build propagates allocation failure" {
    var buffer: [1]u8 = undefined;
    var fixed = std.heap.FixedBufferAllocator.init(&buffer);
    try std.testing.expectError(error.OutOfMemory, Snapshot.build(
        fixed.allocator(),
        .{
            .mm0_uri = "file:///test.mm0",
            .mm0_text = "provable sort wff;",
        },
    ));
}

test "malformed sources still index parsed prefixes" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\not a valid statement
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\bad_block
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.indexOf(u8, proof_text, "top_i") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingPrefixDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "top_i",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "completion uses parsed prefixes before malformed suffixes" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ to $;
        \\not a valid statement
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by ke
        \\
        \\bad_block
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const math_offset = std.mem.indexOf(u8, mm0_text, "to $") orelse {
        return error.MissingMalformedMathContext;
    };
    const math_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        math_offset + "to".len,
        .{},
    );
    defer std.testing.allocator.free(math_items);
    try std.testing.expect(completionNamed(math_items, "top") != null);

    const rule_offset = std.mem.indexOf(u8, proof_text, "ke") orelse {
        return error.MissingMalformedRuleContext;
    };
    const rule_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        rule_offset + "ke".len,
        .{},
    );
    defer std.testing.allocator.free(rule_items);
    try std.testing.expect(completionNamed(rule_items, "top_i") != null);
}

test "completion returns top-level mm0 keywords" {
    const text = "the";
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        text.len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    const item = completionNamed(completions, "theorem") orelse {
        return error.MissingTheoremCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.keyword, item.kind);
    try std.testing.expectEqual(@as(usize, 0), item.replacement.start);
    try std.testing.expectEqual(@as(usize, 3), item.replacement.end);
}

test "completion completes partially typed mm0 sorts" {
    const text =
        \\provable sort wff;
        \\term other: wf
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        text.len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    const wff = completionNamed(completions, "wff") orelse {
        return error.MissingPrefixedSortCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.sort, wff.kind);
    try std.testing.expectEqualStrings(
        "wf",
        text[wff.replacement.start..wff.replacement.end],
    );
}

test "completion omits ordinary mm0 comments" {
    const text =
        \\provable sort wff;
        \\-- theorem:
        \\term top: wff;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const keyword_offset = std.mem.indexOf(u8, text, "theorem") orelse {
        return error.MissingCommentKeywordContext;
    };
    const keyword_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        keyword_offset + "theorem".len,
        .{},
    );
    defer std.testing.allocator.free(keyword_items);
    try std.testing.expectEqual(@as(usize, 0), keyword_items.len);

    const sort_offset = std.mem.indexOf(u8, text, "theorem:") orelse {
        return error.MissingCommentSortContext;
    };
    const sort_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        sort_offset + "theorem:".len,
        .{},
    );
    defer std.testing.allocator.free(sort_items);
    try std.testing.expectEqual(@as(usize, 0), sort_items.len);
}

test "completion omits proof comments" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\-- ma
        \\main
        \\----
        \\l1: $ top $ by ax [] -- ma
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const standalone_offset = std.mem.indexOf(u8, proof_text, "ma") orelse {
        return error.MissingStandaloneProofComment;
    };
    const standalone_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        standalone_offset + "ma".len,
        .{},
    );
    defer std.testing.allocator.free(standalone_items);
    try std.testing.expectEqual(@as(usize, 0), standalone_items.len);

    const trailing_offset = std.mem.lastIndexOf(u8, proof_text, "ma") orelse {
        return error.MissingTrailingProofComment;
    };
    const trailing_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        trailing_offset + "ma".len,
        .{},
    );
    defer std.testing.allocator.free(trailing_items);
    try std.testing.expectEqual(@as(usize, 0), trailing_items.len);
}

test "completion returns sorts and math symbols in mm0 contexts" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main (p: wff): $ p  $;
        \\term other:
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const sort_offset = std.mem.indexOf(u8, text, "term other:") orelse {
        return error.MissingSortContext;
    };
    const sort_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        sort_offset + "term other:".len,
        .{},
    );
    defer std.testing.allocator.free(sort_items);
    try std.testing.expect(completionNamed(sort_items, "wff") != null);

    const math_offset = std.mem.indexOf(u8, text, "  $") orelse {
        return error.MissingMathContext;
    };
    const math_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        math_offset,
        .{},
    );
    defer std.testing.allocator.free(math_items);
    const top = completionNamed(math_items, "top") orelse {
        return error.MissingTopCompletion;
    };
    const p = completionNamed(math_items, "p") orelse {
        return error.MissingBinderCompletion;
    };
    try expectSortPrefix(p, "00");
    try expectSortPrefix(top, "07");
}

test "completion returns notation tokens and aliases in mm0 math" {
    const text =
        \\delimiter $ ( [ $ $ ) ] $;
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\term imp (p q: wff): wff;
        \\term box (p: wff): wff;
        \\theorem main (p q: wff): $ forall p $;
        \\prefix forall: $∀$ prec 40;
        \\infixr imp: $->$ prec 25;
        \\notation box (p: wff): wff = ($[$:20) p ($]$:20);
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const alias_offset = std.mem.indexOf(u8, text, "$ forall p") orelse {
        return error.MissingAliasContext;
    };
    const alias_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        alias_offset + "$ forall".len,
        .{},
    );
    defer std.testing.allocator.free(alias_items);
    const forall = completionNamed(alias_items, "∀") orelse {
        return error.MissingForallNotationCompletion;
    };
    try std.testing.expectEqualStrings("∀", forall.replacement_text);
    try std.testing.expectEqualStrings(
        "forall",
        text[forall.replacement.start..forall.replacement.end],
    );
    try std.testing.expect(forall.filter_text != null);
    try std.testing.expectEqualStrings(
        "forall ∀",
        forall.filter_text.?,
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        forall.detail,
        1,
        "forall",
    ));
    try std.testing.expect(forall.documentation_markdown != null);

    const raw_forall = completionNamed(alias_items, "forall") orelse {
        return error.MissingRawTermCompletion;
    };
    try expectSortPrefix(forall, "04");
    try expectSortPrefix(raw_forall, "07");
    try std.testing.expect(std.mem.order(
        u8,
        forall.sort_text,
        raw_forall.sort_text,
    ) == .lt);

    try std.testing.expect(completionNamed(alias_items, "->") != null);
    const open_bracket = completionNamed(alias_items, "[") orelse {
        return error.MissingBracketNotationCompletion;
    };
    try expectSortPrefix(open_bracket, "05");
}

test "snippet escaping protects snippet metacharacters" {
    const escaped = try Index.escapeSnippetText(
        std.testing.allocator,
        "a$b}c\\d",
    );
    defer std.testing.allocator.free(escaped);
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 'a', '\\', '$', 'b', '\\', '}', 'c', '\\', '\\', 'd' },
        escaped,
    );
}

test "completion returns prefix notation snippets when supported" {
    const text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "fo $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "fo".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "∀ …") orelse {
        return error.MissingPrefixSnippetCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.snippet, snippet.kind);
    try std.testing.expectEqualStrings("∀", snippet.replacement_text);
    try std.testing.expectEqualStrings(
        "∀ ${1:p}$0",
        snippet.snippet_replacement_text orelse "",
    );
    try expectSortPrefix(snippet, "06");
    try std.testing.expect(snippet.filter_text != null);
    try std.testing.expectEqualStrings(
        "forall ∀",
        snippet.filter_text.?,
    );
}

test "completion omits notation snippets without client support" {
    const text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "fo $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "fo".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    try std.testing.expect(completionNamed(items, "∀ …") == null);
    for (items) |item| {
        try std.testing.expect(item.snippet_replacement_text == null);
    }
}

test "completion returns general notation snippets" {
    const text =
        \\delimiter $ ( [ ] ) $;
        \\provable sort wff;
        \\term box (p: wff): wff;
        \\theorem main (p: wff): $ bo $;
        \\notation box (p: wff): wff = ($[$:20) p ($]$:20);
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "bo $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "bo".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "[ … ]") orelse {
        return error.MissingGeneralSnippetCompletion;
    };
    try std.testing.expectEqualStrings(
        "[ ${1:p} ]$0",
        snippet.snippet_replacement_text orelse "",
    );
    try std.testing.expect(snippet.filter_text != null);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        snippet.filter_text.?,
        1,
        "box",
    ));
}

test "snippet placeholders follow binder order" {
    const text =
        \\provable sort wff;
        \\term pair (z a: wff): wff;
        \\theorem main (z a: wff): $ pa $;
        \\notation pair (z a: wff): wff = ($pair$:10) a z;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "pa $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "pa".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "pair … …") orelse {
        return error.MissingOrderSnippetCompletion;
    };
    try std.testing.expectEqualStrings(
        "pair ${2:a} ${1:z}$0",
        snippet.snippet_replacement_text orelse "",
    );
}

test "anonymous term arguments get readable snippet placeholders" {
    const text =
        \\provable sort wff;
        \\term anon (_: wff): wff;
        \\theorem main (p: wff): $ an $;
        \\prefix anon: $anon$ prec 40;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "an $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "an".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "anon …") orelse {
        return error.MissingAnonymousSnippetCompletion;
    };
    try std.testing.expectEqualStrings(
        "anon ${1:arg1}$0",
        snippet.snippet_replacement_text orelse "",
    );
}

test "completion returns notation tokens in proof math" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax (p q: wff): $ p -> q $;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p im q $ by ax []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "im q") orelse {
        return error.MissingProofAliasContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        offset + "im".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    const imp = completionNamed(items, "->") orelse {
        return error.MissingProofNotationCompletion;
    };
    try std.testing.expectEqualStrings("->", imp.replacement_text);
    try std.testing.expectEqualStrings(
        "im",
        proof_text[imp.replacement.start..imp.replacement.end],
    );
}

test "completion returns @vars dummies in proof math" {
    const mm0_text =
        \\--| @vars x y
        \\provable sort obj;
        \\term eq (a b: obj): obj;
        \\axiom eq_refl (a: obj): $ eq a a $;
        \\theorem main (z: obj): $ eq z z $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ eq z x $ by eq_refl []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "x $") orelse {
        return error.MissingVarsCompletionContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        offset + "x".len,
        .{},
    );
    defer std.testing.allocator.free(items);

    const x = completionNamed(items, "x") orelse {
        return error.MissingVarsCompletion;
    };
    const z = completionNamed(items, "z") orelse {
        return error.MissingProofBinderCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.binder, x.kind);
    try std.testing.expectEqual(Index.CompletionKind.binder, z.kind);
    try std.testing.expectEqualStrings(
        "sort variable",
        x.detail,
    );
    try std.testing.expectEqualStrings(
        "x",
        proof_text[x.replacement.start..x.replacement.end],
    );
    try expectSortPrefix(x, "00");
}

test "completion uses math replacement ranges for operator prefixes" {
    const text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\theorem main (p q: wff): $ p - q $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = (std.mem.indexOf(u8, text, "- q") orelse {
        return error.MissingOperatorContext;
    }) + 1;
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset,
        .{},
    );
    defer std.testing.allocator.free(items);
    const imp = completionNamed(items, "->") orelse {
        return error.MissingOperatorNotationCompletion;
    };
    try std.testing.expectEqualStrings(
        "-",
        text[imp.replacement.start..imp.replacement.end],
    );
}

test "completion returns annotation directives" {
    const text =
        \\--| @re
        \\provable sort wff;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "@re") orelse unreachable;
    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + 3,
        .{},
    );
    defer std.testing.allocator.free(completions);
    try std.testing.expect(completionNamed(completions, "@rewrite") != null);
    try std.testing.expect(completionNamed(completions, "@relation") != null);
}

test "completion returns proof rules, references, and binders" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $ > $ p $;
        \\axiom later (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (p := $ p $) []
        \\l2: $ p $ by ke []
        \\l3: $ p $ by use [l]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset = std.mem.indexOf(u8, proof_text, "ke []") orelse {
        return error.MissingRuleContext;
    };
    const rule_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        rule_offset + "ke".len,
        .{},
    );
    defer std.testing.allocator.free(rule_items);
    try std.testing.expect(completionNamed(rule_items, "use") != null);
    try std.testing.expect(completionNamed(rule_items, "later") == null);

    const l2_refs = std.mem.indexOf(u8, proof_text, "ke []") orelse {
        return error.MissingEmptyRefContext;
    };
    var early_ref_arena_state = std.heap.ArenaAllocator.init(
        std.testing.allocator,
    );
    defer early_ref_arena_state.deinit();
    const early_ref_items = try snapshot.completionsAt(
        early_ref_arena_state.allocator(),
        .proof,
        l2_refs + "ke [".len,
        .{},
    );
    try std.testing.expect(completionNamed(early_ref_items, "l1") != null);
    try std.testing.expect(completionNamed(early_ref_items, "l2") == null);
    try std.testing.expect(completionNamed(early_ref_items, "l3") == null);

    const ref_offset = std.mem.lastIndexOf(u8, proof_text, "l]") orelse {
        return error.MissingRefContext;
    };
    var ref_arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ref_arena_state.deinit();
    const ref_items = try snapshot.completionsAt(
        ref_arena_state.allocator(),
        .proof,
        ref_offset + 1,
        .{},
    );
    try std.testing.expect(completionNamed(ref_items, "l1") != null);
    try std.testing.expect(completionNamed(ref_items, "l2") != null);
    try std.testing.expect(completionNamed(ref_items, "l3") == null);
    try std.testing.expect(completionNamed(ref_items, "#1") != null);

    const bind_offset = std.mem.indexOf(u8, proof_text, "p :=") orelse {
        return error.MissingBindingContext;
    };
    const bind_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        bind_offset + 1,
        .{},
    );
    defer std.testing.allocator.free(bind_items);
    try std.testing.expect(completionNamed(bind_items, "p") != null);
}

test "completion returns proof rules inside nested applications" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by keep [to []]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const nested_offset = std.mem.indexOf(u8, proof_text, "to []") orelse {
        return error.MissingNestedRuleContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        nested_offset + "to".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    const top_i = completionNamed(items, "top_i") orelse {
        return error.MissingNestedRuleCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.axiom, top_i.kind);
    try std.testing.expectEqualStrings(
        "to",
        proof_text[top_i.replacement.start..top_i.replacement.end],
    );
    try std.testing.expect(completionNamed(items, "l1") == null);
}

test "completion returns theorem names at proof headers" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
        \\axiom ax: $ top $;
    ;
    const proof_text = "ma";
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        proof_text.len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    try std.testing.expect(completionNamed(completions, "main") != null);
    try std.testing.expect(completionNamed(completions, "ax") == null);
}

test "completion returns binders for unavailable forward rules" {
    const mm0_text =
        \\provable sort wff;
        \\theorem main (p: wff): $ p $;
        \\axiom later (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by later (p := $ p $) []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset = std.mem.indexOf(u8, proof_text, "later") orelse {
        return error.MissingForwardRuleContext;
    };
    const rule_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        rule_offset + "later".len,
        .{},
    );
    defer std.testing.allocator.free(rule_items);
    try std.testing.expect(completionNamed(rule_items, "later") == null);

    const bind_offset = std.mem.indexOf(u8, proof_text, "p :=") orelse {
        return error.MissingForwardBindingContext;
    };
    const bind_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        bind_offset + 1,
        .{},
    );
    defer std.testing.allocator.free(bind_items);
    try std.testing.expect(completionNamed(bind_items, "p") != null);
}

test "snapshot indexes global mm0 declarations" {
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
        \\theorem imp_refl (a: wff): $ imp a a $;
        ,
    });
    defer snapshot.deinit();

    try std.testing.expectEqual(@as(usize, 4), snapshot.declarations.len);
    try std.testing.expect(snapshot.decl_by_name.contains("wff"));
    try std.testing.expect(snapshot.decl_by_name.contains("imp"));
    try std.testing.expect(snapshot.decl_by_name.contains("ax_mp"));
    try std.testing.expect(snapshot.decl_by_name.contains("imp_refl"));
}

test "snapshot outlines mm0 declarations" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const outline = snapshot.outline(.mm0);
    try std.testing.expectEqual(@as(usize, 4), outline.len);
    try std.testing.expectEqualStrings("wff", outline[0].name);
    try std.testing.expectEqual(Index.DeclarationKind.sort, outline[0].kind);
    try std.testing.expectEqualStrings("top", outline[1].name);
    try std.testing.expectEqual(Index.DeclarationKind.term, outline[1].kind);
    try std.testing.expectEqualStrings("top_i", outline[2].name);
    try std.testing.expectEqual(Index.DeclarationKind.axiom, outline[2].kind);
    try std.testing.expectEqualStrings("main", outline[3].name);
    try std.testing.expectEqual(
        Index.DeclarationKind.theorem,
        outline[3].kind,
    );
    try std.testing.expectEqualStrings(
        "theorem main: $ top $;",
        snapshot.mm0_text[outline[3].range.start..outline[3].range.end],
    );
}

test "snapshot outlines proof blocks without line children" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const outline = snapshot.outline(.proof);
    try std.testing.expectEqual(@as(usize, 1), outline.len);
    try std.testing.expectEqualStrings("main", outline[0].name);
    try std.testing.expectEqual(Index.DeclarationKind.theorem, outline[0].kind);
    try std.testing.expectEqual(@as(usize, 0), outline[0].children.len);
}

test "definition lookup resolves declaration and simple global use" {
    const text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\theorem imp_refl (a: wff): $ imp a a $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const decl_offset =
        (std.mem.indexOf(u8, text, "imp") orelse unreachable) + 1;
    const decl_def = snapshot.definitionAt(.mm0, decl_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", decl_def.uri);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[decl_def.range.start..decl_def.range.end],
    );

    const use_offset =
        (std.mem.lastIndexOf(u8, text, "imp") orelse unreachable) + 1;
    const use_def = snapshot.definitionAt(.mm0, use_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(decl_def.range.start, use_def.range.start);
    try std.testing.expectEqual(decl_def.range.end, use_def.range.end);
}

test "hover returns markdown and source token range" {
    const text =
        \\provable sort wff;
        \\term top: wff;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, text, "top") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[hover.range.start..hover.range.end],
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term top",
    ));
}

test "global hover shows definition bodies and assertion formulas" {
    const text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\def id (a: wff): wff = $ a -> a $;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const def_offset =
        (std.mem.indexOf(u8, text, "id") orelse unreachable) + 1;
    const def_hover = snapshot.hoverAt(.mm0, def_offset) orelse {
        return error.MissingDefinitionHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        def_hover.markdown,
        1,
        "$ a -> a $",
    ));
    try std.testing.expect(!std.mem.containsAtLeast(
        u8,
        def_hover.markdown,
        1,
        "Binders:",
    ));

    const ax_offset =
        (std.mem.indexOf(u8, text, "axiom mp") orelse unreachable) +
        "axiom ".len + 1;
    const ax_hover = snapshot.hoverAt(.mm0, ax_offset) orelse {
        return error.MissingAssertionHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "2 hypotheses, conclusion sort `wff`",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "axiom mp (a b: wff):",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "$ a -> b $ >",
    ));
}

test "global hover renders dependency masks as bound names" {
    const text =
        \\sort ctx;
        \\sort tm;
        \\sort ty;
        \\provable sort jdg;
        \\term ok: jdg;
        \\axiom dep_rule (g: ctx) {k ih: tm} (C: ty k)
        \\  (s: tm k ih): $ ok $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, text, "dep_rule") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingDependencyHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "(C: ty k)",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "(s: tm k ih)",
    ));
}

test "sort references in signatures resolve explicitly" {
    const text =
        \\provable sort wff;
        \\term top: wff;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, text, "wff") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingSortDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "wff",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingSortHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Sort `wff`.",
    ));
}

test "comments do not produce global hovers" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\-- top should not be a hover target here
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, text, "top") orelse unreachable) + 1;
    try std.testing.expect(snapshot.hoverAt(.mm0, offset) == null);
    try std.testing.expect(snapshot.definitionAt(.mm0, offset) == null);
}

test "proof block header resolves to matching theorem" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "main") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "main",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "implementation lookup resolves theorem declarations to proof blocks" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, mm0_text, "main") orelse unreachable) + 1;
    const implementation = snapshot.implementationAt(.mm0, offset) orelse {
        return error.MissingImplementation;
    };
    try std.testing.expectEqualStrings("file:///test.auf", implementation.uri);
    try std.testing.expectEqualStrings(
        "main",
        snapshot.proof_text.?[implementation.range.start..implementation.range.end],
    );

    const axiom_offset =
        (std.mem.indexOf(u8, mm0_text, "top_i") orelse unreachable) + 1;
    try std.testing.expect(
        snapshot.implementationAt(.mm0, axiom_offset) == null,
    );
}

test "references lookup returns matching indexed symbol uses" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "top_i") orelse unreachable) + 1;
    const rule_refs = try snapshot.referencesAt(
        std.testing.allocator,
        .proof,
        rule_offset,
        true,
    );
    defer std.testing.allocator.free(rule_refs);
    try std.testing.expectEqual(@as(usize, 3), rule_refs.len);
    try std.testing.expectEqual(Index.DocumentId.mm0, rule_refs[0].document);
    try std.testing.expectEqual(Index.DocumentId.proof, rule_refs[1].document);
    try std.testing.expectEqual(Index.DocumentId.proof, rule_refs[2].document);
    for (rule_refs) |range| {
        const text = snapshot.textForDocument(range.document) orelse unreachable;
        try std.testing.expectEqualStrings("top_i", text[range.start..range.end]);
    }

    const rule_uses = try snapshot.referencesAt(
        std.testing.allocator,
        .proof,
        rule_offset,
        false,
    );
    defer std.testing.allocator.free(rule_uses);
    try std.testing.expectEqual(@as(usize, 2), rule_uses.len);
    for (rule_uses) |range| {
        try std.testing.expectEqual(Index.DocumentId.proof, range.document);
    }

    const theorem_offset =
        (std.mem.indexOf(u8, mm0_text, "main") orelse unreachable) + 1;
    const theorem_refs = try snapshot.referencesAt(
        std.testing.allocator,
        .mm0,
        theorem_offset,
        true,
    );
    defer std.testing.allocator.free(theorem_refs);
    try std.testing.expectEqual(@as(usize, 2), theorem_refs.len);
    try std.testing.expectEqual(Index.DocumentId.mm0, theorem_refs[0].document);
    try std.testing.expectEqual(Index.DocumentId.proof, theorem_refs[1].document);

    const theorem_uses = try snapshot.referencesAt(
        std.testing.allocator,
        .mm0,
        theorem_offset,
        false,
    );
    defer std.testing.allocator.free(theorem_uses);
    try std.testing.expectEqual(@as(usize, 1), theorem_uses.len);
    try std.testing.expectEqual(Index.DocumentId.proof, theorem_uses[0].document);
}

test "proof block header ignores non-theorem globals" {
    const mm0_text =
        \\provable sort wff;
        \\term main: wff;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ main $ by main []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "main") orelse unreachable) + 1;
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
    try std.testing.expect(snapshot.hoverAt(.proof, offset) == null);
}

test "proof rule applications ignore non-rule globals" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, proof_text, "top") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingUnknownRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "unknown rule `top`",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
}

test "forward global proof rules hover but do not define" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
        \\axiom later: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by later []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "later") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingForwardRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "axiom later",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
}

test "current theorem is not available as a proof rule" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by main []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, proof_text, "main") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingSelfRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "theorem main",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, offset) == null);
}

test "proof rule and line references resolve" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by keep [l1]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "keep") orelse unreachable) + 1;
    const rule_def = snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingRuleDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", rule_def.uri);
    try std.testing.expectEqualStrings(
        "keep",
        snapshot.mm0_text[rule_def.range.start..rule_def.range.end],
    );

    const ref_offset =
        (std.mem.lastIndexOf(u8, proof_text, "l1") orelse unreachable) + 1;
    const ref_def = snapshot.definitionAt(.proof, ref_offset) orelse {
        return error.MissingLineDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.auf", ref_def.uri);
    try std.testing.expectEqualStrings(
        "l1",
        snapshot.proof_text.?[ref_def.range.start..ref_def.range.end],
    );
}

test "local lemma rule resolves in later proof block" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\lemma helper: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
        \\
        \\main
        \\----
        \\l1: $ top $ by helper []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "helper") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.auf", def.uri);
    const decl_start = std.mem.indexOf(u8, proof_text, "helper") orelse {
        return error.MissingLemmaHeader;
    };
    try std.testing.expectEqual(decl_start, def.range.start);
}

test "local proof defs navigate, hover, complete, and outline" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\def local_top: wff = $ top $
        \\
        \\main
        \\----
        \\l1: $ local_top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const use_offset = std.mem.lastIndexOf(u8, proof_text, "local_top") orelse {
        return error.MissingLocalDefUse;
    };
    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        use_offset + "local".len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    const item = completionNamed(completions, "local_top") orelse {
        return error.MissingLocalDefCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.def, item.kind);

    const def = snapshot.definitionAt(.proof, use_offset) orelse {
        return error.MissingLocalDefDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.auf", def.uri);
    const decl_offset = std.mem.indexOf(u8, proof_text, "local_top") orelse {
        return error.MissingLocalDefDecl;
    };
    try std.testing.expectEqual(decl_offset, def.range.start);

    const hover = snapshot.hoverAt(.proof, use_offset) orelse {
        return error.MissingLocalDefHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Definition `local_top`",
    ));

    const outline = snapshot.outline(.proof);
    try std.testing.expectEqual(@as(usize, 2), outline.len);
    try std.testing.expectEqualStrings("local_top", outline[0].name);
    try std.testing.expectEqual(Index.DeclarationKind.def, outline[0].kind);
}

test "completion excludes future local proof defs" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
    ;
    const proof_text =
        \\def earlier: wff = $ loc $
        \\def local_top: wff = $ top $
        \\def later: wff = $ loc $
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const early_offset = std.mem.indexOf(u8, proof_text, "loc") orelse {
        return error.MissingEarlyLocalDefContext;
    };
    const early_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        early_offset + "loc".len,
        .{},
    );
    defer std.testing.allocator.free(early_items);
    try std.testing.expect(completionNamed(early_items, "local_top") == null);

    const late_offset = std.mem.lastIndexOf(u8, proof_text, "loc") orelse {
        return error.MissingLateLocalDefContext;
    };
    const late_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        late_offset + "loc".len,
        .{},
    );
    defer std.testing.allocator.free(late_items);
    try std.testing.expect(completionNamed(late_items, "local_top") != null);
}

test "local proof def binders navigate from bodies" {
    const mm0_text =
        \\sort obj;
    ;
    const proof_text =
        \\def choose (.d: obj) (x: obj): obj = $ d $
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const body_offset = std.mem.lastIndexOf(u8, proof_text, "d") orelse {
        return error.MissingLocalDummyUse;
    };
    const def = snapshot.definitionAt(.proof, body_offset) orelse {
        return error.MissingLocalDummyDefinition;
    };
    const dummy_offset = std.mem.indexOf(u8, proof_text, ".d") orelse {
        return error.MissingLocalDummyDecl;
    };
    try std.testing.expectEqual(dummy_offset + 1, def.range.start);
    try std.testing.expectEqualStrings(
        "d",
        snapshot.proof_text.?[def.range.start..def.range.end],
    );
}

test "public proof def bodies navigate to mm0 declarations" {
    const mm0_text =
        \\sort obj;
        \\def hold (x: obj): obj;
    ;
    const proof_text =
        \\def hold = $ x $
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const name_offset = std.mem.indexOf(u8, proof_text, "hold") orelse {
        return error.MissingPublicDefBodyName;
    };
    const name_def = snapshot.definitionAt(.proof, name_offset) orelse {
        return error.MissingPublicDefBodyDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", name_def.uri);
    try std.testing.expectEqualStrings(
        "hold",
        snapshot.mm0_text[name_def.range.start..name_def.range.end],
    );

    const body_offset = std.mem.indexOf(u8, proof_text, "x") orelse {
        return error.MissingPublicDefBodyBinder;
    };
    const binder_def = snapshot.definitionAt(.proof, body_offset) orelse {
        return error.MissingPublicDefBodyBinderDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", binder_def.uri);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[binder_def.range.start..binder_def.range.end],
    );
}

test "hypothesis refs hover and jump to exact theorem hypothesis" {
    const mm0_text =
        \\provable sort wff;
        \\term first: wff;
        \\term second: wff;
        \\term top: wff;
        \\axiom keep: $ second $ > $ top $;
        \\theorem main: $ first $ > $ second $ > $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [#2]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "#2") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "$ second $",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "hypothesis #2",
    ));
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    const second_hyp = std.mem.lastIndexOf(u8, mm0_text, "$ second $") orelse {
        return error.MissingSecondHypothesis;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqual(second_hyp + 1, def.range.start);
    try std.testing.expectEqualStrings(
        " second ",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "unresolved proof symbols still hover" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by missing [future, #1]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.indexOf(u8, proof_text, "missing") orelse unreachable) + 1;
    const rule_hover = snapshot.hoverAt(.proof, rule_offset) orelse {
        return error.MissingRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        rule_hover.markdown,
        1,
        "unknown rule `missing`",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, rule_offset) == null);

    const line_offset =
        (std.mem.indexOf(u8, proof_text, "future") orelse unreachable) + 1;
    const line_hover = snapshot.hoverAt(.proof, line_offset) orelse {
        return error.MissingLineHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        line_hover.markdown,
        1,
        "unknown line `future`",
    ));

    const hyp_offset =
        (std.mem.indexOf(u8, proof_text, "#1") orelse unreachable) + 1;
    const hyp_hover = snapshot.hoverAt(.proof, hyp_offset) orelse {
        return error.MissingHypHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hyp_hover.markdown,
        1,
        "unknown hypothesis #1",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, hyp_offset) == null);
}

test "explicit proof bindings resolve to rule binders" {
    const mm0_text =
        \\sort obj;
        \\provable sort wff;
        \\axiom use {x: obj} (p: wff x): $ p $;
        \\theorem main {x: obj} (p: wff x): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (x := $ x $, p := $ p $)
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const binding_offset =
        (std.mem.indexOf(u8, proof_text, "x :=") orelse unreachable);
    const hover = snapshot.hoverAt(.proof, binding_offset) orelse {
        return error.MissingBindingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Expected sort: `obj`. Bound variable.",
    ));

    const def = snapshot.definitionAt(.proof, binding_offset) orelse {
        return error.MissingBindingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const free_offset =
        (std.mem.indexOf(u8, proof_text, "p :=") orelse unreachable);
    const free_hover = snapshot.hoverAt(.proof, free_offset) orelse {
        return error.MissingFreeBindingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        free_hover.markdown,
        1,
        "Expected sort: `wff`. Free variable.",
    ));
}

test "math notation tokens resolve to defining terms" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, mm0_text, "->") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingNotationDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingNotationHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term imp",
    ));
}

test "general notation tokens resolve to defining terms" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\notation top: wff = ($⊤$:max);
        \\theorem main: $ ⊤ $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, mm0_text, "⊤") orelse unreachable) + 1;
    const def = snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingGeneralNotationDefinition;
    };
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "proof math term definitions use mm0 declaration scope" {
    const mm0_text =
        \\-- padding keeps the mm0 declaration after the proof token offset
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const proof_top = std.mem.indexOf(u8, proof_text, "$ top $") orelse {
        return error.MissingProofMath;
    };
    const offset = proof_top + 2;
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingProofTermDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "proof math notation definitions use mm0 declaration scope" {
    const mm0_text =
        \\-- padding keeps the mm0 declaration after the proof token offset
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax (p q: wff): $ p -> q $;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p -> q $ by ax []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "->") orelse {
        return error.MissingProofNotation;
    };
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingProofNotationDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "forward proof math globals hover without definition" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\term later: wff;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ later $ by top_i []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const proof_later = std.mem.indexOf(u8, proof_text, "later") orelse {
        return error.MissingForwardProofMath;
    };
    const hover = snapshot.hoverAt(.proof, proof_later) orelse {
        return error.MissingForwardProofMathHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term later",
    ));
    try std.testing.expect(snapshot.definitionAt(.proof, proof_later) == null);
}

test "proof math binder references resolve to theorem binders" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (p := $ p $) []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const line_assertion = std.mem.indexOf(u8, proof_text, "$ p $") orelse {
        return error.MissingProofMath;
    };
    const offset = line_assertion + 2;
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingBinderDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "p",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingBinderHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Expected sort: `wff`. Free variable.",
    ));
}

test "proof @vars dummies hover and jump to pool token" {
    const mm0_text =
        \\provable sort wff;
        \\--| @vars x y
        \\sort obj;
        \\term eq (a b: obj): wff;
        \\axiom eq_refl (a: obj): $ eq a a $;
        \\theorem main (t: obj): $ eq t t $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ eq x x $ by eq_refl []
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const proof_token =
        std.mem.indexOf(u8, proof_text, "x x") orelse unreachable;
    const hover = snapshot.hoverAt(.proof, proof_token) orelse {
        return error.MissingVarsHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Theorem-local dummy `x`",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Sort: `obj`",
    ));

    const def = snapshot.definitionAt(.proof, proof_token) orelse {
        return error.MissingVarsDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    const vars_token = std.mem.indexOf(u8, mm0_text, "x y") orelse {
        return error.MissingVarsAnnotation;
    };
    try std.testing.expectEqual(vars_token, def.range.start);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[def.range.start..def.range.end],
    );

    const decl_hover = snapshot.hoverAt(.mm0, vars_token) orelse {
        return error.MissingVarsDeclHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        decl_hover.markdown,
        1,
        "Available in proof-body math.",
    ));
}

test "global hover includes selected metadata summaries" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\--| @rewrite
        \\axiom top_i: $ top $;
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, mm0_text, "top_i") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingMetadataHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Metadata: `@rewrite`.",
    ));
}
