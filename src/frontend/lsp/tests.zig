const std = @import("std");
const Index = @import("index.zig");

const Snapshot = Index.Snapshot;

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

test "hypothesis references hover and jump to owning rule" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $ > $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [#1]
    ;
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "#1") orelse unreachable) + 1;
    const hover = snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "hypothesis #1",
    ));
    const def = snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "main",
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
