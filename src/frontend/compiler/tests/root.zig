const std = @import("std");
const mm0 = @import("mm0");

const Compiler = mm0.Compiler;
const FrontendEnv = mm0.Frontend.Env;
const FrontendExpr = mm0.Frontend.Expr;
const Expr = mm0.Expr;
const CompilerInference = mm0.CompilerSupport.Inference;
const MM0Parser = mm0.MM0Parser;
const Mmb = mm0.Mmb;
const Proof = mm0.Proof;
const ProofScript = mm0.ProofScript;

fn collectStatementCmds(
    allocator: std.mem.Allocator,
    mmb: Mmb,
) ![]Proof.StmtCmd {
    var cmds = std.ArrayListUnmanaged(Proof.StmtCmd){};
    var pos: usize = @intCast(mmb.header.p_proof);

    while (true) {
        const stmt_start = pos;
        const cmd = try Proof.Cmd.read(
            mmb.file_bytes,
            pos,
            mmb.file_bytes.len,
        );
        const stmt_cmd: Proof.StmtCmd = @enumFromInt(cmd.op);
        try cmds.append(allocator, stmt_cmd);
        if (stmt_cmd == .End) break;
        if (cmd.data == 0) return error.BadStatementLength;
        pos = stmt_start + cmd.data;
    }

    return try cmds.toOwnedSlice(allocator);
}

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

test "compiler env retains def dummy metadata" {
    const src = try readProofCaseFile(
        std.testing.allocator,
        "pass_def_dummy",
        "mm0",
    );
    defer std.testing.allocator.free(src);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    const term_id = env.term_names.get("injective") orelse {
        return error.MissingTerm;
    };
    const term = env.terms.items[term_id];
    try std.testing.expect(term.is_def);
    try std.testing.expectEqual(@as(usize, 2), term.dummy_args.len);
    try std.testing.expectEqualStrings("obj", term.dummy_args[0].sort_name);
    try std.testing.expectEqualStrings("obj", term.dummy_args[1].sort_name);
}

test "compiler ignores plain doc comments on terms" {
    const mm0_src =
        \\sort nat;
        \\--| zero is the base natural number constructor
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler rejects unknown term annotations" {
    const mm0_src =
        \\sort nat;
        \\--| @bogus
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownTermAnnotation, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownTermAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("zero", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@bogus", mm0_src[span.start..span.end]);
}

test "compiler pinpoints unknown terms in notation statements" {
    const mm0_src =
        \\sort nat;
        \\prefix succ: $S$ prec 10;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownTerm, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownTerm, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("succ", diag.name.?);
    try std.testing.expectEqualStrings(
        "unknown term",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("succ", mm0_src[span.start..span.end]);
}

test "compiler rejects unexpected top-level mm0 keywords" {
    const mm0_src =
        \\trict sort obj;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnexpectedKeyword, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnexpectedKeyword, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings(
        "unexpected keyword",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("trict", mm0_src[span.start..span.end]);
}

test "compiler still ignores unsupported input and output statements" {
    const mm0_src =
        \\sort nat;
        \\term zero: nat;
        \\output string: $ zero $;
        \\input string: zero;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler pinpoints unknown sorts in mm0 declarations" {
    const mm0_src =
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownSort, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownSort, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("zero", diag.name.?);
    try std.testing.expectEqualStrings(
        "unknown sort",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("nat", mm0_src[span.start..span.end]);
}

test "compiler pinpoints unknown math tokens in mm0 declarations" {
    const mm0_src =
        \\provable sort wff;
        \\theorem bad: $ bogus $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownMathToken, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownMathToken, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "unknown token in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bogus", mm0_src[span.start..span.end]);
    switch (diag.detail) {
        .unknown_math_token => |detail| {
            try std.testing.expectEqualStrings("bogus", detail.token);
        },
        else => return error.ExpectedUnknownMathTokenDetail,
    }
}

test "compiler pinpoints trailing math tokens in mm0 declarations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad: $ top top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.TrailingMathTokens, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.TrailingMathTokens, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "unexpected trailing tokens in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("top", mm0_src[span.start..span.end]);
}

test "compiler pinpoints mismatched closing parens in mm0 math" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad: $ ( top bogus $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.ExpectedCloseParen, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedCloseParen, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "expected closing parenthesis in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bogus", mm0_src[span.start..span.end]);
}

test "compiler pinpoints notation mismatches in mm0 math" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term box (a: wff): wff;
        \\notation box (a: wff): wff = ($L$:10) a ($R$:10);
        \\theorem bad: $ L top X $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.NotationMismatch, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.NotationMismatch, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "token sequence does not match declared notation",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("X", mm0_src[span.start..span.end]);
}

test "compiler pinpoints missing math tokens in mm0 math" {
    const mm0_src =
        \\provable sort wff;
        \\term box (a: wff): wff;
        \\notation box (a: wff): wff = ($L$:10) a ($R$:10);
        \\theorem bad: $ L $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.ExpectedMathToken, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedMathToken, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "expected token in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    const dollar = std.mem.lastIndexOf(u8, mm0_src, "$") orelse {
        return error.MissingMathDelimiter;
    };
    try std.testing.expectEqual(dollar, span.start);
    try std.testing.expectEqual(dollar, span.end);
}

test "compiler env converts rules into binder-indexed templates" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    try std.testing.expectEqual(@as(usize, 1), env.rules.items.len);
    const rule = env.rules.items[0];
    try std.testing.expect(rule.kind == .axiom);
    try std.testing.expectEqual(@as(usize, 2), rule.arg_names.len);
    try std.testing.expectEqualStrings("a", rule.arg_names[0].?);
    try std.testing.expectEqualStrings("b", rule.arg_names[1].?);
    try std.testing.expectEqual(@as(usize, 2), rule.hyps.len);
    switch (rule.hyps[0]) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 0), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            switch (app.args[0]) {
                .binder => |idx| try std.testing.expectEqual(@as(usize, 0), idx),
                else => return error.UnexpectedTemplateExpr,
            }
            switch (app.args[1]) {
                .binder => |idx| try std.testing.expectEqual(@as(usize, 1), idx),
                else => return error.UnexpectedTemplateExpr,
            }
        },
        else => return error.UnexpectedTemplateExpr,
    }
    switch (rule.hyps[1]) {
        .binder => |idx| try std.testing.expectEqual(@as(usize, 0), idx),
        else => return error.UnexpectedTemplateExpr,
    }
    switch (rule.concl) {
        .binder => |idx| try std.testing.expectEqual(@as(usize, 1), idx),
        else => return error.UnexpectedTemplateExpr,
    }
}

test "compiler checks proof blocks in theorem order" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.check();
}

test "compiler rejects lemma names that collide with earlier rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\lemma first: $ top $
        \\------------------
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqualStrings("first", diag.name.?);
    try std.testing.expect(diag.span != null);
}

test "compiler rejects theorem names that collide with earlier lemmas" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem helper: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
        \\
        \\helper
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqualStrings("helper", diag.name.?);
}

test "compiler rejects out-of-order and extra proof blocks" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
    ;

    var mismatch = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\second
        \\------
    );
    try std.testing.expectError(error.TheoremNameMismatch, mismatch.check());

    var extra = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
    );
    try std.testing.expectError(error.ExtraProofBlock, extra.check());
}

test "compiler records proof diagnostics for failing proof lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_label (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_label
        \\----------
        \\l1: $ a -> b -> a $ by ax_keep (a := $ a $, b := $ b $) [missing]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownLabel, compiler.compileMmb(
        std.testing.allocator,
    ));
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownLabel, diag.err);
    try std.testing.expectEqualStrings("keep_label", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing", diag.name.?);
    try std.testing.expect(diag.span != null);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
}

test "compiler pinpoints wrong reference count at the ref list" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem bad_refs (a: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\bad_refs
        \\--------
        \\l1: $ a $ by keep []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.RefCountMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RefCountMismatch, diag.err);
    try std.testing.expectEqualStrings("bad_refs", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("keep", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[]", proof_src[span.start..span.end]);
}

test "compiler pinpoints duplicate proof labels" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem dup_label: $ top $;
    ;
    const proof_src =
        \\dup_label
        \\---------
        \\l1: $ top $ by top_i []
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateLabel, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateLabel, diag.err);
    try std.testing.expectEqualStrings("dup_label", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("l1", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("l1", proof_src[span.start..span.end]);
}

test "compiler pinpoints unknown proof rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem bad_rule: $ top $;
    ;
    const proof_src =
        \\bad_rule
        \\--------
        \\l1: $ top $ by missing_rule []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownRule, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownRule, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_rule", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing_rule", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "missing_rule",
        proof_src[span.start..span.end],
    );
}

test "compiler pinpoints proof parser identifier errors" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_parse: $ top $;
    ;
    const proof_src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.ExpectedIdentifier, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedIdentifier, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_parse", diag.theorem_name.?);
    try std.testing.expectEqualStrings("bad_parse", diag.block_name.?);
    try std.testing.expectEqualStrings(
        "expected identifier",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[", proof_src[span.start..span.end]);
}

test "compiler check diagnostics are marked as mm0 source" {
    const mm0_src =
        \\provable sort wff;
        \\term foo: wff;
        \\axiom dup: $ foo $;
        \\axiom dup: $ foo $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("dup", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("dup", mm0_src[span.start..span.end]);
}

test "compiler pinpoints mm0 parser identifier errors" {
    const mm0_src =
        \\provable sort wff;
        \\theorem [: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.ExpectedIdent, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedIdent, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings(
        "expected identifier",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[", mm0_src[span.start..span.end]);
}

test "compiler records inference diagnostics for omitted arguments" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_bad (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_bad
        \\--------
        \\l1: $ b -> a -> b $ by ax_keep [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnifyMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnifyMismatch, diag.err);
    try std.testing.expectEqualStrings(
        "could not infer omitted rule arguments from the line and refs",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expectEqualStrings("keep_bad", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("ax_keep", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "ax_keep",
        proof_src[span.start..span.end],
    );
}

test "compiler pinpoints unknown math tokens in proof assertions" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem bad_token: $ top $;
    ;
    const proof_src =
        \\bad_token
        \\---------
        \\l1: $ bogus $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.UnknownMathToken,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownMathToken, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_token", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bogus", proof_src[span.start..span.end]);
    switch (diag.detail) {
        .unknown_math_token => |detail| {
            try std.testing.expectEqualStrings("bogus", detail.token);
        },
        else => return error.ExpectedUnknownMathTokenDetail,
    }
}

test "compiler reports which binder assignment is missing" {
    const mm0_src =
        \\provable sort wff;
        \\axiom ax_vacuous (a b: wff): $ a $ > $ a $;
        \\theorem vacuous (a b: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\vacuous
        \\--------
        \\l1: $ a $ by ax_vacuous (a := $ a $) [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.MissingBinderAssignment,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.MissingBinderAssignment, diag.err);
    try std.testing.expectEqual(.missing_binder_assignment, diag.kind);
    try std.testing.expectEqualStrings("vacuous", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("ax_vacuous", diag.rule_name.?);
    try std.testing.expectEqualStrings("b", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "(a := $ a $)",
        proof_src[span.start..span.end],
    );
    switch (diag.detail) {
        .missing_binder_assignment => |detail| {
            try std.testing.expectEqualStrings("b", detail.binder_name);
        },
        else => return error.ExpectedMissingBinderDetail,
    }
}

test "compiler points binding validation errors at explicit assignments" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\axiom use_obj (x: obj): $ top $;
        \\theorem target (x: obj): $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by use_obj (x := $ top $)
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(mm0_src, arena.allocator());
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
                    if (std.mem.eql(u8, value.name, "target")) {
                        break :blk value;
                    }
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };
    const rule_id = env.getRuleId("use_obj") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    try theorem.seedAssertion(assertion);
    const parsed_binding = try parser.parseFormulaText(" top ", &theorem_vars);
    const binding_expr = try theorem.internParsedExpr(parsed_binding);

    const binding_start = std.mem.indexOf(u8, proof_src, "(x := $ top $)") orelse {
        return error.MissingBindingText;
    };
    const binding_span = ProofScript.Span{
        .start = binding_start,
        .end = binding_start + "(x := $ top $)".len,
    };
    const line = ProofScript.ProofLine{
        .label = "l1",
        .label_span = .{ .start = 15, .end = 17 },
        .assertion = .{
            .text = " top ",
            .span = .{ .start = 19, .end = 26 },
        },
        .rule_name = "use_obj",
        .rule_span = .{ .start = 30, .end = 37 },
        .binding_list_span = binding_span,
        .arg_bindings = &.{.{
            .name = "x",
            .formula = .{
                .text = " top ",
                .span = .{ .start = 0, .end = 0 },
            },
            .span = binding_span,
        }},
        .refs_span = null,
        .refs = &.{},
        .span = .{ .start = 15, .end = proof_src.len },
    };

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.SortMismatch,
        CompilerInference.validateResolvedBindings(
            &compiler,
            &env,
            &theorem,
            assertion,
            line,
            rule,
            &.{binding_expr},
        ),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.SortMismatch, diag.err);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "(x := $ top $)",
        proof_src[span.start..span.end],
    );
}

test "compiler reports missing congruence rules for normalization" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\term bi (a b: wff): wff; infixr bi: $<->$ prec 20;
        \\term P: wff;
        \\term Q: wff;
        \\term sb (a b: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_im (a b c: wff): $ sb a (b -> c) <-> (sb a b -> sb a c) $;
        \\--| @rewrite
        \\axiom sb_P (a: wff): $ sb a P <-> a $;
        \\axiom im_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\--| @normalize conc
        \\axiom all_elim (a b: wff): $ sb a b $;
        \\theorem test_normalize: $ Q -> Q $;
    ;
    const proof_src =
        \\test_normalize
        \\--------------
        \\l1: $ Q -> Q $ by all_elim (a := $ Q $, b := $ P -> P $)
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.MissingCongruenceRule,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.MissingCongruenceRule, diag.err);
    try std.testing.expectEqual(.generic, diag.kind);
    try std.testing.expectEqualStrings(
        "test_normalize",
        diag.theorem_name.?,
    );
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("all_elim", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "$ Q -> Q $",
        proof_src[span.start..span.end],
    );
    switch (diag.detail) {
        .missing_congruence_rule => |detail| {
            try std.testing.expectEqual(.missing_rule, detail.reason);
            try std.testing.expectEqualStrings("im", detail.term_name.?);
            try std.testing.expectEqualStrings("wff", detail.sort_name.?);
            try std.testing.expect(detail.arg_index == null);
        },
        else => return error.ExpectedMissingCongruenceDetail,
    }
}

test "compiler reports dependency slot exhaustion clearly" {
    const allocator = std.testing.allocator;

    var mm0_buf = std.ArrayListUnmanaged(u8){};
    defer mm0_buf.deinit(allocator);
    try mm0_buf.appendSlice(allocator,
        \\--| @vars y
        \\provable sort wff;
        \\term top: wff;
        \\--| @fresh y
        \\axiom use_fresh {y: wff}: $ top $;
        \\theorem overflow
    );
    for (0..FrontendExpr.tracked_bound_dep_limit) |idx| {
        try mm0_buf.writer(allocator).print(" {{x{d}: wff}}", .{idx});
    }
    try mm0_buf.appendSlice(allocator, ": $ top $;\n");

    const proof_src =
        \\overflow
        \\--------
        \\l1: $ top $ by use_fresh []
    ;

    var compiler = Compiler.initWithProof(
        allocator,
        mm0_buf.items,
        proof_src,
    );
    try std.testing.expectError(
        error.DependencySlotExhausted,
        compiler.compileMmb(allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DependencySlotExhausted, diag.err);
    try std.testing.expectEqualStrings("overflow", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("use_fresh", diag.rule_name.?);
    try std.testing.expectEqualStrings("y", diag.name.?);
    try std.testing.expectEqualStrings(
        "theorem exceeded the 55 tracked bound-variable dependency slots",
        mm0.compilerDiagnosticSummary(diag),
    );
}

test "strict replay does not open defs during omitted inference" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def id (a: wff): wff = $ a -> a $;
        \\axiom ax_id (a: wff): $ id a $;
        \\theorem strict_infer_expected (a: wff): $ a -> a $;
    ;
    const proof_src =
        \\strict_infer_expected
        \\---------------------
        \\l1: $ a -> a $ by ax_id []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(mm0_src, arena.allocator());
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
                        "strict_infer_expected",
                    )) continue;
                    break :blk value;
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };
    const rule_id = env.getRuleId("ax_id") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    try theorem.seedAssertion(assertion);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try theorem_vars.put(actual_name, expr);
        }
    }

    const parsed_line = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const line_expr = try theorem.internParsedExpr(parsed_line);
    const partial_bindings = [_]?FrontendExpr.ExprId{null};
    const ref_exprs = [_]FrontendExpr.ExprId{};
    const line = ProofScript.ProofLine{
        .label = "l1",
        .label_span = .{ .start = 0, .end = 0 },
        .assertion = .{
            .text = " a -> a ",
            .span = .{ .start = 0, .end = 0 },
        },
        .rule_name = "ax_id",
        .rule_span = .{ .start = 0, .end = 0 },
        .binding_list_span = null,
        .arg_bindings = &.{},
        .refs_span = null,
        .refs = &.{},
        .span = .{ .start = 0, .end = 0 },
    };

    try std.testing.expectError(
        error.TermMismatch,
        CompilerInference.strictInferBindings(
            {},
            arena.allocator(),
            &env,
            &theorem,
            assertion,
            rule,
            line,
            &partial_bindings,
            &ref_exprs,
            line_expr,
        ),
    );
}
