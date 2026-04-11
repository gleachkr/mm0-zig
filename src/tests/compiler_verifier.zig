const std = @import("std");
const mm0 = @import("../lib.zig");

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

const proof_case_ext = "auf";

test "compiler emits a valid hidden-dummy targeted unfold proof" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_def_unfold_dummy",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_def_unfold_dummy",
        proof_case_ext,
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler handles normalize-plus-unfold hidden-dummy proof" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_def_hidden_dummy_all_elim_ctx_unfold",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_def_hidden_dummy_all_elim_ctx_unfold",
        proof_case_ext,
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler rejects repeated binders before emitting bad MMB" {
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\term an: wff > wff > wff;
        \\infixl an: $∧$ prec 1;
        \\axiom anr (P Q: wff): $ P ∧ Q ⊢ Q $;
        \\
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\term fun: type > type > type;
        \\infixr fun: $→$ prec 25;
        \\
        \\sort term;
        \\term ty: term > type > wff;
        \\infixl ty: $:$ prec 2;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\
        \\axiom appT (G: wff) (A B: type) (f x: term):
        \\  $ G ⊢ f: A → B $ > $ G ⊢ x: A $ > $ G ⊢ f · x: B $;
        \\axiom lamT (G: wff) (A B: type) {x: term} (t: term x):
        \\  $ G ∧ x: A ⊢ t: B $ > $ G ⊢ λ x: A. t: A → B $;
        \\
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\
        \\axiom leq (G: wff) (A B: type) {x: term} (a b: term x):
        \\  $ G ∧ x: A ⊢ ≃[B] a = b $ >
        \\  $ G ⊢ ≃[A → B] (λ x: A. a) = (λ x: A. b) $;
        \\axiom beta (A B: type) {x: term} (G: wff x) (t: term x):
        \\  $ G ⊢ (λ x: A. t) · x: B $ >
        \\  $ G ⊢ ≃[B] (λ x: A. t) · x = t $;
        \\
        \\theorem id_bool_has_type (G: wff) {x: term}:
        \\  $ G ⊢ λ x: 𝔹. x: 𝔹 → 𝔹 $;
        \\theorem id_bool_beta (G: wff) {x: term}:
        \\  $ G ⊢ x: 𝔹 $ > $ G ⊢ ≃[𝔹] ((λ x: 𝔹. x) · x) = x $;
        \\theorem bad_eta (G: wff) {x: term}:
        \\  $ G ⊢ ≃[𝔹 → 𝔹]
        \\      (λ x: 𝔹. (λ x: 𝔹. x) · x)
        \\      = (λ x: 𝔹. x) $;
    ;
    const proof_src =
        \\id_bool_has_type
        \\----------------
        \\l1: $ G ∧ x: 𝔹 ⊢ x: 𝔹 $ by anr []
        \\l2: $ G ⊢ λ x: 𝔹. x: 𝔹 → 𝔹 $ by lamT [l1]
        \\
        \\id_bool_beta
        \\------------
        \\l1: $ G ⊢ λ x: 𝔹. x: 𝔹 → 𝔹 $ by id_bool_has_type []
        \\l2: $ G ⊢ (λ x: 𝔹. x) · x: 𝔹 $ by appT [l1, #1]
        \\l3: $ G ⊢ ≃[𝔹] ((λ x: 𝔹. x) · x) = x $ by beta [l2]
        \\
        \\bad_eta
        \\-------
        \\l1: $ G ∧ x: 𝔹 ⊢ x: 𝔹 $ by anr []
        \\l2: $ G ∧ x: 𝔹 ⊢ ≃[𝔹] ((λ x: 𝔹. x) · x) = x $ by id_bool_beta [l1]
        \\l3: $ G ⊢ ≃[𝔹 → 𝔹] (λ x: 𝔹. (λ x: 𝔹. x) · x) = (λ x: 𝔹. x) $ by leq [l2]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.DepViolation,
        compiler.compileMmb(std.testing.allocator),
    );
}

test "compiler compiles lemma proof blocks" {
    const allocator = std.testing.allocator;
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_1 (a b: wff): $ a -> b -> a $;
        \\axiom ax_2 (a b c: wff):
        \\$ (a -> b -> c) -> (a -> b) -> a -> c $;
        \\axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
        \\theorem main (a: wff): $ a -> a $;
    ;
    const proof_src =
        \\lemma id (a: wff): $ a -> a $
        \\---------------------------
        \\l1: $ a -> ((a -> a) -> a) $ by ax_1 []
        \\l2: $ a -> (a -> a) $ by ax_1 []
        \\l3: $ (a -> ((a -> a) -> a)) -> ((a -> (a -> a)) -> (a -> a)) $ by ax_2 []
        \\l4: $ (a -> (a -> a)) -> (a -> a) $ by ax_mp (a := $ a -> ((a -> a) -> a) $, b := $ (a -> (a -> a)) -> (a -> a) $) [l3, l1]
        \\l5: $ a -> a $ by ax_mp (a := $ a -> (a -> a) $, b := $ a -> a $) [l4, l2]
        \\
        \\main
        \\----
        \\l1: $ a -> a $ by id (a := $ a $) []
    ;

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler interleaves LocalThm and Thm statements in MMB order" {
    const allocator = std.testing.allocator;
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
        \\theorem third: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\lemma helper0: $ top $
        \\--------------------
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by helper0 []
        \\
        \\lemma helper1: $ top $
        \\--------------------
        \\l1: $ top $ by helper0 []
        \\
        \\third
        \\-----
        \\l1: $ top $ by helper1 []
    ;

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    try mm0.verifyPair(allocator, mm0_src, mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    const cmds = try collectStatementCmds(allocator, mmb);
    defer allocator.free(cmds);

    const expected_cmds = [_]Proof.StmtCmd{
        .Sort,
        .TermDef,
        .Axiom,
        .Thm,
        .LocalThm,
        .Thm,
        .LocalThm,
        .Thm,
        .End,
    };
    try std.testing.expectEqual(expected_cmds.len, cmds.len);
    for (expected_cmds, cmds) |expected, actual| {
        try std.testing.expectEqual(expected, actual);
    }

    try std.testing.expectEqualStrings("top_i", (try mmb.theoremName(0)).?);
    try std.testing.expectEqualStrings("first", (try mmb.theoremName(1)).?);
    try std.testing.expectEqualStrings("helper0", (try mmb.theoremName(2)).?);
    try std.testing.expectEqualStrings("second", (try mmb.theoremName(3)).?);
    try std.testing.expectEqualStrings("helper1", (try mmb.theoremName(4)).?);
    try std.testing.expectEqualStrings("third", (try mmb.theoremName(5)).?);
}

test "strict replay still infers exact omitted binders" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_exact (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_exact
        \\----------
        \\l1: $ a -> b -> a $ by ax_keep [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);

    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
}

test "compiler normalizes conclusions then transports through defs" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_normalize_def_transport_concl",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_normalize_def_transport_concl",
        proof_case_ext,
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}
