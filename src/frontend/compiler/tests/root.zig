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
const RewriteRegistry = mm0.RewriteRegistry.RewriteRegistry;
const CompilerMetadata = mm0.CompilerSupport.Metadata;

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

fn replaceOnceOwned(
    allocator: std.mem.Allocator,
    src: []const u8,
    needle: []const u8,
    repl: []const u8,
) ![]u8 {
    const start = std.mem.indexOf(u8, src, needle) orelse {
        return error.ExpectedNeedle;
    };
    return try std.fmt.allocPrint(
        allocator,
        "{s}{s}{s}",
        .{
            src[0..start],
            repl,
            src[start + needle.len ..],
        },
    );
}

const AnnotatedMetadata = struct {
    env: FrontendEnv.GlobalEnv,
    registry: RewriteRegistry,
    fresh_bindings: std.AutoHashMap(
        u32,
        []const CompilerMetadata.FreshDecl,
    ),
    freshen_bindings: std.AutoHashMap(
        u32,
        []const CompilerMetadata.FreshenDecl,
    ),
    views: std.AutoHashMap(u32, CompilerMetadata.ViewDecl),
    sort_vars: CompilerMetadata.SortVarRegistry,
};

fn processAnnotatedMetadata(
    allocator: std.mem.Allocator,
    src: []const u8,
) !AnnotatedMetadata {
    var parser = MM0Parser.init(src, allocator);
    var result = AnnotatedMetadata{
        .env = FrontendEnv.GlobalEnv.init(allocator),
        .registry = RewriteRegistry.init(allocator),
        .fresh_bindings = std.AutoHashMap(
            u32,
            []const CompilerMetadata.FreshDecl,
        ).init(allocator),
        .freshen_bindings = std.AutoHashMap(
            u32,
            []const CompilerMetadata.FreshenDecl,
        ).init(allocator),
        .views = std.AutoHashMap(
            u32,
            CompilerMetadata.ViewDecl,
        ).init(allocator),
        .sort_vars = CompilerMetadata.SortVarRegistry.init(allocator),
    };

    while (try parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| {
                try result.env.addStmt(stmt);
                try CompilerMetadata.processSortMetadata(
                    &parser,
                    sort_stmt,
                    parser.last_annotations,
                    &result.sort_vars,
                );
            },
            .term => |term_stmt| {
                try result.env.addStmt(stmt);
                try CompilerMetadata.processTermMetadata(
                    &result.env,
                    &result.registry,
                    term_stmt,
                    parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                try result.env.addStmt(stmt);
                try CompilerMetadata.processAssertionMetadata(
                    allocator,
                    &parser,
                    &result.env,
                    &result.registry,
                    &result.fresh_bindings,
                    &result.freshen_bindings,
                    &result.views,
                    assertion,
                    parser.last_annotations,
                );
            },
        }
    }

    return result;
}

fn ruleArgIndex(
    rule: *const FrontendEnv.RuleDecl,
    name: []const u8,
) !usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return error.MissingRuleArg;
}

fn hasFreshenDecl(
    decls: []const CompilerMetadata.FreshenDecl,
    target_arg_idx: usize,
    blocker_arg_idx: usize,
) bool {
    for (decls) |decl| {
        if (decl.target_arg_idx == target_arg_idx and
            decl.blocker_arg_idx == blocker_arg_idx)
        {
            return true;
        }
    }
    return false;
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

test "compiler pinpoints invalid fallback annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.InvalidFallbackAnnotation, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidFallbackAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@fallback", mm0_src[span.start..span.end]);
}

test "compiler pinpoints duplicate fallback annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_j: $ top $;
        \\axiom top_k: $ top $;
        \\--| @fallback top_j
        \\--| @fallback top_k
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.DuplicateFallbackAnnotation, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateFallbackAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@fallback top_j", mm0_src[span.start..span.end]);
}

test "compiler pinpoints unknown fallback rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback missing_rule
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownFallbackRule, compiler.check());

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownFallbackRule, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@fallback missing_rule", mm0_src[span.start..span.end]);
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

test "compiler preserves local lemma diagnostics after check returns" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\--------------------
        \\l1: $ top $ by missing_rule []
        \\
        \\target
        \\------
        \\l1: $ top $ by helper []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownRule, compiler.check());

    var churn_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer churn_arena.deinit();
    const churn = try churn_arena.allocator().alloc(u8, 4096);
    @memset(churn, 0xaa);

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownRule, diag.err);
    try std.testing.expectEqualStrings("helper", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing_rule", diag.rule_name.?);
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

test "compiler distinguishes rules declared later in mm0 order" {
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
        \\l1: $ top $ by second []
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
    try std.testing.expectError(
        error.RuleNotYetAvailable,
        compiler.check(),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RuleNotYetAvailable, diag.err);
    try std.testing.expectEqual(.rule_not_yet_available, diag.kind);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("first", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("second", diag.rule_name.?);
    try std.testing.expectEqualStrings(
        "rule is declared later and is not yet available here",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("second", proof_src[span.start..span.end]);
    try std.testing.expectEqual(@as(usize, 1), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "rule is declared later in the mm0 file",
        diag.noteSlice()[0].message,
    );
    try std.testing.expectEqual(@as(usize, 1), diag.relatedSlice().len);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.mm0,
        diag.relatedSlice()[0].source,
    );
    try std.testing.expectEqualStrings(
        "rule declaration is here",
        diag.relatedSlice()[0].label,
    );
    try std.testing.expectEqualStrings(
        "second",
        mm0_src[diag.relatedSlice()[0].span.start..diag.relatedSlice()[0].span.end],
    );
}

test "compiler retries theorem lines through fallback chains" {
    const mm0_src =
        \\provable sort wff;
        \\term and (a b: wff): wff;
        \\term fst (a b: wff): wff;
        \\term snd (a b: wff): wff;
        \\axiom and_elim_right (a b: wff): $ and a b $ > $ snd a b $;
        \\--| @fallback and_elim_right
        \\axiom and_elim_mid (a b: wff): $ and a b $ > $ fst a b $;
        \\--| @fallback and_elim_mid
        \\axiom and_elim (a b: wff): $ and a b $ > $ fst a b $;
        \\theorem use_fallback (a b: wff): $ and a b $ > $ snd a b $;
    ;
    const proof_src =
        \\use_fallback
        \\------------
        \\l1: $ snd a b $ by and_elim [#1]
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

test "final mismatch reports reconciliation attempts" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term mid: wff;
        \\axiom top_i: $ top $;
        \\theorem need_mid: $ mid $;
    ;
    const proof_src =
        \\need_mid
        \\--------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.FinalLineMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.FinalLineMismatch, diag.err);
    try std.testing.expectEqual(.final_line_mismatch, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.final_reconciliation,
        diag.phase.?,
    );
    try std.testing.expectEqual(@as(usize, 3), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "attempted transparent final reconciliation",
        diag.noteSlice()[0].message,
    );
    try std.testing.expectEqualStrings(
        "attempted normalized final reconciliation",
        diag.noteSlice()[1].message,
    );
    try std.testing.expectEqualStrings(
        "attempted alpha-cleanup final reconciliation",
        diag.noteSlice()[2].message,
    );
}

test "compiler reports fallback cycles when every candidate fails" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term mid: wff;
        \\--| @fallback step_a
        \\axiom step_a: $ top $;
        \\theorem bad_cycle: $ mid $;
    ;
    const proof_src =
        \\bad_cycle
        \\---------
        \\l1: $ mid $ by step_a []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.FallbackCycle, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.FallbackCycle, diag.err);
    try std.testing.expectEqualStrings("bad_cycle", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("step_a", diag.rule_name.?);
}

test "compiler preserves the first fallback failure diagnostic" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\term mid: wff;
        \\axiom step_b: $ bot $;
        \\--| @fallback step_b
        \\axiom step_a: $ top $;
        \\theorem bad_fallback: $ mid $;
    ;
    const proof_src =
        \\bad_fallback
        \\------------
        \\l1: $ mid $ by step_a []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.ConclusionMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ConclusionMismatch, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_fallback", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("step_a", diag.rule_name.?);
    try std.testing.expectEqual(@as(usize, 2), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "expected: top",
        diag.noteSlice()[0].message,
    );
    try std.testing.expectEqualStrings(
        "actual: mid",
        diag.noteSlice()[1].message,
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
    switch (diag.detail) {
        .inference_failure => |detail| {
            try std.testing.expectEqual(.transparent_fallback, detail.path);
            try std.testing.expect(detail.first_unsolved_binder_name == null);
        },
        else => return error.ExpectedInferenceFailureDetail,
    }
    try std.testing.expectEqual(@as(usize, 3), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "inference path: transparent fallback",
        diag.noteSlice()[0].message,
    );
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
    try std.testing.expectEqual(mm0.CompilerDiagnosticPhase.inference, diag.phase.?);
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
            try std.testing.expectEqual(.strict_replay, detail.path);
        },
        else => return error.ExpectedMissingBinderDetail,
    }
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "inference path: strict replay",
        diag.noteSlice()[0].message,
    );
    try std.testing.expectEqualStrings(
        "explicit bindings: a = v0",
        diag.noteSlice()[1].message,
    );
    try std.testing.expectEqualStrings(
        "inferred bindings before failure: none",
        diag.noteSlice()[2].message,
    );
    try std.testing.expectEqualStrings(
        "first unsolved binder: b",
        diag.noteSlice()[3].message,
    );
}

test "compiler reports conflicting dependency binders by name" {
    const mm0_src =
        \\provable sort wff;
        \\sort obj;
        \\term rel {x y: obj}: wff;
        \\axiom rel_ax {x y: obj}: $ rel x y $;
        \\theorem rel_bad {z: obj}: $ rel z z $;
    ;
    const proof_src =
        \\rel_bad
        \\-------
        \\l1: $ rel z z $ by rel_ax (x := $ z $, y := $ z $) []
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

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DepViolation, diag.err);
    try std.testing.expectEqual(.generic, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqualStrings(
        "binder assignments violate the rule's dependency constraints",
        mm0.compilerDiagnosticSummary(diag),
    );
    switch (diag.detail) {
        .dep_violation => |detail| {
            try std.testing.expectEqual(@as(usize, 0), detail.first_arg_idx);
            try std.testing.expectEqual(@as(usize, 1), detail.second_arg_idx);
            try std.testing.expectEqualStrings("x", detail.first_arg_name.?);
            try std.testing.expectEqualStrings("y", detail.second_arg_name.?);
            try std.testing.expectEqual(@as(u55, 1), detail.first_deps);
            try std.testing.expectEqual(@as(u55, 1), detail.second_deps);
            try std.testing.expect(detail.first_bound);
            try std.testing.expect(detail.second_bound);
        },
        else => return error.ExpectedDepViolationDetail,
    }
}

test "multi-remainder inference handles a simple ACUI cover" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_infer",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_infer",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "repeated ACUI remainder binder infers a principal witness" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_repeated_joint_binder",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_repeated_joint_binder",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "transparent ctx defs satisfy structural intervals" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_transparent_ctx_reuse",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_transparent_ctx_reuse",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "prawitz alpha freshen proof compiles and verifies" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler reports freshen attempt notes on failure" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "fail_alpha_freshen_opaque_theorem_arg",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "fail_alpha_freshen_opaque_theorem_arg",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    try std.testing.expectError(
        error.AlphaRewriteSearchFailed,
        compiler.compileMmb(allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.AlphaRewriteSearchFailed, diag.err);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "attempted @freshen for target binder g",
        diag.noteSlice()[0].message,
    );
    try std.testing.expectEqualStrings(
        "freshen blocker binder: x",
        diag.noteSlice()[1].message,
    );
    try std.testing.expect(std.mem.startsWith(
        u8,
        diag.noteSlice()[2].message,
        "chosen replacement binder:",
    ));
    try std.testing.expectEqualStrings(
        "rewritten target still depends on blocker binder x",
        diag.noteSlice()[3].message,
    );
}

test "compiler pinpoints invalid @freshen binder kinds" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);

    const rewritten = try replaceOnceOwned(
        allocator,
        mm0_src,
        "@freshen g x",
        "@freshen x g",
    );
    defer allocator.free(rewritten);

    var compiler = Compiler.init(allocator, rewritten);
    try std.testing.expectError(
        error.FreshenTargetMustBeRegularBinder,
        compiler.check(),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(
        error.FreshenTargetMustBeRegularBinder,
        diag.err,
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@freshen x g",
        rewritten[span.start..span.end],
    );
}

test "compiler pinpoints invalid @alpha binder kinds" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);

    const rewritten = try replaceOnceOwned(
        allocator,
        mm0_src,
        "@alpha x y",
        "@alpha p y",
    );
    defer allocator.free(rewritten);

    var compiler = Compiler.init(allocator, rewritten);
    try std.testing.expectError(
        error.AlphaRequiresBoundBinders,
        compiler.check(),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.AlphaRequiresBoundBinders, diag.err);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@alpha p y",
        rewritten[span.start..span.end],
    );
}

test "prawitz metadata registers alpha and freshen annotations" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const meta = try processAnnotatedMetadata(arena.allocator(), mm0_src);

    const all_term_id = meta.env.term_names.get("all") orelse {
        return error.MissingTerm;
    };
    const ex_term_id = meta.env.term_names.get("ex") orelse {
        return error.MissingTerm;
    };
    const all_alpha_id = meta.env.getRuleId("all_alpha") orelse {
        return error.MissingRule;
    };
    const ex_alpha_id = meta.env.getRuleId("ex_alpha") orelse {
        return error.MissingRule;
    };

    const all_alpha_rules = meta.registry.getAlphaRules(all_term_id);
    try std.testing.expectEqual(@as(usize, 1), all_alpha_rules.len);
    try std.testing.expectEqual(all_alpha_id, all_alpha_rules[0].rule_id);

    const ex_alpha_rules = meta.registry.getAlphaRules(ex_term_id);
    try std.testing.expectEqual(@as(usize, 1), ex_alpha_rules.len);
    try std.testing.expectEqual(ex_alpha_id, ex_alpha_rules[0].rule_id);

    const all_alpha_rule = &meta.env.rules.items[all_alpha_id];
    try std.testing.expectEqual(
        try ruleArgIndex(all_alpha_rule, "x"),
        all_alpha_rules[0].old_idx,
    );
    try std.testing.expectEqual(
        try ruleArgIndex(all_alpha_rule, "y"),
        all_alpha_rules[0].new_idx,
    );

    const ex_alpha_rule = &meta.env.rules.items[ex_alpha_id];
    try std.testing.expectEqual(
        try ruleArgIndex(ex_alpha_rule, "x"),
        ex_alpha_rules[0].old_idx,
    );
    try std.testing.expectEqual(
        try ruleArgIndex(ex_alpha_rule, "y"),
        ex_alpha_rules[0].new_idx,
    );

    const all_intro_id = meta.env.getRuleId("all_intro") orelse {
        return error.MissingRule;
    };
    const all_intro_rule = &meta.env.rules.items[all_intro_id];
    const all_intro_freshen =
        meta.freshen_bindings.get(all_intro_id) orelse {
            return error.MissingFreshenDecl;
        };
    try std.testing.expectEqual(@as(usize, 1), all_intro_freshen.len);
    try std.testing.expect(hasFreshenDecl(
        all_intro_freshen,
        try ruleArgIndex(all_intro_rule, "g"),
        try ruleArgIndex(all_intro_rule, "x"),
    ));

    const ex_intro_id = meta.env.getRuleId("ex_intro") orelse {
        return error.MissingRule;
    };
    const ex_intro_rule = &meta.env.rules.items[ex_intro_id];
    const ex_intro_freshen = meta.freshen_bindings.get(ex_intro_id) orelse {
        return error.MissingFreshenDecl;
    };
    try std.testing.expectEqual(@as(usize, 1), ex_intro_freshen.len);
    try std.testing.expect(hasFreshenDecl(
        ex_intro_freshen,
        try ruleArgIndex(ex_intro_rule, "g"),
        try ruleArgIndex(ex_intro_rule, "x"),
    ));

    const ex_elim_id = meta.env.getRuleId("ex_elim") orelse {
        return error.MissingRule;
    };
    const ex_elim_rule = &meta.env.rules.items[ex_elim_id];
    const ex_elim_freshen = meta.freshen_bindings.get(ex_elim_id) orelse {
        return error.MissingFreshenDecl;
    };
    try std.testing.expectEqual(@as(usize, 1), ex_elim_freshen.len);
    try std.testing.expect(hasFreshenDecl(
        ex_elim_freshen,
        try ruleArgIndex(ex_elim_rule, "c"),
        try ruleArgIndex(ex_elim_rule, "x"),
    ));
}

test "pass_alpha_freshen metadata registers alpha and freshen annotations" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_alpha_freshen",
        "mm0",
    );
    defer allocator.free(mm0_src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const meta = try processAnnotatedMetadata(arena.allocator(), mm0_src);

    const all_term_id = meta.env.term_names.get("all") orelse {
        return error.MissingTerm;
    };
    const ex_term_id = meta.env.term_names.get("ex") orelse {
        return error.MissingTerm;
    };
    try std.testing.expectEqual(
        @as(usize, 1),
        meta.registry.getAlphaRules(all_term_id).len,
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        meta.registry.getAlphaRules(ex_term_id).len,
    );

    const quantifier_rules = [_][]const u8{
        "all_left",
        "all_right",
        "ex_left",
        "ex_right",
    };
    for (quantifier_rules) |rule_name| {
        const rule_id = meta.env.getRuleId(rule_name) orelse {
            return error.MissingRule;
        };
        const rule = &meta.env.rules.items[rule_id];
        const decls = meta.freshen_bindings.get(rule_id) orelse {
            return error.MissingFreshenDecl;
        };
        try std.testing.expectEqual(@as(usize, 2), decls.len);
        try std.testing.expect(hasFreshenDecl(
            decls,
            try ruleArgIndex(rule, "g"),
            try ruleArgIndex(rule, "x"),
        ));
        try std.testing.expect(hasFreshenDecl(
            decls,
            try ruleArgIndex(rule, "d"),
            try ruleArgIndex(rule, "x"),
        ));
    }
}

test "joint structural cover conflicts fail before missing binders" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "fail_acui_joint_cover_conflict",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "fail_acui_joint_cover_conflict",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    try std.testing.expectError(
        error.UnifyMismatch,
        compiler.compileMmb(allocator),
    );
}

test "multi-remainder ambiguity survives to final bindings" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);

    try std.testing.expectEqual(
        @as(usize, 1),
        compiler.warningDiagnostics().len,
    );
    try std.testing.expect(compiler.last_diagnostic == null);
}

test "compiler reports structural ambiguity without ACUI-only wording" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        diag.severity,
    );
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, diag.err);
    try std.testing.expectEqual(.inference_failed, diag.kind);
    try std.testing.expectEqual(mm0.CompilerDiagnosticPhase.inference, diag.phase.?);
    try std.testing.expectEqualStrings(
        "omitted rule arguments remain ambiguous after structural " ++
            "or def-aware matching",
        mm0.compilerDiagnosticSummary(diag),
    );
    switch (diag.detail) {
        .inference_failure => |detail| {
            try std.testing.expectEqual(.structural_solver, detail.path);
        },
        else => return error.ExpectedInferenceFailureDetail,
    }
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "inference path: structural or def-aware solver",
        diag.noteSlice()[0].message,
    );
    try std.testing.expect(std.mem.startsWith(
        u8,
        diag.noteSlice()[1].message,
        "chosen bindings: ",
    ));
    try std.testing.expect(std.mem.startsWith(
        u8,
        diag.noteSlice()[2].message,
        "alternative bindings: ",
    ));
    try std.testing.expectEqualStrings(
        "distinct solutions considered: 3",
        diag.noteSlice()[3].message,
    );
}

test "-Werror upgrades ambiguity warnings into errors" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    compiler.warnings_as_errors = true;
    try std.testing.expectError(
        error.AmbiguousAcuiMatch,
        compiler.compileMmb(allocator),
    );

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        warnings[0].severity,
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.@"error",
        diag.severity,
    );
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, diag.err);
}

test "compiler warns on unused theorem parameters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term P: wff;
        \\theorem unused_theorem {x: obj}: $ P $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        diag.severity,
    );
    try std.testing.expectEqual(.unused_theorem_parameter, diag.kind);
    try std.testing.expectEqual(error.UnusedTheoremParameter, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("unused_theorem", diag.name.?);
    try std.testing.expect(std.mem.indexOf(
        u8,
        mm0.compilerDiagnosticSummary(diag),
        "@vars",
    ) != null);
    switch (diag.detail) {
        .unused_parameter => |detail| {
            try std.testing.expectEqualStrings("x", detail.parameter_name);
        },
        else => return error.ExpectedUnusedParameterDetail,
    }
}

test "dependency-only theorem parameter use suppresses warning" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\theorem dep_only {x: obj} (p: wff x): $ p $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "compiler warns on unused proof-local theorem parameters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom hp: $ P $;
        \\theorem top: $ P $;
    ;
    const proof_src =
        \\lemma unused_local (q: wff): $ P $
        \\--------------------------------
        \\l1: $ P $ by hp []
        \\
        \\top
        \\---
        \\l1: $ P $ by hp []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(.unused_theorem_parameter, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.proof,
        diag.source,
    );
    try std.testing.expectEqualStrings("unused_local", diag.name.?);
    switch (diag.detail) {
        .unused_parameter => |detail| {
            try std.testing.expectEqualStrings("q", detail.parameter_name);
        },
        else => return error.ExpectedUnusedParameterDetail,
    }
}

test "compiler warns on unused definition parameters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term P: wff;
        \\def unused_def {x: obj}: wff = $ P $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(.unused_definition_parameter, diag.kind);
    try std.testing.expectEqual(error.UnusedDefinitionParameter, diag.err);
    try std.testing.expect(std.mem.indexOf(
        u8,
        mm0.compilerDiagnosticSummary(diag),
        "remove",
    ) != null);
    switch (diag.detail) {
        .unused_parameter => |detail| {
            try std.testing.expectEqualStrings("x", detail.parameter_name);
        },
        else => return error.ExpectedUnusedParameterDetail,
    }
}

test "-Werror upgrades unused theorem parameter warnings into errors" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term P: wff;
        \\theorem unused_theorem {x: obj}: $ P $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    compiler.warnings_as_errors = true;
    try std.testing.expectError(
        error.UnusedTheoremParameter,
        compiler.check(),
    );

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        warnings[0].severity,
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.@"error",
        diag.severity,
    );
    try std.testing.expectEqual(.unused_theorem_parameter, diag.kind);
    try std.testing.expectEqual(error.UnusedTheoremParameter, diag.err);
}

test "robinson demo uses omitted binders across two ACUI sorts" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "robinson",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "robinson",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "fully omitted robinson step emits ambiguity warning" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "robinson",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src =
        \\resolve_on_q
        \\------------
        \\step: $ ⊢ ((¬ p ∨ r) ∧ (p ∧ (¬ r))) $ by resolve(d := $ ¬ r $) [#1]
        \\
        \\robinson
        \\--------
        \\l1: $ ⊢ ((¬ p ∨ r) ∧ (p ∧ (¬ r))) $ by resolve [#1]
        \\l2: $ ⊢ (r ∧ (¬ r)) $ by resolve(d := $ ¬ r $) [l1]
        \\l3: $ ⊢ ⊥ $ by resolve(d := $ ⊤ $) [l2]
    ;

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 1),
        compiler.warningDiagnostics().len,
    );
}

test "or_left demo works with both contexts omitted" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "gentzen",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "gentzen",
        "auf",
    );
    defer allocator.free(proof_src);

    const needle = "by or_left(g := $ _ $)";
    const repl = "by or_left";
    const rewritten = if (std.mem.indexOf(u8, proof_src, needle)) |start|
        try std.fmt.allocPrint(
            allocator,
            "{s}{s}{s}",
            .{
                proof_src[0..start],
                repl,
                proof_src[start + needle.len ..],
            },
        )
    else
        try allocator.dupe(u8, proof_src);
    defer allocator.free(rewritten);

    var compiler = Compiler.initWithProof(allocator, mm0_src, rewritten);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
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

test "compiler reports normalized comparison snapshots on mismatch" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\term bi (a b: wff): wff; infixr bi: $<->$ prec 20;
        \\term sb (a b: wff): wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_im (a b c: wff): $ sb a (b -> c) <-> (sb a b -> sb a c) $;
        \\--| @rewrite
        \\axiom sb_P (a: wff): $ sb a P <-> a $;
        \\--| @congr
        \\axiom im_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\--| @normalize conc
        \\axiom all_elim (a b: wff): $ sb a b $;
        \\theorem test_normalize_bad: $ R -> R $;
    ;
    const proof_src =
        \\test_normalize_bad
        \\------------------
        \\l1: $ R -> R $ by all_elim (a := $ Q $, b := $ P -> P $)
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.ConclusionMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ConclusionMismatch, diag.err);
    try std.testing.expectEqual(.conclusion_mismatch, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqual(@as(usize, 5), diag.noteSlice().len);
    try std.testing.expectEqualStrings(
        "expected: sb(Q, im(P, P))",
        diag.noteSlice()[0].message,
    );
    try std.testing.expectEqualStrings(
        "actual: im(R, R)",
        diag.noteSlice()[1].message,
    );
    try std.testing.expectEqualStrings(
        "attempted normalized comparison",
        diag.noteSlice()[2].message,
    );
    try std.testing.expectEqualStrings(
        "normalized expected: im(Q, Q)",
        diag.noteSlice()[3].message,
    );
    try std.testing.expectEqualStrings(
        "normalized actual: im(R, R)",
        diag.noteSlice()[4].message,
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

test "transparent def compression does not leak temp binders" {
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\term obj: type;
        \\notation obj: type = ($𝕆$:max);
        \\sort term;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($=[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\axiom sym (G: wff) (A: type) (a b: term):
        \\  $ G ⊢ ≃[A] a = b $ > $ G ⊢ ≃[A] b = a $;
        \\axiom eqmp (G: wff) (P Q: term):
        \\  $ G ⊢ P ⇔ Q $ > $ G ⊢ P $ > $ G ⊢ Q $;
        \\term T: term;
        \\theorem crash (G: wff) (s: term):
        \\  $ G ⊢ ≃[𝔹] T = =[𝕆] s = s $ >
        \\  $ G ⊢ =[𝕆] s = s $ >
        \\  $ G ⊢ T $;
    ;
    const proof_src =
        \\crash
        \\-----
        \\l1: $ G ⊢ ≃[𝔹] (=[𝕆] s = s) = T $ by sym [#1]
        \\l2: $ G ⊢ T $ by eqmp [l1, #2]
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

test "transparent transport verifies eqmp over bic symmetry" {
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\sort term;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\axiom symt (G: wff) (A: type) (a b: term):
        \\  $ G ⊢ ≃[A] a = b $ > $ G ⊢ ≃[A] b = a $;
        \\axiom eqmp (G: wff) (P Q: term):
        \\  $ G ⊢ P ⇔ Q $ > $ G ⊢ P $ > $ G ⊢ Q $;
        \\theorem eqmpr (G: wff) (P Q: term):
        \\  $ G ⊢ Q ⇔ P $ > $ G ⊢ P $ > $ G ⊢ Q $;
    ;
    const proof_src =
        \\eqmpr
        \\-----
        \\l1: $ G ⊢ P ⇔ Q $ by symt [#1]
        \\l2: $ G ⊢ Q $ by eqmp [l1, #2]
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

test "transparent final line matching unfolds allc notation" {
    // The last proof line is raw `all A · (λ x: A. t)`, while the theorem
    // statement uses the surface `!x: A. t` notation.
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / ! $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\term an: wff > wff > wff;
        \\infixl an: $∧$ prec 1;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\sort term;
        \\term ty: term > type > wff;
        \\infixl ty: $:$ prec 2;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\term all: type > term;
        \\def allc {x: term} (A: type) (t: term x): term =
        \\  $ all A · (λ x: A. t) $;
        \\notation allc {x: term} (A: type) (t: term x): term =
        \\  ($!$:20) x ($:$:2) A ($.$:0) t;
        \\axiom allc_raw (G: wff) (A: type) {x: term} (t: term x):
        \\  $ G ∧ x: A ⊢ t: 𝔹 $ >
        \\  $ G ⊢ all A · (λ x: A. t): 𝔹 $;
        \\theorem final_allc (G: wff) (A: type) {x: term} (t: term x):
        \\  $ G ∧ x: A ⊢ t: 𝔹 $ >
        \\  $ G ⊢ !x: A. t: 𝔹 $;
    ;
    const proof_src =
        \\final_allc
        \\----------
        \\l1: $ G ⊢ all A · (λ x: A. t): 𝔹 $ by allc_raw [#1]
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

test "transparent final line matching unfolds bic and allc under coercion" {
    const mm0_src =
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
        \\axiom all_bic_raw (A: type) {x: term} (t u: term x):
        \\  $ ≃[𝔹] all A · (λ x: A. t) = all A · (λ x: A. u) $;
        \\theorem final_bic_allc (A: type) {x: term} (t u: term x):
        \\  $ (!x: A. t) ⇔ (!x: A. u) $;
    ;
    const proof_src =
        \\final_bic_allc
        \\--------------
        \\l1: $ ≃[𝔹] all A · (λ x: A. t) = all A · (λ x: A. u) $ by all_bic_raw []
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

test "transparent betacv matching handles quantified bic operands" {
    const mm0_src =
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
    const omitted_proof_src =
        "orc_betacv_probe\n" ++
        "----------------\n" ++
        "l1: $ G ⊢ ≃[𝔹] ((λ q: 𝔹. !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) ·" ++
        " b) = (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $" ++
        " by betacv [#1, #2, #3, #4]\n";
    const explicit_proof_src =
        "orc_betacv_probe\n" ++
        "----------------\n" ++
        "l1: $ G ⊢ ≃[𝔹] ((λ q: 𝔹. !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) ·" ++
        " b) = (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $ by" ++
        " betacv (G := $ G $, A := $ 𝔹 $, B := $ 𝔹 $, x := $ q $," ++
        " t := $ b $, u := $ !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r $," ++
        " v := $ all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r) $)" ++
        " [#1, #2, #3, #4]\n";

    {
        var compiler = Compiler.initWithProof(
            std.testing.allocator,
            mm0_src,
            omitted_proof_src,
        );
        const mmb = try compiler.compileMmb(std.testing.allocator);
        defer std.testing.allocator.free(mmb);
        try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
    }

    {
        var compiler = Compiler.initWithProof(
            std.testing.allocator,
            mm0_src,
            explicit_proof_src,
        );
        const mmb = try compiler.compileMmb(std.testing.allocator);
        defer std.testing.allocator.free(mmb);
        try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
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
