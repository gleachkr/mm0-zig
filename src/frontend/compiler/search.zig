const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const Expr = @import("../../trusted/expressions.zig").Expr;
const ProofScript = @import("../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const RuleCatalog = @import("./rule_catalog.zig");
const CompilerViews = @import("./views.zig");
const FreshSelect = @import("./fresh_select.zig");
const CompilerDiag = @import("./diag.zig");
const CompilerContext = @import("./context.zig").CompilerContext;
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("./inference.zig");
const Check = @import("./check.zig");
const CompilerVars = @import("./vars.zig");

pub const NameExprMap = Check.NameExprMap;
pub const LabelIndexMap = Check.LabelIndexMap;
pub const FreshDecl = FreshSelect.FreshDecl;
pub const FreshenDecl = FreshSelect.FreshenDecl;
pub const ViewDecl = CompilerViews.ViewDecl;
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const Goal = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
    implicit_whole_conclusion: ?ExprId,

    fn lineAssertion(self: Goal) Check.LineAssertion {
        return switch (self) {
            .concrete => |expr| .{ .concrete = expr },
            .holey => |expr| .{ .holey = expr },
            .implicit_whole_conclusion => .implicit_whole_conclusion,
        };
    }

    fn expectedHint(self: Goal) ?ExprId {
        return switch (self) {
            .implicit_whole_conclusion => |hint| hint,
            else => null,
        };
    }
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    labels: *const LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
};

pub const AttemptOptions = struct {
    commit: bool = false,
    line_label: []const u8 = "<search>",
    assertion_span: Span = .{ .start = 0, .end = 0 },
    diagnostic_span: ?Span = null,
};

pub const AttemptResult = struct {
    allocator: std.mem.Allocator,
    committed: bool,
    line_idx: usize,
    checked_start: usize,
    checked_lines: []const CheckedLine,
    theorem: ?TheoremContext,
    theorem_vars: ?NameExprMap,

    pub fn deinit(self: *AttemptResult) void {
        if (!self.committed) {
            CheckedIr.deinitLines(self.allocator, self.checked_lines);
        }
        self.allocator.free(self.checked_lines);
        if (self.theorem_vars) |*vars| vars.deinit();
        if (self.theorem) |*theorem| theorem.deinit();
        self.* = undefined;
    }
};

const Metadata = @import("./metadata.zig");
const Holes = @import("./holes.zig");
const DiagnosticSink = @import("./diagnostic_sink.zig").DiagnosticSink;
const ProofParser = ProofScript.Parser;

pub fn tryCandidate(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    options: AttemptOptions,
) !AttemptResult {
    const allocator = context.allocator;
    const saved_diag = compiler.getDiagnostic();

    var attempt_theorem = try theorem.clone();
    errdefer attempt_theorem.deinit();
    var attempt_theorem_vars = try Check.cloneNameExprMap(
        allocator,
        theorem_vars,
    );
    errdefer attempt_theorem_vars.deinit();

    var scratch_checked = std.ArrayListUnmanaged(CheckedLine){};
    defer scratch_checked.deinit(allocator);
    try scratch_checked.appendSlice(allocator, context.checked.items);
    const checked_mark = scratch_checked.items.len;

    var attempt_context = Check.RuleApplyContext{
        .allocator = allocator,
        .parser = context.parser,
        .env = context.env,
        .registry = context.registry,
        .rule_catalog = context.rule_catalog,
        .fresh_bindings = context.fresh_bindings,
        .freshen_bindings = context.freshen_bindings,
        .views = context.views,
        .sort_vars = context.sort_vars,
        .assertion = context.assertion,
        .labels = context.labels,
        .checked = &scratch_checked,
        .diag_scratch = context.diag_scratch,
        .rule_unify_cache = context.rule_unify_cache,
    };
    const line = Check.ApplicationLine{
        .label = options.line_label,
        .application = application,
        .assertion_span = options.assertion_span,
    };
    const diag_context = Check.ApplicationDiagnosticContext{
        .theorem_name = context.assertion.name,
        .line_label = options.line_label,
        .span = options.diagnostic_span,
    };
    const diag_mark = context.diag_scratch.mark();

    const attempt = Check.applyRuleApplication(
        compiler,
        &attempt_context,
        application,
        goal.lineAssertion(),
        goal.expectedHint(),
        diag_context,
        line,
        &attempt_theorem,
        &attempt_theorem_vars,
    ) catch |err| {
        CheckedIr.rollbackToMark(allocator, &scratch_checked, checked_mark);
        context.diag_scratch.discard(diag_mark);
        compiler.restoreDiagnostic(saved_diag);
        return err;
    };
    context.diag_scratch.discard(diag_mark);
    compiler.restoreDiagnostic(saved_diag);

    errdefer CheckedIr.rollbackToMark(
        allocator,
        &scratch_checked,
        checked_mark,
    );
    const new_lines = try allocator.dupe(
        CheckedLine,
        scratch_checked.items[checked_mark..],
    );
    scratch_checked.shrinkRetainingCapacity(checked_mark);

    if (options.commit) {
        errdefer {
            CheckedIr.deinitLines(allocator, new_lines);
            allocator.free(new_lines);
        }
        try context.checked.appendSlice(allocator, new_lines);
        var old_theorem = theorem.*;
        theorem.* = attempt_theorem;
        old_theorem.deinit();
        theorem_vars.deinit();
        theorem_vars.* = attempt_theorem_vars;
        return .{
            .allocator = allocator,
            .committed = true,
            .line_idx = attempt.line_idx,
            .checked_start = checked_mark,
            .checked_lines = new_lines,
            .theorem = null,
            .theorem_vars = null,
        };
    }

    return .{
        .allocator = allocator,
        .committed = false,
        .line_idx = attempt.line_idx,
        .checked_start = checked_mark,
        .checked_lines = new_lines,
        .theorem = attempt_theorem,
        .theorem_vars = attempt_theorem_vars,
    };
}

const TestFixture = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    registry: RewriteRegistry,
    rule_catalog: RuleCatalog.Catalog,
    fresh_bindings: std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: std.AutoHashMap(u32, []const FreshenDecl),
    views: std.AutoHashMap(u32, ViewDecl),
    sort_vars: SortVarRegistry,
    assertion: @import("../parse_recovery.zig").AssertionStmt,
};

fn fixtureFor(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !TestFixture {
    var fixture = TestFixture{
        .parser = MM0Parser.init(mm0_src, allocator),
        .env = GlobalEnv.init(allocator),
        .registry = RewriteRegistry.init(allocator),
        .rule_catalog = try RuleCatalog.build(allocator, mm0_src),
        .fresh_bindings = std.AutoHashMap(
            u32,
            []const FreshDecl,
        ).init(allocator),
        .freshen_bindings = std.AutoHashMap(
            u32,
            []const FreshenDecl,
        ).init(allocator),
        .views = std.AutoHashMap(u32, ViewDecl).init(allocator),
        .sort_vars = SortVarRegistry.init(allocator),
        .assertion = undefined,
    };

    while (try fixture.parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processSortMetadata(
                    &fixture.parser,
                    sort_stmt,
                    fixture.parser.last_annotations,
                    &fixture.sort_vars,
                );
            },
            .term => |term_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processTermMetadata(
                    &fixture.env,
                    &fixture.registry,
                    term_stmt,
                    fixture.parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                if (std.mem.eql(u8, assertion.name, theorem_name)) {
                    fixture.assertion = assertion;
                    return fixture;
                }
                try fixture.env.addStmt(stmt);
                try Metadata.processAssertionMetadata(
                    allocator,
                    &fixture.parser,
                    &fixture.env,
                    &fixture.registry,
                    &fixture.fresh_bindings,
                    &fixture.freshen_bindings,
                    &fixture.views,
                    assertion,
                    fixture.parser.last_annotations,
                );
            },
        }
    }
    return error.MissingTheorem;
}

fn readProofCase(
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

fn parseGoal(
    fixture: *TestFixture,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !Goal {
    const parsed = try Holes.parseAssertion(
        &fixture.parser,
        theorem,
        theorem_vars,
        &fixture.sort_vars,
        text,
    );
    return switch (parsed) {
        .concrete => |expr| .{ .concrete = expr },
        .holey => |expr| .{ .holey = expr },
    };
}

fn runSearchLine(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    fixture: *TestFixture,
    labels: *LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
    line: ProofScript.ProofLine,
    commit: bool,
) !AttemptResult {
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = labels,
        .checked = checked,
        .diag_scratch = diag_scratch,
        .rule_unify_cache = rule_unify_cache,
    };
    return tryCandidate(
        compiler,
        &context,
        line.application,
        try parseGoal(fixture, theorem, theorem_vars, line.assertion.text),
        theorem,
        theorem_vars,
        .{
            .commit = commit,
            .line_label = line.label,
            .assertion_span = line.assertion.span,
            .diagnostic_span = line.span,
        },
    );
}

fn expectCaseLineSearch(
    stem: []const u8,
    theorem_name: []const u8,
    line_index: usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);

    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer {
        CheckedIr.deinitLines(allocator, checked.items);
        checked.deinit(allocator);
    }
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    for (block.lines[0..line_index]) |line| {
        var result = try runSearchLine(
            allocator,
            &compiler,
            &fixture,
            &labels,
            &checked,
            &theorem,
            &theorem_vars,
            &diag_scratch,
            &cache,
            line,
            true,
        );
        defer result.deinit();
        try labels.put(line.label, result.line_idx);
    }

    var result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[line_index],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try CheckedIr.validateLines(&result.theorem.?, result.checked_lines);
    try std.testing.expectEqual(line_index, checked.items.len);
}

fn expectInlineSearch(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    line_index: usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    var result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[line_index],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
}

test "search candidate matches exactly" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectInlineSearch(mm0_src, proof_src, "t", 0);
}

test "search candidate failure leaves no checked lines" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by p
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();
    const line = block.lines[0];
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
    };
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        line.assertion.text,
    );
    const interner_count = theorem.interner.count();
    const vars_len = theorem.theorem_vars.items.len;
    const dummies_len = theorem.theorem_dummies.items.len;
    const placeholders_len = theorem.theorem_placeholders.items.len;
    const theorem_vars_count = theorem_vars.count();

    try std.testing.expectError(
        error.ConclusionMismatch,
        tryCandidate(
            &compiler,
            &context,
            line.application,
            goal,
            &theorem,
            &theorem_vars,
            .{
                .line_label = line.label,
                .assertion_span = line.assertion.span,
                .diagnostic_span = line.span,
            },
        ),
    );
    try std.testing.expectEqual(interner_count, theorem.interner.count());
    try std.testing.expectEqual(vars_len, theorem.theorem_vars.items.len);
    try std.testing.expectEqual(dummies_len, theorem.theorem_dummies.items.len);
    try std.testing.expectEqual(
        placeholders_len,
        theorem.theorem_placeholders.items.len,
    );
    try std.testing.expectEqual(theorem_vars_count, theorem_vars.count());
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
    try std.testing.expectEqual(@as(usize, 0), diag_scratch.entries.items.len);
    try std.testing.expect(compiler.getDiagnostic() == null);
}

test "search candidate uses transparent definition conversion" {
    try expectCaseLineSearch("pass_def_transport", "hyp_transport", 1);
}

test "search candidate uses normalization and transport" {
    try expectCaseLineSearch(
        "pass_normalize_def_transport_concl",
        "normalize_def_transport_concl",
        0,
    );
}

test "search candidate uses view inference" {
    try expectCaseLineSearch("pass_view_basic", "imp_refl", 3);
}

test "search candidate uses view recover" {
    try expectCaseLineSearch("pass_recover_basic", "inst_use", 0);
}

test "search candidate rejects boundness failures" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort nat;
        \\term all {x: nat} (p: wff x): wff;
        \\prefix all: $A.$ prec 41;
        \\axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
        \\theorem gen_bad (n: nat) (q: wff): $ q $ > $ q $;
    ;
    const proof_src =
        \\gen_bad
        \\-------
        \\l1: $ q $ by ax_gen (x := $ n $, p := $ q $) [#1]
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "gen_bad");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(allocator);
    defer cache.deinit();

    const err = runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &labels,
        &checked,
        &theorem,
        &theorem_vars,
        &diag_scratch,
        &cache,
        block.lines[0],
        false,
    );
    try std.testing.expectError(error.BoundnessMismatch, err);
    try std.testing.expectEqual(@as(usize, 0), checked.items.len);
    try std.testing.expectEqual(@as(usize, 0), diag_scratch.entries.items.len);
    try std.testing.expect(compiler.getDiagnostic() == null);
}
