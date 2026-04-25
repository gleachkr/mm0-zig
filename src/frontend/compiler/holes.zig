const std = @import("std");

const ExprModule = @import("../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const SurfaceExpr = @import("../surface_expr.zig");
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const CompilerVars = @import("./vars.zig");

pub const NameExprMap = std.StringHashMap(*const Expr);
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const contains = SurfaceExpr.containsHole;
pub const firstHoleSourceSpan = SurfaceExpr.firstHoleSourceSpan;
pub const sortNameById = SurfaceExpr.sortNameById;
pub const exprIdSortName = SurfaceExpr.exprIdSortName;
pub const exprIdSort = SurfaceExpr.exprIdSort;
pub const sortName = SurfaceExpr.parserSortName;
pub const containsStructuralHole = SurfaceExpr.containsStructuralHole;
pub const lowerStructuralHolesToUnits =
    SurfaceExpr.lowerStructuralHolesToUnits;

pub fn processSortHoleAnnotations(
    parser: *MM0Parser,
    sort_name: []const u8,
    annotations: []const []const u8,
    sort_vars: *const SortVarRegistry,
) !void {
    const hole_tag = "@hole";

    var hole_token: ?[]const u8 = null;
    for (annotations) |ann| {
        if (!annotationMatchesTag(ann, hole_tag)) continue;

        if (hole_token != null) return error.DuplicateHoleAnnotation;
        const tail = std.mem.trim(u8, ann[hole_tag.len..], " \t\r\n");
        if (tail.len == 0) return error.InvalidHoleAnnotation;

        var iter = std.mem.tokenizeAny(u8, tail, " \t\r\n");
        const token = iter.next() orelse return error.InvalidHoleAnnotation;
        if (iter.next() != null) return error.InvalidHoleAnnotation;
        if (sort_vars.getTokenDecl(token) != null) {
            return error.HoleTokenNameCollision;
        }
        hole_token = token;
    }

    if (hole_token) |token| {
        try parser.registerHoleTokenForSort(sort_name, token);
    }
}

fn annotationMatchesTag(ann: []const u8, tag: []const u8) bool {
    if (!std.mem.startsWith(u8, ann, tag)) return false;
    if (ann.len == tag.len) return true;
    return isAsciiWhitespace(ann[tag.len]);
}

fn isAsciiWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r';
}

pub const ParsedAssertion = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
};

pub const InferenceFailure = union(enum) {
    hypothesis_mismatch,
    visible_structure_mismatch,
    missing_binder: struct {
        index: usize,
        name: ?[]const u8,
    },
};

pub const InferenceReport = struct {
    failure: ?InferenceFailure = null,
};

pub const ConcreteMatchFailure = union(enum) {
    visible_structure_mismatch,
    hole_sort_mismatch: struct {
        token: []const u8,
        token_span: ?SourceSpan,
        expected_sort_name: []const u8,
        actual_sort_name: []const u8,
    },
};

pub const ConcreteMatchReport = struct {
    failure: ?ConcreteMatchFailure = null,
};

pub fn parseAssertion(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    math: []const u8,
) !ParsedAssertion {
    try CompilerVars.ensureMathTextVars(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        math,
    );
    const expr = try parser.parseHoleyFormulaText(math, theorem_vars);
    if (contains(expr)) return .{ .holey = expr };
    return .{ .concrete = try theorem.internParsedExpr(expr) };
}

pub fn inferBindingsFromAssertion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    holey: *const Expr,
) ![]const ExprId {
    var report = InferenceReport{};
    return try inferBindingsFromAssertionDetailed(
        allocator,
        theorem,
        rule,
        partial_bindings,
        ref_exprs,
        holey,
        &report,
    );
}

pub fn inferBindingsFromAssertionDetailed(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    holey: *const Expr,
    report: *InferenceReport,
) ![]const ExprId {
    const bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(bindings);

    for (rule.hyps, ref_exprs) |hyp, ref_expr| {
        if (!theorem.matchTemplate(hyp, ref_expr, bindings)) {
            setInferenceFailure(report, .hypothesis_mismatch);
            return error.UnifyMismatch;
        }
    }

    if (!try matchTemplateToSurfaceDetailed(
        theorem,
        rule.concl,
        holey,
        bindings,
        report,
    )) {
        return error.HoleyInferenceMismatch;
    }

    if (firstMissingBinding(bindings)) |idx| {
        setInferenceFailure(report, .{ .missing_binder = .{
            .index = idx,
            .name = if (idx < rule.arg_names.len) rule.arg_names[idx] else null,
        } });
        return error.MissingBinderAssignment;
    }

    const concrete = try allocator.alloc(ExprId, bindings.len);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding.?;
    }
    return concrete;
}

pub fn matchTemplateToSurface(
    theorem: *TheoremContext,
    template: TemplateExpr,
    holey: *const Expr,
    bindings: []?ExprId,
) !bool {
    var report = InferenceReport{};
    return try matchTemplateToSurfaceDetailed(
        theorem,
        template,
        holey,
        bindings,
        &report,
    );
}

pub fn matchTemplateToSurfaceDetailed(
    theorem: *TheoremContext,
    template: TemplateExpr,
    holey: *const Expr,
    bindings: []?ExprId,
    report: *InferenceReport,
) !bool {
    switch (holey.*) {
        .hole => return true,
        .variable => {
            const expr_id = try theorem.internParsedExpr(holey);
            if (theorem.matchTemplate(template, expr_id, bindings)) {
                return true;
            }
            setInferenceFailure(report, .visible_structure_mismatch);
            return false;
        },
        .term => |holey_term| switch (template) {
            .binder => |idx| {
                const expr_id = try theorem.internParsedExpr(holey);
                if (idx >= bindings.len) {
                    setInferenceFailure(report, .visible_structure_mismatch);
                    return false;
                }
                if (bindings[idx]) |existing| {
                    if (existing == expr_id) return true;
                    setInferenceFailure(report, .visible_structure_mismatch);
                    return false;
                }
                bindings[idx] = expr_id;
                return true;
            },
            .app => |tmpl_app| {
                if (tmpl_app.term_id != holey_term.id) {
                    setInferenceFailure(report, .visible_structure_mismatch);
                    return false;
                }
                if (tmpl_app.args.len != holey_term.args.len) {
                    setInferenceFailure(report, .visible_structure_mismatch);
                    return false;
                }
                for (tmpl_app.args, holey_term.args) |tmpl_arg, holey_arg| {
                    if (!try matchTemplateToSurfaceDetailed(
                        theorem,
                        tmpl_arg,
                        holey_arg,
                        bindings,
                        report,
                    )) return false;
                }
                return true;
            },
        },
    }
}

pub fn matchesConcrete(
    parser: *MM0Parser,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    concrete: ExprId,
) !bool {
    var report = ConcreteMatchReport{};
    return try matchesConcreteDetailed(
        parser,
        theorem,
        env,
        holey,
        concrete,
        &report,
    );
}

pub fn matchesConcreteDetailed(
    parser: *MM0Parser,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    concrete: ExprId,
    report: *ConcreteMatchReport,
) !bool {
    switch (holey.*) {
        .hole => |hole| {
            const actual_sort_name = try exprIdSortName(theorem, env, concrete);
            const actual_sort = parser.sort_names.get(actual_sort_name) orelse {
                return error.UnknownSort;
            };
            if (hole.sort == actual_sort) return true;
            setConcreteFailure(report, .{ .hole_sort_mismatch = .{
                .token = hole.token,
                .token_span = hole.token_span,
                .expected_sort_name = sortName(parser, hole.sort),
                .actual_sort_name = actual_sort_name,
            } });
            return false;
        },
        .variable => {
            const expr_id = try @constCast(theorem).internParsedExpr(holey);
            if (expr_id == concrete) return true;
            setConcreteFailure(report, .visible_structure_mismatch);
            return false;
        },
        .term => |holey_term| {
            const node = theorem.interner.node(concrete);
            const concrete_app = switch (node.*) {
                .app => |app| app,
                else => {
                    setConcreteFailure(report, .visible_structure_mismatch);
                    return false;
                },
            };
            if (holey_term.id != concrete_app.term_id) {
                setConcreteFailure(report, .visible_structure_mismatch);
                return false;
            }
            if (holey_term.args.len != concrete_app.args.len) {
                setConcreteFailure(report, .visible_structure_mismatch);
                return false;
            }
            for (holey_term.args, concrete_app.args) |arg, actual_arg| {
                if (!try matchesConcreteDetailed(
                    parser,
                    theorem,
                    env,
                    arg,
                    actual_arg,
                    report,
                )) return false;
            }
            return true;
        },
    }
}

/// Fill holes from the same visible positions in a selected candidate.
///
/// This does not prove that non-hole subtrees match the candidate. Callers
/// that use the result must still validate the resulting concrete line through
/// the ordinary rule-application pipeline.
pub fn materializeSurfaceWithCandidate(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    candidate: ExprId,
    report: *ConcreteMatchReport,
) !?ExprId {
    if (!contains(holey)) {
        const visible = try theorem.internParsedExpr(holey);
        const visible_sort = try exprIdSortName(theorem, env, visible);
        const candidate_sort = try exprIdSortName(theorem, env, candidate);
        if (std.mem.eql(u8, visible_sort, candidate_sort)) return visible;
        setConcreteFailure(report, .visible_structure_mismatch);
        return null;
    }

    switch (holey.*) {
        .hole => |hole| {
            const actual_sort_name = try exprIdSortName(theorem, env, candidate);
            const actual_sort = parser.sort_names.get(actual_sort_name) orelse {
                return error.UnknownSort;
            };
            if (hole.sort == actual_sort) return candidate;
            setConcreteFailure(report, .{ .hole_sort_mismatch = .{
                .token = hole.token,
                .token_span = hole.token_span,
                .expected_sort_name = sortName(parser, hole.sort),
                .actual_sort_name = actual_sort_name,
            } });
            return null;
        },
        .variable => unreachable,
        .term => |holey_term| {
            const node = theorem.interner.node(candidate);
            const candidate_app = switch (node.*) {
                .app => |app| app,
                else => {
                    setConcreteFailure(report, .visible_structure_mismatch);
                    return null;
                },
            };
            if (holey_term.id != candidate_app.term_id or
                holey_term.args.len != candidate_app.args.len)
            {
                setConcreteFailure(report, .visible_structure_mismatch);
                return null;
            }

            const args = try theorem.allocator.alloc(ExprId, holey_term.args.len);
            errdefer theorem.allocator.free(args);
            for (holey_term.args, candidate_app.args, 0..) |
                arg,
                candidate_arg,
                idx,
            | {
                args[idx] = (try materializeSurfaceWithCandidate(
                    parser,
                    theorem,
                    env,
                    arg,
                    candidate_arg,
                    report,
                )) orelse return null;
            }
            return try theorem.interner.internAppOwned(holey_term.id, args);
        },
    }
}

/// Match a holey assertion against a selected concrete candidate.
///
/// This is intentionally a candidate-validation relation, not a candidate
/// inference relation.  Holes only check sort compatibility.  Visible subtrees
/// with no nested holes may match either exactly or by transparent definition
/// conversion; mixed trees still require the same visible head and arity before
/// recursing into their arguments.
pub fn matchesConcreteSemanticallyDetailed(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    concrete: ExprId,
    report: *ConcreteMatchReport,
) !bool {
    var def_ops = DefOps.Context.init(allocator, theorem, env);
    defer def_ops.deinit();
    return try matchesConcreteSemanticallyWithContext(
        &def_ops,
        parser,
        theorem,
        env,
        holey,
        concrete,
        report,
    );
}

fn matchesConcreteSemanticallyWithContext(
    def_ops: *DefOps.Context,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    concrete: ExprId,
    report: *ConcreteMatchReport,
) !bool {
    if (!contains(holey)) {
        const visible = try theorem.internParsedExpr(holey);
        if (visible == concrete) return true;
        if ((try def_ops.compareTransparent(visible, concrete)) != null) {
            return true;
        }
        setConcreteFailure(report, .visible_structure_mismatch);
        return false;
    }

    switch (holey.*) {
        .hole => |hole| {
            const actual_sort_name = try exprIdSortName(theorem, env, concrete);
            const actual_sort = parser.sort_names.get(actual_sort_name) orelse {
                return error.UnknownSort;
            };
            if (hole.sort == actual_sort) return true;
            setConcreteFailure(report, .{ .hole_sort_mismatch = .{
                .token = hole.token,
                .token_span = hole.token_span,
                .expected_sort_name = sortName(parser, hole.sort),
                .actual_sort_name = actual_sort_name,
            } });
            return false;
        },
        .variable => unreachable,
        .term => |holey_term| {
            const node = theorem.interner.node(concrete);
            const concrete_app = switch (node.*) {
                .app => |app| app,
                else => {
                    setConcreteFailure(report, .visible_structure_mismatch);
                    return false;
                },
            };
            if (holey_term.id != concrete_app.term_id) {
                setConcreteFailure(report, .visible_structure_mismatch);
                return false;
            }
            if (holey_term.args.len != concrete_app.args.len) {
                setConcreteFailure(report, .visible_structure_mismatch);
                return false;
            }
            for (holey_term.args, concrete_app.args) |arg, actual_arg| {
                if (!try matchesConcreteSemanticallyWithContext(
                    def_ops,
                    parser,
                    theorem,
                    env,
                    arg,
                    actual_arg,
                    report,
                )) return false;
            }
            return true;
        },
    }
}

fn setInferenceFailure(
    report: *InferenceReport,
    failure: InferenceFailure,
) void {
    if (report.failure == null) report.failure = failure;
}

fn setConcreteFailure(
    report: *ConcreteMatchReport,
    failure: ConcreteMatchFailure,
) void {
    if (report.failure == null) report.failure = failure;
}

fn firstMissingBinding(bindings: []const ?ExprId) ?usize {
    for (bindings, 0..) |binding, idx| {
        if (binding == null) return idx;
    }
    return null;
}

const TestFixture = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    theorem: TheoremContext,
    vars: NameExprMap,
    sort_vars: SortVarRegistry,
    rule_id: u32,
    wff_sort: u7,
    obj_sort: u7,

    fn init(allocator: std.mem.Allocator) !TestFixture {
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort obj;
            \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
            \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
            \\theorem th (a b: wff): $ a $ > $ a -> b -> a $;
        ;

        var parser = MM0Parser.init(src, allocator);
        var env = GlobalEnv.init(allocator);
        var theorem_assertion: ?@import(
            "../../trusted/parse.zig",
        ).AssertionStmt = null;
        var rule_id: ?u32 = null;

        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |assertion| {
                    if (std.mem.eql(u8, assertion.name, "ax_keep")) {
                        rule_id = @intCast(env.rules.items.len - 1);
                    }
                    if (std.mem.eql(u8, assertion.name, "th")) {
                        theorem_assertion = assertion;
                    }
                },
                else => {},
            }
        }
        try parser.registerHoleTokenForSort("wff", "_wff");

        var theorem = TheoremContext.init(allocator);
        try theorem.seedAssertion(theorem_assertion.?);

        var vars = NameExprMap.init(allocator);
        for (
            theorem_assertion.?.arg_names,
            theorem_assertion.?.arg_exprs,
        ) |maybe_name, expr| {
            if (maybe_name) |name| try vars.put(name, expr);
        }

        return .{
            .parser = parser,
            .env = env,
            .theorem = theorem,
            .vars = vars,
            .sort_vars = SortVarRegistry.init(allocator),
            .rule_id = rule_id.?,
            .wff_sort = @intCast(parser.sort_names.get("wff").?),
            .obj_sort = @intCast(parser.sort_names.get("obj").?),
        };
    }

    fn deinit(self: *TestFixture) void {
        self.sort_vars.deinit();
        self.vars.deinit();
        self.theorem.deinit();
    }
};

test "hole detection walks nested surface expressions" {
    const allocator = std.testing.allocator;
    const hole = try allocator.create(Expr);
    defer allocator.destroy(hole);
    hole.* = .{ .hole = .{ .sort = 0, .token = "_wff" } };

    const variable = try allocator.create(Expr);
    defer allocator.destroy(variable);
    variable.* = .{ .variable = .{
        .sort = 0,
        .bound = false,
        .deps = 0,
    } };

    const args = try allocator.alloc(*const Expr, 2);
    defer allocator.free(args);
    args[0] = variable;
    args[1] = hole;

    const term = try allocator.create(Expr);
    defer allocator.destroy(term);
    term.* = .{ .term = .{
        .sort = 0,
        .deps = 0,
        .id = 0,
        .args = args,
    } };

    try std.testing.expect(!contains(variable));
    try std.testing.expect(contains(hole));
    try std.testing.expect(contains(term));
}

test "holey assertion parse keeps holes out of the theorem dag" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const before = fixture.theorem.interner.count();
    const holey = try parseAssertion(
        &fixture.parser,
        &fixture.theorem,
        &fixture.vars,
        &fixture.sort_vars,
        "_wff -> b -> _wff",
    );
    try std.testing.expectEqual(before, fixture.theorem.interner.count());
    try std.testing.expectEqual(.holey, std.meta.activeTag(holey));

    const concrete = try parseAssertion(
        &fixture.parser,
        &fixture.theorem,
        &fixture.vars,
        &fixture.sort_vars,
        "a -> b -> a",
    );
    try std.testing.expectEqual(.concrete, std.meta.activeTag(concrete));
    try std.testing.expect(fixture.theorem.interner.count() > before);
}

test "holey matching checks concrete hole sorts" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const concrete_parsed = try fixture.parser.parseMathText(
        "a -> b -> a",
        &fixture.vars,
    );
    const concrete = try fixture.theorem.internParsedExpr(concrete_parsed);
    const holey = try fixture.parser.parseHoleyFormulaText(
        "_wff -> b -> _wff",
        &fixture.vars,
    );
    try std.testing.expect(try matchesConcrete(
        &fixture.parser,
        &fixture.theorem,
        &fixture.env,
        holey,
        concrete,
    ));

    const wrong_hole = try arena.allocator().create(Expr);
    wrong_hole.* = .{ .hole = .{
        .sort = fixture.obj_sort,
        .token = "_obj",
    } };
    try std.testing.expect(!try matchesConcrete(
        &fixture.parser,
        &fixture.theorem,
        &fixture.env,
        wrong_hole,
        fixture.theorem.theorem_vars.items[0],
    ));
}

test "holey template matching binds visible conclusion structure" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const rule = &fixture.env.rules.items[fixture.rule_id];
    const holey = try fixture.parser.parseHoleyFormulaText(
        "_wff -> b -> _wff",
        &fixture.vars,
    );
    const partial = try arena.allocator().alloc(?ExprId, rule.args.len);
    @memset(partial, null);

    try std.testing.expect(try matchTemplateToSurface(
        &fixture.theorem,
        rule.concl,
        holey,
        partial,
    ));
    try std.testing.expect(partial[0] == null);
    try std.testing.expect(partial[1] != null);
}
