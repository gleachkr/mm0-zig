const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const Inference = @import("./inference.zig");
const CompilerVars = @import("./vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;
const DefOps = @import("../def_ops.zig");
const DerivedBinding = @import("../derived_bindings.zig").DerivedBinding;
const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;

pub const FreshDecl = struct {
    target_arg_idx: usize,
};

pub const FreshenDecl = struct {
    target_arg_idx: usize,
    blocker_arg_idx: usize,
};

pub const FreshSelection = struct {
    expr_id: ExprId,
    deps: u55,
    token: []const u8,
};

pub const HiddenRootNeed = struct {
    root_slot: usize,
    sort_name: []const u8,
};

pub const HiddenRootAssignment = struct {
    root_slot: usize,
    expr_id: ExprId,
    deps: u55,
};

pub fn processFreshAnnotations(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    assertion: AssertionStmt,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    annotations: []const []const u8,
) !void {
    const rule_id = env.getRuleId(assertion.name) orelse return;
    const rule = &env.rules.items[rule_id];

    var decls = std.ArrayListUnmanaged(FreshDecl){};
    defer decls.deinit(allocator);
    var freshen_decls = std.ArrayListUnmanaged(FreshenDecl){};
    defer freshen_decls.deinit(allocator);

    for (annotations) |ann| {
        if (annotationMatchesTag(ann, "@dummy")) {
            return error.DummyAnnotationRemoved;
        }
        if (annotationMatchesTag(ann, "@fresh")) {
            const decl = try parseFreshAnnotation(
                parser,
                rule,
                ann["@fresh".len..],
            );

            for (decls.items) |existing| {
                if (existing.target_arg_idx == decl.target_arg_idx) {
                    return error.DuplicateFreshBinder;
                }
            }
            try decls.append(allocator, decl);
            continue;
        }
        if (!annotationMatchesTag(ann, "@freshen")) continue;

        const decl = try parseFreshenAnnotation(
            rule,
            ann["@freshen".len..],
        );
        for (freshen_decls.items) |existing| {
            if (existing.target_arg_idx == decl.target_arg_idx and
                existing.blocker_arg_idx == decl.blocker_arg_idx)
            {
                return error.DuplicateFreshenPair;
            }
        }
        try freshen_decls.append(allocator, decl);
    }

    if (decls.items.len != 0) {
        try fresh_bindings.put(rule_id, try decls.toOwnedSlice(allocator));
    }
    if (freshen_decls.items.len != 0) {
        try freshen_bindings.put(
            rule_id,
            try freshen_decls.toOwnedSlice(allocator),
        );
    }
}

pub fn chooseFreshBinding(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: anytype,
    sort_vars: *const SortVarRegistry,
    sort_name: []const u8,
    used_deps: u55,
    reserved_deps: u55,
) !FreshSelection {
    const pool = sort_vars.getPool(sort_name) orelse {
        return error.FreshNoAvailableVar;
    };
    var first_unallocated: ?[]const u8 = null;

    for (pool.tokens.items) |token| {
        if (theorem_vars.get(token)) |parser_expr| {
            const var_id = theorem.parser_vars.get(parser_expr) orelse {
                return error.UnknownTheoremVariable;
            };
            switch (var_id) {
                .dummy_var => |dummy_id| {
                    const dummy_info = theorem.theorem_dummies.items[dummy_id];
                    if ((used_deps & dummy_info.deps) != 0) continue;
                    if ((reserved_deps & dummy_info.deps) != 0) continue;
                    return .{
                        .expr_id = try theorem.interner.internVar(var_id),
                        .deps = dummy_info.deps,
                        .token = token,
                    };
                },
                .theorem_var => continue,
            }
        } else if (first_unallocated == null) {
            first_unallocated = token;
        }
    }

    const token = first_unallocated orelse return error.FreshNoAvailableVar;
    try theorem.ensureNamedDummyParserVar(
        parser.allocator,
        theorem_vars,
        token,
        pool.sort_name,
        pool.sort_id,
    );
    const parser_expr = theorem_vars.get(token) orelse {
        return error.UnknownTheoremVariable;
    };
    const var_id = theorem.parser_vars.get(parser_expr) orelse {
        return error.UnknownTheoremVariable;
    };
    return switch (var_id) {
        .dummy_var => |dummy_id| .{
            .expr_id = try theorem.interner.internVar(var_id),
            .deps = theorem.theorem_dummies.items[dummy_id].deps,
            .token = token,
        },
        .theorem_var => error.FreshNoAvailableVar,
    };
}

pub fn collectUsedDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    bindings: []const ?ExprId,
    extra_used_deps: u55,
) !u55 {
    var deps = extra_used_deps | try exprDeps(env, theorem, line_expr);
    for (ref_exprs) |expr_id| {
        deps |= try exprDeps(env, theorem, expr_id);
    }
    for (bindings) |maybe_expr_id| {
        if (maybe_expr_id) |expr_id| {
            deps |= try exprDeps(env, theorem, expr_id);
        }
    }
    return deps;
}

pub fn assignHiddenRootsFromVarsPool(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_vars: anytype,
    sort_vars: *const SortVarRegistry,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    explicit_bindings: []const ?ExprId,
    extra_used_deps: u55,
    needs: []const HiddenRootNeed,
) ![]HiddenRootAssignment {
    const used_deps = try collectUsedDeps(
        env,
        theorem,
        line_expr,
        ref_exprs,
        explicit_bindings,
        extra_used_deps,
    );
    const assignments = try allocator.alloc(HiddenRootAssignment, needs.len);
    errdefer allocator.free(assignments);

    var reserved_deps: u55 = 0;
    for (needs, 0..) |need, idx| {
        const selection = try chooseFreshBinding(
            parser,
            theorem,
            theorem_vars,
            sort_vars,
            need.sort_name,
            used_deps,
            reserved_deps,
        );
        assignments[idx] = .{
            .root_slot = need.root_slot,
            .expr_id = selection.expr_id,
            .deps = selection.deps,
        };
        reserved_deps |= selection.deps;
    }
    return assignments;
}

pub fn seedRecoverHolesFromVarsPool(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_vars: anytype,
    sort_vars: *const SortVarRegistry,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    partial_bindings: []const ?ExprId,
    num_binders: usize,
    binder_map: []const ?usize,
    arg_infos: []const ArgInfo,
    derived_bindings: []const DerivedBinding,
) ![]DefOps.BindingSeed {
    const seeds = try allocator.alloc(DefOps.BindingSeed, num_binders);
    errdefer allocator.free(seeds);
    @memset(seeds, .none);

    const used_deps = try collectUsedDeps(
        env,
        theorem,
        line_expr,
        ref_exprs,
        partial_bindings,
        0,
    );
    var reserved_deps: u55 = 0;
    const seeded_holes = try allocator.alloc(bool, num_binders);
    defer allocator.free(seeded_holes);
    @memset(seeded_holes, false);

    for (derived_bindings) |binding| {
        const recover = switch (binding) {
            .recover => |recover| recover,
            .abstract => continue,
        };
        const hole_view_idx = recover.hole_view_idx;
        if (seeded_holes[hole_view_idx]) continue;
        const rule_idx = binder_map[hole_view_idx] orelse continue;
        if (partial_bindings[rule_idx] != null) continue;
        if (!arg_infos[hole_view_idx].bound) continue;

        const selection = chooseFreshBinding(
            parser,
            theorem,
            theorem_vars,
            sort_vars,
            arg_infos[hole_view_idx].sort_name,
            used_deps,
            reserved_deps,
        ) catch |err| switch (err) {
            error.FreshNoAvailableVar => continue,
            else => return err,
        };
        seeds[hole_view_idx] = .{ .exact = selection.expr_id };
        reserved_deps |= selection.deps;
        seeded_holes[hole_view_idx] = true;
    }
    return seeds;
}

fn parseFreshAnnotation(
    parser: *const MM0Parser,
    rule: *const RuleDecl,
    text: []const u8,
) !FreshDecl {
    const trimmed = std.mem.trim(u8, text, " \t\r\n;");
    if (trimmed.len == 0) return error.InvalidFreshAnnotation;
    if (!isIdentStart(trimmed[0])) return error.InvalidFreshAnnotation;

    var name_end: usize = 1;
    while (name_end < trimmed.len and isIdentChar(trimmed[name_end])) {
        name_end += 1;
    }
    if (std.mem.trim(u8, trimmed[name_end..], " \t\r\n").len != 0) {
        return error.InvalidFreshAnnotation;
    }

    const name = trimmed[0..name_end];
    const target_arg_idx = findRuleArgIndex(rule, name) orelse {
        return error.UnknownFreshBinder;
    };
    if (!rule.args[target_arg_idx].bound) {
        return error.FreshRequiresBoundBinder;
    }

    const sort_name = rule.args[target_arg_idx].sort_name;
    const sort_id = parser.sort_names.get(sort_name) orelse {
        return error.UnknownSort;
    };
    const sort = parser.sort_infos.items[sort_id];
    if (sort.strict) return error.FreshStrictSort;
    if (sort.free) return error.FreshFreeSort;

    return .{
        .target_arg_idx = target_arg_idx,
    };
}

fn parseFreshenAnnotation(
    rule: *const RuleDecl,
    text: []const u8,
) !FreshenDecl {
    var it = std.mem.tokenizeAny(
        u8,
        std.mem.trimRight(u8, text, " \t\r\n;"),
        " \t\r\n",
    );
    const target_name = it.next() orelse return error.InvalidFreshenAnnotation;
    const blocker_name =
        it.next() orelse return error.InvalidFreshenAnnotation;
    if (it.next() != null) return error.InvalidFreshenAnnotation;

    const target_arg_idx = findRuleArgIndex(rule, target_name) orelse {
        return error.UnknownFreshenBinder;
    };
    const blocker_arg_idx = findRuleArgIndex(rule, blocker_name) orelse {
        return error.UnknownFreshenBinder;
    };
    if (rule.args[target_arg_idx].bound) {
        return error.FreshenTargetMustBeRegularBinder;
    }
    if (!rule.args[blocker_arg_idx].bound) {
        return error.FreshenBlockerMustBeBoundBinder;
    }

    return .{
        .target_arg_idx = target_arg_idx,
        .blocker_arg_idx = blocker_arg_idx,
    };
}

fn annotationMatchesTag(ann: []const u8, tag: []const u8) bool {
    if (!std.mem.startsWith(u8, ann, tag)) return false;
    if (ann.len == tag.len) return true;
    return isAsciiWhitespace(ann[tag.len]);
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}

fn exprDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !u55 {
    return (try Inference.exprInfo(
        env,
        theorem,
        theorem.arg_infos,
        expr_id,
    )).deps;
}

fn isAsciiWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r';
}

fn isIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}
