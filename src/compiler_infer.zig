const std = @import("std");
const AppView = @import("./compiler_env.zig").AppView;
const AppViewPosition = @import("./compiler_env.zig").AppViewPosition;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const CompilerRewrite = @import("./compiler_rewrite.zig");
const CompilerRules = @import("./compiler_rules.zig");

pub const ViewFailure = struct {
    view_name: []const u8,
    position: ?AppViewPosition,
    binder_index: ?usize = null,
    err: anyerror,
};

pub const Success = struct {
    bindings: []const ExprId,
    view_name: []const u8,
};

pub const Outcome = union(enum) {
    success: Success,
    no_match: []const ViewFailure,
    ambiguous: []const []const u8,

    pub fn deinit(self: Outcome, allocator: std.mem.Allocator) void {
        switch (self) {
            .success => |success| allocator.free(success.bindings),
            .no_match => |failures| allocator.free(failures),
            .ambiguous => |names| allocator.free(names),
        }
    }
};

pub fn recoverBindings(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) anyerror!Outcome {
    const canonical_refs = try allocator.alloc(ExprId, ref_exprs.len);
    defer allocator.free(canonical_refs);
    const canonical_line = try canonicalizeUserExprs(
        allocator,
        theorem,
        ref_exprs,
        canonical_refs,
        line_expr,
    );

    var failures = std.ArrayListUnmanaged(ViewFailure){};
    defer failures.deinit(allocator);

    var ambiguous = std.ArrayListUnmanaged([]const u8){};
    defer ambiguous.deinit(allocator);

    var first_success: ?Success = null;
    errdefer if (first_success) |success| allocator.free(success.bindings);

    for (rule.views) |view| {
        const matched = try matchView(
            allocator,
            theorem,
            rule,
            view,
            partial_bindings,
            canonical_refs,
            canonical_line,
        );
        switch (matched) {
            .failure => |failure| try failures.append(allocator, failure),
            .success => |success| {
                if (ambiguous.items.len != 0) {
                    try ambiguous.append(allocator, success.view_name);
                    allocator.free(success.bindings);
                    continue;
                }
                if (first_success) |prior| {
                    try ambiguous.append(allocator, prior.view_name);
                    try ambiguous.append(allocator, success.view_name);
                    allocator.free(prior.bindings);
                    allocator.free(success.bindings);
                    first_success = null;
                    continue;
                }
                first_success = success;
            },
        }
    }

    if (ambiguous.items.len != 0) {
        return .{ .ambiguous = try ambiguous.toOwnedSlice(allocator) };
    }
    if (first_success) |success| {
        return .{ .success = success };
    }
    return .{ .no_match = try failures.toOwnedSlice(allocator) };
}

const MatchViewResult = union(enum) {
    success: Success,
    failure: ViewFailure,
};

fn canonicalizeUserExprs(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    ref_exprs: []const ExprId,
    canonical_refs: []ExprId,
    line_expr: ExprId,
) anyerror!ExprId {
    var system = CompilerRewrite.RewriteSystem.init(allocator);
    defer system.deinit();
    const bundle_id = try system.addBundle("syntactic", null, null);

    var canonicalizer = CompilerRewrite.Canonicalizer.init(
        allocator,
        &system,
        theorem,
        256,
    );
    defer canonicalizer.deinit();

    for (ref_exprs, 0..) |expr_id, idx| {
        canonical_refs[idx] =
            (try canonicalizer.canonicalize(bundle_id, expr_id)).expr_id;
    }
    return (try canonicalizer.canonicalize(bundle_id, line_expr)).expr_id;
}

fn matchView(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    view: AppView,
    partial_bindings: []const ?ExprId,
    canonical_refs: []const ExprId,
    canonical_line: ExprId,
) !MatchViewResult {
    const bindings = try allocator.alloc(?ExprId, partial_bindings.len);
    defer allocator.free(bindings);
    @memcpy(bindings, partial_bindings);

    for (view.positions) |position| {
        const template = positionTemplate(rule, position) orelse {
            return .{ .failure = .{
                .view_name = view.name,
                .position = position,
                .err = error.InvalidViewPosition,
            } };
        };
        const actual = positionExpr(position, canonical_refs, canonical_line) orelse {
            return .{ .failure = .{
                .view_name = view.name,
                .position = position,
                .err = error.InvalidViewPosition,
            } };
        };
        if (!CompilerRules.matchExpr(
            &theorem.interner,
            template,
            actual,
            bindings,
        )) {
            return .{ .failure = .{
                .view_name = view.name,
                .position = position,
                .err = error.TemplateMismatch,
            } };
        }
    }

    const concrete = try allocator.alloc(ExprId, bindings.len);
    errdefer allocator.free(concrete);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding orelse {
            return .{ .failure = .{
                .view_name = view.name,
                .position = null,
                .binder_index = idx,
                .err = error.MissingBinderAssignment,
            } };
        };
    }
    return .{ .success = .{
        .bindings = concrete,
        .view_name = view.name,
    } };
}

fn positionTemplate(
    rule: *const RuleDecl,
    position: AppViewPosition,
) ?CompilerRules.TemplateExpr {
    return switch (position) {
        .concl => rule.concl,
        .hyp => |idx| if (idx < rule.hyps.len) rule.hyps[idx] else null,
    };
}

fn positionExpr(
    position: AppViewPosition,
    canonical_refs: []const ExprId,
    canonical_line: ExprId,
) ?ExprId {
    return switch (position) {
        .concl => canonical_line,
        .hyp => |idx| if (idx < canonical_refs.len) canonical_refs[idx] else null,
    };
}
