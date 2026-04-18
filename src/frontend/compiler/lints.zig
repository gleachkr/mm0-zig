const std = @import("std");
const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;
const RuleDecl = @import("../env.zig").RuleDecl;
const TermDecl = @import("../env.zig").TermDecl;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const Span = @import("../proof_script.zig").Span;
const DiagnosticDetail = @import("./diag.zig").DiagnosticDetail;
const DiagnosticSource = @import("./diag.zig").DiagnosticSource;

const UseState = struct {
    used_args: []bool,
    used_dummies: []bool,
};

pub fn lintUnusedTheoremParameters(
    self: anytype,
    allocator: std.mem.Allocator,
    rule: *const RuleDecl,
    span: ?Span,
    source: DiagnosticSource,
) !void {
    const used_args = try allocator.alloc(bool, rule.args.len);
    @memset(used_args, false);

    const state: UseState = .{
        .used_args = used_args,
        .used_dummies = &.{},
    };
    for (rule.hyps) |hyp| {
        markTemplateExprUses(state, hyp, rule.args.len);
    }
    markTemplateExprUses(state, rule.concl, rule.args.len);
    try propagateDependencyOnlyUses(
        allocator,
        used_args,
        rule.args,
        &.{},
        &.{},
    );

    for (rule.arg_names, 0..) |arg_name, idx| {
        if (used_args[idx]) continue;
        const parameter_name = try parameterDisplayName(
            allocator,
            arg_name,
            idx,
        );
        self.addWarning(.{
            .kind = .unused_theorem_parameter,
            .err = error.UnusedTheoremParameter,
            .source = source,
            .name = rule.name,
            .span = span,
            .detail = DiagnosticDetail{ .unused_parameter = .{
                .parameter_name = parameter_name,
            } },
        });
    }
}

pub fn lintUnusedDefinitionParameters(
    self: anytype,
    allocator: std.mem.Allocator,
    term: *const TermDecl,
    span: ?Span,
    source: DiagnosticSource,
) !void {
    const body = term.body orelse return;

    const used_args = try allocator.alloc(bool, term.args.len);
    @memset(used_args, false);
    const used_dummies = try allocator.alloc(bool, term.dummy_args.len);
    @memset(used_dummies, false);

    const state: UseState = .{
        .used_args = used_args,
        .used_dummies = used_dummies,
    };
    markTemplateExprUses(state, body, term.args.len);
    try propagateDependencyOnlyUses(
        allocator,
        used_args,
        term.args,
        used_dummies,
        term.dummy_args,
    );

    for (term.arg_names, 0..) |arg_name, idx| {
        if (used_args[idx]) continue;
        const parameter_name = try parameterDisplayName(
            allocator,
            arg_name,
            idx,
        );
        self.addWarning(.{
            .kind = .unused_definition_parameter,
            .err = error.UnusedDefinitionParameter,
            .source = source,
            .name = term.name,
            .span = span,
            .detail = DiagnosticDetail{ .unused_parameter = .{
                .parameter_name = parameter_name,
            } },
        });
    }
}

fn parameterDisplayName(
    allocator: std.mem.Allocator,
    arg_name: ?[]const u8,
    idx: usize,
) ![]const u8 {
    return arg_name orelse try std.fmt.allocPrint(
        allocator,
        "argument #{d}",
        .{idx + 1},
    );
}

fn markTemplateExprUses(
    state: UseState,
    expr: TemplateExpr,
    arg_count: usize,
) void {
    switch (expr) {
        .binder => |idx| {
            if (idx < arg_count) {
                state.used_args[idx] = true;
                return;
            }
            const dummy_idx = idx - arg_count;
            if (dummy_idx < state.used_dummies.len) {
                state.used_dummies[dummy_idx] = true;
            }
        },
        .app => |app| {
            for (app.args) |arg| {
                markTemplateExprUses(state, arg, arg_count);
            }
        },
    }
}

fn propagateDependencyOnlyUses(
    allocator: std.mem.Allocator,
    used_args: []bool,
    args: []const ArgInfo,
    used_dummies: []const bool,
    dummy_args: []const ArgInfo,
) !void {
    const bound_masks = try allocator.alloc(u55, args.len);
    defer allocator.free(bound_masks);
    @memset(bound_masks, 0);

    var next_bound_idx: u32 = 0;
    for (args, 0..) |arg, idx| {
        if (!arg.bound) continue;
        if (next_bound_idx >= @bitSizeOf(u55)) break;
        bound_masks[idx] = @as(u55, 1) << @intCast(next_bound_idx);
        next_bound_idx += 1;
    }

    for (args, 0..) |arg, idx| {
        if (!used_args[idx]) continue;
        markDependencyMaskUses(used_args, bound_masks, arg.deps);
    }
    for (dummy_args, 0..) |arg, idx| {
        if (!used_dummies[idx]) continue;
        markDependencyMaskUses(used_args, bound_masks, arg.deps);
    }
}

fn markDependencyMaskUses(
    used_args: []bool,
    bound_masks: []const u55,
    deps: u55,
) void {
    if (deps == 0) return;
    for (bound_masks, 0..) |mask, idx| {
        if (mask == 0) continue;
        if (deps & mask != 0) used_args[idx] = true;
    }
}
