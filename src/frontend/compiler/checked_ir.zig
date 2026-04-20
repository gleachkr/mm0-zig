const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;

pub const CheckedRef = union(enum) {
    hyp: usize,
    line: usize,
};

pub const CheckedLine = struct {
    expr: ExprId,
    data: union(enum) {
        rule: RuleLine,
        transport: TransportLine,
    },

    pub const RuleLine = struct {
        rule_id: u32,
        bindings: []const ExprId,
        refs: []const CheckedRef,
    };

    pub const TransportLine = struct {
        source: CheckedRef,
        source_expr: ExprId,
    };
};

pub fn validateNoPlaceholderExpr(
    theorem: *const TheoremContext,
    expr: ExprId,
) error{PlaceholderLeakage}!void {
    switch (theorem.interner.node(expr).*) {
        .variable => {},
        .placeholder => return error.PlaceholderLeakage,
        .app => |app| {
            for (app.args) |arg| {
                try validateNoPlaceholderExpr(theorem, arg);
            }
        },
    }
}

pub fn validateNoPlaceholderSlice(
    theorem: *const TheoremContext,
    exprs: []const ExprId,
) error{PlaceholderLeakage}!void {
    for (exprs) |expr| {
        try validateNoPlaceholderExpr(theorem, expr);
    }
}

pub fn validateLine(
    theorem: *const TheoremContext,
    line: CheckedLine,
) error{PlaceholderLeakage}!void {
    try validateNoPlaceholderExpr(theorem, line.expr);
    switch (line.data) {
        .rule => |rule| try validateNoPlaceholderSlice(
            theorem,
            rule.bindings,
        ),
        .transport => |transport| try validateNoPlaceholderExpr(
            theorem,
            transport.source_expr,
        ),
    }
}

pub fn validateLines(
    theorem: *const TheoremContext,
    lines: []const CheckedLine,
) error{PlaceholderLeakage}!void {
    for (lines) |line| {
        try validateLine(theorem, line);
    }
}

pub fn appendRuleLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{
        .expr = expr,
        .data = .{ .rule = .{
            .rule_id = rule_id,
            .bindings = bindings,
            .refs = refs,
        } },
    });
    return idx;
}

pub fn appendTransportLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
    source_expr: ExprId,
    source: CheckedRef,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{
        .expr = expr,
        .data = .{ .transport = .{
            .source = source,
            .source_expr = source_expr,
        } },
    });
    return idx;
}

pub fn deinitLine(
    allocator: std.mem.Allocator,
    line: CheckedLine,
) void {
    switch (line.data) {
        .rule => |rule| {
            allocator.free(rule.bindings);
            allocator.free(rule.refs);
        },
        .transport => {},
    }
}

pub fn deinitLines(
    allocator: std.mem.Allocator,
    lines: []const CheckedLine,
) void {
    for (lines) |line| {
        deinitLine(allocator, line);
    }
}

pub fn rollbackToMark(
    allocator: std.mem.Allocator,
    lines: *std.ArrayListUnmanaged(CheckedLine),
    mark: usize,
) void {
    deinitLines(allocator, lines.items[mark..]);
    lines.shrinkRetainingCapacity(mark);
}

test "validateLines rejects placeholder bindings" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const bindings = [_]ExprId{placeholder};
    const lines = [_]CheckedLine{.{
        .expr = theorem.theorem_vars.items[0],
        .data = .{ .rule = .{
            .rule_id = 0,
            .bindings = &bindings,
            .refs = &.{},
        } },
    }};

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateLines(&theorem, &lines),
    );
}

test "validateLine rejects placeholder transports" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const line: CheckedLine = .{
        .expr = theorem.theorem_vars.items[0],
        .data = .{ .transport = .{
            .source = .{ .hyp = 0 },
            .source_expr = placeholder,
        } },
    };

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateLine(&theorem, line),
    );
}
