const std = @import("std");
const ExprId = @import("../compiler_expr.zig").ExprId;

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
