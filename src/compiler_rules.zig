const std = @import("std");
const Expr = @import("./expressions.zig").Expr;

pub const TemplateExpr = union(enum) {
    binder: usize,
    app: App,

    pub const App = struct {
        term_id: u32,
        args: []const TemplateExpr,
    };

    pub fn fromExpr(
        allocator: std.mem.Allocator,
        expr: *const Expr,
        binders: []const *const Expr,
    ) !TemplateExpr {
        return switch (expr.*) {
            .variable => blk: {
                const idx = binderIndex(binders, expr) orelse {
                    return error.UnknownTemplateVariable;
                };
                break :blk .{ .binder = idx };
            },
            .term => |term| blk: {
                const args = try allocator.alloc(TemplateExpr, term.args.len);
                for (term.args, 0..) |arg, idx| {
                    args[idx] = try fromExpr(allocator, arg, binders);
                }
                break :blk .{ .app = .{
                    .term_id = term.id,
                    .args = args,
                } };
            },
        };
    }

    pub fn eql(a: TemplateExpr, b: TemplateExpr) bool {
        return switch (a) {
            .binder => |lhs| switch (b) {
                .binder => |rhs| lhs == rhs,
                else => false,
            },
            .app => |lhs| switch (b) {
                .app => |rhs| blk: {
                    if (lhs.term_id != rhs.term_id) break :blk false;
                    if (lhs.args.len != rhs.args.len) break :blk false;
                    for (lhs.args, rhs.args) |l_arg, r_arg| {
                        if (!l_arg.eql(r_arg)) break :blk false;
                    }
                    break :blk true;
                },
                else => false,
            },
        };
    }

    pub fn deinit(
        self: *const TemplateExpr,
        allocator: std.mem.Allocator,
    ) void {
        switch (self.*) {
            .binder => {},
            .app => |app| {
                for (app.args) |*arg| arg.deinit(allocator);
                allocator.free(app.args);
            },
        }
    }
};

fn binderIndex(
    binders: []const *const Expr,
    needle: *const Expr,
) ?usize {
    for (binders, 0..) |binder, idx| {
        if (binder == needle) return idx;
    }
    return null;
}
