const std = @import("std");
const ExprId = @import("../compiler_expr.zig").ExprId;
const TheoremContext = @import("../compiler_expr.zig").TheoremContext;
const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;

pub const MirroredTheoremContext = struct {
    theorem: TheoremContext,
    source_dummy_map: []const ExprId,
    mirror_dummy_map: []const ExprId,

    pub fn init(
        allocator: std.mem.Allocator,
        source: *const TheoremContext,
    ) !MirroredTheoremContext {
        var theorem = TheoremContext.init(allocator);
        theorem.arg_infos = source.arg_infos;
        try theorem.seedBinderCount(source.theorem_vars.items.len);
        theorem.next_dummy_dep = countBoundArgs(source.arg_infos);

        const source_dummy_map = try allocator.alloc(
            ExprId,
            source.theorem_dummies.items.len,
        );
        errdefer allocator.free(source_dummy_map);

        const mirror_dummy_map = try allocator.alloc(
            ExprId,
            source.theorem_dummies.items.len,
        );
        errdefer allocator.free(mirror_dummy_map);

        for (source.theorem_dummies.items, 0..) |dummy, idx| {
            const mirror_dummy = try theorem.addDummyVarResolved(
                dummy.sort_name,
                dummy.sort_id,
            );
            source_dummy_map[idx] = mirror_dummy;
            mirror_dummy_map[idx] = try originalDummyExprId(source, idx);
        }

        return .{
            .theorem = theorem,
            .source_dummy_map = source_dummy_map,
            .mirror_dummy_map = mirror_dummy_map,
        };
    }

    pub fn deinit(
        self: *MirroredTheoremContext,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.source_dummy_map);
        allocator.free(self.mirror_dummy_map);
        self.theorem.deinit();
    }
};

pub fn countBoundArgs(args: []const ArgInfo) u32 {
    var count: u32 = 0;
    for (args) |arg| {
        if (arg.bound) count += 1;
    }
    return count;
}

pub fn originalDummyExprId(
    theorem: *const TheoremContext,
    idx: usize,
) !ExprId {
    return try @constCast(&theorem.interner).internVar(.{
        .dummy_var = @intCast(idx),
    });
}

pub fn copyExprBetweenTheorems(
    allocator: std.mem.Allocator,
    source: *const TheoremContext,
    target: *TheoremContext,
    source_expr: ExprId,
    source_dummy_map: []const ExprId,
    cache: *std.AutoHashMapUnmanaged(ExprId, ExprId),
) !ExprId {
    if (cache.get(source_expr)) |existing| return existing;

    const copied = switch (source.interner.node(source_expr).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= target.theorem_vars.items.len) {
                    return error.UnknownTheoremVariable;
                }
                break :blk target.theorem_vars.items[idx];
            },
            .dummy_var => |idx| blk: {
                if (idx >= source_dummy_map.len) {
                    return error.UnknownDummyVar;
                }
                break :blk source_dummy_map[idx];
            },
        },
        .app => |app| blk: {
            const args = try allocator.alloc(ExprId, app.args.len);
            errdefer allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = try copyExprBetweenTheorems(
                    allocator,
                    source,
                    target,
                    arg,
                    source_dummy_map,
                    cache,
                );
            }
            break :blk try target.interner.internAppOwned(app.term_id, args);
        },
    };

    try cache.put(allocator, source_expr, copied);
    return copied;
}
