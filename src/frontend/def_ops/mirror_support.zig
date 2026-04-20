const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
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

        // Mirror-only allocation: these dummies live in a temporary
        // MirroredTheoremContext, not the real theorem being compiled.
        // They do not consume real theorem dependency slots.
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
    reverse_cache: ?*std.AutoHashMapUnmanaged(ExprId, ExprId),
) !ExprId {
    if (cache.get(source_expr)) |existing| {
        try noteReverseMapping(
            allocator,
            reverse_cache,
            existing,
            source_expr,
        );
        return existing;
    }

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
        .placeholder => |idx| blk: {
            const placeholder = try source.requirePlaceholderInfo(idx);
            break :blk try target.addPlaceholderResolved(
                placeholder.sort_name,
            );
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
                    reverse_cache,
                );
            }
            break :blk try target.interner.internAppOwned(app.term_id, args);
        },
    };

    try cache.put(allocator, source_expr, copied);
    errdefer _ = cache.remove(source_expr);
    try noteReverseMapping(allocator, reverse_cache, copied, source_expr);
    return copied;
}

fn noteReverseMapping(
    allocator: std.mem.Allocator,
    reverse_cache: ?*std.AutoHashMapUnmanaged(ExprId, ExprId),
    copied_expr: ExprId,
    source_expr: ExprId,
) !void {
    const reverse = reverse_cache orelse return;
    const gop = try reverse.getOrPut(allocator, copied_expr);
    if (!gop.found_existing) {
        gop.value_ptr.* = source_expr;
        return;
    }
    std.debug.assert(gop.value_ptr.* == source_expr);
}

test "copyExprBetweenTheorems tracks reverse mappings incrementally" {
    var source = TheoremContext.init(std.testing.allocator);
    defer source.deinit();
    try source.seedBinderCount(1);
    const source_dummy = try source.addDummyVarResolved("obj", 0);
    const inner = try source.interner.internApp(
        1,
        &[_]ExprId{source.theorem_vars.items[0]},
    );
    const outer = try source.interner.internApp(
        2,
        &[_]ExprId{ inner, source_dummy },
    );

    var mirror = try MirroredTheoremContext.init(
        std.testing.allocator,
        &source,
    );
    defer mirror.deinit(std.testing.allocator);

    var forward: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty;
    defer forward.deinit(std.testing.allocator);
    var reverse: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty;
    defer reverse.deinit(std.testing.allocator);

    const copied_outer = try copyExprBetweenTheorems(
        std.testing.allocator,
        &source,
        &mirror.theorem,
        outer,
        mirror.source_dummy_map,
        &forward,
        &reverse,
    );
    const copied_inner = forward.get(inner) orelse return error.MissingMapping;

    try std.testing.expectEqual(outer, reverse.get(copied_outer).?);
    try std.testing.expectEqual(inner, reverse.get(copied_inner).?);

    const reverse_count = reverse.count();
    try std.testing.expectEqual(
        copied_outer,
        try copyExprBetweenTheorems(
            std.testing.allocator,
            &source,
            &mirror.theorem,
            outer,
            mirror.source_dummy_map,
            &forward,
            &reverse,
        ),
    );
    try std.testing.expectEqual(reverse_count, reverse.count());
}
