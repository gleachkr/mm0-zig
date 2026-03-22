const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;

/// Identifies a single symbolic fresh variable introduced by one specific
/// definition unfolding. Two `FreshId`s are equal iff they refer to the same
/// hidden dummy slot within the same unfolding occurrence.
pub const FreshId = struct {
    /// Which unfolding occurrence produced this fresh variable.
    /// Each call to `openDefSymbolic` increments a global counter.
    occurrence: u32,
    /// Which hidden-dummy slot within the definition body.
    slot: u16,
    /// Sort of this dummy (carried for matching constraints).
    sort_name: []const u8,
};

/// Interned symbolic expression identifier.
pub const SExprId = u32;

/// A symbolic expression node. Unlike `ExprId`, these can represent
/// speculative structure that hasn't been committed to the theorem context.
pub const SExprNode = union(enum) {
    /// An existing concrete theorem expression, used atomically.
    concrete: ExprId,
    /// A term application with symbolically exposed children.
    app: App,
    /// A symbolic fresh variable from a definition unfolding.
    fresh: FreshId,

    pub const App = struct {
        term_id: u32,
        args: []const SExprId,
    };
};

const SExprNodeContext = struct {
    pub fn hash(_: SExprNodeContext, key: SExprNode) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hashSExprNode(&hasher, key);
        return hasher.final();
    }

    pub fn eql(_: SExprNodeContext, a: SExprNode, b: SExprNode) bool {
        return eqlSExprNode(a, b);
    }
};

fn hashSExprNode(hasher: *std.hash.Wyhash, node: SExprNode) void {
    switch (node) {
        .concrete => |id| {
            hasher.update(&[_]u8{0});
            hasher.update(std.mem.asBytes(&id));
        },
        .app => |app| {
            hasher.update(&[_]u8{1});
            hasher.update(std.mem.asBytes(&app.term_id));
            for (app.args) |arg| {
                hasher.update(std.mem.asBytes(&arg));
            }
        },
        .fresh => |fresh| {
            hasher.update(&[_]u8{2});
            hasher.update(std.mem.asBytes(&fresh.occurrence));
            hasher.update(std.mem.asBytes(&fresh.slot));
        },
    }
}

fn eqlSExprNode(a: SExprNode, b: SExprNode) bool {
    const a_tag: u2 = switch (a) {
        .concrete => 0,
        .app => 1,
        .fresh => 2,
    };
    const b_tag: u2 = switch (b) {
        .concrete => 0,
        .app => 1,
        .fresh => 2,
    };
    if (a_tag != b_tag) return false;

    return switch (a) {
        .concrete => |a_id| a_id == b.concrete,
        .app => |a_app| blk: {
            const b_app = b.app;
            if (a_app.term_id != b_app.term_id) break :blk false;
            if (a_app.args.len != b_app.args.len) break :blk false;
            for (a_app.args, b_app.args) |a_arg, b_arg| {
                if (a_arg != b_arg) break :blk false;
            }
            break :blk true;
        },
        .fresh => |a_fresh| blk: {
            const b_fresh = b.fresh;
            break :blk a_fresh.occurrence == b_fresh.occurrence and
                a_fresh.slot == b_fresh.slot;
        },
    };
}

const SExprNodeMap = std.HashMapUnmanaged(
    SExprNode,
    SExprId,
    SExprNodeContext,
    std.hash_map.default_max_load_percentage,
);

/// Hash-consing interner for symbolic expressions. Lifetime is typically
/// scoped to one solver invocation.
pub const SExprInterner = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayListUnmanaged(SExprNode) = .{},
    index: SExprNodeMap = .empty,

    pub fn init(allocator: std.mem.Allocator) SExprInterner {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *SExprInterner) void {
        for (self.nodes.items) |expr_node| {
            switch (expr_node) {
                .app => |app| self.allocator.free(app.args),
                .concrete, .fresh => {},
            }
        }
        self.nodes.deinit(self.allocator);
        self.index.deinit(self.allocator);
    }

    pub fn node(self: *const SExprInterner, id: SExprId) *const SExprNode {
        return &self.nodes.items[@intCast(id)];
    }

    pub fn internConcrete(self: *SExprInterner, expr_id: ExprId) !SExprId {
        return try self.internNode(.{ .concrete = expr_id });
    }

    pub fn internFresh(self: *SExprInterner, fresh: FreshId) !SExprId {
        return try self.internNode(.{ .fresh = fresh });
    }

    pub fn internApp(
        self: *SExprInterner,
        term_id: u32,
        args: []const SExprId,
    ) !SExprId {
        const owned = try self.allocator.dupe(SExprId, args);
        return try self.internAppOwned(term_id, owned);
    }

    pub fn internAppOwned(
        self: *SExprInterner,
        term_id: u32,
        args: []SExprId,
    ) !SExprId {
        const key = SExprNode{
            .app = .{
                .term_id = term_id,
                .args = args,
            },
        };
        const gop = try self.index.getOrPutContext(self.allocator, key, .{});
        if (gop.found_existing) {
            self.allocator.free(args);
            return gop.value_ptr.*;
        }

        errdefer _ = self.index.removeContext(key, .{});
        errdefer self.allocator.free(args);

        const id = std.math.cast(SExprId, self.nodes.items.len) orelse {
            return error.TooManySymbolicExprs;
        };
        gop.value_ptr.* = id;
        try self.nodes.append(self.allocator, key);
        return id;
    }

    fn internNode(self: *SExprInterner, key: SExprNode) !SExprId {
        const gop = try self.index.getOrPutContext(self.allocator, key, .{});
        if (gop.found_existing) return gop.value_ptr.*;

        errdefer _ = self.index.removeContext(key, .{});

        const id = std.math.cast(SExprId, self.nodes.items.len) orelse {
            return error.TooManySymbolicExprs;
        };
        gop.value_ptr.* = id;
        try self.nodes.append(self.allocator, key);
        return id;
    }
};

/// Environment for alpha-equivalence comparison between two symbolic
/// expressions that may contain `Fresh` atoms from different unfolding
/// occurrences. Two fresh variables are alpha-equivalent if they occupy
/// corresponding positions and have the same sort.
pub const AlphaEnv = struct {
    allocator: std.mem.Allocator,
    /// Maps lhs FreshId → rhs FreshId that it has been paired with.
    lhs_to_rhs: std.ArrayListUnmanaged(FreshPair) = .{},

    const FreshPair = struct {
        lhs: FreshKey,
        rhs: FreshKey,
    };

    const FreshKey = struct {
        occurrence: u32,
        slot: u16,
    };

    pub fn init(allocator: std.mem.Allocator) AlphaEnv {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *AlphaEnv) void {
        self.lhs_to_rhs.deinit(self.allocator);
    }

    /// Check whether two symbolic expressions are alpha-equivalent.
    pub fn alphaEq(
        self: *AlphaEnv,
        interner: *const SExprInterner,
        lhs: SExprId,
        rhs: SExprId,
    ) !bool {
        if (lhs == rhs) return true;

        const lhs_node = interner.node(lhs);
        const rhs_node = interner.node(rhs);

        return switch (lhs_node.*) {
            .concrete => |lhs_id| switch (rhs_node.*) {
                .concrete => |rhs_id| lhs_id == rhs_id,
                else => false,
            },
            .fresh => |lhs_fresh| switch (rhs_node.*) {
                .fresh => |rhs_fresh| try self.matchFresh(lhs_fresh, rhs_fresh),
                else => false,
            },
            .app => |lhs_app| switch (rhs_node.*) {
                .app => |rhs_app| blk: {
                    if (lhs_app.term_id != rhs_app.term_id) break :blk false;
                    if (lhs_app.args.len != rhs_app.args.len) break :blk false;
                    const checkpoint = self.lhs_to_rhs.items.len;
                    for (lhs_app.args, rhs_app.args) |l, r| {
                        if (!try self.alphaEq(interner, l, r)) {
                            self.lhs_to_rhs.shrinkRetainingCapacity(checkpoint);
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
                else => false,
            },
        };
    }

    fn matchFresh(
        self: *AlphaEnv,
        lhs: FreshId,
        rhs: FreshId,
    ) !bool {
        // Must have the same sort.
        if (!std.mem.eql(u8, lhs.sort_name, rhs.sort_name)) return false;

        const lhs_key = FreshKey{ .occurrence = lhs.occurrence, .slot = lhs.slot };
        const rhs_key = FreshKey{ .occurrence = rhs.occurrence, .slot = rhs.slot };

        // Check existing pairings.
        for (self.lhs_to_rhs.items) |pair| {
            if (pair.lhs.occurrence == lhs_key.occurrence and
                pair.lhs.slot == lhs_key.slot)
            {
                return pair.rhs.occurrence == rhs_key.occurrence and
                    pair.rhs.slot == rhs_key.slot;
            }
            if (pair.rhs.occurrence == rhs_key.occurrence and
                pair.rhs.slot == rhs_key.slot)
            {
                return pair.lhs.occurrence == lhs_key.occurrence and
                    pair.lhs.slot == lhs_key.slot;
            }
        }

        // New pairing.
        try self.lhs_to_rhs.append(self.allocator, .{
            .lhs = lhs_key,
            .rhs = rhs_key,
        });
        return true;
    }
};
