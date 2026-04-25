const std = @import("std");
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const Expr = @import("../trusted/expressions.zig").Expr;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const TermStmt = @import("../trusted/parse.zig").TermStmt;

pub const ExprId = u32;
pub const TheoremVarId = u32;
pub const DummyVarId = u32;
pub const PlaceholderId = u32;
pub const tracked_bound_dep_limit: u32 = @bitSizeOf(u55);

pub const VarId = union(enum) {
    theorem_var: TheoremVarId,
    dummy_var: DummyVarId,
};

pub const ExprNode = union(enum) {
    variable: VarId,
    placeholder: PlaceholderId,
    app: App,

    pub const App = struct {
        term_id: u32,
        args: []const ExprId,
    };
};

pub const DummyInfo = struct {
    sort_name: []const u8,
    sort_id: u8,
    deps: u55,
};

pub const PlaceholderInfo = struct {
    sort_name: []const u8,
    deps: u55,
};

pub const ExprLeafInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

const ExprNodeContext = struct {
    pub fn hash(_: ExprNodeContext, key: ExprNode) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hashExprNode(&hasher, key);
        return hasher.final();
    }

    pub fn eql(_: ExprNodeContext, a: ExprNode, b: ExprNode) bool {
        return eqlExprNode(a, b);
    }
};

const ExprNodeMap = std.HashMapUnmanaged(
    ExprNode,
    ExprId,
    ExprNodeContext,
    std.hash_map.default_max_load_percentage,
);

pub const ExprInterner = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayListUnmanaged(ExprNode) = .{},
    index: ExprNodeMap = .empty,

    pub fn init(allocator: std.mem.Allocator) ExprInterner {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ExprInterner) void {
        for (self.nodes.items) |expr_node| {
            switch (expr_node) {
                .variable, .placeholder => {},
                .app => |app| self.allocator.free(app.args),
            }
        }
        self.nodes.deinit(self.allocator);
        self.index.deinit(self.allocator);
    }

    pub fn clone(self: *const ExprInterner) !ExprInterner {
        var copy = ExprInterner.init(self.allocator);
        errdefer copy.deinit();

        try copy.nodes.ensureTotalCapacity(
            self.allocator,
            self.nodes.items.len,
        );
        try copy.index.ensureTotalCapacity(
            self.allocator,
            self.index.count(),
        );

        for (self.nodes.items, 0..) |expr_node, idx| {
            const cloned: ExprNode = switch (expr_node) {
                .variable, .placeholder => expr_node,
                .app => |app| .{ .app = .{
                    .term_id = app.term_id,
                    .args = try self.allocator.dupe(ExprId, app.args),
                } },
            };
            errdefer switch (cloned) {
                .variable, .placeholder => {},
                .app => |app| self.allocator.free(app.args),
            };

            try copy.nodes.append(self.allocator, cloned);
            try copy.index.putContext(
                self.allocator,
                cloned,
                @intCast(idx),
                .{},
            );
        }
        return copy;
    }

    pub fn count(self: *const ExprInterner) usize {
        return self.nodes.items.len;
    }

    pub fn node(self: *const ExprInterner, id: ExprId) *const ExprNode {
        return &self.nodes.items[@intCast(id)];
    }

    pub fn internVar(self: *ExprInterner, var_id: VarId) !ExprId {
        return try self.internNode(.{ .variable = var_id });
    }

    pub fn internPlaceholder(
        self: *ExprInterner,
        placeholder_id: PlaceholderId,
    ) !ExprId {
        return try self.internNode(.{ .placeholder = placeholder_id });
    }

    pub fn internApp(
        self: *ExprInterner,
        term_id: u32,
        args: []const ExprId,
    ) !ExprId {
        const owned = try self.allocator.dupe(ExprId, args);
        return try self.internAppOwned(term_id, owned);
    }

    pub fn internAppOwned(
        self: *ExprInterner,
        term_id: u32,
        args: []ExprId,
    ) !ExprId {
        const key = ExprNode{
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

        const id = std.math.cast(ExprId, self.nodes.items.len) orelse {
            return error.TooManyTheoremExprs;
        };
        gop.value_ptr.* = id;
        try self.nodes.append(self.allocator, key);
        return id;
    }

    fn internNode(self: *ExprInterner, key: ExprNode) !ExprId {
        const gop = try self.index.getOrPutContext(self.allocator, key, .{});
        if (gop.found_existing) return gop.value_ptr.*;

        errdefer _ = self.index.removeContext(key, .{});

        const id = std.math.cast(ExprId, self.nodes.items.len) orelse {
            return error.TooManyTheoremExprs;
        };
        gop.value_ptr.* = id;
        try self.nodes.append(self.allocator, key);
        return id;
    }
};

pub const TheoremContext = struct {
    allocator: std.mem.Allocator,
    interner: ExprInterner,
    parser_vars: std.AutoHashMapUnmanaged(*const Expr, VarId) = .empty,
    arg_infos: []const ArgInfo = &.{},
    theorem_vars: std.ArrayListUnmanaged(ExprId) = .{},
    theorem_hyps: std.ArrayListUnmanaged(ExprId) = .{},
    theorem_dummies: std.ArrayListUnmanaged(DummyInfo) = .{},
    theorem_placeholders: std.ArrayListUnmanaged(PlaceholderInfo) = .{},
    next_dummy_id: DummyVarId = 0,
    next_placeholder_id: PlaceholderId = 0,
    // Placeholder deps are frontend-only synthetic masks. They must stay
    // disjoint from real theorem dep bits because internal matching and
    // freshening code still reasons over one shared u55 dep universe.
    next_placeholder_dep: u32 = 0,
    next_dummy_dep: u32 = 0,

    pub fn init(allocator: std.mem.Allocator) TheoremContext {
        return .{
            .allocator = allocator,
            .interner = ExprInterner.init(allocator),
        };
    }

    pub fn deinit(self: *TheoremContext) void {
        self.interner.deinit();
        self.theorem_vars.deinit(self.allocator);
        self.theorem_hyps.deinit(self.allocator);
        self.theorem_dummies.deinit(self.allocator);
        self.theorem_placeholders.deinit(self.allocator);
        self.parser_vars.deinit(self.allocator);
    }

    pub fn clone(self: *const TheoremContext) !TheoremContext {
        var copy = TheoremContext.init(self.allocator);
        errdefer copy.deinit();

        copy.interner = try self.interner.clone();
        copy.arg_infos = self.arg_infos;
        try copy.theorem_vars.appendSlice(
            self.allocator,
            self.theorem_vars.items,
        );
        try copy.theorem_hyps.appendSlice(
            self.allocator,
            self.theorem_hyps.items,
        );
        try copy.theorem_dummies.appendSlice(
            self.allocator,
            self.theorem_dummies.items,
        );
        try copy.theorem_placeholders.appendSlice(
            self.allocator,
            self.theorem_placeholders.items,
        );
        copy.next_dummy_id = self.next_dummy_id;
        copy.next_placeholder_id = self.next_placeholder_id;
        copy.next_placeholder_dep = self.next_placeholder_dep;
        copy.next_dummy_dep = self.next_dummy_dep;

        try copy.parser_vars.ensureTotalCapacity(
            self.allocator,
            self.parser_vars.count(),
        );
        var it = self.parser_vars.iterator();
        while (it.next()) |entry| {
            try copy.parser_vars.put(
                self.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return copy;
    }

    // Seed a context with `count` theorem binders but without any parser-side
    // `Expr*` nodes. This is used when we need a temporary binder-indexed DAG,
    // for example to rebuild a rule's unify stream for argument inference.
    pub fn seedBinderCount(
        self: *TheoremContext,
        count: usize,
    ) !void {
        for (0..count) |idx| {
            const var_id = VarId{
                .theorem_var = std.math.cast(TheoremVarId, idx) orelse {
                    return error.TooManyTheoremVars;
                },
            };
            const expr_id = try self.interner.internVar(var_id);
            try self.theorem_vars.append(self.allocator, expr_id);
        }
    }

    pub fn seedArgs(
        self: *TheoremContext,
        arg_infos: []const ArgInfo,
        arg_exprs: []const *const Expr,
    ) !void {
        self.arg_infos = arg_infos;
        try self.seedBinderCount(arg_exprs.len);
        var next_bound_dep: u32 = 0;
        for (arg_infos) |arg| {
            if (arg.bound) next_bound_dep += 1;
        }
        self.next_dummy_dep = next_bound_dep;
        for (arg_exprs, 0..) |arg_expr, idx| {
            try self.parser_vars.put(
                self.allocator,
                arg_expr,
                .{ .theorem_var = @intCast(idx) },
            );
        }
    }

    pub fn seedTerm(self: *TheoremContext, parser: *const MM0Parser, stmt: TermStmt) !void {
        try self.seedArgs(stmt.args, stmt.arg_exprs);
        // Explicit source allocation: dummies declared in the .mm0 source term definition.
        for (stmt.dummy_args, stmt.dummy_exprs) |arg, expr| {
            const dummy_var_id = try self.addDummyVar(parser, arg);
            const var_id = self.interner.node(dummy_var_id).*.variable;
            try self.parser_vars.put(self.allocator, expr, var_id);
        }
    }

    pub fn seedAssertion(
        self: *TheoremContext,
        stmt: AssertionStmt,
    ) !void {
        try self.seedArgs(stmt.args, stmt.arg_exprs);
        for (stmt.hyps) |hyp| {
            const hyp_id = try self.internParsedExpr(hyp);
            try self.theorem_hyps.append(self.allocator, hyp_id);
        }
    }

    pub fn addDummyVar(
        self: *TheoremContext,
        parser: *const MM0Parser,
        arg: ArgInfo,
    ) !ExprId {
        const sort_id = parser.sort_names.get(arg.sort_name) orelse {
            return error.UnknownSort;
        };
        return try self.addDummyVarResolved(arg.sort_name, sort_id);
    }

    /// Allocate a fresh theorem-local dummy variable. This is the low-level
    /// API that all dummy allocation routes through. It is intentionally kept
    /// for legitimate use cases:
    ///
    /// - Explicit source/user dummies: seedTerm in this file for dot binders
    ///   declared in .mm0, plus named theorem-local vars created through
    ///   @vars / @fresh when a proof line needs them.
    /// - Temporary mirror-context dummies in def_ops for copied real dummies.
    ///
    /// The accidental allocation site,
    /// materializeEscapingWitnessForDummySlot in
    /// def_ops/symbolic_engine.zig, is the footgun targeted for removal
    /// (see PLAN.md).
    /// Do NOT remove this API; only remove the accidental caller.
    pub fn addDummyVarResolved(
        self: *TheoremContext,
        sort_name: []const u8,
        sort_id: u8,
    ) !ExprId {
        if (self.next_dummy_dep >= tracked_bound_dep_limit) {
            return error.DependencySlotExhausted;
        }

        const dummy_id = self.next_dummy_id;
        self.next_dummy_id = try std.math.add(DummyVarId, dummy_id, 1);
        try self.theorem_dummies.append(self.allocator, .{
            .sort_name = sort_name,
            .sort_id = sort_id,
            .deps = @as(u55, 1) << @intCast(self.next_dummy_dep),
        });
        self.next_dummy_dep = try std.math.add(u32, self.next_dummy_dep, 1);
        return try self.interner.internVar(.{ .dummy_var = dummy_id });
    }

    /// Allocate a frontend-only placeholder. These never reach emission, but
    /// they still participate in internal dep-sensitive matching and freshening
    /// logic. So they get synthetic dep bits from the top of the same u55 mask
    /// space while remaining disjoint from real theorem dep bookkeeping.
    pub fn addPlaceholderResolved(
        self: *TheoremContext,
        sort_name: []const u8,
    ) !ExprId {
        const total_dep_uses = try std.math.add(
            u32,
            self.next_dummy_dep,
            self.next_placeholder_dep,
        );
        if (total_dep_uses >= tracked_bound_dep_limit) {
            return error.DependencySlotExhausted;
        }

        const placeholder_id = self.next_placeholder_id;
        self.next_placeholder_id = try std.math.add(
            PlaceholderId,
            placeholder_id,
            1,
        );
        const dep_bit = tracked_bound_dep_limit - 1 - self.next_placeholder_dep;
        self.next_placeholder_dep = try std.math.add(
            u32,
            self.next_placeholder_dep,
            1,
        );
        try self.theorem_placeholders.append(self.allocator, .{
            .sort_name = sort_name,
            .deps = @as(u55, 1) << @intCast(dep_bit),
        });
        return try self.interner.internPlaceholder(placeholder_id);
    }

    pub fn placeholderInfo(
        self: *const TheoremContext,
        idx: usize,
    ) ?PlaceholderInfo {
        if (idx >= self.theorem_placeholders.items.len) return null;
        return self.theorem_placeholders.items[idx];
    }

    pub fn requirePlaceholderInfo(
        self: *const TheoremContext,
        idx: usize,
    ) !PlaceholderInfo {
        return self.placeholderInfo(idx) orelse error.UnknownPlaceholder;
    }

    pub fn requireDummyInfo(
        self: *const TheoremContext,
        idx: usize,
    ) !DummyInfo {
        if (idx >= self.theorem_dummies.items.len) {
            return error.UnknownDummyVar;
        }
        return self.theorem_dummies.items[idx];
    }

    pub fn requireTheoremArgInfo(
        self: *const TheoremContext,
        theorem_args: []const ArgInfo,
        idx: usize,
    ) !ArgInfo {
        _ = self;
        if (idx >= theorem_args.len) {
            return error.UnknownTheoremVariable;
        }
        return theorem_args[idx];
    }

    pub fn leafInfoWithArgs(
        self: *const TheoremContext,
        theorem_args: []const ArgInfo,
        expr_id: ExprId,
    ) !?ExprLeafInfo {
        return switch (self.interner.node(expr_id).*) {
            .app => null,
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| blk: {
                    const arg = try self.requireTheoremArgInfo(
                        theorem_args,
                        idx,
                    );
                    break :blk .{
                        .sort_name = arg.sort_name,
                        .bound = arg.bound,
                        .deps = arg.deps,
                    };
                },
                .dummy_var => |idx| blk: {
                    const dummy = try self.requireDummyInfo(idx);
                    break :blk .{
                        .sort_name = dummy.sort_name,
                        .bound = true,
                        .deps = dummy.deps,
                    };
                },
            },
            .placeholder => |idx| blk: {
                const placeholder = try self.requirePlaceholderInfo(idx);
                break :blk .{
                    .sort_name = placeholder.sort_name,
                    .bound = true,
                    .deps = placeholder.deps,
                };
            },
        };
    }

    pub fn currentLeafInfo(
        self: *const TheoremContext,
        expr_id: ExprId,
    ) !?ExprLeafInfo {
        return self.leafInfoWithArgs(self.arg_infos, expr_id);
    }

    pub fn currentLeafSortName(
        self: *const TheoremContext,
        expr_id: ExprId,
    ) ?[]const u8 {
        const info = self.currentLeafInfo(expr_id) catch return null;
        return if (info) |leaf| leaf.sort_name else null;
    }

    pub fn ensureNamedDummyParserVar(
        self: *TheoremContext,
        parser_allocator: std.mem.Allocator,
        theorem_vars: anytype,
        token: []const u8,
        sort_name: []const u8,
        sort_id: u8,
    ) !void {
        if (theorem_vars.contains(token)) return;

        const dummy_expr_id = try self.addDummyVarResolved(sort_name, sort_id);
        const var_id = self.interner.node(dummy_expr_id).*.variable;
        const dummy_id = switch (var_id) {
            .dummy_var => |id| id,
            else => unreachable,
        };
        const dummy_info = try self.requireDummyInfo(dummy_id);

        const expr = try parser_allocator.create(Expr);
        expr.* = .{
            .variable = .{
                .sort = @intCast(sort_id),
                .bound = true,
                .deps = dummy_info.deps,
            },
        };

        try self.parser_vars.put(self.allocator, expr, var_id);
        try theorem_vars.put(token, expr);
    }

    pub fn internParsedExpr(
        self: *TheoremContext,
        expr: *const Expr,
    ) !ExprId {
        return switch (expr.*) {
            .variable => blk: {
                const var_id = self.parser_vars.get(expr) orelse {
                    return error.UnknownTheoremVariable;
                };
                break :blk try self.interner.internVar(var_id);
            },
            .term => |term| blk: {
                const args = try self.allocator.alloc(ExprId, term.args.len);
                errdefer self.allocator.free(args);
                for (term.args, 0..) |arg, idx| {
                    args[idx] = try self.internParsedExpr(arg);
                }
                break :blk try self.interner.internAppOwned(term.id, args);
            },
            .hole => return error.HoleNotConcrete,
        };
    }

    /// Reverse of instantiateTemplate: given a TemplateExpr and a concrete
    /// ExprId, solve for binder values. Returns true on success.
    pub fn matchTemplate(
        self: *const TheoremContext,
        template: TemplateExpr,
        expr_id: ExprId,
        bindings: []?ExprId,
    ) bool {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= bindings.len) break :blk false;
                if (bindings[idx]) |existing| {
                    break :blk existing == expr_id;
                } else {
                    bindings[idx] = expr_id;
                    break :blk true;
                }
            },
            .app => |app| blk: {
                const node = self.interner.node(expr_id);
                switch (node.*) {
                    .app => |concrete| {
                        if (concrete.term_id != app.term_id) break :blk false;
                        if (concrete.args.len != app.args.len) break :blk false;
                        for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                            if (!self.matchTemplate(tmpl_arg, conc_arg, bindings))
                                break :blk false;
                        }
                        break :blk true;
                    },
                    else => break :blk false,
                }
            },
        };
    }

    pub fn instantiateTemplate(
        self: *TheoremContext,
        template: TemplateExpr,
        binders: []const ExprId,
    ) !ExprId {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= binders.len) {
                    return error.TemplateBinderOutOfRange;
                }
                break :blk binders[idx];
            },
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.instantiateTemplate(arg, binders);
                }
                break :blk try self.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }
};

fn hashExprNode(hasher: *std.hash.Wyhash, key: ExprNode) void {
    switch (key) {
        .variable => |var_id| {
            hasher.update(&[_]u8{0});
            hashVarId(hasher, var_id);
        },
        .placeholder => |id| {
            hasher.update(&[_]u8{1});
            hasher.update(std.mem.asBytes(&id));
        },
        .app => |app| {
            hasher.update(&[_]u8{2});
            hasher.update(std.mem.asBytes(&app.term_id));
            for (app.args) |arg| {
                hasher.update(std.mem.asBytes(&arg));
            }
        },
    }
}

fn hashVarId(hasher: *std.hash.Wyhash, var_id: VarId) void {
    switch (var_id) {
        .theorem_var => |id| {
            hasher.update(&[_]u8{0});
            hasher.update(std.mem.asBytes(&id));
        },
        .dummy_var => |id| {
            hasher.update(&[_]u8{1});
            hasher.update(std.mem.asBytes(&id));
        },
    }
}

fn eqlExprNode(a: ExprNode, b: ExprNode) bool {
    return switch (a) {
        .variable => |lhs| switch (b) {
            .variable => |rhs| eqlVarId(lhs, rhs),
            else => false,
        },
        .placeholder => |lhs| switch (b) {
            .placeholder => |rhs| lhs == rhs,
            else => false,
        },
        .app => |lhs| switch (b) {
            .app => |rhs| blk: {
                if (lhs.term_id != rhs.term_id) break :blk false;
                if (lhs.args.len != rhs.args.len) break :blk false;
                for (lhs.args, rhs.args) |l_arg, r_arg| {
                    if (l_arg != r_arg) break :blk false;
                }
                break :blk true;
            },
            else => false,
        },
    };
}

fn eqlVarId(a: VarId, b: VarId) bool {
    return switch (a) {
        .theorem_var => |lhs| switch (b) {
            .theorem_var => |rhs| lhs == rhs,
            else => false,
        },
        .dummy_var => |lhs| switch (b) {
            .dummy_var => |rhs| lhs == rhs,
            else => false,
        },
    };
}
