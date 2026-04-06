const std = @import("std");
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const Expr = @import("../trusted/expressions.zig").Expr;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const TermStmt = @import("../trusted/parse.zig").TermStmt;

pub const ExprId = u32;
pub const TheoremVarId = u32;
pub const DummyVarId = u32;
pub const tracked_bound_dep_limit: u32 = @bitSizeOf(u55);

pub const VarId = union(enum) {
    theorem_var: TheoremVarId,
    dummy_var: DummyVarId,
};

pub const ExprNode = union(enum) {
    variable: VarId,
    app: App,

    pub const App = struct {
        term_id: u32,
        args: []const ExprId,
    };
};

pub const DummyKind = enum {
    concrete,
    placeholder,
};

pub const DummyInfo = struct {
    sort_name: []const u8,
    sort_id: u8,
    deps: u55,
    kind: DummyKind,
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
                .variable => {},
                .app => |app| self.allocator.free(app.args),
            }
        }
        self.nodes.deinit(self.allocator);
        self.index.deinit(self.allocator);
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
    next_dummy_id: DummyVarId = 0,
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
        self.parser_vars.deinit(self.allocator);
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
    /// - Explicit source/user dummies: seedTerm (compiler_expr.zig) and
    ///   applyDummyBindings (compiler_check.zig) for user-written @dummy.
    /// - Temporary mirror-context dummies in def_ops, including normalized
    ///   matching placeholders, which do not consume real theorem dependency
    ///   slots.
    ///
    /// The *accidental* allocation site — materializeEscapingWitnessForDummySlot
    /// in symbolic_engine.zig — is the footgun targeted for removal (see PLAN.md).
    /// Do NOT remove this API; only remove the accidental caller.
    pub fn addDummyVarResolved(
        self: *TheoremContext,
        sort_name: []const u8,
        sort_id: u8,
    ) !ExprId {
        return try self.addDummyVarResolvedWithKind(
            sort_name,
            sort_id,
            .concrete,
        );
    }

    pub fn addPlaceholderDummyVarResolved(
        self: *TheoremContext,
        sort_name: []const u8,
        sort_id: u8,
    ) !ExprId {
        return try self.addDummyVarResolvedWithKind(
            sort_name,
            sort_id,
            .placeholder,
        );
    }

    fn addDummyVarResolvedWithKind(
        self: *TheoremContext,
        sort_name: []const u8,
        sort_id: u8,
        kind: DummyKind,
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
            .kind = kind,
        });
        self.next_dummy_dep = try std.math.add(u32, self.next_dummy_dep, 1);
        return try self.interner.internVar(.{ .dummy_var = dummy_id });
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
        const dummy_info = self.theorem_dummies.items[dummy_id];

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
        .app => |app| {
            hasher.update(&[_]u8{1});
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
