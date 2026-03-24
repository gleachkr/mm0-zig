const std = @import("std");
const TermDecl = @import("./compiler_env.zig").TermDecl;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprApp = @import("./compiler_expr.zig").ExprNode.App;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;

pub const ConversionPlan = union(enum) {
    refl,
    unfold_lhs: struct {
        witness: ExprId,
        next: *const ConversionPlan,
    },
    unfold_rhs: struct {
        witness: ExprId,
        next: *const ConversionPlan,
    },
    cong: struct {
        children: []const *const ConversionPlan,
    },
};

const DummyBinding = struct {
    slot: usize,
    actual: ExprId,
};

const SymbolicDummyInfo = struct {
    sort_name: []const u8,
};

const SymbolicExpr = union(enum) {
    binder: usize,
    fixed: ExprId,
    dummy: usize,
    app: App,

    const App = struct {
        term_id: u32,
        args: []const *const SymbolicExpr,
    };
};

const ConcreteVarInfo = struct {
    sort_name: []const u8,
    bound: bool,
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    symbolic_dummy_infos: std.ArrayListUnmanaged(SymbolicDummyInfo) = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) Context {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
        };
    }

    pub fn deinit(self: *Context) void {
        self.symbolic_dummy_infos.deinit(self.allocator);
    }

    pub fn defCoversItem(
        self: *Context,
        def_expr: ExprId,
        item_expr: ExprId,
    ) anyerror!bool {
        return (try self.planDefCoversItem(def_expr, item_expr)) != null;
    }

    pub fn planDefCoversItem(
        self: *Context,
        def_expr: ExprId,
        item_expr: ExprId,
    ) anyerror!?*const ConversionPlan {
        return try self.planDefToTarget(def_expr, item_expr, .lhs);
    }

    pub fn planDefToTarget(
        self: *Context,
        def_expr: ExprId,
        target_expr: ExprId,
        side: enum { lhs, rhs },
    ) anyerror!?*const ConversionPlan {
        const witness = try self.instantiateDefTowardExpr(def_expr, target_expr) orelse {
            return null;
        };
        const next = try self.compareTransparent(witness, target_expr) orelse {
            return null;
        };
        return switch (side) {
            .lhs => try self.allocPlan(.{ .unfold_lhs = .{
                .witness = witness,
                .next = next,
            } }),
            .rhs => try self.allocPlan(.{ .unfold_rhs = .{
                .witness = witness,
                .next = next,
            } }),
        };
    }

    pub fn compareTransparent(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?*const ConversionPlan {
        if (lhs == rhs) {
            return try self.allocPlan(.refl);
        }

        const lhs_node = self.theorem.interner.node(lhs);
        const rhs_node = self.theorem.interner.node(rhs);
        if (lhs_node.* == .app and rhs_node.* == .app) {
            const lhs_app = lhs_node.app;
            const rhs_app = rhs_node.app;
            if (lhs_app.term_id == rhs_app.term_id and
                lhs_app.args.len == rhs_app.args.len)
            {
                const children = try self.allocator.alloc(
                    *const ConversionPlan,
                    lhs_app.args.len,
                );
                for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
                    children[idx] = try self.compareTransparent(
                        lhs_arg,
                        rhs_arg,
                    ) orelse {
                        return null;
                    };
                }
                return try self.allocPlan(.{ .cong = .{ .children = children } });
            }
        }

        if (try self.planDefToTarget(lhs, rhs, .lhs)) |plan| {
            return plan;
        }
        if (try self.planDefToTarget(rhs, lhs, .rhs)) |plan| {
            return plan;
        }
        return null;
    }

    pub fn matchTemplateTransparent(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        return try self.matchTemplateRec(template, actual, bindings);
    }

    // Compatibility wrappers for current callers while the rest of the
    // frontend is migrated to the new names.
    pub fn exprMatchesByDefOpening(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!bool {
        return (try self.compareTransparent(lhs, rhs)) != null;
    }

    pub fn matchTemplateWithDefOpening(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        return try self.matchTemplateTransparent(template, actual, bindings);
    }

    pub fn planConversionByDefOpening(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?*const ConversionPlan {
        return try self.compareTransparent(lhs, rhs);
    }

    fn instantiateDefTowardExpr(
        self: *Context,
        def_expr: ExprId,
        target_expr: ExprId,
    ) anyerror!?ExprId {
        const def = self.getConcreteDef(def_expr) orelse return null;
        const symbolic = try self.expandConcreteDef(def_expr) orelse return null;

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.allocator);

        if (!try self.matchSymbolicToExpr(
            symbolic,
            target_expr,
            &[_]?ExprId{},
            &dummy_bindings,
        )) {
            return null;
        }
        if (dummy_bindings.items.len != def.term.dummy_args.len) return null;

        const binders = try self.allocator.alloc(
            ExprId,
            def.term.args.len + def.term.dummy_args.len,
        );
        @memcpy(binders[0..def.term.args.len], def.app.args);
        for (def.term.dummy_args, 0..) |_, idx| {
            const actual = findDummyBinding(dummy_bindings.items, idx) orelse {
                return null;
            };
            binders[def.term.args.len + idx] = actual;
        }
        return try self.theorem.instantiateTemplate(def.body, binders);
    }

    fn matchTemplateRec(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= bindings.len) break :blk false;
                if (bindings[idx]) |existing| {
                    break :blk (try self.compareTransparent(
                        existing,
                        actual,
                    )) != null;
                }
                bindings[idx] = actual;
                break :blk true;
            },
            .app => |app| blk: {
                if (try self.matchTemplateAppDirect(app, actual, bindings)) {
                    break :blk true;
                }

                if (try self.matchExpandedTemplateApp(app, actual, bindings)) {
                    break :blk true;
                }

                if (try self.matchActualDefToTemplate(template, actual, bindings)) {
                    break :blk true;
                }

                break :blk false;
            },
        };
    }

    fn matchTemplateAppDirect(
        self: *Context,
        app: TemplateExpr.App,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        const actual_node = self.theorem.interner.node(actual);
        const actual_app = switch (actual_node.*) {
            .app => |value| value,
            .variable => return false,
        };
        if (actual_app.term_id != app.term_id or
            actual_app.args.len != app.args.len)
        {
            return false;
        }

        const saved_bindings = try self.allocator.dupe(?ExprId, bindings);
        defer self.allocator.free(saved_bindings);
        for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
            if (!try self.matchTemplateRec(tmpl_arg, actual_arg, bindings)) {
                @memcpy(bindings, saved_bindings);
                return false;
            }
        }
        return true;
    }

    fn matchExpandedTemplateApp(
        self: *Context,
        app: TemplateExpr.App,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        const saved_bindings = try self.allocator.dupe(?ExprId, bindings);
        defer self.allocator.free(saved_bindings);

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.allocator);
        const checkpoint = self.symbolic_dummy_infos.items.len;
        defer self.symbolic_dummy_infos.shrinkRetainingCapacity(checkpoint);

        const symbolic = try self.expandTemplateApp(app) orelse return false;
        if (try self.matchSymbolicToExpr(
            symbolic,
            actual,
            bindings,
            &dummy_bindings,
        )) {
            return true;
        }

        @memcpy(bindings, saved_bindings);
        return false;
    }

    fn matchActualDefToTemplate(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        _ = self.getConcreteDef(actual) orelse return false;

        const saved_bindings = try self.allocator.dupe(?ExprId, bindings);
        defer self.allocator.free(saved_bindings);

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.allocator);
        const checkpoint = self.symbolic_dummy_infos.items.len;
        defer self.symbolic_dummy_infos.shrinkRetainingCapacity(checkpoint);

        const symbolic = try self.symbolicFromTemplate(template);
        if (try self.matchSymbolicToExpr(
            symbolic,
            actual,
            bindings,
            &dummy_bindings,
        )) {
            return true;
        }

        @memcpy(bindings, saved_bindings);
        return false;
    }

    fn matchSymbolicToExpr(
        self: *Context,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        bindings: []?ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) anyerror!bool {
        switch (symbolic.*) {
            .binder => |idx| {
                if (idx >= bindings.len) return false;
                if (bindings[idx]) |existing| {
                    return (try self.compareTransparent(existing, actual)) != null;
                }
                bindings[idx] = actual;
                return true;
            },
            .fixed => |expr_id| {
                return (try self.compareTransparent(expr_id, actual)) != null;
            },
            .dummy => |slot| {
                const info = self.symbolic_dummy_infos.items[slot];
                return try self.matchSymbolicDummy(
                    slot,
                    info,
                    actual,
                    dummy_bindings,
                );
            },
            .app => |app| {
                const saved_bindings = try self.allocator.dupe(
                    ?ExprId,
                    bindings,
                );
                defer self.allocator.free(saved_bindings);
                const dummy_checkpoint = dummy_bindings.items.len;

                const actual_node = self.theorem.interner.node(actual);
                if (actual_node.* == .app) {
                    const actual_app = actual_node.app;
                    if (actual_app.term_id == app.term_id and
                        actual_app.args.len == app.args.len)
                    {
                        for (app.args, actual_app.args) |sym_arg, actual_arg| {
                            if (!try self.matchSymbolicToExpr(
                                sym_arg,
                                actual_arg,
                                bindings,
                                dummy_bindings,
                            )) {
                                @memcpy(bindings, saved_bindings);
                                dummy_bindings.shrinkRetainingCapacity(
                                    dummy_checkpoint,
                                );
                                break;
                            }
                        } else {
                            return true;
                        }
                    }
                }

                @memcpy(bindings, saved_bindings);
                dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);

                if (try self.expandSymbolicApp(app)) |expanded| {
                    if (try self.matchSymbolicToExpr(
                        expanded,
                        actual,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }

                if (try self.expandConcreteDef(actual)) |expanded_actual| {
                    if (try self.matchSymbolicToSymbolic(
                        symbolic,
                        expanded_actual,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }
                return false;
            },
        }
    }

    fn matchSymbolicToSymbolic(
        self: *Context,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        bindings: []?ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) anyerror!bool {
        switch (lhs.*) {
            .binder => |idx| {
                if (idx >= bindings.len) return false;
                const rhs_expr = try self.materializeSymbolic(
                    rhs,
                    dummy_bindings.items,
                ) orelse return false;
                if (bindings[idx]) |existing| {
                    return (try self.compareTransparent(existing, rhs_expr)) != null;
                }
                bindings[idx] = rhs_expr;
                return true;
            },
            .fixed => |expr_id| {
                const rhs_expr = try self.materializeSymbolic(
                    rhs,
                    dummy_bindings.items,
                ) orelse return false;
                return (try self.compareTransparent(expr_id, rhs_expr)) != null;
            },
            .dummy => |slot| {
                const rhs_expr = try self.materializeSymbolic(
                    rhs,
                    dummy_bindings.items,
                ) orelse return false;
                const info = self.symbolic_dummy_infos.items[slot];
                return try self.matchSymbolicDummy(
                    slot,
                    info,
                    rhs_expr,
                    dummy_bindings,
                );
            },
            .app => |lhs_app| {
                const saved_bindings = try self.allocator.dupe(
                    ?ExprId,
                    bindings,
                );
                defer self.allocator.free(saved_bindings);
                const dummy_checkpoint = dummy_bindings.items.len;

                if (rhs.* == .app) {
                    const rhs_app = rhs.app;
                    if (lhs_app.term_id == rhs_app.term_id and
                        lhs_app.args.len == rhs_app.args.len)
                    {
                        for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                            if (!try self.matchSymbolicToSymbolic(
                                lhs_arg,
                                rhs_arg,
                                bindings,
                                dummy_bindings,
                            )) {
                                @memcpy(bindings, saved_bindings);
                                dummy_bindings.shrinkRetainingCapacity(
                                    dummy_checkpoint,
                                );
                                break;
                            }
                        } else {
                            return true;
                        }
                    }
                }

                @memcpy(bindings, saved_bindings);
                dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);

                if (try self.expandSymbolicApp(lhs_app)) |expanded_lhs| {
                    if (try self.matchSymbolicToSymbolic(
                        expanded_lhs,
                        rhs,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }
                if (rhs.* == .app) {
                    if (try self.expandSymbolicApp(rhs.app)) |expanded_rhs| {
                        if (try self.matchSymbolicToSymbolic(
                            lhs,
                            expanded_rhs,
                            bindings,
                            dummy_bindings,
                        )) {
                            return true;
                        }
                        @memcpy(bindings, saved_bindings);
                        dummy_bindings.shrinkRetainingCapacity(
                            dummy_checkpoint,
                        );
                    }
                }
                return false;
            },
        }
    }

    fn matchSymbolicDummy(
        self: *Context,
        slot: usize,
        info: SymbolicDummyInfo,
        actual: ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) anyerror!bool {
        const actual_info = try self.getConcreteVarInfo(actual);
        if (!actual_info.bound) return false;
        if (!std.mem.eql(u8, info.sort_name, actual_info.sort_name)) {
            return false;
        }

        for (dummy_bindings.items) |binding| {
            if (binding.slot == slot) return binding.actual == actual;
        }
        try dummy_bindings.append(self.allocator, .{
            .slot = slot,
            .actual = actual,
        });
        return true;
    }

    fn materializeSymbolic(
        self: *Context,
        symbolic: *const SymbolicExpr,
        dummy_bindings: []const DummyBinding,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => null,
            .fixed => |expr_id| expr_id,
            .dummy => |slot| findDummyBinding(dummy_bindings, slot),
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeSymbolic(
                        arg,
                        dummy_bindings,
                    ) orelse break :blk null;
                }
                break :blk try self.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn getConcreteVarInfo(self: *Context, expr_id: ExprId) !ConcreteVarInfo {
        const node = self.theorem.interner.node(expr_id);
        const var_id = switch (node.*) {
            .variable => |value| value,
            .app => return error.ExpectedVariable,
        };
        return switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= self.theorem.arg_infos.len) {
                    return error.UnknownTheoremVariable;
                }
                const arg = self.theorem.arg_infos[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= self.theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = self.theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                };
            },
        };
    }

    fn expandTemplateApp(
        self: *Context,
        app: TemplateExpr.App,
    ) anyerror!?*const SymbolicExpr {
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const subst = try self.allocator.alloc(
            *const SymbolicExpr,
            term.args.len + term.dummy_args.len,
        );
        for (app.args, 0..) |arg, idx| {
            subst[idx] = try self.symbolicFromTemplate(arg);
        }
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = self.symbolic_dummy_infos.items.len;
            try self.symbolic_dummy_infos.append(self.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[term.args.len + idx] = try self.allocSymbolic(
                .{ .dummy = slot },
            );
        }
        return try self.symbolicFromTemplateSubst(body, subst);
    }

    fn expandConcreteDef(
        self: *Context,
        expr_id: ExprId,
    ) anyerror!?*const SymbolicExpr {
        const def = self.getConcreteDef(expr_id) orelse return null;

        const subst = try self.allocator.alloc(
            *const SymbolicExpr,
            def.term.args.len + def.term.dummy_args.len,
        );
        for (def.app.args, 0..) |arg, idx| {
            subst[idx] = try self.allocSymbolic(.{ .fixed = arg });
        }
        for (def.term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = self.symbolic_dummy_infos.items.len;
            try self.symbolic_dummy_infos.append(self.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[def.term.args.len + idx] = try self.allocSymbolic(
                .{ .dummy = slot },
            );
        }
        return try self.symbolicFromTemplateSubst(def.body, subst);
    }

    fn expandSymbolicApp(
        self: *Context,
        app: SymbolicExpr.App,
    ) anyerror!?*const SymbolicExpr {
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const subst = try self.allocator.alloc(
            *const SymbolicExpr,
            term.args.len + term.dummy_args.len,
        );
        @memcpy(subst[0..term.args.len], app.args);
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = self.symbolic_dummy_infos.items.len;
            try self.symbolic_dummy_infos.append(self.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[term.args.len + idx] = try self.allocSymbolic(
                .{ .dummy = slot },
            );
        }
        return try self.symbolicFromTemplateSubst(body, subst);
    }

    fn symbolicFromTemplate(
        self: *Context,
        template: TemplateExpr,
    ) anyerror!*const SymbolicExpr {
        return try self.symbolicFromTemplateSubst(template, null);
    }

    fn symbolicFromTemplateSubst(
        self: *Context,
        template: TemplateExpr,
        subst: ?[]const *const SymbolicExpr,
    ) anyerror!*const SymbolicExpr {
        switch (template) {
            .binder => |idx| {
                if (subst) |args| {
                    if (idx >= args.len) return error.TemplateBinderOutOfRange;
                    return args[idx];
                }
                return try self.allocSymbolic(.{ .binder = idx });
            },
            .app => |app| {
                const args = try self.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.symbolicFromTemplateSubst(arg, subst);
                }
                return try self.allocSymbolic(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        }
    }

    fn getConcreteDef(self: *const Context, expr_id: ExprId) ?struct {
        app: ExprApp,
        term: *const TermDecl,
        body: TemplateExpr,
    } {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return null,
        };
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;
        return .{
            .app = app,
            .term = term,
            .body = body,
        };
    }

    fn getOpenableTerm(self: *const Context, term_id: u32) ?*const TermDecl {
        if (term_id >= self.env.terms.items.len) return null;
        const term = &self.env.terms.items[term_id];
        if (!term.is_def or term.body == null) return null;
        return term;
    }

    fn allocSymbolic(
        self: *Context,
        symbolic: SymbolicExpr,
    ) anyerror!*const SymbolicExpr {
        const node = try self.allocator.create(SymbolicExpr);
        node.* = symbolic;
        return node;
    }

    fn allocPlan(
        self: *Context,
        plan: ConversionPlan,
    ) anyerror!*const ConversionPlan {
        const node = try self.allocator.create(ConversionPlan);
        node.* = plan;
        return node;
    }
};

fn findDummyBinding(bindings: []const DummyBinding, slot: usize) ?ExprId {
    for (bindings) |binding| {
        if (binding.slot == slot) return binding.actual;
    }
    return null;
}
