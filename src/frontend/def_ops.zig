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

const BoundValue = union(enum) {
    concrete: ExprId,
    symbolic: *const SymbolicExpr,
};

const WitnessMap = std.AutoHashMapUnmanaged(usize, ExprId);

const MatchSession = struct {
    bindings: []?BoundValue,
    witnesses: WitnessMap = .{},
    symbolic_dummy_infos: std.ArrayListUnmanaged(SymbolicDummyInfo) = .{},
    provisional_witness_infos: std.AutoHashMapUnmanaged(
        ExprId,
        SymbolicDummyInfo,
    ) = .empty,

    fn init(
        allocator: std.mem.Allocator,
        binding_len: usize,
    ) !MatchSession {
        return .{
            .bindings = try allocator.alloc(?BoundValue, binding_len),
        };
    }

    fn deinit(
        self: *MatchSession,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.bindings);
        self.witnesses.deinit(allocator);
        self.symbolic_dummy_infos.deinit(allocator);
        self.provisional_witness_infos.deinit(allocator);
    }
};

const MatchSnapshot = struct {
    bindings: []?BoundValue,
    witnesses: WitnessMap,
    dummy_info_len: usize,
};

const ConcreteVarInfo = struct {
    sort_name: []const u8,
    bound: bool,
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,

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
        _ = self;
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

    pub fn instantiateDefTowardAcuiItem(
        self: *Context,
        def_expr: ExprId,
        item_expr: ExprId,
        head_term_id: u32,
    ) anyerror!?ExprId {
        const def = self.getConcreteDef(def_expr) orelse return null;
        var session = try MatchSession.init(self.allocator, 0);
        defer session.deinit(self.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.allocator);

        if (!try self.matchSymbolicAcuiLeafToExpr(
            symbolic,
            item_expr,
            head_term_id,
            &session,
            &dummy_bindings,
        )) {
            return null;
        }
        if (dummy_bindings.items.len != def.term.dummy_args.len) return null;
        return try self.materializeSymbolic(
            symbolic,
            &session,
            dummy_bindings.items,
        );
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
        var state = try MatchSession.init(self.allocator, bindings.len);
        defer state.deinit(self.allocator);

        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(self.allocator);
        for (bindings, 0..) |binding, idx| {
            state.bindings[idx] = if (binding) |expr_id|
                try self.rebuildBoundValue(
                    expr_id,
                    &state,
                    &witness_slots,
                )
            else
                null;
        }

        if (!try self.matchTemplateRecState(template, actual, &state)) {
            return false;
        }
        try self.finalizeBindings(&state, bindings);
        return true;
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
        var session = try MatchSession.init(self.allocator, 0);
        defer session.deinit(self.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.allocator);

        if (!try self.matchSymbolicToExpr(
            symbolic,
            target_expr,
            &session,
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

    fn matchTemplateRecState(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk false;
                if (state.bindings[idx]) |existing| {
                    break :blk try self.boundValueMatchesExpr(
                        existing,
                        actual,
                        state,
                    );
                }
                state.bindings[idx] = .{ .concrete = actual };
                break :blk true;
            },
            .app => |app| blk: {
                if (try self.matchTemplateAppDirectState(app, actual, state)) {
                    break :blk true;
                }

                if (try self.matchExpandedTemplateAppState(app, actual, state)) {
                    break :blk true;
                }

                if (try self.matchActualDefToTemplateState(
                    template,
                    actual,
                    state,
                )) {
                    break :blk true;
                }

                break :blk false;
            },
        };
    }

    fn matchTemplateAppDirectState(
        self: *Context,
        app: TemplateExpr.App,
        actual: ExprId,
        state: *MatchSession,
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

        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
            if (!try self.matchTemplateRecState(tmpl_arg, actual_arg, state)) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
        }
        return true;
    }

    fn matchExpandedTemplateAppState(
        self: *Context,
        app: TemplateExpr.App,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        const symbolic = try self.expandTemplateApp(app, state) orelse return false;
        if (try self.matchSymbolicToExprState(symbolic, actual, state)) {
            return true;
        }

        try self.restoreMatchSnapshot(&snapshot, state);
        return false;
    }

    fn matchActualDefToTemplateState(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        _ = self.getConcreteDef(actual) orelse return false;

        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        const symbolic_template = try self.symbolicFromTemplate(template);
        const symbolic_actual = try self.expandConcreteDef(actual, state) orelse {
            return false;
        };
        if (try self.matchSymbolicToSymbolicState(
            symbolic_template,
            symbolic_actual,
            state,
        )) {
            return true;
        }

        try self.restoreMatchSnapshot(&snapshot, state);
        return false;
    }

    fn matchSymbolicToExprState(
        self: *Context,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk false;
                if (state.bindings[idx]) |existing| {
                    break :blk try self.boundValueMatchesExpr(
                        existing,
                        actual,
                        state,
                    );
                }
                state.bindings[idx] = .{ .concrete = actual };
                break :blk true;
            },
            .fixed => |expr_id| {
                return (try self.compareTransparent(expr_id, actual)) != null;
            },
            .dummy => |slot| {
                const info = state.symbolic_dummy_infos.items[slot];
                return try self.matchSymbolicDummyState(
                    slot,
                    info,
                    actual,
                    state,
                );
            },
            .app => |app| {
                var snapshot = try self.saveMatchSnapshot(state);
                defer self.deinitMatchSnapshot(&snapshot);

                const actual_node = self.theorem.interner.node(actual);
                if (actual_node.* == .app) {
                    const actual_app = actual_node.app;
                    if (actual_app.term_id == app.term_id and
                        actual_app.args.len == app.args.len)
                    {
                        for (app.args, actual_app.args) |sym_arg, actual_arg| {
                            if (!try self.matchSymbolicToExprState(
                                sym_arg,
                                actual_arg,
                                state,
                            )) {
                                try self.restoreMatchSnapshot(
                                    &snapshot,
                                    state,
                                );
                                break;
                            }
                        } else {
                            return true;
                        }
                    }
                }

                try self.restoreMatchSnapshot(&snapshot, state);

                if (try self.expandSymbolicApp(app, state)) |expanded| {
                    if (try self.matchSymbolicToExprState(
                        expanded,
                        actual,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                }

                if (try self.expandConcreteDef(actual, state)) |expanded_actual| {
                    if (try self.matchSymbolicToSymbolicState(
                        symbolic,
                        expanded_actual,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                }
                return false;
            },
        };
    }

    fn matchExprToSymbolic(
        self: *Context,
        actual: ExprId,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk false;
                if (state.bindings[idx]) |existing| {
                    break :blk try self.boundValueMatchesExpr(
                        existing,
                        actual,
                        state,
                    );
                }
                state.bindings[idx] = .{ .concrete = actual };
                break :blk true;
            },
            .fixed => |expr_id| {
                return (try self.compareTransparent(actual, expr_id)) != null;
            },
            .dummy => |slot| {
                const info = state.symbolic_dummy_infos.items[slot];
                return try self.matchSymbolicDummyState(
                    slot,
                    info,
                    actual,
                    state,
                );
            },
            .app => |app| {
                var snapshot = try self.saveMatchSnapshot(state);
                defer self.deinitMatchSnapshot(&snapshot);

                const actual_node = self.theorem.interner.node(actual);
                if (actual_node.* == .app) {
                    const actual_app = actual_node.app;
                    if (actual_app.term_id == app.term_id and
                        actual_app.args.len == app.args.len)
                    {
                        for (actual_app.args, app.args) |actual_arg, sym_arg| {
                            if (!try self.matchExprToSymbolic(
                                actual_arg,
                                sym_arg,
                                state,
                            )) {
                                try self.restoreMatchSnapshot(
                                    &snapshot,
                                    state,
                                );
                                break;
                            }
                        } else {
                            return true;
                        }
                    }
                }

                try self.restoreMatchSnapshot(&snapshot, state);

                if (try self.expandConcreteDef(actual, state)) |expanded_actual| {
                    if (try self.matchSymbolicToSymbolicState(
                        expanded_actual,
                        symbolic,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                }

                if (try self.expandSymbolicApp(app, state)) |expanded| {
                    if (try self.matchExprToSymbolic(
                        actual,
                        expanded,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                }
                return false;
            },
        };
    }

    fn matchSymbolicToSymbolicState(
        self: *Context,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (lhs.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk false;
                if (state.bindings[idx]) |existing| {
                    break :blk try self.boundValueMatchesSymbolic(
                        existing,
                        rhs,
                        state,
                    );
                }
                state.bindings[idx] = .{ .symbolic = rhs };
                break :blk true;
            },
            .fixed => |expr_id| {
                return try self.matchExprToSymbolic(expr_id, rhs, state);
            },
            .dummy => |slot| {
                return try self.matchDummyToSymbolic(slot, rhs, state);
            },
            .app => |lhs_app| {
                var snapshot = try self.saveMatchSnapshot(state);
                defer self.deinitMatchSnapshot(&snapshot);

                if (rhs.* == .app) {
                    const rhs_app = rhs.app;
                    if (lhs_app.term_id == rhs_app.term_id and
                        lhs_app.args.len == rhs_app.args.len)
                    {
                        for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                            if (!try self.matchSymbolicToSymbolicState(
                                lhs_arg,
                                rhs_arg,
                                state,
                            )) {
                                try self.restoreMatchSnapshot(
                                    &snapshot,
                                    state,
                                );
                                break;
                            }
                        } else {
                            return true;
                        }
                    }
                }

                try self.restoreMatchSnapshot(&snapshot, state);

                if (try self.expandSymbolicApp(lhs_app, state)) |expanded_lhs| {
                    if (try self.matchSymbolicToSymbolicState(
                        expanded_lhs,
                        rhs,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                }
                if (rhs.* == .app) {
                    if (try self.expandSymbolicApp(rhs.app, state)) |expanded_rhs| {
                        if (try self.matchSymbolicToSymbolicState(
                            lhs,
                            expanded_rhs,
                            state,
                        )) {
                            return true;
                        }
                        try self.restoreMatchSnapshot(
                            &snapshot,
                            state,
                        );
                    }
                }
                return false;
            },
        };
    }

    fn matchSymbolicToExpr(
        self: *Context,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
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
                const info = state.symbolic_dummy_infos.items[slot];
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
                                state,
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

                if (try self.expandSymbolicApp(app, state)) |expanded| {
                    if (try self.matchSymbolicToExpr(
                        expanded,
                        actual,
                        state,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }

                if (try self.expandConcreteDef(actual, state)) |expanded_actual| {
                    if (try self.matchSymbolicToSymbolic(
                        symbolic,
                        expanded_actual,
                        state,
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
        state: *MatchSession,
        bindings: []?ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) anyerror!bool {
        switch (lhs.*) {
            .binder => |idx| {
                if (idx >= bindings.len) return false;
                const rhs_expr = try self.materializeSymbolic(
                    rhs,
                    state,
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
                    state,
                    dummy_bindings.items,
                ) orelse return false;
                return (try self.compareTransparent(expr_id, rhs_expr)) != null;
            },
            .dummy => |slot| {
                const rhs_expr = try self.materializeSymbolic(
                    rhs,
                    state,
                    dummy_bindings.items,
                ) orelse return false;
                const info = state.symbolic_dummy_infos.items[slot];
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
                                state,
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

                if (try self.expandSymbolicApp(lhs_app, state)) |expanded_lhs| {
                    if (try self.matchSymbolicToSymbolic(
                        expanded_lhs,
                        rhs,
                        state,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }
                if (rhs.* == .app) {
                    if (try self.expandSymbolicApp(rhs.app, state)) |expanded_rhs| {
                        if (try self.matchSymbolicToSymbolic(
                            lhs,
                            expanded_rhs,
                            state,
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

    fn matchSymbolicAcuiLeafToExpr(
        self: *Context,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        head_term_id: u32,
        state: *MatchSession,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) anyerror!bool {
        switch (symbolic.*) {
            .app => |app| {
                if (app.term_id == head_term_id and app.args.len == 2) {
                    const checkpoint = dummy_bindings.items.len;
                    if (try self.matchSymbolicAcuiLeafToExpr(
                        app.args[0],
                        actual,
                        head_term_id,
                        state,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    dummy_bindings.shrinkRetainingCapacity(checkpoint);
                    if (try self.matchSymbolicAcuiLeafToExpr(
                        app.args[1],
                        actual,
                        head_term_id,
                        state,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    dummy_bindings.shrinkRetainingCapacity(checkpoint);
                    return false;
                }
            },
            else => {},
        }

        const checkpoint = dummy_bindings.items.len;
        if (try self.matchSymbolicToExpr(
            symbolic,
            actual,
            state,
            &[_]?ExprId{},
            dummy_bindings,
        )) {
            return true;
        }
        dummy_bindings.shrinkRetainingCapacity(checkpoint);
        return false;
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
        state: *MatchSession,
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
                        state,
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

    fn rebuildBoundValue(
        self: *Context,
        expr_id: ExprId,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    ) anyerror!BoundValue {
        if (try self.resymbolizeBinding(expr_id, state, witness_slots)) |symbolic| {
            return .{ .symbolic = symbolic };
        }
        return .{ .concrete = expr_id };
    }

    fn resymbolizeBinding(
        self: *Context,
        expr_id: ExprId,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    ) anyerror!?*const SymbolicExpr {
        if (try self.getResymbolizableWitnessInfo(expr_id)) |info| {
            const slot = try self.slotForWitness(
                expr_id,
                info,
                state,
                witness_slots,
            );
            return try self.allocSymbolic(.{ .dummy = slot });
        }

        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .variable => null,
            .app => |app| blk: {
                var has_symbolic = false;
                const args = try self.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg_expr, idx| {
                    if (try self.resymbolizeBinding(
                        arg_expr,
                        state,
                        witness_slots,
                    )) |symbolic_arg| {
                        args[idx] = symbolic_arg;
                        has_symbolic = true;
                    } else {
                        args[idx] = try self.allocSymbolic(.{ .fixed = arg_expr });
                    }
                }
                if (!has_symbolic) {
                    self.allocator.free(args);
                    break :blk null;
                }
                break :blk try self.allocSymbolic(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        };
    }

    fn slotForWitness(
        self: *Context,
        witness: ExprId,
        info: SymbolicDummyInfo,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    ) anyerror!usize {
        if (witness_slots.get(witness)) |slot| return slot;

        const slot = state.symbolic_dummy_infos.items.len;
        try state.symbolic_dummy_infos.append(self.allocator, info);
        try witness_slots.put(self.allocator, witness, slot);
        try state.witnesses.put(self.allocator, slot, witness);
        try state.provisional_witness_infos.put(
            self.allocator,
            witness,
            info,
        );
        return slot;
    }

    fn saveMatchSnapshot(
        self: *Context,
        state: *const MatchSession,
    ) anyerror!MatchSnapshot {
        return .{
            .bindings = try self.allocator.dupe(?BoundValue, state.bindings),
            .witnesses = try self.cloneWitnessMap(state.witnesses),
            .dummy_info_len = state.symbolic_dummy_infos.items.len,
        };
    }

    fn restoreMatchSnapshot(
        self: *Context,
        snapshot: *const MatchSnapshot,
        state: *MatchSession,
    ) anyerror!void {
        @memcpy(state.bindings, snapshot.bindings);
        state.witnesses.deinit(self.allocator);
        state.witnesses = try self.cloneWitnessMap(snapshot.witnesses);
        state.symbolic_dummy_infos.shrinkRetainingCapacity(
            snapshot.dummy_info_len,
        );
    }

    fn deinitMatchSnapshot(
        self: *Context,
        snapshot: *MatchSnapshot,
    ) void {
        self.allocator.free(snapshot.bindings);
        snapshot.witnesses.deinit(self.allocator);
    }

    fn cloneWitnessMap(self: *Context, map: WitnessMap) anyerror!WitnessMap {
        var clone: WitnessMap = .{};
        var it = map.iterator();
        while (it.next()) |entry| {
            try clone.put(
                self.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return clone;
    }

    fn boundValueMatchesExpr(
        self: *Context,
        bound: BoundValue,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (bound) {
            .concrete => |expr_id| {
                return (try self.compareTransparent(expr_id, actual)) != null;
            },
            .symbolic => |symbolic| {
                return try self.matchSymbolicToExprState(
                    symbolic,
                    actual,
                    state,
                );
            },
        };
    }

    fn boundValueMatchesSymbolic(
        self: *Context,
        bound: BoundValue,
        actual: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (bound) {
            .concrete => |expr_id| {
                return try self.matchExprToSymbolic(expr_id, actual, state);
            },
            .symbolic => |symbolic| {
                return try self.matchSymbolicToSymbolicState(
                    symbolic,
                    actual,
                    state,
                );
            },
        };
    }

    fn matchSymbolicDummyState(
        self: *Context,
        slot: usize,
        info: SymbolicDummyInfo,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        const actual_info = try self.getConcreteVarInfo(actual);
        if (!actual_info.bound) return false;
        if (!std.mem.eql(u8, info.sort_name, actual_info.sort_name)) {
            return false;
        }

        if (state.witnesses.get(slot)) |existing| {
            if (existing == actual) return true;
            if (state.provisional_witness_infos.contains(existing)) {
                try state.witnesses.put(self.allocator, slot, actual);
                return true;
            }
            return false;
        }
        try state.witnesses.put(self.allocator, slot, actual);
        return true;
    }

    fn matchDummyToSymbolic(
        self: *Context,
        slot: usize,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (rhs.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk false;
                const symbolic = try self.allocSymbolic(.{ .dummy = slot });
                if (state.bindings[idx]) |existing| {
                    break :blk try self.boundValueMatchesSymbolic(
                        existing,
                        symbolic,
                        state,
                    );
                }
                state.bindings[idx] = .{ .symbolic = symbolic };
                break :blk true;
            },
            .fixed => |expr_id| {
                const info = state.symbolic_dummy_infos.items[slot];
                return try self.matchSymbolicDummyState(
                    slot,
                    info,
                    expr_id,
                    state,
                );
            },
            .dummy => |rhs_slot| {
                const lhs_info = state.symbolic_dummy_infos.items[slot];
                const rhs_info = state.symbolic_dummy_infos.items[rhs_slot];
                if (!std.mem.eql(u8, lhs_info.sort_name, rhs_info.sort_name)) {
                    return false;
                }
                if (slot == rhs_slot) return true;
                if (state.witnesses.get(slot)) |lhs_witness| {
                    if (state.witnesses.get(rhs_slot)) |rhs_witness| {
                        return lhs_witness == rhs_witness;
                    }
                    try state.witnesses.put(
                        self.allocator,
                        rhs_slot,
                        lhs_witness,
                    );
                    return true;
                }
                if (state.witnesses.get(rhs_slot)) |rhs_witness| {
                    try state.witnesses.put(
                        self.allocator,
                        slot,
                        rhs_witness,
                    );
                    return true;
                }
                return false;
            },
            .app => {
                const rhs_expr = try self.materializeAssignedSymbolic(
                    rhs,
                    state,
                ) orelse return false;
                const info = state.symbolic_dummy_infos.items[slot];
                return try self.matchSymbolicDummyState(
                    slot,
                    info,
                    rhs_expr,
                    state,
                );
            },
        };
    }

    fn finalizeBindings(
        self: *Context,
        state: *MatchSession,
        bindings: []?ExprId,
    ) anyerror!void {
        for (state.bindings, 0..) |binding, idx| {
            bindings[idx] = if (binding) |value|
                try self.finalizeBoundValue(value, state)
            else
                null;
        }
    }

    fn finalizeBoundValue(
        self: *Context,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!ExprId {
        return switch (bound) {
            .concrete => |expr_id| expr_id,
            .symbolic => |symbolic| {
                return try self.materializeTemplateSymbolic(symbolic, state);
            },
        };
    }

    fn materializeAssignedBoundValue(
        self: *Context,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (bound) {
            .concrete => |expr_id| expr_id,
            .symbolic => |symbolic| {
                return try self.materializeAssignedSymbolic(symbolic, state);
            },
        };
    }

    fn materializeAssignedSymbolic(
        self: *Context,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk null;
                const bound = state.bindings[idx] orelse break :blk null;
                break :blk try self.materializeAssignedBoundValue(bound, state);
            },
            .fixed => |expr_id| expr_id,
            .dummy => |slot| state.witnesses.get(slot),
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeAssignedSymbolic(
                        arg,
                        state,
                    ) orelse break :blk null;
                }
                break :blk try self.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn materializeTemplateSymbolic(
        self: *Context,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!ExprId {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) {
                    return error.TemplateBinderOutOfRange;
                }
                const bound = state.bindings[idx] orelse {
                    return error.MissingBinderAssignment;
                };
                break :blk try self.finalizeBoundValue(bound, state);
            },
            .fixed => |expr_id| expr_id,
            .dummy => |slot| try self.witnessForDummySlot(slot, state),
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeTemplateSymbolic(
                        arg,
                        state,
                    );
                }
                break :blk try self.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn witnessForDummySlot(
        self: *Context,
        slot: usize,
        state: *MatchSession,
    ) anyerror!ExprId {
        if (state.witnesses.get(slot)) |existing| return existing;
        if (slot >= state.symbolic_dummy_infos.items.len) {
            return error.UnknownDummyVar;
        }
        const info = state.symbolic_dummy_infos.items[slot];
        const sort_id = self.env.sort_names.get(info.sort_name) orelse {
            return error.UnknownSort;
        };
        const witness = try self.theorem.addDummyVarResolved(
            info.sort_name,
            sort_id,
        );
        try state.witnesses.put(self.allocator, slot, witness);
        return witness;
    }

    fn getResymbolizableWitnessInfo(
        self: *Context,
        expr_id: ExprId,
    ) !?SymbolicDummyInfo {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => null,
            .variable => |var_id| switch (var_id) {
                .theorem_var => null,
                .dummy_var => |idx| blk: {
                    if (idx >= self.theorem.theorem_dummies.items.len) {
                        return error.UnknownDummyVar;
                    }
                    const dummy = self.theorem.theorem_dummies.items[idx];
                    break :blk .{ .sort_name = dummy.sort_name };
                },
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
        state: *MatchSession,
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
            const slot = state.symbolic_dummy_infos.items.len;
            try state.symbolic_dummy_infos.append(self.allocator, .{
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
        state: *MatchSession,
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
            const slot = state.symbolic_dummy_infos.items.len;
            try state.symbolic_dummy_infos.append(self.allocator, .{
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
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const subst = try self.allocator.alloc(
            *const SymbolicExpr,
            term.args.len + term.dummy_args.len,
        );
        @memcpy(subst[0..term.args.len], app.args);
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = state.symbolic_dummy_infos.items.len;
            try state.symbolic_dummy_infos.append(self.allocator, .{
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
