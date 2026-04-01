const std = @import("std");
const TermDecl = @import("../compiler_env.zig").TermDecl;
const ExprId = @import("../compiler_expr.zig").ExprId;
const ExprApp = @import("../compiler_expr.zig").ExprNode.App;
const TemplateExpr = @import("../compiler_rules.zig").TemplateExpr;
const Canonicalizer = @import("../canonicalizer.zig").Canonicalizer;
const Types = @import("./types.zig");
const MatchState = @import("./match_state.zig");
const SharedContext = @import("./shared_context.zig").SharedContext;

const ConversionPlan = Types.ConversionPlan;
const DummyBinding = struct {
    slot: usize,
    actual: ExprId,
};
const SymbolicDummyInfo = Types.SymbolicDummyInfo;
const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const BindingSeed = Types.BindingSeed;
const ConcreteBinding = Types.ConcreteBinding;
const BoundValue = Types.BoundValue;
const WitnessMap = Types.WitnessMap;
const WitnessSlotMap = Types.WitnessSlotMap;
const ProvisionalWitnessInfoMap = Types.ProvisionalWitnessInfoMap;
const MaterializedWitnessInfoMap = Types.MaterializedWitnessInfoMap;
const RepresentativeCache = Types.RepresentativeCache;
const MatchSession = MatchState.MatchSession;
const MatchSnapshot = MatchState.MatchSnapshot;
const ConcreteVarInfo = Types.ConcreteVarInfo;

pub const SymbolicEngine = struct {
    shared: *SharedContext,

    pub fn defCoversItem(
        self: *SymbolicEngine,
        def_expr: ExprId,
        item_expr: ExprId,
    ) anyerror!bool {
        return (try self.planDefCoversItem(def_expr, item_expr)) != null;
    }

    pub fn planDefCoversItem(
        self: *SymbolicEngine,
        def_expr: ExprId,
        item_expr: ExprId,
    ) anyerror!?*const ConversionPlan {
        return try self.planDefToTarget(def_expr, item_expr, .lhs);
    }

    pub fn instantiateDefTowardAcuiItem(
        self: *SymbolicEngine,
        def_expr: ExprId,
        item_expr: ExprId,
        head_term_id: u32,
    ) anyerror!?ExprId {
        const def = self.getConcreteDef(def_expr) orelse return null;
        var session = try MatchSession.init(self.shared.allocator, 0);
        defer session.deinit(self.shared.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.shared.allocator);

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
        self: *SymbolicEngine,
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
        self: *SymbolicEngine,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?*const ConversionPlan {
        if (lhs == rhs) {
            return try self.allocPlan(.refl);
        }

        const lhs_node = self.shared.theorem.interner.node(lhs);
        const rhs_node = self.shared.theorem.interner.node(rhs);
        if (lhs_node.* == .app and rhs_node.* == .app) {
            const lhs_app = lhs_node.app;
            const rhs_app = rhs_node.app;
            if (lhs_app.term_id == rhs_app.term_id and
                lhs_app.args.len == rhs_app.args.len)
            {
                const children = try self.shared.allocator.alloc(
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
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) anyerror!bool {
        var state = try MatchSession.init(self.shared.allocator, bindings.len);
        defer state.deinit(self.shared.allocator);

        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(self.shared.allocator);
        for (bindings, 0..) |binding, idx| {
            state.bindings[idx] = if (binding) |expr_id|
                try self.rebuildBoundValue(
                    expr_id,
                    &state,
                    &witness_slots,
                    .exact,
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

    fn instantiateDefTowardExpr(
        self: *SymbolicEngine,
        def_expr: ExprId,
        target_expr: ExprId,
    ) anyerror!?ExprId {
        const def = self.getConcreteDef(def_expr) orelse return null;
        var session = try MatchSession.init(self.shared.allocator, 0);
        defer session.deinit(self.shared.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.shared.allocator);

        if (!try self.matchSymbolicToExpr(
            symbolic,
            target_expr,
            &session,
            &[_]?ExprId{},
            &dummy_bindings,
            .transparent,
        )) {
            return null;
        }
        if (dummy_bindings.items.len != def.term.dummy_args.len) return null;

        const binders = try self.shared.allocator.alloc(
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
        return try self.shared.theorem.instantiateTemplate(def.body, binders);
    }

    pub fn matchTemplateRecState(
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (template) {
            .binder => |idx| blk: {
                break :blk try self.assignBinderFromExpr(
                    idx,
                    actual,
                    state,
                    .transparent,
                );
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
        self: *SymbolicEngine,
        app: TemplateExpr.App,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        const actual_node = self.shared.theorem.interner.node(actual);
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
        self: *SymbolicEngine,
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
        self: *SymbolicEngine,
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
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                break :blk try self.assignBinderFromExpr(
                    idx,
                    actual,
                    state,
                    .transparent,
                );
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

                const actual_node = self.shared.theorem.interner.node(actual);
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
        self: *SymbolicEngine,
        actual: ExprId,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        assign_mode: BindingMode,
    ) anyerror!bool {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                break :blk try self.assignBinderFromExpr(
                    idx,
                    actual,
                    state,
                    assign_mode,
                );
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

                const actual_node = self.shared.theorem.interner.node(actual);
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
                                assign_mode,
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
                        assign_mode,
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
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (lhs.*) {
            .binder => |idx| blk: {
                break :blk try self.assignBinderFromSymbolic(
                    idx,
                    rhs,
                    state,
                    .transparent,
                );
            },
            .fixed => |expr_id| {
                return try self.matchExprToSymbolic(
                    expr_id,
                    rhs,
                    state,
                    .transparent,
                );
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
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
        bindings: []?ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
        assign_mode: BindingMode,
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
                const saved_bindings = try self.shared.allocator.dupe(
                    ?ExprId,
                    bindings,
                );
                defer self.shared.allocator.free(saved_bindings);
                const dummy_checkpoint = dummy_bindings.items.len;

                const actual_node = self.shared.theorem.interner.node(actual);
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
                                assign_mode,
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
                        assign_mode,
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
        self: *SymbolicEngine,
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
                const saved_bindings = try self.shared.allocator.dupe(
                    ?ExprId,
                    bindings,
                );
                defer self.shared.allocator.free(saved_bindings);
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
        self: *SymbolicEngine,
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
            .transparent,
        )) {
            return true;
        }
        dummy_bindings.shrinkRetainingCapacity(checkpoint);
        return false;
    }

    fn matchSymbolicDummy(
        self: *SymbolicEngine,
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
        try dummy_bindings.append(self.shared.allocator, .{
            .slot = slot,
            .actual = actual,
        });
        return true;
    }

    fn materializeSymbolic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        dummy_bindings: []const DummyBinding,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => null,
            .fixed => |expr_id| expr_id,
            .dummy => |slot| findDummyBinding(dummy_bindings, slot),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(ExprId, app.args.len);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeSymbolic(
                        arg,
                        state,
                        dummy_bindings,
                    ) orelse break :blk null;
                }
                break :blk try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn rebuildBoundValue(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
        mode: BindingMode,
    ) anyerror!BoundValue {
        if (try self.resymbolizeBinding(expr_id, state, witness_slots)) |symbolic| {
            return self.makeSymbolicBoundValue(symbolic, mode);
        }
        return try self.makeConcreteBoundValue(expr_id, state, mode);
    }

    fn rebuildBoundValueFromState(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!BoundValue {
        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(self.shared.allocator);

        var it = state.witnesses.iterator();
        while (it.next()) |entry| {
            try witness_slots.put(
                self.shared.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }
        var materialized_it = state.materialized_witnesses.iterator();
        while (materialized_it.next()) |entry| {
            try witness_slots.put(
                self.shared.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }
        return try self.rebuildBoundValue(
            expr_id,
            state,
            &witness_slots,
            mode,
        );
    }

    pub fn makeConcreteBoundValue(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!BoundValue {
        return .{ .concrete = .{
            .raw = expr_id,
            .repr = try self.chooseRepresentativeSymbolic(
                expr_id,
                state,
                mode,
            ),
            .mode = mode,
        } };
    }

    pub fn makeSymbolicBoundValue(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        mode: BindingMode,
    ) BoundValue {
        _ = self;
        return .{ .symbolic = .{
            .expr = symbolic,
            .mode = mode,
        } };
    }

    fn assignBinderFromExpr(
        self: *SymbolicEngine,
        idx: usize,
        actual: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!bool {
        if (idx >= state.bindings.len) return false;
        if (state.bindings[idx]) |existing| {
            return try self.boundValueMatchesExpr(existing, actual, state);
        }
        state.bindings[idx] = try self.rebuildBoundValueFromState(
            actual,
            state,
            mode,
        );
        return true;
    }

    fn assignBinderFromSymbolic(
        self: *SymbolicEngine,
        idx: usize,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!bool {
        if (idx >= state.bindings.len) return false;
        if (state.bindings[idx]) |existing| {
            return try self.boundValueMatchesSymbolic(
                existing,
                symbolic,
                state,
            );
        }
        state.bindings[idx] = self.makeSymbolicBoundValue(symbolic, mode);
        return true;
    }

    pub fn assignBinderValue(
        self: *SymbolicEngine,
        idx: usize,
        value: BoundValue,
        state: *MatchSession,
    ) anyerror!bool {
        if (idx >= state.bindings.len) return false;
        if (state.bindings[idx]) |existing| {
            return switch (value) {
                .concrete => |concrete| blk: {
                    const actual = (try self.concreteBindingMatchExpr(
                        concrete,
                        state,
                    )) orelse break :blk false;
                    break :blk try self.boundValueMatchesExpr(
                        existing,
                        actual,
                        state,
                    );
                },
                .symbolic => |symbolic| try self.boundValueMatchesSymbolic(
                    existing,
                    symbolic.expr,
                    state,
                ),
            };
        }
        state.bindings[idx] = value;
        return true;
    }

    pub fn boundValueFromSeed(
        self: *SymbolicEngine,
        seed: BindingSeed,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    ) anyerror!?BoundValue {
        return switch (seed) {
            .none => null,
            .exact => |expr_id| try self.rebuildBoundValue(
                expr_id,
                state,
                witness_slots,
                .exact,
            ),
            .semantic => |semantic| try self.rebuildBoundValue(
                semantic.expr_id,
                state,
                witness_slots,
                semantic.mode,
            ),
        };
    }

    pub fn chooseRepresentative(
        self: *SymbolicEngine,
        expr_id: ExprId,
        mode: BindingMode,
    ) anyerror!ExprId {
        if (mode == .exact) return expr_id;

        var state = try MatchSession.init(self.shared.allocator, 0);
        defer state.deinit(self.shared.allocator);

        const symbolic = try self.chooseRepresentativeSymbolic(
            expr_id,
            &state,
            mode,
        );
        return (try self.materializeRepresentativeSymbolic(
            symbolic,
            &state,
        )) orelse error.MissingRepresentative;
    }

    fn representativeCacheForMode(
        self: *SymbolicEngine,
        state: *MatchSession,
        mode: BindingMode,
    ) *RepresentativeCache {
        _ = self;
        return switch (mode) {
            .exact => unreachable,
            .transparent => &state.transparent_representatives,
            .normalized => &state.normalized_representatives,
        };
    }

    pub fn chooseRepresentativeSymbolic(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!*const SymbolicExpr {
        if (mode == .exact) {
            return try self.allocSymbolic(.{ .fixed = expr_id });
        }

        const cache = self.representativeCacheForMode(state, mode);
        if (cache.get(expr_id)) |cached| return cached;

        var current = try self.rebuildExprRepresentativeSymbolic(
            expr_id,
            state,
            mode,
        );
        if (self.shared.registry) |registry| {
            if (try self.symbolicToConcreteIfPlain(current, state)) |plain| {
                var canonicalizer = Canonicalizer.init(
                    self.shared.allocator,
                    self.shared.theorem,
                    registry,
                    self.shared.env,
                );
                const canonical = try canonicalizer.canonicalize(plain);
                current = try self.allocSymbolic(.{ .fixed = canonical });
            }
        }
        while (try self.compressRepresentativeToDef(current, state)) |compressed| {
            if (self.symbolicExprEql(current, compressed)) break;
            current = compressed;
        }
        try cache.put(self.shared.allocator, expr_id, current);
        return current;
    }

    fn rebuildExprRepresentativeSymbolic(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!*const SymbolicExpr {
        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(self.shared.allocator);

        var witness_it = state.witnesses.iterator();
        while (witness_it.next()) |entry| {
            try witness_slots.put(
                self.shared.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }
        var materialized_it = state.materialized_witnesses.iterator();
        while (materialized_it.next()) |entry| {
            try witness_slots.put(
                self.shared.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }

        if (try self.getResymbolizableWitnessInfo(expr_id)) |info| {
            const slot = try self.slotForWitness(
                expr_id,
                info,
                state,
                &witness_slots,
            );
            return try self.allocSymbolic(.{ .dummy = slot });
        }

        const node = self.shared.theorem.interner.node(expr_id);
        return switch (node.*) {
            .variable => try self.allocSymbolic(.{ .fixed = expr_id }),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                errdefer self.shared.allocator.free(args);
                const plain_args = try self.shared.allocator.alloc(ExprId, app.args.len);
                errdefer self.shared.allocator.free(plain_args);

                var all_plain = true;
                var changed = false;
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.chooseRepresentativeSymbolic(
                        arg,
                        state,
                        mode,
                    );
                    if (try self.symbolicToConcreteIfPlain(args[idx], state)) |plain| {
                        plain_args[idx] = plain;
                        changed = changed or plain != arg;
                    } else {
                        all_plain = false;
                        changed = true;
                    }
                }
                if (all_plain) {
                    self.shared.allocator.free(args);
                    if (!changed) {
                        self.shared.allocator.free(plain_args);
                        break :blk try self.allocSymbolic(
                            .{ .fixed = expr_id },
                        );
                    }
                    const rebuilt = try self.shared.theorem.interner.internAppOwned(
                        app.term_id,
                        plain_args,
                    );
                    break :blk try self.allocSymbolic(
                        .{ .fixed = rebuilt },
                    );
                }
                self.shared.allocator.free(plain_args);
                break :blk try self.allocSymbolic(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        };
    }

    fn compressRepresentativeToDef(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *const MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const sort_name = self.symbolicSortName(symbolic, state) orelse {
            return null;
        };

        term_loop: for (self.shared.env.terms.items, 0..) |term, term_id| {
            if (!term.is_def or term.body == null) continue;
            if (!std.mem.eql(u8, term.ret_sort_name, sort_name)) continue;

            var temp = try self.cloneRepresentativeState(
                state,
                term.args.len + term.dummy_args.len,
            );
            defer temp.deinit(self.shared.allocator);

            const symbolic_template = try self.symbolicFromTemplate(term.body.?);
            const matched = if (try self.symbolicToConcreteIfPlain(
                symbolic,
                state,
            )) |plain|
                try self.matchExprToSymbolic(
                    plain,
                    symbolic_template,
                    &temp,
                    .transparent,
                )
            else
                try self.matchSymbolicToSymbolicState(
                    symbolic_template,
                    symbolic,
                    &temp,
                );
            if (!matched) {
                continue;
            }

            const args = try self.shared.allocator.alloc(*const SymbolicExpr, term.args.len);
            errdefer self.shared.allocator.free(args);
            const plain_args = try self.shared.allocator.alloc(ExprId, term.args.len);
            errdefer self.shared.allocator.free(plain_args);

            var all_plain = true;
            for (0..term.args.len) |idx| {
                const binding = temp.bindings[idx] orelse {
                    self.shared.allocator.free(args);
                    self.shared.allocator.free(plain_args);
                    continue :term_loop;
                };
                args[idx] = try self.boundValueRepresentative(binding);
                if (try self.symbolicToConcreteIfPlain(args[idx], &temp)) |plain| {
                    plain_args[idx] = plain;
                } else {
                    all_plain = false;
                }
            }

            if (all_plain) {
                self.shared.allocator.free(args);
                const rebuilt = try self.shared.theorem.interner.internAppOwned(
                    @intCast(term_id),
                    plain_args,
                );
                return try self.allocSymbolic(.{ .fixed = rebuilt });
            }
            self.shared.allocator.free(plain_args);
            return try self.allocSymbolic(.{ .app = .{
                .term_id = @intCast(term_id),
                .args = args,
            } });
        }
        return null;
    }

    fn symbolicSortName(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *const MatchSession,
    ) ?[]const u8 {
        return switch (symbolic.*) {
            .binder => null,
            .fixed => |expr_id| self.exprSortName(expr_id),
            .dummy => |slot| if (slot < state.symbolic_dummy_infos.items.len)
                state.symbolic_dummy_infos.items[slot].sort_name
            else
                null,
            .app => |app| if (app.term_id < self.shared.env.terms.items.len)
                self.shared.env.terms.items[app.term_id].ret_sort_name
            else
                null,
        };
    }

    fn symbolicToConcreteIfPlain(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *const MatchSession,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => null,
            .dummy => null,
            .fixed => |expr_id| expr_id,
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(ExprId, app.args.len);
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.symbolicToConcreteIfPlain(
                        arg,
                        state,
                    )) orelse {
                        self.shared.allocator.free(args);
                        break :blk null;
                    };
                }
                break :blk try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    pub fn symbolicExprEql(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
    ) bool {
        return switch (lhs.*) {
            .binder => |idx| switch (rhs.*) {
                .binder => |rhs_idx| idx == rhs_idx,
                else => false,
            },
            .fixed => |expr_id| switch (rhs.*) {
                .fixed => |rhs_expr| expr_id == rhs_expr,
                else => false,
            },
            .dummy => |slot| switch (rhs.*) {
                .dummy => |rhs_slot| slot == rhs_slot,
                else => false,
            },
            .app => |app| switch (rhs.*) {
                .app => |rhs_app| blk: {
                    if (app.term_id != rhs_app.term_id) break :blk false;
                    if (app.args.len != rhs_app.args.len) break :blk false;
                    for (app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                        if (!self.symbolicExprEql(lhs_arg, rhs_arg)) {
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
                else => false,
            },
        };
    }

    fn boundValueRepresentative(
        self: *SymbolicEngine,
        bound: BoundValue,
    ) anyerror!*const SymbolicExpr {
        return switch (bound) {
            .concrete => |concrete| if (concrete.mode == .exact)
                try self.allocSymbolic(.{ .fixed = concrete.raw })
            else
                concrete.repr,
            .symbolic => |symbolic| symbolic.expr,
        };
    }

    fn exprSortName(
        self: *SymbolicEngine,
        expr_id: ExprId,
    ) ?[]const u8 {
        const node = self.shared.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| if (app.term_id < self.shared.env.terms.items.len)
                self.shared.env.terms.items[app.term_id].ret_sort_name
            else
                null,
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| if (idx < self.shared.theorem.arg_infos.len)
                    self.shared.theorem.arg_infos[idx].sort_name
                else
                    null,
                .dummy_var => |idx| if (idx < self.shared.theorem.theorem_dummies.items.len)
                    self.shared.theorem.theorem_dummies.items[idx].sort_name
                else
                    null,
            },
        };
    }

    fn resymbolizeBinding(
        self: *SymbolicEngine,
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

        const node = self.shared.theorem.interner.node(expr_id);
        return switch (node.*) {
            .variable => null,
            .app => |app| blk: {
                var has_symbolic = false;
                const args = try self.shared.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                errdefer self.shared.allocator.free(args);
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
                    self.shared.allocator.free(args);
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
        self: *SymbolicEngine,
        witness: ExprId,
        info: SymbolicDummyInfo,
        state: *MatchSession,
        witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    ) anyerror!usize {
        if (witness_slots.get(witness)) |slot| return slot;
        if (state.materialized_witness_slots.get(witness)) |slot| {
            try witness_slots.put(self.shared.allocator, witness, slot);
            return slot;
        }

        const slot = state.symbolic_dummy_infos.items.len;
        try state.symbolic_dummy_infos.append(self.shared.allocator, info);
        try witness_slots.put(self.shared.allocator, witness, slot);
        try state.witnesses.put(self.shared.allocator, slot, witness);
        try state.provisional_witness_infos.put(
            self.shared.allocator,
            witness,
            info,
        );
        return slot;
    }

    fn saveMatchSnapshot(
        self: *SymbolicEngine,
        state: *const MatchSession,
    ) anyerror!MatchSnapshot {
        return .{
            .bindings = try self.shared.allocator.dupe(?BoundValue, state.bindings),
            .witnesses = try self.cloneWitnessMap(state.witnesses),
            .materialized_witnesses = try self.cloneWitnessMap(state.materialized_witnesses),
            .materialized_witness_slots = try self.cloneWitnessSlotMap(state.materialized_witness_slots),
            .provisional_witness_infos = try self.cloneProvisionalWitnessInfoMap(
                state.provisional_witness_infos,
            ),
            .materialized_witness_infos = try self.cloneMaterializedWitnessInfoMap(
                state.materialized_witness_infos,
            ),
            .transparent_representatives = try self.cloneRepresentativeCache(
                state.transparent_representatives,
            ),
            .normalized_representatives = try self.cloneRepresentativeCache(
                state.normalized_representatives,
            ),
            .dummy_info_len = state.symbolic_dummy_infos.items.len,
        };
    }

    fn restoreMatchSnapshot(
        self: *SymbolicEngine,
        snapshot: *const MatchSnapshot,
        state: *MatchSession,
    ) anyerror!void {
        @memcpy(state.bindings, snapshot.bindings);
        state.witnesses.deinit(self.shared.allocator);
        state.witnesses = try self.cloneWitnessMap(snapshot.witnesses);
        state.materialized_witnesses.deinit(self.shared.allocator);
        state.materialized_witnesses =
            try self.cloneWitnessMap(snapshot.materialized_witnesses);
        state.materialized_witness_slots.deinit(self.shared.allocator);
        state.materialized_witness_slots = try self.cloneWitnessSlotMap(
            snapshot.materialized_witness_slots,
        );
        state.provisional_witness_infos.deinit(self.shared.allocator);
        state.provisional_witness_infos =
            try self.cloneProvisionalWitnessInfoMap(
                snapshot.provisional_witness_infos,
            );
        state.materialized_witness_infos.deinit(self.shared.allocator);
        state.materialized_witness_infos =
            try self.cloneMaterializedWitnessInfoMap(
                snapshot.materialized_witness_infos,
            );
        state.transparent_representatives.deinit(self.shared.allocator);
        state.transparent_representatives =
            try self.cloneRepresentativeCache(
                snapshot.transparent_representatives,
            );
        state.normalized_representatives.deinit(self.shared.allocator);
        state.normalized_representatives =
            try self.cloneRepresentativeCache(
                snapshot.normalized_representatives,
            );
        state.symbolic_dummy_infos.shrinkRetainingCapacity(
            snapshot.dummy_info_len,
        );
    }

    fn deinitMatchSnapshot(
        self: *SymbolicEngine,
        snapshot: *MatchSnapshot,
    ) void {
        self.shared.allocator.free(snapshot.bindings);
        snapshot.witnesses.deinit(self.shared.allocator);
        snapshot.materialized_witnesses.deinit(self.shared.allocator);
        snapshot.materialized_witness_slots.deinit(self.shared.allocator);
        snapshot.provisional_witness_infos.deinit(self.shared.allocator);
        snapshot.materialized_witness_infos.deinit(self.shared.allocator);
        snapshot.transparent_representatives.deinit(self.shared.allocator);
        snapshot.normalized_representatives.deinit(self.shared.allocator);
    }

    fn cloneWitnessMap(self: *SymbolicEngine, map: WitnessMap) anyerror!WitnessMap {
        var clone: WitnessMap = .{};
        var it = map.iterator();
        while (it.next()) |entry| {
            try clone.put(
                self.shared.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return clone;
    }

    fn cloneWitnessSlotMap(
        self: *SymbolicEngine,
        map: WitnessSlotMap,
    ) anyerror!WitnessSlotMap {
        var clone: WitnessSlotMap = .{};
        var it = map.iterator();
        while (it.next()) |entry| {
            try clone.put(
                self.shared.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return clone;
    }

    fn cloneProvisionalWitnessInfoMap(
        self: *SymbolicEngine,
        map: ProvisionalWitnessInfoMap,
    ) anyerror!ProvisionalWitnessInfoMap {
        var clone: ProvisionalWitnessInfoMap = .{};
        var it = map.iterator();
        while (it.next()) |entry| {
            try clone.put(
                self.shared.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return clone;
    }

    fn cloneMaterializedWitnessInfoMap(
        self: *SymbolicEngine,
        map: MaterializedWitnessInfoMap,
    ) anyerror!MaterializedWitnessInfoMap {
        var clone: MaterializedWitnessInfoMap = .{};
        var it = map.iterator();
        while (it.next()) |entry| {
            try clone.put(
                self.shared.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return clone;
    }

    fn cloneRepresentativeCache(
        self: *SymbolicEngine,
        map: RepresentativeCache,
    ) anyerror!RepresentativeCache {
        var clone: RepresentativeCache = .{};
        var it = map.iterator();
        while (it.next()) |entry| {
            try clone.put(
                self.shared.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return clone;
    }

    fn cloneRepresentativeState(
        self: *SymbolicEngine,
        source: *const MatchSession,
        binding_len: usize,
    ) anyerror!MatchSession {
        var clone = try MatchSession.init(self.shared.allocator, binding_len);
        errdefer clone.deinit(self.shared.allocator);

        clone.witnesses = try self.cloneWitnessMap(source.witnesses);
        clone.materialized_witnesses =
            try self.cloneWitnessMap(source.materialized_witnesses);
        clone.materialized_witness_slots =
            try self.cloneWitnessSlotMap(source.materialized_witness_slots);
        clone.provisional_witness_infos =
            try self.cloneProvisionalWitnessInfoMap(
                source.provisional_witness_infos,
            );
        clone.materialized_witness_infos =
            try self.cloneMaterializedWitnessInfoMap(
                source.materialized_witness_infos,
            );
        try clone.symbolic_dummy_infos.appendSlice(
            self.shared.allocator,
            source.symbolic_dummy_infos.items,
        );
        return clone;
    }

    fn boundValueMatchesExpr(
        self: *SymbolicEngine,
        bound: BoundValue,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (bound) {
            .concrete => |concrete| {
                return try self.concreteBindingMatchesExpr(
                    concrete,
                    actual,
                    state,
                );
            },
            .symbolic => |symbolic| {
                return try self.matchSymbolicToExprState(
                    symbolic.expr,
                    actual,
                    state,
                );
            },
        };
    }

    fn concreteBindingMatchesExpr(
        self: *SymbolicEngine,
        concrete: ConcreteBinding,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        if (concrete.mode == .exact) {
            return concrete.raw == actual;
        }
        const actual_repr = try self.chooseRepresentativeSymbolic(
            actual,
            state,
            concrete.mode,
        );
        return self.symbolicExprEql(concrete.repr, actual_repr);
    }

    fn boundValueMatchesSymbolic(
        self: *SymbolicEngine,
        bound: BoundValue,
        actual: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (bound) {
            .concrete => |concrete| {
                const match_expr = (try self.concreteBindingMatchExpr(
                    concrete,
                    state,
                )) orelse return false;
                return try self.matchExprToSymbolic(
                    match_expr,
                    actual,
                    state,
                    concrete.mode,
                );
            },
            .symbolic => |symbolic| {
                return try self.matchSymbolicToSymbolicState(
                    symbolic.expr,
                    actual,
                    state,
                );
            },
        };
    }

    pub fn concreteBindingMatchExpr(
        self: *SymbolicEngine,
        concrete: ConcreteBinding,
        state: *MatchSession,
    ) anyerror!?ExprId {
        if (concrete.mode == .exact) return concrete.raw;
        return try self.materializeRepresentativeSymbolic(
            concrete.repr,
            state,
        );
    }

    pub fn matchSymbolicDummyState(
        self: *SymbolicEngine,
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

        if (self.currentWitnessExpr(slot, state)) |existing| {
            if (existing == actual) return true;
            if (self.isProvisionalWitnessExpr(existing, state)) {
                try state.witnesses.put(self.shared.allocator, slot, actual);
                return true;
            }
            return false;
        }
        try state.witnesses.put(self.shared.allocator, slot, actual);
        return true;
    }

    pub fn matchDummyToSymbolic(
        self: *SymbolicEngine,
        slot: usize,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (rhs.*) {
            .binder => |idx| blk: {
                const symbolic = try self.allocSymbolic(.{ .dummy = slot });
                break :blk try self.assignBinderFromSymbolic(
                    idx,
                    symbolic,
                    state,
                    .transparent,
                );
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
                if (self.currentWitnessExpr(slot, state)) |lhs_witness| {
                    if (self.currentWitnessExpr(rhs_slot, state)) |rhs_witness| {
                        return lhs_witness == rhs_witness;
                    }
                    try state.witnesses.put(
                        self.shared.allocator,
                        rhs_slot,
                        lhs_witness,
                    );
                    return true;
                }
                if (self.currentWitnessExpr(rhs_slot, state)) |rhs_witness| {
                    try state.witnesses.put(
                        self.shared.allocator,
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
                    .transparent,
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
        self: *SymbolicEngine,
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

    // This is the only escape path that turns symbolic match state back into
    // main-theorem expressions. Internal matching and representative work
    // should stay symbolic until a caller explicitly finalizes bindings.
    pub fn finalizeBoundValue(
        self: *SymbolicEngine,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!ExprId {
        return switch (bound) {
            .concrete => |concrete| {
                return (try self.concreteBindingMatchExpr(
                    concrete,
                    state,
                )) orelse error.MissingRepresentative;
            },
            .symbolic => |symbolic| {
                const expr_id = try self.materializeFinalSymbolicForEscape(
                    symbolic.expr,
                    state,
                );
                return try self.chooseRepresentative(expr_id, symbolic.mode);
            },
        };
    }

    fn materializeAssignedBoundValue(
        self: *SymbolicEngine,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (bound) {
            .concrete => |concrete| try self.concreteBindingMatchExpr(
                concrete,
                state,
            ),
            .symbolic => |symbolic| {
                return try self.materializeAssignedSymbolic(
                    symbolic.expr,
                    state,
                    symbolic.mode,
                );
            },
        };
    }

    fn materializeRepresentativeSymbolic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) break :blk null;
                const bound = state.bindings[idx] orelse break :blk null;
                break :blk try self.materializeAssignedBoundValue(bound, state);
            },
            .fixed => |expr| expr,
            .dummy => |slot| self.currentWitnessExpr(slot, state),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(ExprId, app.args.len);
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.materializeRepresentativeSymbolic(
                        arg,
                        state,
                    )) orelse break :blk null;
                }
                break :blk try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn materializeAssignedSymbolic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!?ExprId {
        const expr_id = try self.materializeRepresentativeSymbolic(
            symbolic,
            state,
        ) orelse return null;
        return try self.chooseRepresentative(expr_id, mode);
    }

    fn materializeFinalSymbolicForEscape(
        self: *SymbolicEngine,
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
            .dummy => |slot| try self.materializeEscapingWitnessForDummySlot(
                slot,
                state,
            ),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(ExprId, app.args.len);
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeFinalSymbolicForEscape(
                        arg,
                        state,
                    );
                }
                break :blk try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    pub fn currentWitnessExpr(
        self: *SymbolicEngine,
        slot: usize,
        state: *const MatchSession,
    ) ?ExprId {
        _ = self;
        return state.witnesses.get(slot) orelse
            state.materialized_witnesses.get(slot);
    }

    pub fn isProvisionalWitnessExpr(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *const MatchSession,
    ) bool {
        _ = self;
        return state.provisional_witness_infos.contains(expr_id) or
            state.materialized_witness_infos.contains(expr_id);
    }

    // This is the only main-theorem dummy allocation point in the def-ops
    // subsystem. Call it only from explicit escape/finalization paths.
    fn materializeEscapingWitnessForDummySlot(
        self: *SymbolicEngine,
        slot: usize,
        state: *MatchSession,
    ) anyerror!ExprId {
        if (state.witnesses.get(slot)) |existing| return existing;
        if (state.materialized_witnesses.get(slot)) |existing| return existing;
        if (slot >= state.symbolic_dummy_infos.items.len) {
            return error.UnknownDummyVar;
        }
        const info = state.symbolic_dummy_infos.items[slot];
        const sort_id = self.shared.env.sort_names.get(info.sort_name) orelse {
            return error.UnknownSort;
        };
        const witness = try self.shared.theorem.addDummyVarResolved(
            info.sort_name,
            sort_id,
        );
        try state.materialized_witnesses.put(self.shared.allocator, slot, witness);
        try state.materialized_witness_slots.put(
            self.shared.allocator,
            witness,
            slot,
        );
        try state.materialized_witness_infos.put(
            self.shared.allocator,
            witness,
            info,
        );
        return witness;
    }

    fn getResymbolizableWitnessInfo(
        self: *SymbolicEngine,
        expr_id: ExprId,
    ) !?SymbolicDummyInfo {
        const node = self.shared.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => null,
            .variable => |var_id| switch (var_id) {
                .theorem_var => null,
                .dummy_var => |idx| blk: {
                    if (idx >= self.shared.theorem.theorem_dummies.items.len) {
                        return error.UnknownDummyVar;
                    }
                    const dummy = self.shared.theorem.theorem_dummies.items[idx];
                    break :blk .{ .sort_name = dummy.sort_name };
                },
            },
        };
    }

    fn getConcreteVarInfo(self: *SymbolicEngine, expr_id: ExprId) !ConcreteVarInfo {
        const node = self.shared.theorem.interner.node(expr_id);
        const var_id = switch (node.*) {
            .variable => |value| value,
            .app => return error.ExpectedVariable,
        };
        return switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= self.shared.theorem.arg_infos.len) {
                    return error.UnknownTheoremVariable;
                }
                const arg = self.shared.theorem.arg_infos[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= self.shared.theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = self.shared.theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                };
            },
        };
    }

    fn expandTemplateApp(
        self: *SymbolicEngine,
        app: TemplateExpr.App,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const subst = try self.shared.allocator.alloc(
            *const SymbolicExpr,
            term.args.len + term.dummy_args.len,
        );
        for (app.args, 0..) |arg, idx| {
            subst[idx] = try self.symbolicFromTemplate(arg);
        }
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = state.symbolic_dummy_infos.items.len;
            try state.symbolic_dummy_infos.append(self.shared.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[term.args.len + idx] = try self.allocSymbolic(
                .{ .dummy = slot },
            );
        }
        return try self.symbolicFromTemplateSubst(body, subst);
    }

    fn expandConcreteDef(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const def = self.getConcreteDef(expr_id) orelse return null;

        const subst = try self.shared.allocator.alloc(
            *const SymbolicExpr,
            def.term.args.len + def.term.dummy_args.len,
        );
        for (def.app.args, 0..) |arg, idx| {
            subst[idx] = try self.allocSymbolic(.{ .fixed = arg });
        }
        for (def.term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = state.symbolic_dummy_infos.items.len;
            try state.symbolic_dummy_infos.append(self.shared.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[def.term.args.len + idx] = try self.allocSymbolic(
                .{ .dummy = slot },
            );
        }
        return try self.symbolicFromTemplateSubst(def.body, subst);
    }

    fn expandSymbolicApp(
        self: *SymbolicEngine,
        app: SymbolicExpr.App,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const subst = try self.shared.allocator.alloc(
            *const SymbolicExpr,
            term.args.len + term.dummy_args.len,
        );
        @memcpy(subst[0..term.args.len], app.args);
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = state.symbolic_dummy_infos.items.len;
            try state.symbolic_dummy_infos.append(self.shared.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[term.args.len + idx] = try self.allocSymbolic(
                .{ .dummy = slot },
            );
        }
        return try self.symbolicFromTemplateSubst(body, subst);
    }

    fn symbolicFromTemplate(
        self: *SymbolicEngine,
        template: TemplateExpr,
    ) anyerror!*const SymbolicExpr {
        return try self.symbolicFromTemplateSubst(template, null);
    }

    fn symbolicFromTemplateSubst(
        self: *SymbolicEngine,
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
                const args = try self.shared.allocator.alloc(
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

    fn getConcreteDef(self: *const SymbolicEngine, expr_id: ExprId) ?struct {
        app: ExprApp,
        term: *const TermDecl,
        body: TemplateExpr,
    } {
        const node = self.shared.theorem.interner.node(expr_id);
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

    fn getOpenableTerm(self: *const SymbolicEngine, term_id: u32) ?*const TermDecl {
        if (term_id >= self.shared.env.terms.items.len) return null;
        const term = &self.shared.env.terms.items[term_id];
        if (!term.is_def or term.body == null) return null;
        return term;
    }

    pub fn allocSymbolic(
        self: *SymbolicEngine,
        symbolic: SymbolicExpr,
    ) anyerror!*const SymbolicExpr {
        const node = try self.shared.allocator.create(SymbolicExpr);
        node.* = symbolic;
        return node;
    }

    fn allocPlan(
        self: *SymbolicEngine,
        plan: ConversionPlan,
    ) anyerror!*const ConversionPlan {
        const node = try self.shared.allocator.create(ConversionPlan);
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
