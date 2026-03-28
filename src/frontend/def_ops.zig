const std = @import("std");
const TermDecl = @import("./compiler_env.zig").TermDecl;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprApp = @import("./compiler_expr.zig").ExprNode.App;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const RewriteRegistry =
    @import("./rewrite_registry.zig").RewriteRegistry;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const MirrorSupport = @import("./def_ops/mirror_support.zig");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const Expr = @import("../trusted/expressions.zig").Expr;
const MirroredTheoremContext = MirrorSupport.MirroredTheoremContext;
const copyExprBetweenTheorems = MirrorSupport.copyExprBetweenTheorems;

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

pub const BindingMode = enum {
    exact,
    transparent,
    normalized,
};

pub const BindingSeed = union(enum) {
    none,
    exact: ExprId,
    semantic: struct {
        expr_id: ExprId,
        mode: BindingMode,
    },
};

const ConcreteBinding = struct {
    raw: ExprId,
    repr: *const SymbolicExpr,
    mode: BindingMode,
};

const SymbolicBinding = struct {
    expr: *const SymbolicExpr,
    mode: BindingMode,
};

const BoundValue = union(enum) {
    concrete: ConcreteBinding,
    symbolic: SymbolicBinding,
};

const WitnessMap = std.AutoHashMapUnmanaged(usize, ExprId);
const WitnessSlotMap = std.AutoHashMapUnmanaged(ExprId, usize);
const ProvisionalWitnessInfoMap = std.AutoHashMapUnmanaged(
    ExprId,
    SymbolicDummyInfo,
);
const MaterializedWitnessInfoMap = std.AutoHashMapUnmanaged(
    ExprId,
    SymbolicDummyInfo,
);
const RepresentativeCache = std.AutoHashMapUnmanaged(
    ExprId,
    *const SymbolicExpr,
);

const MatchSession = struct {
    bindings: []?BoundValue,
    witnesses: WitnessMap = .{},
    materialized_witnesses: WitnessMap = .{},
    materialized_witness_slots: WitnessSlotMap = .empty,
    provisional_witness_infos: ProvisionalWitnessInfoMap = .empty,
    materialized_witness_infos: MaterializedWitnessInfoMap = .empty,
    transparent_representatives: RepresentativeCache = .empty,
    normalized_representatives: RepresentativeCache = .empty,
    symbolic_dummy_infos: std.ArrayListUnmanaged(SymbolicDummyInfo) = .{},

    fn init(
        allocator: std.mem.Allocator,
        binding_len: usize,
    ) !MatchSession {
        const bindings = try allocator.alloc(?BoundValue, binding_len);
        @memset(bindings, null);
        return .{
            .bindings = bindings,
        };
    }

    fn deinit(
        self: *MatchSession,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.bindings);
        self.witnesses.deinit(allocator);
        self.materialized_witnesses.deinit(allocator);
        self.materialized_witness_slots.deinit(allocator);
        self.provisional_witness_infos.deinit(allocator);
        self.materialized_witness_infos.deinit(allocator);
        self.transparent_representatives.deinit(allocator);
        self.normalized_representatives.deinit(allocator);
        self.symbolic_dummy_infos.deinit(allocator);
    }
};

const MatchSnapshot = struct {
    bindings: []?BoundValue,
    witnesses: WitnessMap,
    materialized_witnesses: WitnessMap,
    materialized_witness_slots: WitnessSlotMap,
    provisional_witness_infos: ProvisionalWitnessInfoMap,
    materialized_witness_infos: MaterializedWitnessInfoMap,
    transparent_representatives: RepresentativeCache,
    normalized_representatives: RepresentativeCache,
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
    registry: ?*RewriteRegistry,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) Context {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = null,
        };
    }

    pub fn initWithRegistry(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
    ) Context {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = registry,
        };
    }

    pub fn deinit(self: *Context) void {
        _ = self;
    }

    pub fn beginRuleMatch(
        self: *Context,
        rule_args: []const ArgInfo,
        seeds: []const BindingSeed,
    ) anyerror!RuleMatchSession {
        return try RuleMatchSession.init(
            self,
            rule_args,
            seeds,
        );
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
            .transparent,
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
        self: *Context,
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
        self: *Context,
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
            .transparent,
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
        mode: BindingMode,
    ) anyerror!BoundValue {
        if (try self.resymbolizeBinding(expr_id, state, witness_slots)) |symbolic| {
            return self.makeSymbolicBoundValue(symbolic, mode);
        }
        return try self.makeConcreteBoundValue(expr_id, state, mode);
    }

    fn rebuildBoundValueFromState(
        self: *Context,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!BoundValue {
        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(self.allocator);

        var it = state.witnesses.iterator();
        while (it.next()) |entry| {
            try witness_slots.put(
                self.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }
        var materialized_it = state.materialized_witnesses.iterator();
        while (materialized_it.next()) |entry| {
            try witness_slots.put(
                self.allocator,
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

    fn makeConcreteBoundValue(
        self: *Context,
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

    fn makeSymbolicBoundValue(
        self: *Context,
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
        self: *Context,
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
        self: *Context,
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

    fn assignBinderValue(
        self: *Context,
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

    fn boundValueFromSeed(
        self: *Context,
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

    fn chooseRepresentative(
        self: *Context,
        expr_id: ExprId,
        mode: BindingMode,
    ) anyerror!ExprId {
        if (mode == .exact) return expr_id;

        var state = try MatchSession.init(self.allocator, 0);
        defer state.deinit(self.allocator);

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
        self: *Context,
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

    fn chooseRepresentativeSymbolic(
        self: *Context,
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
        if (self.registry) |registry| {
            if (try self.symbolicToConcreteIfPlain(current, state)) |plain| {
                var canonicalizer = Canonicalizer.init(
                    self.allocator,
                    self.theorem,
                    registry,
                    self.env,
                );
                const canonical = try canonicalizer.canonicalize(plain);
                current = try self.allocSymbolic(.{ .fixed = canonical });
            }
        }
        while (try self.compressRepresentativeToDef(current, state)) |compressed| {
            if (self.symbolicExprEql(current, compressed)) break;
            current = compressed;
        }
        try cache.put(self.allocator, expr_id, current);
        return current;
    }

    fn rebuildExprRepresentativeSymbolic(
        self: *Context,
        expr_id: ExprId,
        state: *MatchSession,
        mode: BindingMode,
    ) anyerror!*const SymbolicExpr {
        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(self.allocator);

        var witness_it = state.witnesses.iterator();
        while (witness_it.next()) |entry| {
            try witness_slots.put(
                self.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }
        var materialized_it = state.materialized_witnesses.iterator();
        while (materialized_it.next()) |entry| {
            try witness_slots.put(
                self.allocator,
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

        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .variable => try self.allocSymbolic(.{ .fixed = expr_id }),
            .app => |app| blk: {
                const args = try self.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                errdefer self.allocator.free(args);
                const plain_args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(plain_args);

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
                    self.allocator.free(args);
                    if (!changed) {
                        self.allocator.free(plain_args);
                        break :blk try self.allocSymbolic(
                            .{ .fixed = expr_id },
                        );
                    }
                    const rebuilt = try self.theorem.interner.internAppOwned(
                        app.term_id,
                        plain_args,
                    );
                    break :blk try self.allocSymbolic(
                        .{ .fixed = rebuilt },
                    );
                }
                self.allocator.free(plain_args);
                break :blk try self.allocSymbolic(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        };
    }

    fn compressRepresentativeToDef(
        self: *Context,
        symbolic: *const SymbolicExpr,
        state: *const MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const sort_name = self.symbolicSortName(symbolic, state) orelse {
            return null;
        };

        term_loop: for (self.env.terms.items, 0..) |term, term_id| {
            if (!term.is_def or term.body == null) continue;
            if (!std.mem.eql(u8, term.ret_sort_name, sort_name)) continue;

            var temp = try self.cloneRepresentativeState(
                state,
                term.args.len + term.dummy_args.len,
            );
            defer temp.deinit(self.allocator);

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

            const args = try self.allocator.alloc(*const SymbolicExpr, term.args.len);
            errdefer self.allocator.free(args);
            const plain_args = try self.allocator.alloc(ExprId, term.args.len);
            errdefer self.allocator.free(plain_args);

            var all_plain = true;
            for (0..term.args.len) |idx| {
                const binding = temp.bindings[idx] orelse {
                    self.allocator.free(args);
                    self.allocator.free(plain_args);
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
                self.allocator.free(args);
                const rebuilt = try self.theorem.interner.internAppOwned(
                    @intCast(term_id),
                    plain_args,
                );
                return try self.allocSymbolic(.{ .fixed = rebuilt });
            }
            self.allocator.free(plain_args);
            return try self.allocSymbolic(.{ .app = .{
                .term_id = @intCast(term_id),
                .args = args,
            } });
        }
        return null;
    }

    fn symbolicSortName(
        self: *Context,
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
            .app => |app| if (app.term_id < self.env.terms.items.len)
                self.env.terms.items[app.term_id].ret_sort_name
            else
                null,
        };
    }

    fn symbolicToConcreteIfPlain(
        self: *Context,
        symbolic: *const SymbolicExpr,
        state: *const MatchSession,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => null,
            .dummy => null,
            .fixed => |expr_id| expr_id,
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.symbolicToConcreteIfPlain(
                        arg,
                        state,
                    )) orelse {
                        self.allocator.free(args);
                        break :blk null;
                    };
                }
                break :blk try self.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn symbolicExprEql(
        self: *Context,
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
        self: *Context,
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
        self: *Context,
        expr_id: ExprId,
    ) ?[]const u8 {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| if (app.term_id < self.env.terms.items.len)
                self.env.terms.items[app.term_id].ret_sort_name
            else
                null,
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| if (idx < self.theorem.arg_infos.len)
                    self.theorem.arg_infos[idx].sort_name
                else
                    null,
                .dummy_var => |idx| if (idx < self.theorem.theorem_dummies.items.len)
                    self.theorem.theorem_dummies.items[idx].sort_name
                else
                    null,
            },
        };
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
        if (state.materialized_witness_slots.get(witness)) |slot| {
            try witness_slots.put(self.allocator, witness, slot);
            return slot;
        }

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
        self: *Context,
        snapshot: *const MatchSnapshot,
        state: *MatchSession,
    ) anyerror!void {
        @memcpy(state.bindings, snapshot.bindings);
        state.witnesses.deinit(self.allocator);
        state.witnesses = try self.cloneWitnessMap(snapshot.witnesses);
        state.materialized_witnesses.deinit(self.allocator);
        state.materialized_witnesses =
            try self.cloneWitnessMap(snapshot.materialized_witnesses);
        state.materialized_witness_slots.deinit(self.allocator);
        state.materialized_witness_slots = try self.cloneWitnessSlotMap(
            snapshot.materialized_witness_slots,
        );
        state.provisional_witness_infos.deinit(self.allocator);
        state.provisional_witness_infos =
            try self.cloneProvisionalWitnessInfoMap(
                snapshot.provisional_witness_infos,
            );
        state.materialized_witness_infos.deinit(self.allocator);
        state.materialized_witness_infos =
            try self.cloneMaterializedWitnessInfoMap(
                snapshot.materialized_witness_infos,
            );
        state.transparent_representatives.deinit(self.allocator);
        state.transparent_representatives =
            try self.cloneRepresentativeCache(
                snapshot.transparent_representatives,
            );
        state.normalized_representatives.deinit(self.allocator);
        state.normalized_representatives =
            try self.cloneRepresentativeCache(
                snapshot.normalized_representatives,
            );
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
        snapshot.materialized_witnesses.deinit(self.allocator);
        snapshot.materialized_witness_slots.deinit(self.allocator);
        snapshot.provisional_witness_infos.deinit(self.allocator);
        snapshot.materialized_witness_infos.deinit(self.allocator);
        snapshot.transparent_representatives.deinit(self.allocator);
        snapshot.normalized_representatives.deinit(self.allocator);
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

    fn cloneWitnessSlotMap(
        self: *Context,
        map: WitnessSlotMap,
    ) anyerror!WitnessSlotMap {
        var clone: WitnessSlotMap = .{};
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

    fn cloneProvisionalWitnessInfoMap(
        self: *Context,
        map: ProvisionalWitnessInfoMap,
    ) anyerror!ProvisionalWitnessInfoMap {
        var clone: ProvisionalWitnessInfoMap = .{};
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

    fn cloneMaterializedWitnessInfoMap(
        self: *Context,
        map: MaterializedWitnessInfoMap,
    ) anyerror!MaterializedWitnessInfoMap {
        var clone: MaterializedWitnessInfoMap = .{};
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

    fn cloneRepresentativeCache(
        self: *Context,
        map: RepresentativeCache,
    ) anyerror!RepresentativeCache {
        var clone: RepresentativeCache = .{};
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

    fn cloneRepresentativeState(
        self: *Context,
        source: *const MatchSession,
        binding_len: usize,
    ) anyerror!MatchSession {
        var clone = try MatchSession.init(self.allocator, binding_len);
        errdefer clone.deinit(self.allocator);

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
            self.allocator,
            source.symbolic_dummy_infos.items,
        );
        return clone;
    }

    fn boundValueMatchesExpr(
        self: *Context,
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
        self: *Context,
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
        self: *Context,
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

    fn concreteBindingMatchExpr(
        self: *Context,
        concrete: ConcreteBinding,
        state: *MatchSession,
    ) anyerror!?ExprId {
        if (concrete.mode == .exact) return concrete.raw;
        return try self.materializeRepresentativeSymbolic(
            concrete.repr,
            state,
        );
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

        if (self.currentWitnessExpr(slot, state)) |existing| {
            if (existing == actual) return true;
            if (self.isProvisionalWitnessExpr(existing, state)) {
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
                        self.allocator,
                        rhs_slot,
                        lhs_witness,
                    );
                    return true;
                }
                if (self.currentWitnessExpr(rhs_slot, state)) |rhs_witness| {
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

    // This is the only escape path that turns symbolic match state back into
    // main-theorem expressions. Internal matching and representative work
    // should stay symbolic until a caller explicitly finalizes bindings.
    fn finalizeBoundValue(
        self: *Context,
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
        self: *Context,
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
            .fixed => |expr| expr,
            .dummy => |slot| self.currentWitnessExpr(slot, state),
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.materializeRepresentativeSymbolic(
                        arg,
                        state,
                    )) orelse break :blk null;
                }
                break :blk try self.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn materializeAssignedSymbolic(
        self: *Context,
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
            .dummy => |slot| try self.materializeEscapingWitnessForDummySlot(
                slot,
                state,
            ),
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeFinalSymbolicForEscape(
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

    fn currentWitnessExpr(
        self: *Context,
        slot: usize,
        state: *const MatchSession,
    ) ?ExprId {
        _ = self;
        return state.witnesses.get(slot) orelse
            state.materialized_witnesses.get(slot);
    }

    fn isProvisionalWitnessExpr(
        self: *Context,
        expr_id: ExprId,
        state: *const MatchSession,
    ) bool {
        _ = self;
        return state.provisional_witness_infos.contains(expr_id) or
            state.materialized_witness_infos.contains(expr_id);
    }

    // This is the only main-theorem dummy allocation point in def_ops.zig.
    // Call it only from explicit escape/finalization paths.
    fn materializeEscapingWitnessForDummySlot(
        self: *Context,
        slot: usize,
        state: *MatchSession,
    ) anyerror!ExprId {
        if (state.witnesses.get(slot)) |existing| return existing;
        if (state.materialized_witnesses.get(slot)) |existing| return existing;
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
        try state.materialized_witnesses.put(self.allocator, slot, witness);
        try state.materialized_witness_slots.put(
            self.allocator,
            witness,
            slot,
        );
        try state.materialized_witness_infos.put(
            self.allocator,
            witness,
            info,
        );
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

const NormalizedPlaceholderTarget = union(enum) {
    binder: usize,
    dummy: usize,
};

const NormalizedView = struct {
    mirror: MirroredTheoremContext,
    to_mirror: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,
    placeholder_targets: std.AutoHashMapUnmanaged(
        ExprId,
        NormalizedPlaceholderTarget,
    ) = .empty,
    mirror_binders: []ExprId,
    binder_status: []u8,
    dummy_values: []?ExprId,

    fn init(session: *RuleMatchSession) !NormalizedView {
        var mirror = try MirroredTheoremContext.init(
            session.ctx.allocator,
            session.ctx.theorem,
        );
        errdefer mirror.deinit(session.ctx.allocator);

        const mirror_binders = try session.ctx.allocator.alloc(
            ExprId,
            session.state.bindings.len,
        );
        errdefer session.ctx.allocator.free(mirror_binders);
        const binder_status = try session.ctx.allocator.alloc(
            u8,
            session.state.bindings.len,
        );
        errdefer session.ctx.allocator.free(binder_status);
        const dummy_values = try session.ctx.allocator.alloc(
            ?ExprId,
            session.state.symbolic_dummy_infos.items.len,
        );
        errdefer session.ctx.allocator.free(dummy_values);

        @memset(binder_status, 0);
        @memset(dummy_values, null);

        var view = NormalizedView{
            .mirror = mirror,
            .mirror_binders = mirror_binders,
            .binder_status = binder_status,
            .dummy_values = dummy_values,
        };
        errdefer view.deinit(session.ctx.allocator);

        for (0..session.state.bindings.len) |idx| {
            _ = try view.ensureMirrorBinder(session, idx);
        }
        return view;
    }

    fn deinit(
        self: *NormalizedView,
        allocator: std.mem.Allocator,
    ) void {
        self.to_mirror.deinit(allocator);
        self.placeholder_targets.deinit(allocator);
        allocator.free(self.mirror_binders);
        allocator.free(self.binder_status);
        allocator.free(self.dummy_values);
        self.mirror.deinit(allocator);
    }

    fn ensureMirrorBinder(
        self: *NormalizedView,
        session: *RuleMatchSession,
        idx: usize,
    ) anyerror!ExprId {
        if (idx >= self.mirror_binders.len or idx >= session.rule_args.len) {
            return error.TemplateBinderOutOfRange;
        }
        switch (self.binder_status[idx]) {
            2 => return self.mirror_binders[idx],
            1 => return error.CyclicSymbolicBinding,
            else => {},
        }

        self.binder_status[idx] = 1;
        errdefer self.binder_status[idx] = 0;

        const value = if (session.state.bindings[idx]) |bound| blk: {
            break :blk try session.boundValueToMirror(bound, self);
        } else blk: {
            const sort_id = session.ctx.env.sort_names.get(
                session.rule_args[idx].sort_name,
            ) orelse return error.UnknownSort;
            const placeholder = try self.mirror.theorem.addDummyVarResolved(
                session.rule_args[idx].sort_name,
                sort_id,
            );
            try self.placeholder_targets.put(
                session.ctx.allocator,
                placeholder,
                .{ .binder = idx },
            );
            break :blk placeholder;
        };
        self.mirror_binders[idx] = value;
        self.binder_status[idx] = 2;
        return value;
    }

    fn ensureMirrorDummy(
        self: *NormalizedView,
        session: *RuleMatchSession,
        slot: usize,
    ) anyerror!ExprId {
        if (slot >= self.dummy_values.len) return error.UnknownDummyVar;
        if (self.dummy_values[slot]) |existing| return existing;

        if (session.ctx.currentWitnessExpr(slot, &session.state)) |witness| {
            if (!session.ctx.isProvisionalWitnessExpr(witness, &session.state)) {
                const copied = try copyExprBetweenTheorems(
                    session.ctx.allocator,
                    session.ctx.theorem,
                    &self.mirror.theorem,
                    witness,
                    self.mirror.source_dummy_map,
                    &self.to_mirror,
                );
                self.dummy_values[slot] = copied;
                return copied;
            }
        }

        const info = session.state.symbolic_dummy_infos.items[slot];
        const sort_id = session.ctx.env.sort_names.get(info.sort_name) orelse {
            return error.UnknownSort;
        };
        const placeholder = try self.mirror.theorem.addDummyVarResolved(
            info.sort_name,
            sort_id,
        );
        try self.placeholder_targets.put(
            session.ctx.allocator,
            placeholder,
            .{ .dummy = slot },
        );
        self.dummy_values[slot] = placeholder;
        return placeholder;
    }
};

pub const RuleMatchSession = struct {
    ctx: *Context,
    rule_args: []const ArgInfo,
    state: MatchSession,

    fn init(
        ctx: *Context,
        rule_args: []const ArgInfo,
        seeds: []const BindingSeed,
    ) anyerror!RuleMatchSession {
        var state = try MatchSession.init(
            ctx.allocator,
            seeds.len,
        );
        errdefer state.deinit(ctx.allocator);

        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(ctx.allocator);
        for (seeds, 0..) |seed, idx| {
            state.bindings[idx] = try ctx.boundValueFromSeed(
                seed,
                &state,
                &witness_slots,
            );
        }

        return .{
            .ctx = ctx,
            .rule_args = rule_args,
            .state = state,
        };
    }

    pub fn deinit(self: *RuleMatchSession) void {
        self.state.deinit(self.ctx.allocator);
    }

    pub fn matchTransparent(
        self: *RuleMatchSession,
        template: TemplateExpr,
        actual: ExprId,
    ) anyerror!bool {
        return try self.ctx.matchTemplateRecState(
            template,
            actual,
            &self.state,
        );
    }

    pub fn beginNormalizedComparison(
        self: *RuleMatchSession,
        template: TemplateExpr,
        actual: ExprId,
    ) anyerror!NormalizedComparison {
        var view = try NormalizedView.init(self);
        errdefer view.deinit(self.ctx.allocator);

        const expected_expr = try view.mirror.theorem.instantiateTemplate(
            template,
            view.mirror_binders,
        );
        const actual_expr = try copyExprBetweenTheorems(
            self.ctx.allocator,
            self.ctx.theorem,
            &view.mirror.theorem,
            actual,
            view.mirror.source_dummy_map,
            &view.to_mirror,
        );
        return .{
            .session = self,
            .view = view,
            .expected_expr = expected_expr,
            .actual_expr = actual_expr,
        };
    }

    // This is the session-level escape point. A successful call may
    // materialize main-theorem dummy witnesses so the bindings can outlive the
    // match session.
    pub fn finalizeConcreteBindings(self: *RuleMatchSession) ![]const ExprId {
        const bindings = try self.ctx.allocator.alloc(
            ExprId,
            self.state.bindings.len,
        );
        for (self.state.bindings, 0..) |binding, idx| {
            const bound = binding orelse return error.MissingBinderAssignment;
            bindings[idx] = try self.ctx.finalizeBoundValue(
                bound,
                &self.state,
            );
        }
        return bindings;
    }

    fn boundValueToMirror(
        self: *RuleMatchSession,
        bound: BoundValue,
        view: *NormalizedView,
    ) anyerror!ExprId {
        return switch (bound) {
            .concrete => |concrete| try copyExprBetweenTheorems(
                self.ctx.allocator,
                self.ctx.theorem,
                &view.mirror.theorem,
                (try self.ctx.concreteBindingMatchExpr(
                    concrete,
                    &self.state,
                )) orelse return error.MissingRepresentative,
                view.mirror.source_dummy_map,
                &view.to_mirror,
            ),
            .symbolic => |symbolic| try self.symbolicToMirror(
                symbolic.expr,
                view,
            ),
        };
    }

    fn symbolicToMirror(
        self: *RuleMatchSession,
        symbolic: *const SymbolicExpr,
        view: *NormalizedView,
    ) anyerror!ExprId {
        return switch (symbolic.*) {
            .binder => |idx| try view.ensureMirrorBinder(self, idx),
            .fixed => |expr_id| try copyExprBetweenTheorems(
                self.ctx.allocator,
                self.ctx.theorem,
                &view.mirror.theorem,
                expr_id,
                view.mirror.source_dummy_map,
                &view.to_mirror,
            ),
            .dummy => |slot| try view.ensureMirrorDummy(self, slot),
            .app => |app| blk: {
                const args = try self.ctx.allocator.alloc(
                    ExprId,
                    app.args.len,
                );
                errdefer self.ctx.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.symbolicToMirror(arg, view);
                }
                break :blk try view.mirror.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn matchNormalizedPattern(
        self: *RuleMatchSession,
        view: *const NormalizedView,
        pattern_expr: ExprId,
        actual_expr: ExprId,
    ) anyerror!bool {
        if (view.placeholder_targets.get(pattern_expr)) |target| {
            return try self.assignNormalizedTarget(target, actual_expr, view);
        }

        if (!view.placeholder_targets.contains(actual_expr)) {
            const pattern_concrete =
                try self.mirrorExprToConcrete(pattern_expr, view);
            const actual_concrete =
                try self.mirrorExprToConcrete(actual_expr, view);
            if (pattern_concrete != null and actual_concrete != null) {
                const pattern_repr = try self.ctx.chooseRepresentativeSymbolic(
                    pattern_concrete.?,
                    &self.state,
                    .normalized,
                );
                const actual_repr = try self.ctx.chooseRepresentativeSymbolic(
                    actual_concrete.?,
                    &self.state,
                    .normalized,
                );
                if (self.ctx.symbolicExprEql(pattern_repr, actual_repr)) {
                    return true;
                }
            }
        }

        const pattern_node = view.mirror.theorem.interner.node(pattern_expr);
        const actual_node = view.mirror.theorem.interner.node(actual_expr);
        return switch (pattern_node.*) {
            .variable => switch (actual_node.*) {
                .variable => pattern_expr == actual_expr,
                .app => false,
            },
            .app => |pattern_app| switch (actual_node.*) {
                .variable => false,
                .app => |actual_app| blk: {
                    if (pattern_app.term_id != actual_app.term_id) {
                        break :blk false;
                    }
                    if (pattern_app.args.len != actual_app.args.len) {
                        break :blk false;
                    }
                    for (pattern_app.args, actual_app.args) |pattern_arg, actual_arg| {
                        if (!try self.matchNormalizedPattern(
                            view,
                            pattern_arg,
                            actual_arg,
                        )) {
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
            },
        };
    }

    fn assignNormalizedTarget(
        self: *RuleMatchSession,
        target: NormalizedPlaceholderTarget,
        actual_expr: ExprId,
        view: *const NormalizedView,
    ) anyerror!bool {
        if (view.placeholder_targets.get(actual_expr)) |actual_target| {
            if (samePlaceholderTarget(target, actual_target)) return true;
        }

        const translated = try self.mirrorExprToBoundValue(actual_expr, view);
        return switch (target) {
            .binder => |idx| blk: {
                if (translated == .symbolic and
                    self.symbolicContainsBinder(translated.symbolic.expr, idx))
                {
                    break :blk false;
                }
                break :blk try self.ctx.assignBinderValue(
                    idx,
                    translated,
                    &self.state,
                );
            },
            .dummy => |slot| blk: {
                if (translated == .symbolic and
                    self.symbolicContainsDummy(translated.symbolic.expr, slot))
                {
                    break :blk false;
                }
                const info = self.state.symbolic_dummy_infos.items[slot];
                break :blk switch (translated) {
                    .concrete => |concrete| blk_inner: {
                        const actual = (try self.ctx.concreteBindingMatchExpr(
                            concrete,
                            &self.state,
                        )) orelse break :blk_inner false;
                        break :blk_inner try self.ctx.matchSymbolicDummyState(
                            slot,
                            info,
                            actual,
                            &self.state,
                        );
                    },
                    .symbolic => |symbolic| try self.ctx.matchDummyToSymbolic(
                        slot,
                        symbolic.expr,
                        &self.state,
                    ),
                };
            },
        };
    }

    fn mirrorExprToBoundValue(
        self: *RuleMatchSession,
        expr_id: ExprId,
        view: *const NormalizedView,
    ) anyerror!BoundValue {
        if (try self.mirrorExprToConcrete(expr_id, view)) |concrete| {
            return try self.ctx.makeConcreteBoundValue(
                concrete,
                &self.state,
                .normalized,
            );
        }
        return self.ctx.makeSymbolicBoundValue(
            try self.mirrorExprToSymbolic(expr_id, view),
            .normalized,
        );
    }

    fn mirrorExprToConcrete(
        self: *RuleMatchSession,
        expr_id: ExprId,
        view: *const NormalizedView,
    ) anyerror!?ExprId {
        if (view.placeholder_targets.contains(expr_id)) return null;

        return switch (view.mirror.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| blk: {
                    if (idx >= self.ctx.theorem.theorem_vars.items.len) {
                        return error.UnknownTheoremVariable;
                    }
                    break :blk self.ctx.theorem.theorem_vars.items[idx];
                },
                .dummy_var => |idx| blk: {
                    if (idx >= view.mirror.mirror_dummy_map.len) {
                        return error.UnknownDummyVar;
                    }
                    break :blk view.mirror.mirror_dummy_map[idx];
                },
            },
            .app => |app| blk: {
                const args = try self.ctx.allocator.alloc(ExprId, app.args.len);
                errdefer self.ctx.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.mirrorExprToConcrete(arg, view)) orelse {
                        self.ctx.allocator.free(args);
                        break :blk null;
                    };
                }
                break :blk try self.ctx.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn mirrorExprToSymbolic(
        self: *RuleMatchSession,
        expr_id: ExprId,
        view: *const NormalizedView,
    ) anyerror!*const SymbolicExpr {
        if (view.placeholder_targets.get(expr_id)) |target| {
            return switch (target) {
                .binder => |idx| try self.ctx.allocSymbolic(.{ .binder = idx }),
                .dummy => |slot| try self.ctx.allocSymbolic(.{ .dummy = slot }),
            };
        }

        return switch (view.mirror.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| blk: {
                    if (idx >= self.ctx.theorem.theorem_vars.items.len) {
                        return error.UnknownTheoremVariable;
                    }
                    break :blk try self.ctx.allocSymbolic(.{ .fixed = self.ctx.theorem.theorem_vars.items[idx] });
                },
                .dummy_var => |idx| blk: {
                    if (idx >= view.mirror.mirror_dummy_map.len) {
                        return error.UnknownDummyVar;
                    }
                    break :blk try self.ctx.allocSymbolic(.{ .fixed = view.mirror.mirror_dummy_map[idx] });
                },
            },
            .app => |app| blk: {
                const args = try self.ctx.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                errdefer self.ctx.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.mirrorExprToSymbolic(arg, view);
                }
                break :blk try self.ctx.allocSymbolic(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        };
    }

    fn symbolicContainsBinder(
        self: *RuleMatchSession,
        symbolic: *const SymbolicExpr,
        target: usize,
    ) bool {
        return switch (symbolic.*) {
            .binder => |idx| idx == target,
            .fixed => false,
            .dummy => false,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.symbolicContainsBinder(arg, target)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
        };
    }

    fn symbolicContainsDummy(
        self: *RuleMatchSession,
        symbolic: *const SymbolicExpr,
        target: usize,
    ) bool {
        return switch (symbolic.*) {
            .binder => false,
            .fixed => false,
            .dummy => |slot| slot == target,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.symbolicContainsDummy(arg, target)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
        };
    }
};

pub const NormalizedComparison = struct {
    session: *RuleMatchSession,
    view: NormalizedView,
    expected_expr: ExprId,
    actual_expr: ExprId,

    pub fn deinit(self: *NormalizedComparison) void {
        self.view.deinit(self.session.ctx.allocator);
    }

    pub fn mirrorTheorem(self: *NormalizedComparison) *TheoremContext {
        return &self.view.mirror.theorem;
    }

    pub fn finish(
        self: *NormalizedComparison,
        normalized_expected: ExprId,
        normalized_actual: ExprId,
    ) anyerror!bool {
        return try self.session.matchNormalizedPattern(
            &self.view,
            normalized_expected,
            normalized_actual,
        );
    }
};

fn samePlaceholderTarget(
    lhs: NormalizedPlaceholderTarget,
    rhs: NormalizedPlaceholderTarget,
) bool {
    return switch (lhs) {
        .binder => |idx| switch (rhs) {
            .binder => |rhs_idx| idx == rhs_idx,
            .dummy => false,
        },
        .dummy => |idx| switch (rhs) {
            .binder => false,
            .dummy => |rhs_idx| idx == rhs_idx,
        },
    };
}

fn findDummyBinding(bindings: []const DummyBinding, slot: usize) ?ExprId {
    for (bindings) |binding| {
        if (binding.slot == slot) return binding.actual;
    }
    return null;
}

const SessionWitnessFixture = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    theorem: TheoremContext,
    actual: ExprId,
    raw: ExprId,
    rule_args: []const ArgInfo,
    body: TemplateExpr,
    dummy_arg_count: usize,

    fn init() !SessionWitnessFixture {
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort mor;
            \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
            \\term all {x: mor} (p: wff x): wff; prefix all: $A.$ prec 41;
            \\term mor_eq (f g: mor): wff; infixl mor_eq: $~$ prec 15;
            \\term comp (f g: mor): mor; infixl comp: $o$ prec 35;
            \\def mono {.a .b: mor} (f: mor): wff =
            \\  $ A. a A. b ((f o a ~ f o b) -> (a ~ b)) $;
            \\theorem host (f: mor): $ mono f $;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        errdefer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        var env = GlobalEnv.init(arena.allocator());
        var theorem = TheoremContext.init(arena.allocator());
        errdefer theorem.deinit();
        var theorem_vars = std.StringHashMap(*const Expr).init(
            arena.allocator(),
        );
        defer theorem_vars.deinit();

        var actual: ?ExprId = null;
        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |assertion| {
                    if (!std.mem.eql(u8, assertion.name, "host")) continue;
                    try theorem.seedAssertion(assertion);
                    actual = try theorem.internParsedExpr(assertion.concl);
                    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
                        if (name) |actual_name| {
                            try theorem_vars.put(actual_name, expr);
                        }
                    }
                },
                else => {},
            }
        }

        const raw_expr = try parser.parseFormulaText(
            " A. x A. y ((f o x ~ f o y) -> (x ~ y)) ",
            &theorem_vars,
        );
        const raw = try theorem.internParsedExpr(raw_expr);

        const mono_id = env.term_names.get("mono") orelse {
            return error.MissingTerm;
        };
        const mono = env.terms.items[mono_id];
        const body = mono.body orelse return error.MissingTermBody;
        const rule_args = try arena.allocator().alloc(
            ArgInfo,
            mono.args.len + mono.dummy_args.len,
        );
        @memcpy(rule_args[0..mono.args.len], mono.args);
        @memcpy(rule_args[mono.args.len..], mono.dummy_args);

        return .{
            .arena = arena,
            .env = env,
            .theorem = theorem,
            .actual = actual orelse return error.MissingAssertion,
            .raw = raw,
            .rule_args = rule_args,
            .body = body,
            .dummy_arg_count = mono.dummy_args.len,
        };
    }

    fn deinit(self: *SessionWitnessFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }
};

fn allocNoneSeeds(
    allocator: std.mem.Allocator,
    len: usize,
) ![]BindingSeed {
    const seeds = try allocator.alloc(BindingSeed, len);
    for (seeds) |*seed| {
        seed.* = .none;
    }
    return seeds;
}

test "match sessions keep witness placeholders session-local" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "fresh match sessions start with fresh witness namespaces" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds1 = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session1 = try ctx.beginRuleMatch(fixture.rule_args, seeds1);
    defer session1.deinit();
    try std.testing.expect(
        try session1.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        session1.state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(usize, 0), session1.state.witnesses.count());

    const seeds2 = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session2 = try ctx.beginRuleMatch(fixture.rule_args, seeds2);
    defer session2.deinit();
    try std.testing.expect(
        try session2.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        session2.state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(@as(usize, 0), session2.state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "representative computation stays symbolic inside one session" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const first = try ctx.chooseRepresentativeSymbolic(
        fixture.raw,
        &state,
        .transparent,
    );
    try std.testing.expectEqual(
        fixture.actual,
        try ctx.chooseRepresentative(fixture.raw, .transparent),
    );

    const cache_count = state.transparent_representatives.count();
    const second = try ctx.chooseRepresentativeSymbolic(
        fixture.raw,
        &state,
        .transparent,
    );

    try std.testing.expect(first == second);
    try std.testing.expectEqual(
        cache_count,
        state.transparent_representatives.count(),
    );
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "repeated transparent comparison through defs stays symbolic" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    for (0..32) |_| {
        try std.testing.expect(
            (try ctx.compareTransparent(fixture.raw, fixture.actual)) != null,
        );
    }

    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "finalization materializes escaping witnesses exactly once" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();

    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const first = try session.finalizeConcreteBindings();
    try std.testing.expectEqual(
        start_dummy_id + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_id,
    );
    try std.testing.expectEqual(
        start_dummy_dep + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        fixture.theorem.theorem_dummies.items.len,
    );

    const second = try session.finalizeConcreteBindings();
    try std.testing.expectEqual(
        start_dummy_id + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_id,
    );
    try std.testing.expectEqual(
        start_dummy_dep + fixture.dummy_arg_count,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        fixture.dummy_arg_count,
        fixture.theorem.theorem_dummies.items.len,
    );
    try std.testing.expectEqual(first.len, second.len);
    for (first, second) |lhs, rhs| {
        try std.testing.expectEqual(lhs, rhs);
    }
}

test "abandoning a matched session leaves theorem dummy state unchanged" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    {
        var ctx = Context.init(
            fixture.arena.allocator(),
            &fixture.theorem,
            &fixture.env,
        );
        defer ctx.deinit();

        const seeds = try allocNoneSeeds(
            fixture.arena.allocator(),
            fixture.rule_args.len,
        );
        var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
        defer session.deinit();

        try std.testing.expect(
            try session.matchTransparent(fixture.body, fixture.actual),
        );
    }

    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
    try std.testing.expectEqual(
        @as(usize, 0),
        fixture.theorem.theorem_dummies.items.len,
    );
}

test "many sessions only spend theorem dummies on escaped results" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var finalized_sessions: usize = 0;
    for (0..40) |idx| {
        {
            const seeds = try allocNoneSeeds(
                fixture.arena.allocator(),
                fixture.rule_args.len,
            );
            var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
            defer session.deinit();

            try std.testing.expect(
                try session.matchTransparent(fixture.body, fixture.actual),
            );
            try std.testing.expect(
                (try ctx.compareTransparent(fixture.raw, fixture.actual)) != null,
            );

            if (idx % 3 == 0) {
                _ = try session.finalizeConcreteBindings();
                finalized_sessions += 1;
            }
        }

        const expected = finalized_sessions * fixture.dummy_arg_count;
        try std.testing.expectEqual(
            expected,
            fixture.theorem.theorem_dummies.items.len,
        );
        try std.testing.expectEqual(
            @as(u32, @intCast(expected)),
            fixture.theorem.next_dummy_id,
        );
        try std.testing.expectEqual(
            @as(u32, @intCast(expected)),
            fixture.theorem.next_dummy_dep,
        );
    }
}

test "real escape-point exhaustion stays explicit under repeated finalization" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    const limit = @as(usize, @intCast(@import("./compiler_expr.zig")
        .tracked_bound_dep_limit));

    while (fixture.theorem.theorem_dummies.items.len +
        fixture.dummy_arg_count < limit)
    {
        {
            const seeds = try allocNoneSeeds(
                fixture.arena.allocator(),
                fixture.rule_args.len,
            );
            var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
            defer session.deinit();
            try std.testing.expect(
                try session.matchTransparent(fixture.body, fixture.actual),
            );
            _ = try session.finalizeConcreteBindings();
        }
    }

    try std.testing.expectEqual(limit - 1, fixture.theorem.next_dummy_dep);
    try std.testing.expectEqual(
        limit - 1,
        fixture.theorem.theorem_dummies.items.len,
    );

    const seeds = try allocNoneSeeds(
        fixture.arena.allocator(),
        fixture.rule_args.len,
    );
    var session = try ctx.beginRuleMatch(fixture.rule_args, seeds);
    defer session.deinit();
    try std.testing.expect(
        try session.matchTransparent(fixture.body, fixture.actual),
    );
    try std.testing.expectError(
        error.DependencySlotExhausted,
        session.finalizeConcreteBindings(),
    );
    try std.testing.expectEqual(limit, fixture.theorem.next_dummy_dep);
    try std.testing.expectEqual(
        limit,
        fixture.theorem.theorem_dummies.items.len,
    );
}

test "transparent and normalized representative caches stay separate" {
    var fixture = try SessionWitnessFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    const transparent = try ctx.chooseRepresentativeSymbolic(
        fixture.actual,
        &state,
        .transparent,
    );
    const normalized = try ctx.chooseRepresentativeSymbolic(
        fixture.actual,
        &state,
        .normalized,
    );

    try std.testing.expect(transparent != normalized);
    try std.testing.expectEqual(
        transparent,
        state.transparent_representatives.get(fixture.actual).?,
    );
    try std.testing.expectEqual(
        normalized,
        state.normalized_representatives.get(fixture.actual).?,
    );
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}
