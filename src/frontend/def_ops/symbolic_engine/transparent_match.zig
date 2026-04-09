const std = @import("std");
const TermDecl = @import("../../env.zig").TermDecl;
const ExprId = @import("../../expr.zig").ExprId;
const ExprApp = @import("../../expr.zig").ExprNode.App;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const AcuiSupport = @import("../../acui_support.zig");
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const WitnessState = @import("./witness_state.zig");

const ConversionPlan = Types.ConversionPlan;
const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const MatchSession = MatchState.MatchSession;
const semantic_match_budget: usize = 8;

pub fn defCoversItem(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
) anyerror!bool {
    return (try planDefCoversItem(self, def_expr, item_expr)) != null;
}

pub fn planDefCoversItem(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
) anyerror!?*const ConversionPlan {
    return try planDefToTarget(self, def_expr, item_expr, .lhs);
}

pub fn instantiateDefTowardAcuiItem(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
    head_term_id: u32,
) anyerror!?ExprId {
    _ = getConcreteDef(self, def_expr) orelse return null;
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    if (!try matchSymbolicAcuiLeafToExprState(
        self,
        symbolic,
        item_expr,
        head_term_id,
        &session,
    ) and !try self.matchSymbolicAcuiLeafToExprSemantic(
        symbolic,
        item_expr,
        head_term_id,
        &session,
        semantic_match_budget,
    )) {
        return null;
    }
    return try WitnessState.materializeFinalSymbolic(
        self,
        symbolic,
        &session,
    );
}

pub fn planDefToTarget(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
    side: enum { lhs, rhs },
) anyerror!?*const ConversionPlan {
    const witness = try instantiateDefTowardExpr(self, def_expr, target_expr) orelse {
        return null;
    };
    const next = try compareTransparent(self, witness, target_expr) orelse {
        return null;
    };
    return switch (side) {
        .lhs => try allocPlan(self, .{ .unfold_lhs = .{
            .witness = witness,
            .next = next,
        } }),
        .rhs => try allocPlan(self, .{ .unfold_rhs = .{
            .witness = witness,
            .next = next,
        } }),
    };
}

pub fn compareTransparent(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?*const ConversionPlan {
    if (lhs == rhs) {
        return try allocPlan(self, .refl);
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
                children[idx] = try compareTransparent(
                    self,
                    lhs_arg,
                    rhs_arg,
                ) orelse {
                    return null;
                };
            }
            return try allocPlan(self, .{ .cong = .{ .children = children } });
        }
    }

    if (try planDefToTarget(self, lhs, rhs, .lhs)) |plan| {
        return plan;
    }
    if (try planDefToTarget(self, rhs, lhs, .rhs)) |plan| {
        return plan;
    }
    return null;
}

pub fn matchTemplateTransparent(
    self: anytype,
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
            try WitnessState.rebuildBoundValue(
                self,
                expr_id,
                &state,
                &witness_slots,
                .exact,
            )
        else
            null;
    }

    if (!try matchTemplateRecState(self, template, actual, &state)) {
        return false;
    }
    try WitnessState.representResolvedBindings(self, &state, bindings);
    return true;
}

pub fn instantiateDefTowardExpr(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    _ = getConcreteDef(self, def_expr) orelse return null;

    if (try instantiateDefTowardExprViaSearch(
        self,
        def_expr,
        target_expr,
    )) |witness| {
        return witness;
    }
    return try instantiateDefTowardExprViaTargetGuidance(
        self,
        def_expr,
        target_expr,
    );
}

pub fn instantiateDefTowardExprViaSearch(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    if (!try matchSymbolicToExprState(
        self,
        symbolic,
        target_expr,
        &session,
    ) and !try self.matchSymbolicToExprSemantic(
        symbolic,
        target_expr,
        &session,
        semantic_match_budget,
    )) {
        return null;
    }
    return try WitnessState.materializeResolvedSymbolic(
        self,
        symbolic,
        &session,
    );
}

pub fn instantiateDefTowardExprViaTargetGuidance(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    while (true) {
        if (try WitnessState.materializeResolvedSymbolic(
            self,
            symbolic,
            &session,
        )) |witness| {
            return witness;
        }
        if (!try guideSymbolicWitnessesFromTarget(
            self,
            symbolic,
            target_expr,
            &session,
        )) {
            return null;
        }
    }
}

pub fn guideSymbolicWitnessesFromTarget(
    self: anytype,
    symbolic: *const SymbolicExpr,
    target_expr: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const symbolic_app = switch (symbolic.*) {
        .app => |app| app,
        else => return false,
    };
    const target_node = self.shared.theorem.interner.node(target_expr);
    const target_app = switch (target_node.*) {
        .app => |app| app,
        .variable => return try guideSymbolicWitnessesFromAcuiTarget(
            self,
            symbolic,
            target_expr,
            state,
        ),
    };

    if (symbolic_app.term_id == target_app.term_id and
        symbolic_app.args.len == target_app.args.len)
    {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        var made_progress = false;
        var same_head_failed = false;
        for (symbolic_app.args, target_app.args) |symbolic_arg, target_arg| {
            if (try tryMatchSymbolicToExprDirect(
                self,
                symbolic_arg,
                target_arg,
                state,
            )) {
                continue;
            }
            if (!try guideSymbolicWitnessesFromTarget(
                self,
                symbolic_arg,
                target_arg,
                state,
            )) {
                same_head_failed = true;
                break;
            }
            made_progress = true;
        }
        if (!same_head_failed) {
            if (made_progress) return true;
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        } else {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        }
    }

    return try guideSymbolicWitnessesFromAcuiTarget(
        self,
        symbolic,
        target_expr,
        state,
    );
}

pub fn guideSymbolicWitnessesFromAcuiTarget(
    self: anytype,
    symbolic: *const SymbolicExpr,
    target_expr: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const registry = self.shared.registry orelse return false;
    const symbolic_sort = WitnessState.symbolicSortName(self, symbolic, state) orelse {
        return false;
    };
    const acui = registry.resolveStructuralCombinerForSort(
        self.shared.env,
        symbolic_sort,
    ) orelse return false;

    var support = AcuiSupport.Context.init(
        self.shared.allocator,
        self.shared.theorem,
        self.shared.env,
        registry,
    );
    if (!support.exprMatchesCombinerSort(target_expr, acui)) return false;

    var items = std.ArrayListUnmanaged(ExprId){};
    defer items.deinit(self.shared.allocator);
    try support.collectConcreteSetItems(
        target_expr,
        acui.head_term_id,
        acui.unit_term_id,
        &items,
    );

    for (items.items) |item_expr| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        if (!try matchSymbolicAcuiLeafToExprState(
            self,
            symbolic,
            item_expr,
            acui.head_term_id,
            state,
        ) and !try self.matchSymbolicAcuiLeafToExprSemantic(
            symbolic,
            item_expr,
            acui.head_term_id,
            state,
            semantic_match_budget,
        )) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        }
        return true;
    }
    return false;
}

pub fn matchTemplateRecState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    return switch (template) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromExpr(
                self,
                idx,
                actual,
                state,
                .transparent,
            );
        },
        .app => |app| blk: {
            if (try matchTemplateAppDirectState(self, app, actual, state)) {
                break :blk true;
            }

            if (try matchExpandedTemplateAppState(self, app, actual, state)) {
                break :blk true;
            }

            if (try matchActualDefToTemplateState(
                self,
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

pub fn matchTemplateAppDirectState(
    self: anytype,
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

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
        if (!try matchTemplateRecState(self, tmpl_arg, actual_arg, state)) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
    }
    return true;
}

pub fn matchExpandedTemplateAppState(
    self: anytype,
    app: TemplateExpr.App,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    const symbolic = try expandTemplateApp(self, app, state) orelse return false;
    if (try matchSymbolicToExprState(self, symbolic, actual, state)) {
        return true;
    }

    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

pub fn matchActualDefToTemplateState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    _ = getConcreteDef(self, actual) orelse return false;

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    const symbolic_template = try symbolicFromTemplate(self, template);
    const symbolic_actual = try expandConcreteDef(self, actual, state) orelse {
        return false;
    };
    if (try matchSymbolicToSymbolicState(
        self,
        symbolic_template,
        symbolic_actual,
        state,
    )) {
        return true;
    }

    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

pub fn matchSymbolicToExprState(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromExpr(
                self,
                idx,
                actual,
                state,
                .transparent,
            );
        },
        .fixed => |expr_id| {
            return (try compareTransparent(self, expr_id, actual)) != null;
        },
        .dummy => |slot| {
            const info = state.symbolic_dummy_infos.items[slot];
            return try WitnessState.matchSymbolicDummyState(
                self,
                slot,
                info,
                actual,
                state,
            );
        },
        .app => |app| {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            const actual_node = self.shared.theorem.interner.node(actual);
            if (actual_node.* == .app) {
                const actual_app = actual_node.app;
                if (actual_app.term_id == app.term_id and
                    actual_app.args.len == app.args.len)
                {
                    for (app.args, actual_app.args) |sym_arg, actual_arg| {
                        if (!try matchSymbolicToExprState(
                            self,
                            sym_arg,
                            actual_arg,
                            state,
                        )) {
                            try WitnessState.restoreMatchSnapshot(
                                self,
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

            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

            if (try expandSymbolicApp(self, app, state)) |expanded| {
                if (try matchSymbolicToExprState(
                    self,
                    expanded,
                    actual,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }

            if (try expandConcreteDef(self, actual, state)) |expanded_actual| {
                if (try matchSymbolicToSymbolicState(
                    self,
                    symbolic,
                    expanded_actual,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
            return false;
        },
    };
}

pub fn matchExprToSymbolic(
    self: anytype,
    actual: ExprId,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    assign_mode: BindingMode,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromExpr(
                self,
                idx,
                actual,
                state,
                assign_mode,
            );
        },
        .fixed => |expr_id| {
            return (try compareTransparent(self, actual, expr_id)) != null;
        },
        .dummy => |slot| {
            const info = state.symbolic_dummy_infos.items[slot];
            return try WitnessState.matchSymbolicDummyState(
                self,
                slot,
                info,
                actual,
                state,
            );
        },
        .app => |app| {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            const actual_node = self.shared.theorem.interner.node(actual);
            if (actual_node.* == .app) {
                const actual_app = actual_node.app;
                if (actual_app.term_id == app.term_id and
                    actual_app.args.len == app.args.len)
                {
                    for (actual_app.args, app.args) |actual_arg, sym_arg| {
                        if (!try matchExprToSymbolic(
                            self,
                            actual_arg,
                            sym_arg,
                            state,
                            assign_mode,
                        )) {
                            try WitnessState.restoreMatchSnapshot(
                                self,
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

            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

            if (try expandConcreteDef(self, actual, state)) |expanded_actual| {
                if (try matchSymbolicToSymbolicState(
                    self,
                    expanded_actual,
                    symbolic,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }

            if (try expandSymbolicApp(self, app, state)) |expanded| {
                if (try matchExprToSymbolic(
                    self,
                    actual,
                    expanded,
                    state,
                    assign_mode,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
            return false;
        },
    };
}

pub fn matchSymbolicToSymbolicState(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    return switch (lhs.*) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromSymbolic(
                self,
                idx,
                rhs,
                state,
                .transparent,
            );
        },
        .fixed => |expr_id| {
            return try matchExprToSymbolic(
                self,
                expr_id,
                rhs,
                state,
                .transparent,
            );
        },
        .dummy => |slot| {
            return try WitnessState.matchDummyToSymbolic(self, slot, rhs, state);
        },
        .app => |lhs_app| {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            if (rhs.* == .app) {
                const rhs_app = rhs.app;
                if (lhs_app.term_id == rhs_app.term_id and
                    lhs_app.args.len == rhs_app.args.len)
                {
                    for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                        if (!try matchSymbolicToSymbolicState(
                            self,
                            lhs_arg,
                            rhs_arg,
                            state,
                        )) {
                            try WitnessState.restoreMatchSnapshot(
                                self,
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

            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

            if (try expandSymbolicApp(self, lhs_app, state)) |expanded_lhs| {
                if (try matchSymbolicToSymbolicState(
                    self,
                    expanded_lhs,
                    rhs,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
            if (rhs.* == .app) {
                if (try expandSymbolicApp(self, rhs.app, state)) |expanded_rhs| {
                    if (try matchSymbolicToSymbolicState(
                        self,
                        lhs,
                        expanded_rhs,
                        state,
                    )) {
                        return true;
                    }
                    try WitnessState.restoreMatchSnapshot(
                        self,
                        &snapshot,
                        state,
                    );
                }
            }
            return false;
        },
    };
}

pub fn tryMatchTemplateStateDirect(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchTemplateRecState(self, template, actual, state)) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

pub fn tryMatchSymbolicToExprDirect(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchSymbolicToExprState(self, symbolic, actual, state)) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}
pub fn matchSymbolicAcuiLeafToExprState(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    head_term_id: u32,
    state: *MatchSession,
) anyerror!bool {
    switch (symbolic.*) {
        .app => |app| {
            if (app.term_id == head_term_id and app.args.len == 2) {
                var snapshot = try WitnessState.saveMatchSnapshot(self, state);
                defer WitnessState.deinitMatchSnapshot(self, &snapshot);

                if (try matchSymbolicAcuiLeafToExprState(
                    self,
                    app.args[0],
                    actual,
                    head_term_id,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                if (try matchSymbolicAcuiLeafToExprState(
                    self,
                    app.args[1],
                    actual,
                    head_term_id,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                return false;
            }
        },
        else => {},
    }
    return try tryMatchSymbolicToExprDirect(self, symbolic, actual, state);
}

pub fn expandTemplateApp(
    self: anytype,
    app: TemplateExpr.App,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const term = getOpenableTerm(self, app.term_id) orelse return null;
    const body = term.body orelse return null;

    const subst = try self.shared.allocator.alloc(
        *const SymbolicExpr,
        term.args.len + term.dummy_args.len,
    );
    for (app.args, 0..) |arg, idx| {
        subst[idx] = try symbolicFromTemplate(self, arg);
    }
    for (term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = state.symbolic_dummy_infos.items.len;
        try state.symbolic_dummy_infos.append(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
        });
        subst[term.args.len + idx] = try self.allocSymbolic(
            .{ .dummy = slot },
        );
    }
    return try symbolicFromTemplateSubst(self, body, subst);
}

pub fn expandConcreteDef(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const def = getConcreteDef(self, expr_id) orelse return null;

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
            .bound = dummy_arg.bound,
        });
        subst[def.term.args.len + idx] = try self.allocSymbolic(
            .{ .dummy = slot },
        );
    }
    return try symbolicFromTemplateSubst(self, def.body, subst);
}

pub fn expandSymbolicApp(
    self: anytype,
    app: SymbolicExpr.App,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const term = getOpenableTerm(self, app.term_id) orelse return null;
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
            .bound = dummy_arg.bound,
        });
        subst[term.args.len + idx] = try self.allocSymbolic(
            .{ .dummy = slot },
        );
    }
    return try symbolicFromTemplateSubst(self, body, subst);
}

pub fn symbolicFromTemplate(
    self: anytype,
    template: TemplateExpr,
) anyerror!*const SymbolicExpr {
    return try symbolicFromTemplateSubst(self, template, null);
}

pub fn symbolicFromTemplateSubst(
    self: anytype,
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
                args[idx] = try symbolicFromTemplateSubst(self, arg, subst);
            }
            return try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = args,
            } });
        },
    }
}

pub fn getConcreteDef(self: anytype, expr_id: ExprId) ?struct {
    app: ExprApp,
    term: *const TermDecl,
    body: TemplateExpr,
} {
    const node = self.shared.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
    };
    const term = getOpenableTerm(self, app.term_id) orelse return null;
    const body = term.body orelse return null;
    return .{
        .app = app,
        .term = term,
        .body = body,
    };
}

pub fn getOpenableTerm(self: anytype, term_id: u32) ?*const TermDecl {
    if (term_id >= self.shared.env.terms.items.len) return null;
    const term = &self.shared.env.terms.items[term_id];
    if (!term.is_def or term.body == null) return null;
    return term;
}

pub fn allocPlan(
    self: anytype,
    plan: ConversionPlan,
) anyerror!*const ConversionPlan {
    const node = try self.shared.allocator.create(ConversionPlan);
    node.* = plan;
    return node;
}
