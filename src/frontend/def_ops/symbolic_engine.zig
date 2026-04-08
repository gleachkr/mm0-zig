const std = @import("std");
const TermDecl = @import("../compiler_env.zig").TermDecl;
const ExprId = @import("../compiler_expr.zig").ExprId;
const ExprApp = @import("../compiler_expr.zig").ExprNode.App;
const TemplateExpr = @import("../compiler_rules.zig").TemplateExpr;
const Canonicalizer = @import("../canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("../acui_support.zig");
const RewriteRule = @import("../rewrite_registry.zig").RewriteRule;
const ResolvedStructuralCombiner =
    @import("../rewrite_registry.zig").ResolvedStructuralCombiner;
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
const DummyAliasMap = Types.DummyAliasMap;
const ProvisionalWitnessInfoMap = Types.ProvisionalWitnessInfoMap;
const MaterializedWitnessInfoMap = Types.MaterializedWitnessInfoMap;
const RepresentativeCache = Types.RepresentativeCache;
const MatchSession = MatchState.MatchSession;
const MatchSnapshot = MatchState.MatchSnapshot;
const ConcreteVarInfo = Types.ConcreteVarInfo;
const semantic_match_budget: usize = 8;

pub const SemanticStepCandidate = union(enum) {
    unfold_concrete_def: struct {
        expr_id: ExprId,
        term_id: u32,
    },
    unfold_symbolic_def: struct {
        term_id: u32,
    },
    rewrite_rule: RewriteRule,
    acui: ResolvedStructuralCombiner,
};

const SemanticSearchKey = struct {
    lhs_hash: u64,
    rhs_hash: u64,
    state_hash: u64,
};

const SemanticSearchVisited =
    std.AutoHashMapUnmanaged(SemanticSearchKey, usize);

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
        _ = self.getConcreteDef(def_expr) orelse return null;
        var session = try MatchSession.init(self.shared.allocator, 0);
        defer session.deinit(self.shared.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        if (!try self.matchSymbolicAcuiLeafToExprState(
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
        return try self.materializeFinalSymbolic(
            symbolic,
            &session,
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

    pub fn collectSemanticStepCandidatesExpr(
        self: *SymbolicEngine,
        expr_id: ExprId,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        const node = self.shared.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return,
        };

        if (self.getOpenableTerm(app.term_id) != null) {
            try out.append(self.shared.allocator, .{
                .unfold_concrete_def = .{
                    .expr_id = expr_id,
                    .term_id = app.term_id,
                },
            });
        }
        try self.appendSemanticHeadStepCandidates(app.term_id, out);
    }

    pub fn collectSemanticStepCandidatesSymbolic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        switch (symbolic.*) {
            .fixed => |expr_id| {
                return try self.collectSemanticStepCandidatesExpr(expr_id, out);
            },
            .app => |app| {
                if (self.getOpenableTerm(app.term_id) != null) {
                    try out.append(self.shared.allocator, .{
                        .unfold_symbolic_def = .{
                            .term_id = app.term_id,
                        },
                    });
                }
                try self.appendSemanticHeadStepCandidates(app.term_id, out);
            },
            .binder, .dummy => {},
        }
    }

    fn appendSemanticHeadStepCandidates(
        self: *SymbolicEngine,
        head_term_id: u32,
        out: *std.ArrayListUnmanaged(SemanticStepCandidate),
    ) anyerror!void {
        const registry = self.shared.registry orelse return;
        for (registry.getRewriteRules(head_term_id)) |rule| {
            try out.append(self.shared.allocator, .{ .rewrite_rule = rule });
        }
        if (registry.resolveStructuralCombiner(
            self.shared.env,
            head_term_id,
        )) |acui| {
            try out.append(self.shared.allocator, .{ .acui = acui });
        }
    }

    pub fn matchTemplateSemanticState(
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        if (try self.tryMatchTemplateStateDirect(template, actual, state)) {
            return true;
        }

        var visited: SemanticSearchVisited = .empty;
        defer visited.deinit(self.shared.allocator);
        const symbolic = try self.symbolicFromTemplate(template);
        return try self.matchSymbolicToExprSemanticSearch(
            symbolic,
            actual,
            state,
            budget,
            &visited,
        );
    }

    pub fn matchSymbolicToExprSemantic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var visited: SemanticSearchVisited = .empty;
        defer visited.deinit(self.shared.allocator);
        return try self.matchSymbolicToExprSemanticSearch(
            symbolic,
            actual,
            state,
            budget,
            &visited,
        );
    }

    pub fn matchExprToSymbolicSemantic(
        self: *SymbolicEngine,
        actual: ExprId,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var visited: SemanticSearchVisited = .empty;
        defer visited.deinit(self.shared.allocator);
        return try self.matchExprToSymbolicSemanticSearch(
            actual,
            symbolic,
            state,
            budget,
            &visited,
        );
    }

    pub fn matchSymbolicToSymbolicSemantic(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var visited: SemanticSearchVisited = .empty;
        defer visited.deinit(self.shared.allocator);
        return try self.matchSymbolicToSymbolicSemanticSearch(
            lhs,
            rhs,
            state,
            budget,
            &visited,
        );
    }

    fn matchSymbolicToExprSemanticSearch(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        if (try self.tryMatchSymbolicToExprDirect(symbolic, actual, state)) {
            return true;
        }
        if (budget == 0) return false;
        if (!try self.noteSemanticExprSearchState(
            symbolic,
            actual,
            state,
            budget,
            visited,
        )) {
            return false;
        }
        if (try self.tryMatchSymbolicToExprChildrenSemantic(
            symbolic,
            actual,
            state,
            budget,
            visited,
        )) {
            return true;
        }

        var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer symbolic_steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesSymbolic(symbolic, &symbolic_steps);
        for (symbolic_steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToSymbolic(
                step,
                symbolic,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchSymbolicToExprSemanticSearch(
                next,
                actual,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }

        var expr_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer expr_steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesExpr(actual, &expr_steps);
        for (expr_steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToExpr(
                step,
                actual,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchSymbolicToSymbolicSemanticSearch(
                symbolic,
                next,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return false;
    }

    fn matchExprToSymbolicSemanticSearch(
        self: *SymbolicEngine,
        actual: ExprId,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        if (try self.tryMatchExprToSymbolicDirect(
            actual,
            symbolic,
            state,
        )) {
            return true;
        }
        if (budget == 0) return false;
        if (!try self.noteExprSemanticSearchState(
            actual,
            symbolic,
            state,
            budget,
            visited,
        )) {
            return false;
        }
        if (try self.tryMatchExprToSymbolicChildrenSemantic(
            actual,
            symbolic,
            state,
            budget,
            visited,
        )) {
            return true;
        }

        var expr_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer expr_steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesExpr(actual, &expr_steps);
        for (expr_steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToExpr(
                step,
                actual,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchSymbolicToSymbolicSemanticSearch(
                next,
                symbolic,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }

        var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer symbolic_steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesSymbolic(symbolic, &symbolic_steps);
        for (symbolic_steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToSymbolic(
                step,
                symbolic,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchExprToSymbolicSemanticSearch(
                actual,
                next,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return false;
    }

    fn matchSymbolicToSymbolicSemanticSearch(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        if (try self.tryMatchSymbolicToSymbolicDirect(lhs, rhs, state)) {
            return true;
        }
        if (budget == 0) return false;
        if (!try self.noteSymbolicSemanticSearchState(
            lhs,
            rhs,
            state,
            budget,
            visited,
        )) {
            return false;
        }
        if (try self.tryMatchSymbolicToSymbolicChildrenSemantic(
            lhs,
            rhs,
            state,
            budget,
            visited,
        )) {
            return true;
        }

        var lhs_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer lhs_steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesSymbolic(lhs, &lhs_steps);
        for (lhs_steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToSymbolic(
                step,
                lhs,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchSymbolicToSymbolicSemanticSearch(
                next,
                rhs,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }

        var rhs_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer rhs_steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesSymbolic(rhs, &rhs_steps);
        for (rhs_steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToSymbolic(
                step,
                rhs,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchSymbolicToSymbolicSemanticSearch(
                lhs,
                next,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return false;
    }

    fn tryMatchTemplateStateDirect(
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);
        if (try self.matchTemplateRecState(template, actual, state)) {
            return true;
        }
        try self.restoreMatchSnapshot(&snapshot, state);
        return false;
    }

    fn tryMatchSymbolicToExprDirect(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);
        if (try self.matchSymbolicToExprState(symbolic, actual, state)) {
            return true;
        }
        try self.restoreMatchSnapshot(&snapshot, state);
        return false;
    }

    fn tryMatchSymbolicToExprChildrenSemantic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        const symbolic_app = switch (symbolic.*) {
            .app => |app| app,
            else => return false,
        };
        const actual_node = self.shared.theorem.interner.node(actual);
        const actual_app = switch (actual_node.*) {
            .app => |app| app,
            .variable => return false,
        };
        if (symbolic_app.term_id != actual_app.term_id) return false;
        if (symbolic_app.args.len != actual_app.args.len) return false;

        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        var remaining_budget = budget;
        var used_semantic = false;
        for (symbolic_app.args, actual_app.args) |symbolic_arg, actual_arg| {
            if (try self.tryMatchSymbolicToExprDirect(
                symbolic_arg,
                actual_arg,
                state,
            )) {
                continue;
            }
            if (remaining_budget == 0) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
            remaining_budget -= 1;
            if (!try self.matchSymbolicToExprSemanticSearch(
                symbolic_arg,
                actual_arg,
                state,
                remaining_budget,
                visited,
            )) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
            used_semantic = true;
        }
        if (!used_semantic) {
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return used_semantic;
    }

    fn tryMatchExprToSymbolicDirect(
        self: *SymbolicEngine,
        actual: ExprId,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);
        if (try self.matchExprToSymbolic(
            actual,
            symbolic,
            state,
            .transparent,
        )) {
            return true;
        }
        try self.restoreMatchSnapshot(&snapshot, state);
        return false;
    }

    fn tryMatchExprToSymbolicChildrenSemantic(
        self: *SymbolicEngine,
        actual: ExprId,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        const actual_node = self.shared.theorem.interner.node(actual);
        const actual_app = switch (actual_node.*) {
            .app => |app| app,
            .variable => return false,
        };
        const symbolic_app = switch (symbolic.*) {
            .app => |app| app,
            else => return false,
        };
        if (actual_app.term_id != symbolic_app.term_id) return false;
        if (actual_app.args.len != symbolic_app.args.len) return false;

        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        var remaining_budget = budget;
        var used_semantic = false;
        for (actual_app.args, symbolic_app.args) |actual_arg, symbolic_arg| {
            if (try self.tryMatchExprToSymbolicDirect(
                actual_arg,
                symbolic_arg,
                state,
            )) {
                continue;
            }
            if (remaining_budget == 0) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
            remaining_budget -= 1;
            if (!try self.matchExprToSymbolicSemanticSearch(
                actual_arg,
                symbolic_arg,
                state,
                remaining_budget,
                visited,
            )) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
            used_semantic = true;
        }
        if (!used_semantic) {
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return used_semantic;
    }

    fn tryMatchSymbolicToSymbolicDirect(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);
        if (try self.matchSymbolicToSymbolicState(lhs, rhs, state)) {
            return true;
        }
        try self.restoreMatchSnapshot(&snapshot, state);

        if (rhs.* == .fixed) {
            if (try self.matchExprToSymbolic(
                rhs.fixed,
                lhs,
                state,
                .transparent,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return false;
    }

    fn tryMatchSymbolicToSymbolicChildrenSemantic(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        const lhs_app = switch (lhs.*) {
            .app => |app| app,
            else => return false,
        };
        const rhs_app = switch (rhs.*) {
            .app => |app| app,
            else => return false,
        };
        if (lhs_app.term_id != rhs_app.term_id) return false;
        if (lhs_app.args.len != rhs_app.args.len) return false;

        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        var remaining_budget = budget;
        var used_semantic = false;
        for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
            if (try self.tryMatchSymbolicToSymbolicDirect(
                lhs_arg,
                rhs_arg,
                state,
            )) {
                continue;
            }
            if (remaining_budget == 0) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
            remaining_budget -= 1;
            if (!try self.matchSymbolicToSymbolicSemanticSearch(
                lhs_arg,
                rhs_arg,
                state,
                remaining_budget,
                visited,
            )) {
                try self.restoreMatchSnapshot(&snapshot, state);
                return false;
            }
            used_semantic = true;
        }
        if (!used_semantic) {
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return used_semantic;
    }

    fn applySemanticStepToExpr(
        self: *SymbolicEngine,
        step: SemanticStepCandidate,
        expr_id: ExprId,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        return switch (step) {
            .unfold_concrete_def => |unfold| if (unfold.expr_id != expr_id)
                null
            else
                try self.expandConcreteDef(expr_id, state),
            .unfold_symbolic_def => null,
            .rewrite_rule => |rule| try self.applyRewriteRuleToExpr(
                rule,
                expr_id,
                state,
            ),
            .acui => |acui| try self.applyAcuiToExpr(acui, expr_id),
        };
    }

    fn applySemanticStepToSymbolic(
        self: *SymbolicEngine,
        step: SemanticStepCandidate,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        return switch (step) {
            .unfold_concrete_def => switch (symbolic.*) {
                .fixed => |expr_id| blk: {
                    if (expr_id != step.unfold_concrete_def.expr_id) {
                        break :blk null;
                    }
                    break :blk try self.expandConcreteDef(expr_id, state);
                },
                else => null,
            },
            .unfold_symbolic_def => |unfold| switch (symbolic.*) {
                .app => |app| if (app.term_id != unfold.term_id)
                    null
                else
                    try self.expandSymbolicApp(app, state),
                .fixed => |expr_id| blk: {
                    const node = self.shared.theorem.interner.node(expr_id);
                    const app = switch (node.*) {
                        .app => |value| value,
                        .variable => break :blk null,
                    };
                    if (app.term_id != unfold.term_id) break :blk null;
                    break :blk try self.expandConcreteDef(expr_id, state);
                },
                else => null,
            },
            .rewrite_rule => |rule| try self.applyRewriteRuleToSymbolic(
                rule,
                symbolic,
                state,
            ),
            .acui => |acui| try self.applyAcuiToSymbolic(acui, symbolic, state),
        };
    }

    fn applyAcuiToExpr(
        self: *SymbolicEngine,
        acui: ResolvedStructuralCombiner,
        expr_id: ExprId,
    ) anyerror!?*const SymbolicExpr {
        const registry = self.shared.registry orelse return null;
        var support = AcuiSupport.Context.init(
            self.shared.allocator,
            self.shared.theorem,
            self.shared.env,
            registry,
        );
        const canonical = try support.canonicalizeAcui(expr_id, acui);
        if (canonical == expr_id) return null;
        return try self.allocSymbolic(.{ .fixed = canonical });
    }

    fn applyAcuiToSymbolic(
        self: *SymbolicEngine,
        acui: ResolvedStructuralCombiner,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const plain = switch (symbolic.*) {
            .fixed => |expr_id| expr_id,
            else => (try self.symbolicToConcreteIfPlain(symbolic, state)) orelse {
                return null;
            },
        };
        return try self.applyAcuiToExpr(acui, plain);
    }

    fn noteSemanticExprSearchState(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: ExprId,
        state: *const MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        return try self.noteSemanticSearchState(
            self.hashSymbolicForSearch(lhs),
            self.hashExprForSearch(rhs),
            state,
            budget,
            visited,
        );
    }

    fn noteExprSemanticSearchState(
        self: *SymbolicEngine,
        lhs: ExprId,
        rhs: *const SymbolicExpr,
        state: *const MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        return try self.noteSemanticSearchState(
            self.hashExprForSearch(lhs),
            self.hashSymbolicForSearch(rhs),
            state,
            budget,
            visited,
        );
    }

    fn noteSymbolicSemanticSearchState(
        self: *SymbolicEngine,
        lhs: *const SymbolicExpr,
        rhs: *const SymbolicExpr,
        state: *const MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        return try self.noteSemanticSearchState(
            self.hashSymbolicForSearch(lhs),
            self.hashSymbolicForSearch(rhs),
            state,
            budget,
            visited,
        );
    }

    fn noteSemanticSearchState(
        self: *SymbolicEngine,
        lhs_hash: u64,
        rhs_hash: u64,
        state: *const MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        const key = SemanticSearchKey{
            .lhs_hash = lhs_hash,
            .rhs_hash = rhs_hash,
            .state_hash = try self.hashMatchSessionForSearch(state),
        };
        const entry = try visited.getOrPut(self.shared.allocator, key);
        if (entry.found_existing) {
            if (entry.value_ptr.* >= budget) return false;
        }
        entry.value_ptr.* = budget;
        return true;
    }

    fn hashExprForSearch(
        self: *SymbolicEngine,
        expr_id: ExprId,
    ) u64 {
        var hasher = std.hash.Wyhash.init(0x7419ef6a1fd348d1);
        const tag: u8 = 1;
        hasher.update(std.mem.asBytes(&tag));
        hasher.update(std.mem.asBytes(&expr_id));
        _ = self;
        return hasher.final();
    }

    fn hashSymbolicForSearch(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
    ) u64 {
        var hasher = std.hash.Wyhash.init(0x4fd443d41d41de49);
        self.hashSymbolicExprForSearch(symbolic, &hasher);
        return hasher.final();
    }

    fn hashSymbolicExprForSearch(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        hasher: *std.hash.Wyhash,
    ) void {
        switch (symbolic.*) {
            .binder => |idx| {
                const tag: u8 = 2;
                hasher.update(std.mem.asBytes(&tag));
                hasher.update(std.mem.asBytes(&idx));
            },
            .fixed => |expr_id| {
                const tag: u8 = 3;
                hasher.update(std.mem.asBytes(&tag));
                hasher.update(std.mem.asBytes(&expr_id));
            },
            .dummy => |slot| {
                const tag: u8 = 4;
                hasher.update(std.mem.asBytes(&tag));
                hasher.update(std.mem.asBytes(&slot));
            },
            .app => |app| {
                const tag: u8 = 5;
                hasher.update(std.mem.asBytes(&tag));
                hasher.update(std.mem.asBytes(&app.term_id));
                hasher.update(std.mem.asBytes(&app.args.len));
                for (app.args) |arg| {
                    self.hashSymbolicExprForSearch(arg, hasher);
                }
            },
        }
    }

    fn hashMatchSessionForSearch(
        self: *SymbolicEngine,
        state: *const MatchSession,
    ) anyerror!u64 {
        var hasher = std.hash.Wyhash.init(0x9ff6116d7c0ed8a3);

        hasher.update(std.mem.asBytes(&state.bindings.len));
        for (state.bindings) |binding_opt| {
            const present: u8 = if (binding_opt == null) 0 else 1;
            hasher.update(std.mem.asBytes(&present));
            if (binding_opt) |binding| {
                try self.hashBoundValueForSearch(binding, &hasher);
            }
        }

        hasher.update(std.mem.asBytes(&state.symbolic_dummy_infos.items.len));
        for (state.symbolic_dummy_infos.items) |info| {
            hasher.update(info.sort_name);
            hasher.update(std.mem.asBytes(&info.bound));
        }

        try self.hashWitnessMapForSearch(state.witnesses, &hasher);
        try self.hashWitnessMapForSearch(
            state.materialized_witnesses,
            &hasher,
        );
        try self.hashWitnessSlotMapForSearch(
            state.materialized_witness_slots,
            &hasher,
        );
        try self.hashDummyAliasMapForSearch(
            state.dummy_aliases,
            &hasher,
        );
        return hasher.final();
    }

    fn hashBoundValueForSearch(
        self: *SymbolicEngine,
        bound: BoundValue,
        hasher: *std.hash.Wyhash,
    ) anyerror!void {
        switch (bound) {
            .concrete => |concrete| {
                const tag: u8 = 6;
                const mode = @intFromEnum(concrete.mode);
                hasher.update(std.mem.asBytes(&tag));
                hasher.update(std.mem.asBytes(&concrete.raw));
                hasher.update(std.mem.asBytes(&mode));
                self.hashSymbolicExprForSearch(concrete.repr, hasher);
            },
            .symbolic => |symbolic| {
                const tag: u8 = 7;
                const mode = @intFromEnum(symbolic.mode);
                hasher.update(std.mem.asBytes(&tag));
                hasher.update(std.mem.asBytes(&mode));
                self.hashSymbolicExprForSearch(symbolic.expr, hasher);
            },
        }
    }

    fn hashWitnessMapForSearch(
        self: *SymbolicEngine,
        map: WitnessMap,
        hasher: *std.hash.Wyhash,
    ) anyerror!void {
        var count: usize = 0;
        var xor_acc: u64 = 0;
        var sum_acc: u64 = 0;
        var it = map.iterator();
        while (it.next()) |entry| {
            var entry_hasher = std.hash.Wyhash.init(0x0d48ab295c1ee8d7);
            entry_hasher.update(std.mem.asBytes(entry.key_ptr));
            entry_hasher.update(std.mem.asBytes(entry.value_ptr));
            const entry_hash = entry_hasher.final();
            count += 1;
            xor_acc ^= entry_hash;
            sum_acc +%= entry_hash;
        }
        const tag: u8 = 8;
        hasher.update(std.mem.asBytes(&tag));
        hasher.update(std.mem.asBytes(&count));
        hasher.update(std.mem.asBytes(&xor_acc));
        hasher.update(std.mem.asBytes(&sum_acc));
        _ = self;
    }

    fn hashWitnessSlotMapForSearch(
        self: *SymbolicEngine,
        map: WitnessSlotMap,
        hasher: *std.hash.Wyhash,
    ) anyerror!void {
        var count: usize = 0;
        var xor_acc: u64 = 0;
        var sum_acc: u64 = 0;
        var it = map.iterator();
        while (it.next()) |entry| {
            var entry_hasher = std.hash.Wyhash.init(0x8c64a0f5a76d9f19);
            entry_hasher.update(std.mem.asBytes(entry.key_ptr));
            entry_hasher.update(std.mem.asBytes(entry.value_ptr));
            const entry_hash = entry_hasher.final();
            count += 1;
            xor_acc ^= entry_hash;
            sum_acc +%= entry_hash;
        }
        const tag: u8 = 9;
        hasher.update(std.mem.asBytes(&tag));
        hasher.update(std.mem.asBytes(&count));
        hasher.update(std.mem.asBytes(&xor_acc));
        hasher.update(std.mem.asBytes(&sum_acc));
        _ = self;
    }

    fn hashDummyAliasMapForSearch(
        self: *SymbolicEngine,
        map: DummyAliasMap,
        hasher: *std.hash.Wyhash,
    ) anyerror!void {
        var count: usize = 0;
        var xor_acc: u64 = 0;
        var sum_acc: u64 = 0;
        var it = map.iterator();
        while (it.next()) |entry| {
            var entry_hasher = std.hash.Wyhash.init(0x3f4bb85ca84d2b13);
            entry_hasher.update(std.mem.asBytes(entry.key_ptr));
            entry_hasher.update(std.mem.asBytes(entry.value_ptr));
            const entry_hash = entry_hasher.final();
            count += 1;
            xor_acc ^= entry_hash;
            sum_acc +%= entry_hash;
        }
        const tag: u8 = 10;
        hasher.update(std.mem.asBytes(&tag));
        hasher.update(std.mem.asBytes(&count));
        hasher.update(std.mem.asBytes(&xor_acc));
        hasher.update(std.mem.asBytes(&sum_acc));
        _ = self;
    }

    pub fn applyRewriteRuleToExpr(
        self: *SymbolicEngine,
        rule: RewriteRule,
        expr_id: ExprId,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        const node = self.shared.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return null,
        };
        if (app.term_id != rule.head_term_id) return null;

        var snapshot = try self.saveMatchSnapshot(state);
        defer self.deinitMatchSnapshot(&snapshot);

        const rewrite_bindings = try self.shared.allocator.alloc(
            ?BoundValue,
            rule.num_binders,
        );
        defer self.shared.allocator.free(rewrite_bindings);
        @memset(rewrite_bindings, null);

        if (!try self.matchRewriteTemplateToExpr(
            rule.lhs,
            expr_id,
            rewrite_bindings,
            state,
        )) {
            try self.restoreMatchSnapshot(&snapshot, state);
            return null;
        }
        if (!try self.validateRewriteRuleBindings(
            rule,
            rewrite_bindings,
            state,
        )) {
            try self.restoreMatchSnapshot(&snapshot, state);
            return null;
        }
        return try self.instantiateRewriteRuleRhs(
            rule,
            rewrite_bindings,
        ) orelse blk: {
            try self.restoreMatchSnapshot(&snapshot, state);
            break :blk null;
        };
    }

    pub fn applyRewriteRuleToSymbolic(
        self: *SymbolicEngine,
        rule: RewriteRule,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?*const SymbolicExpr {
        return switch (symbolic.*) {
            .fixed => |expr_id| try self.applyRewriteRuleToExpr(
                rule,
                expr_id,
                state,
            ),
            .app => |app| blk: {
                if (app.term_id != rule.head_term_id) break :blk null;

                var snapshot = try self.saveMatchSnapshot(state);
                defer self.deinitMatchSnapshot(&snapshot);

                const rewrite_bindings = try self.shared.allocator.alloc(
                    ?BoundValue,
                    rule.num_binders,
                );
                defer self.shared.allocator.free(rewrite_bindings);
                @memset(rewrite_bindings, null);

                if (!try self.matchRewriteTemplateToSymbolic(
                    rule.lhs,
                    symbolic,
                    rewrite_bindings,
                    state,
                )) {
                    try self.restoreMatchSnapshot(&snapshot, state);
                    break :blk null;
                }
                if (!try self.validateRewriteRuleBindings(
                    rule,
                    rewrite_bindings,
                    state,
                )) {
                    try self.restoreMatchSnapshot(&snapshot, state);
                    break :blk null;
                }
                break :blk try self.instantiateRewriteRuleRhs(
                    rule,
                    rewrite_bindings,
                ) orelse inner: {
                    try self.restoreMatchSnapshot(&snapshot, state);
                    break :inner null;
                };
            },
            .binder, .dummy => null,
        };
    }

    fn matchRewriteTemplateToExpr(
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: ExprId,
        rewrite_bindings: []?BoundValue,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (template) {
            .binder => |idx| try self.assignRewriteBinderFromExpr(
                rewrite_bindings,
                idx,
                actual,
                state,
            ),
            .app => |tmpl_app| blk: {
                const actual_node = self.shared.theorem.interner.node(actual);
                const actual_app = switch (actual_node.*) {
                    .app => |value| value,
                    .variable => break :blk false,
                };
                if (actual_app.term_id != tmpl_app.term_id or
                    actual_app.args.len != tmpl_app.args.len)
                {
                    break :blk false;
                }

                const saved = try self.shared.allocator.dupe(
                    ?BoundValue,
                    rewrite_bindings,
                );
                defer self.shared.allocator.free(saved);
                var snapshot = try self.saveMatchSnapshot(state);
                defer self.deinitMatchSnapshot(&snapshot);

                for (tmpl_app.args, actual_app.args) |tmpl_arg, actual_arg| {
                    if (!try self.matchRewriteTemplateToExpr(
                        tmpl_arg,
                        actual_arg,
                        rewrite_bindings,
                        state,
                    )) {
                        @memcpy(rewrite_bindings, saved);
                        try self.restoreMatchSnapshot(&snapshot, state);
                        break :blk false;
                    }
                }
                break :blk true;
            },
        };
    }

    fn matchRewriteTemplateToSymbolic(
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: *const SymbolicExpr,
        rewrite_bindings: []?BoundValue,
        state: *MatchSession,
    ) anyerror!bool {
        return switch (template) {
            .binder => |idx| try self.assignRewriteBinderFromSymbolic(
                rewrite_bindings,
                idx,
                actual,
                state,
            ),
            .app => |tmpl_app| switch (actual.*) {
                .fixed => |expr_id| try self.matchRewriteTemplateToExpr(
                    template,
                    expr_id,
                    rewrite_bindings,
                    state,
                ),
                .app => |actual_app| blk: {
                    if (actual_app.term_id != tmpl_app.term_id or
                        actual_app.args.len != tmpl_app.args.len)
                    {
                        break :blk false;
                    }

                    const saved = try self.shared.allocator.dupe(
                        ?BoundValue,
                        rewrite_bindings,
                    );
                    defer self.shared.allocator.free(saved);
                    var snapshot = try self.saveMatchSnapshot(state);
                    defer self.deinitMatchSnapshot(&snapshot);

                    for (tmpl_app.args, actual_app.args) |tmpl_arg, actual_arg| {
                        if (!try self.matchRewriteTemplateToSymbolic(
                            tmpl_arg,
                            actual_arg,
                            rewrite_bindings,
                            state,
                        )) {
                            @memcpy(rewrite_bindings, saved);
                            try self.restoreMatchSnapshot(&snapshot, state);
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
                .binder, .dummy => false,
            },
        };
    }

    fn assignRewriteBinderFromExpr(
        self: *SymbolicEngine,
        rewrite_bindings: []?BoundValue,
        idx: usize,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        if (idx >= rewrite_bindings.len) return false;
        const value = try self.rebuildBoundValueFromState(
            actual,
            state,
            .transparent,
        );
        if (rewrite_bindings[idx]) |existing| {
            return try self.rewriteBoundValuesEql(existing, value);
        }
        rewrite_bindings[idx] = value;
        return true;
    }

    fn assignRewriteBinderFromSymbolic(
        self: *SymbolicEngine,
        rewrite_bindings: []?BoundValue,
        idx: usize,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!bool {
        if (idx >= rewrite_bindings.len) return false;
        const value = try self.rewriteBoundValueFromSymbolic(symbolic, state);
        if (rewrite_bindings[idx]) |existing| {
            return try self.rewriteBoundValuesEql(existing, value);
        }
        rewrite_bindings[idx] = value;
        return true;
    }

    fn rewriteBoundValueFromSymbolic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!BoundValue {
        return switch (symbolic.*) {
            .fixed => |expr_id| try self.rebuildBoundValueFromState(
                expr_id,
                state,
                .transparent,
            ),
            else => self.makeSymbolicBoundValue(symbolic, .transparent),
        };
    }

    fn rewriteBoundValuesEql(
        self: *SymbolicEngine,
        lhs: BoundValue,
        rhs: BoundValue,
    ) anyerror!bool {
        const lhs_repr = try self.boundValueRepresentative(lhs);
        const rhs_repr = try self.boundValueRepresentative(rhs);
        return self.symbolicExprEql(lhs_repr, rhs_repr);
    }

    fn validateRewriteRuleBindings(
        self: *SymbolicEngine,
        rule: RewriteRule,
        rewrite_bindings: []const ?BoundValue,
        state: *MatchSession,
    ) anyerror!bool {
        if (rule.rule_id >= self.shared.env.rules.items.len) return false;
        const rule_decl = &self.shared.env.rules.items[rule.rule_id];
        if (rule_decl.args.len != rewrite_bindings.len) return false;

        for (rule_decl.args, rewrite_bindings) |arg, binding_opt| {
            const binding = binding_opt orelse return false;
            const sort_name = try self.rewriteBoundValueSortName(
                binding,
                state,
            ) orelse return false;
            if (!std.mem.eql(u8, sort_name, arg.sort_name)) return false;
            const actual_bound = try self.rewriteBoundValueIsBound(
                binding,
                state,
            );
            if (arg.bound and !actual_bound) {
                return false;
            }
        }
        return true;
    }

    fn rewriteBoundValueSortName(
        self: *SymbolicEngine,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!?[]const u8 {
        const symbolic = try self.boundValueRepresentative(bound);
        return self.symbolicSortName(symbolic, state);
    }

    fn rewriteBoundValueIsBound(
        self: *SymbolicEngine,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!bool {
        _ = state;
        const symbolic = try self.boundValueRepresentative(bound);
        return try self.symbolicIsBound(symbolic);
    }

    fn symbolicIsBound(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
    ) anyerror!bool {
        return switch (symbolic.*) {
            .binder => false,
            .dummy => true,
            .app => false,
            .fixed => |expr_id| blk: {
                const node = self.shared.theorem.interner.node(expr_id);
                switch (node.*) {
                    .app => break :blk false,
                    .variable => break :blk (try self.getConcreteVarInfo(expr_id)).bound,
                }
            },
        };
    }

    fn instantiateRewriteRuleRhs(
        self: *SymbolicEngine,
        rule: RewriteRule,
        rewrite_bindings: []const ?BoundValue,
    ) anyerror!?*const SymbolicExpr {
        const subst = try self.shared.allocator.alloc(
            *const SymbolicExpr,
            rewrite_bindings.len,
        );
        for (rewrite_bindings, 0..) |binding_opt, idx| {
            const binding = binding_opt orelse return null;
            subst[idx] = try self.boundValueRepresentative(binding);
        }
        return try self.symbolicFromTemplateSubst(rule.rhs, subst);
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
        try self.resolveBindings(&state, bindings);
        return true;
    }

    pub fn matchTemplateSemantic(
        self: *SymbolicEngine,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
        budget: usize,
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

        if (!try self.matchTemplateSemanticState(
            template,
            actual,
            &state,
            budget,
        )) {
            return false;
        }
        try self.resolveBindings(&state, bindings);
        return true;
    }

    pub fn instantiateDefTowardExpr(
        self: *SymbolicEngine,
        def_expr: ExprId,
        target_expr: ExprId,
    ) anyerror!?ExprId {
        _ = self.getConcreteDef(def_expr) orelse return null;

        if (try self.instantiateDefTowardExprViaSearch(
            def_expr,
            target_expr,
        )) |witness| {
            return witness;
        }
        return try self.instantiateDefTowardExprViaTargetGuidance(
            def_expr,
            target_expr,
        );
    }

    fn instantiateDefTowardExprViaSearch(
        self: *SymbolicEngine,
        def_expr: ExprId,
        target_expr: ExprId,
    ) anyerror!?ExprId {
        var session = try MatchSession.init(self.shared.allocator, 0);
        defer session.deinit(self.shared.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        if (!try self.matchSymbolicToExprState(
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
        return try self.materializeResolvedSymbolic(
            symbolic,
            &session,
        );
    }

    fn instantiateDefTowardExprViaTargetGuidance(
        self: *SymbolicEngine,
        def_expr: ExprId,
        target_expr: ExprId,
    ) anyerror!?ExprId {
        var session = try MatchSession.init(self.shared.allocator, 0);
        defer session.deinit(self.shared.allocator);
        const symbolic = try self.expandConcreteDef(
            def_expr,
            &session,
        ) orelse return null;

        while (true) {
            if (try self.materializeResolvedSymbolic(
                symbolic,
                &session,
            )) |witness| {
                return witness;
            }
            if (!try self.guideSymbolicWitnessesFromTarget(
                symbolic,
                target_expr,
                &session,
            )) {
                return null;
            }
        }
    }

    fn guideSymbolicWitnessesFromTarget(
        self: *SymbolicEngine,
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
            .variable => return try self.guideSymbolicWitnessesFromAcuiTarget(
                symbolic,
                target_expr,
                state,
            ),
        };

        if (symbolic_app.term_id == target_app.term_id and
            symbolic_app.args.len == target_app.args.len)
        {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            var made_progress = false;
            var same_head_failed = false;
            for (symbolic_app.args, target_app.args) |symbolic_arg, target_arg| {
                if (try self.tryMatchSymbolicToExprDirect(
                    symbolic_arg,
                    target_arg,
                    state,
                )) {
                    continue;
                }
                if (!try self.guideSymbolicWitnessesFromTarget(
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
                try self.restoreMatchSnapshot(&snapshot, state);
            } else {
                try self.restoreMatchSnapshot(&snapshot, state);
            }
        }

        return try self.guideSymbolicWitnessesFromAcuiTarget(
            symbolic,
            target_expr,
            state,
        );
    }

    fn guideSymbolicWitnessesFromAcuiTarget(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        target_expr: ExprId,
        state: *MatchSession,
    ) anyerror!bool {
        const registry = self.shared.registry orelse return false;
        const symbolic_sort = self.symbolicSortName(symbolic, state) orelse {
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
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            if (!try self.matchSymbolicAcuiLeafToExprState(
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
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            }
            return true;
        }
        return false;
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

    fn matchSymbolicAcuiLeafToExprState(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        head_term_id: u32,
        state: *MatchSession,
    ) anyerror!bool {
        switch (symbolic.*) {
            .app => |app| {
                if (app.term_id == head_term_id and app.args.len == 2) {
                    var snapshot = try self.saveMatchSnapshot(state);
                    defer self.deinitMatchSnapshot(&snapshot);

                    if (try self.matchSymbolicAcuiLeafToExprState(
                        app.args[0],
                        actual,
                        head_term_id,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                    if (try self.matchSymbolicAcuiLeafToExprState(
                        app.args[1],
                        actual,
                        head_term_id,
                        state,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                    return false;
                }
            },
            else => {},
        }
        return try self.tryMatchSymbolicToExprDirect(symbolic, actual, state);
    }

    fn matchSymbolicAcuiLeafToExprSemantic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        head_term_id: u32,
        state: *MatchSession,
        budget: usize,
    ) anyerror!bool {
        var visited: SemanticSearchVisited = .empty;
        defer visited.deinit(self.shared.allocator);
        return try self.matchSymbolicAcuiLeafToExprSemanticSearch(
            symbolic,
            actual,
            head_term_id,
            state,
            budget,
            &visited,
        );
    }

    fn matchSymbolicAcuiLeafToExprSemanticSearch(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        actual: ExprId,
        head_term_id: u32,
        state: *MatchSession,
        budget: usize,
        visited: *SemanticSearchVisited,
    ) anyerror!bool {
        if (try self.matchSymbolicAcuiLeafToExprState(
            symbolic,
            actual,
            head_term_id,
            state,
        )) {
            return true;
        }
        if (budget == 0) return false;
        if (!try self.noteSemanticExprSearchState(
            symbolic,
            actual,
            state,
            budget,
            visited,
        )) {
            return false;
        }

        switch (symbolic.*) {
            .app => |app| {
                if (app.term_id == head_term_id and app.args.len == 2) {
                    var snapshot = try self.saveMatchSnapshot(state);
                    defer self.deinitMatchSnapshot(&snapshot);

                    if (try self.matchSymbolicAcuiLeafToExprSemanticSearch(
                        app.args[0],
                        actual,
                        head_term_id,
                        state,
                        budget,
                        visited,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                    if (try self.matchSymbolicAcuiLeafToExprSemanticSearch(
                        app.args[1],
                        actual,
                        head_term_id,
                        state,
                        budget,
                        visited,
                    )) {
                        return true;
                    }
                    try self.restoreMatchSnapshot(&snapshot, state);
                }
            },
            else => {},
        }

        var steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
        defer steps.deinit(self.shared.allocator);
        try self.collectSemanticStepCandidatesSymbolic(symbolic, &steps);
        for (steps.items) |step| {
            var snapshot = try self.saveMatchSnapshot(state);
            defer self.deinitMatchSnapshot(&snapshot);

            const next = try self.applySemanticStepToSymbolic(
                step,
                symbolic,
                state,
            ) orelse {
                try self.restoreMatchSnapshot(&snapshot, state);
                continue;
            };
            if (try self.matchSymbolicAcuiLeafToExprSemanticSearch(
                next,
                actual,
                head_term_id,
                state,
                budget - 1,
                visited,
            )) {
                return true;
            }
            try self.restoreMatchSnapshot(&snapshot, state);
        }
        return false;
    }

    fn matchSymbolicDummy(
        self: *SymbolicEngine,
        slot: usize,
        info: SymbolicDummyInfo,
        actual: ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) anyerror!bool {
        // Matching a symbolic dummy against a non-variable is a plain mismatch,
        // not a fatal error.
        const actual_info = self.getConcreteVarInfo(actual) catch |err| switch (err) {
            error.ExpectedVariable => return false,
            else => return err,
        };
        if (info.bound and !actual_info.bound) return false;
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
            if (!try self.boundValueMatchesExpr(existing, actual, state)) {
                return false;
            }
            switch (existing) {
                .concrete => {},
                .symbolic => {
                    // If a binder was first solved from a symbolic expansion
                    // with hidden dummy slots, and we later see a concrete
                    // proof expression that matches it, prefer the concrete
                    // witness-preserving form over keeping the symbolic
                    // placeholder. This avoids needlessly finalizing hidden
                    // binders back into fresh theorem dummies.
                    state.bindings[idx] = try self.rebuildBoundValueFromState(
                        actual,
                        state,
                        mode,
                    );
                },
            }
            return true;
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
            .bound => |bv| bv,
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
        if (try self.symbolicForExistingConcreteBinding(expr_id, state)) |binding| {
            return binding;
        }

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

    fn symbolicForExistingConcreteBinding(
        self: *SymbolicEngine,
        expr_id: ExprId,
        state: *const MatchSession,
    ) anyerror!?*const SymbolicExpr {
        for (state.bindings, 0..) |binding_opt, idx| {
            const binding = binding_opt orelse continue;
            switch (binding) {
                .concrete => |concrete| {
                    if (concrete.raw != expr_id) continue;
                    return try self.allocSymbolic(.{ .binder = idx });
                },
                .symbolic => {},
            }
        }
        return null;
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

    fn resolveDummySlot(
        self: *SymbolicEngine,
        slot: usize,
        state: *const MatchSession,
    ) anyerror!usize {
        if (slot >= state.symbolic_dummy_infos.items.len) {
            return error.UnknownDummyVar;
        }
        var current = slot;
        var steps: usize = 0;
        while (state.dummy_aliases.get(current)) |next| {
            if (next >= state.symbolic_dummy_infos.items.len) {
                return error.UnknownDummyVar;
            }
            current = next;
            steps += 1;
            if (steps > state.symbolic_dummy_infos.items.len) {
                return error.CyclicSymbolicDummyAlias;
            }
        }
        _ = self;
        return current;
    }

    fn putWitnessForDummySlot(
        self: *SymbolicEngine,
        slot: usize,
        actual: ExprId,
        state: *MatchSession,
    ) anyerror!void {
        const root = try self.resolveDummySlot(slot, state);
        try state.witnesses.put(self.shared.allocator, root, actual);
    }

    fn alignDummySlots(
        self: *SymbolicEngine,
        lhs_slot: usize,
        rhs_slot: usize,
        state: *MatchSession,
    ) anyerror!bool {
        const lhs_root = try self.resolveDummySlot(lhs_slot, state);
        const rhs_root = try self.resolveDummySlot(rhs_slot, state);
        if (lhs_root == rhs_root) return true;

        const lhs_info = state.symbolic_dummy_infos.items[lhs_root];
        const rhs_info = state.symbolic_dummy_infos.items[rhs_root];
        if (!std.mem.eql(u8, lhs_info.sort_name, rhs_info.sort_name)) {
            return false;
        }
        if (lhs_info.bound != rhs_info.bound) {
            return false;
        }

        const lhs_witness = self.currentWitnessExpr(lhs_root, state);
        const rhs_witness = self.currentWitnessExpr(rhs_root, state);
        if (lhs_witness != null and rhs_witness != null and
            lhs_witness.? != rhs_witness.?)
        {
            return false;
        }

        const winner = if (lhs_witness != null)
            lhs_root
        else if (rhs_witness != null)
            rhs_root
        else if (lhs_root <= rhs_root)
            lhs_root
        else
            rhs_root;
        const loser = if (winner == lhs_root) rhs_root else lhs_root;

        if (state.witnesses.get(loser)) |existing| {
            if (state.witnesses.get(winner)) |winner_existing| {
                if (winner_existing != existing) return false;
            } else {
                try state.witnesses.put(self.shared.allocator, winner, existing);
            }
            _ = state.witnesses.remove(loser);
        }
        if (state.materialized_witnesses.get(loser)) |existing| {
            if (state.materialized_witnesses.get(winner)) |winner_existing| {
                if (winner_existing != existing) return false;
            } else {
                try state.materialized_witnesses.put(
                    self.shared.allocator,
                    winner,
                    existing,
                );
                try state.materialized_witness_slots.put(
                    self.shared.allocator,
                    existing,
                    winner,
                );
            }
            _ = state.materialized_witnesses.remove(loser);
        }

        try state.dummy_aliases.put(self.shared.allocator, loser, winner);
        return true;
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
            .dummy_aliases = try self.cloneDummyAliasMap(state.dummy_aliases),
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
        state.dummy_aliases.deinit(self.shared.allocator);
        state.dummy_aliases = try self.cloneDummyAliasMap(
            snapshot.dummy_aliases,
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
        snapshot.dummy_aliases.deinit(self.shared.allocator);
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

    fn cloneDummyAliasMap(
        self: *SymbolicEngine,
        map: DummyAliasMap,
    ) anyerror!DummyAliasMap {
        var clone: DummyAliasMap = .{};
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
        clone.dummy_aliases = try self.cloneDummyAliasMap(source.dummy_aliases);
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
        const root = try self.resolveDummySlot(slot, state);
        const root_info = state.symbolic_dummy_infos.items[root];

        // Matching a symbolic dummy against a non-variable is a plain mismatch,
        // not a fatal error.
        const actual_info = self.getConcreteVarInfo(actual) catch |err| switch (err) {
            error.ExpectedVariable => return false,
            else => return err,
        };
        if (root_info.bound and !actual_info.bound) return false;
        if (!std.mem.eql(u8, root_info.sort_name, actual_info.sort_name)) {
            return false;
        }
        _ = info;

        if (self.currentWitnessExpr(root, state)) |existing| {
            if (existing == actual) return true;
            if (self.isProvisionalWitnessExpr(existing, state)) {
                try self.putWitnessForDummySlot(root, actual, state);
                return true;
            }
            return false;
        }
        try self.putWitnessForDummySlot(root, actual, state);
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
                return try self.alignDummySlots(slot, rhs_slot, state);
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

    fn resolveBindings(
        self: *SymbolicEngine,
        state: *MatchSession,
        bindings: []?ExprId,
    ) anyerror!void {
        for (state.bindings, 0..) |binding, idx| {
            bindings[idx] = if (binding) |value|
                try self.resolveBoundValue(value, state)
            else
                null;
        }
    }

    /// Materialize the concrete expression justified by the current match
    /// state without applying representative selection.
    pub fn materializeResolvedBoundValue(
        self: *SymbolicEngine,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (bound) {
            .concrete => |concrete| concrete.raw,
            .symbolic => |symbolic| try self.materializeResolvedSymbolic(
                symbolic.expr,
                state,
            ),
        };
    }

    /// Project a materialized expression through the binding mode's
    /// representative-selection semantics.
    pub fn projectMaterializedExpr(
        self: *SymbolicEngine,
        expr_id: ?ExprId,
        mode: BindingMode,
    ) anyerror!?ExprId {
        const materialized = expr_id orelse return null;
        return try self.chooseRepresentative(materialized, mode);
    }

    /// Temporary compatibility wrapper. This preserves the old represented
    /// behavior and will go away once callers choose materialization or
    /// projection explicitly.
    pub fn resolveBoundValue(
        self: *SymbolicEngine,
        bound: BoundValue,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (bound) {
            .concrete => |concrete| try self.projectMaterializedExpr(
                try self.materializeResolvedBoundValue(bound, state),
                concrete.mode,
            ),
            .symbolic => |symbolic| try self.projectMaterializedExpr(
                try self.materializeResolvedBoundValue(bound, state),
                symbolic.mode,
            ),
        };
    }

    // This is the only escape path that turns symbolic match state back into
    // main-theorem expressions. Internal matching and representative work
    // should stay symbolic until a caller explicitly finalizes bindings.
    /// Finalize a BoundValue to a concrete ExprId. Returns
    /// error.UnresolvedDummyWitness if any hidden-dummy slot in the
    /// symbolic structure lacks a witness.
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
                const expr_id = try self.materializeFinalSymbolic(
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

    fn materializeResolvedSymbolic(
        self: *SymbolicEngine,
        symbolic: *const SymbolicExpr,
        state: *MatchSession,
    ) anyerror!?ExprId {
        return switch (symbolic.*) {
            .binder => |idx| blk: {
                if (idx >= state.bindings.len) {
                    return error.TemplateBinderOutOfRange;
                }
                const bound = state.bindings[idx] orelse break :blk null;
                break :blk try self.materializeResolvedBoundValue(
                    bound,
                    state,
                );
            },
            .fixed => |expr_id| expr_id,
            .dummy => |slot| self.currentWitnessExpr(slot, state),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(ExprId, app.args.len);
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.materializeResolvedSymbolic(
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

    /// Materialize a symbolic expression to a concrete ExprId. Returns
    /// error.UnresolvedDummyWitness if any hidden-dummy slot lacks a witness.
    fn materializeFinalSymbolic(
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
            .dummy => |slot| try self.resolveWitnessForDummySlot(slot, state),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(ExprId, app.args.len);
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.materializeFinalSymbolic(
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
        const root = self.resolveDummySlot(slot, state) catch return null;
        return state.witnesses.get(root) orelse
            state.materialized_witnesses.get(root);
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

    /// Resolve a hidden-dummy slot to a concrete ExprId. Only succeeds
    /// if the slot was previously filled by a witness during matching.
    /// Returns error.UnresolvedDummyWitness if the slot has no witness —
    /// the user must provide explicit bindings that cover the hidden
    /// def structure.
    fn resolveWitnessForDummySlot(
        self: *SymbolicEngine,
        slot: usize,
        state: *MatchSession,
    ) anyerror!ExprId {
        const root = try self.resolveDummySlot(slot, state);
        if (state.witnesses.get(root)) |existing| return existing;
        if (state.materialized_witnesses.get(root)) |existing| return existing;
        return error.UnresolvedDummyWitness;
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
                    if (dummy.kind != .placeholder) break :blk null;
                    break :blk .{
                        .sort_name = dummy.sort_name,
                        .bound = true,
                    };
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
                .bound = dummy_arg.bound,
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
                .bound = dummy_arg.bound,
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
                .bound = dummy_arg.bound,
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
