const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const AcuiSupport = @import("../../acui_support.zig");
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch = @import("./transparent_match.zig");
const RewriteApplication =
    @import("./rewrite_application.zig");
const WitnessState = @import("./witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BoundValue = Types.BoundValue;
const BindingMode = Types.BindingMode;
const WitnessMap = Types.WitnessMap;
const WitnessSlotMap = Types.WitnessSlotMap;
const DummyAliasMap = Types.DummyAliasMap;
const MatchSession = MatchState.MatchSession;

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

pub fn collectSemanticStepCandidatesExpr(
    self: anytype,
    expr_id: ExprId,
    out: *std.ArrayListUnmanaged(SemanticStepCandidate),
) anyerror!void {
    const node = self.shared.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return,
        .placeholder => return,
    };

    if (TransparentMatch.getOpenableTerm(self, app.term_id) != null) {
        try out.append(self.shared.allocator, .{
            .unfold_concrete_def = .{
                .expr_id = expr_id,
                .term_id = app.term_id,
            },
        });
    }
    try appendSemanticHeadStepCandidates(self, app.term_id, out);
}

pub fn collectSemanticStepCandidatesSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    out: *std.ArrayListUnmanaged(SemanticStepCandidate),
) anyerror!void {
    switch (symbolic.*) {
        .fixed => |expr_id| {
            return try collectSemanticStepCandidatesExpr(self, expr_id, out);
        },
        .app => |app| {
            if (TransparentMatch.getOpenableTerm(self, app.term_id) != null) {
                try out.append(self.shared.allocator, .{
                    .unfold_symbolic_def = .{
                        .term_id = app.term_id,
                    },
                });
            }
            try appendSemanticHeadStepCandidates(self, app.term_id, out);
        },
        .binder, .dummy => {},
    }
}

fn appendSemanticHeadStepCandidates(
    self: anytype,
    head_term_id: u32,
    out: *std.ArrayListUnmanaged(SemanticStepCandidate),
) anyerror!void {
    const registry = self.shared.registry orelse return;
    for (registry.getRewriteRules(head_term_id)) |rule| {
        try out.append(self.shared.allocator, .{ .rewrite_rule = rule });
    }
    if (try registry.resolveStructuralCombiner(
        self.shared.env,
        head_term_id,
    )) |acui| {
        try out.append(self.shared.allocator, .{ .acui = acui });
    }
}

pub fn matchTemplateSemanticState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
    budget: usize,
) anyerror!bool {
    if (try TransparentMatch.tryMatchTemplateStateDirect(
        self,
        template,
        actual,
        state,
    )) {
        return true;
    }

    var visited: SemanticSearchVisited = .empty;
    defer visited.deinit(self.shared.allocator);
    const symbolic = try TransparentMatch.symbolicFromTemplate(self, template);
    return try matchSymbolicToExprSemanticSearch(
        self,
        symbolic,
        actual,
        state,
        budget,
        &visited,
    );
}

pub fn matchSymbolicToExprSemantic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
    budget: usize,
) anyerror!bool {
    var visited: SemanticSearchVisited = .empty;
    defer visited.deinit(self.shared.allocator);
    return try matchSymbolicToExprSemanticSearch(
        self,
        symbolic,
        actual,
        state,
        budget,
        &visited,
    );
}

pub fn matchExprToSymbolicSemantic(
    self: anytype,
    actual: ExprId,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    budget: usize,
) anyerror!bool {
    var visited: SemanticSearchVisited = .empty;
    defer visited.deinit(self.shared.allocator);
    return try matchExprToSymbolicSemanticSearch(
        self,
        actual,
        symbolic,
        state,
        budget,
        &visited,
    );
}

pub fn matchSymbolicToSymbolicSemantic(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
    budget: usize,
) anyerror!bool {
    var visited: SemanticSearchVisited = .empty;
    defer visited.deinit(self.shared.allocator);
    return try matchSymbolicToSymbolicSemanticSearch(
        self,
        lhs,
        rhs,
        state,
        budget,
        &visited,
    );
}

fn matchSymbolicToExprSemanticSearch(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    if (try TransparentMatch.tryMatchSymbolicToExprDirect(
        self,
        symbolic,
        actual,
        state,
    )) {
        return true;
    }
    if (budget == 0) return false;
    if (!try noteSemanticExprSearchState(
        self,
        symbolic,
        actual,
        state,
        budget,
        visited,
    )) {
        return false;
    }
    if (try tryMatchSymbolicToExprChildrenSemantic(
        self,
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
    try collectSemanticStepCandidatesSymbolic(self, symbolic, &symbolic_steps);
    for (symbolic_steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToSymbolic(
            self,
            step,
            symbolic,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchSymbolicToExprSemanticSearch(
            self,
            next,
            actual,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }

    var expr_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer expr_steps.deinit(self.shared.allocator);
    try collectSemanticStepCandidatesExpr(self, actual, &expr_steps);
    for (expr_steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToExpr(
            self,
            step,
            actual,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchSymbolicToSymbolicSemanticSearch(
            self,
            symbolic,
            next,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return false;
}

fn matchExprToSymbolicSemanticSearch(
    self: anytype,
    actual: ExprId,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    if (try tryMatchExprToSymbolicDirect(self, actual, symbolic, state)) {
        return true;
    }
    if (budget == 0) return false;
    if (!try noteExprSemanticSearchState(
        self,
        actual,
        symbolic,
        state,
        budget,
        visited,
    )) {
        return false;
    }
    if (try tryMatchExprToSymbolicChildrenSemantic(
        self,
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
    try collectSemanticStepCandidatesExpr(self, actual, &expr_steps);
    for (expr_steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToExpr(
            self,
            step,
            actual,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchSymbolicToSymbolicSemanticSearch(
            self,
            next,
            symbolic,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }

    var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer symbolic_steps.deinit(self.shared.allocator);
    try collectSemanticStepCandidatesSymbolic(self, symbolic, &symbolic_steps);
    for (symbolic_steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToSymbolic(
            self,
            step,
            symbolic,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchExprToSymbolicSemanticSearch(
            self,
            actual,
            next,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return false;
}

fn matchSymbolicToSymbolicSemanticSearch(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    if (try tryMatchSymbolicToSymbolicDirect(self, lhs, rhs, state)) {
        return true;
    }
    if (budget == 0) return false;
    if (!try noteSymbolicSemanticSearchState(
        self,
        lhs,
        rhs,
        state,
        budget,
        visited,
    )) {
        return false;
    }
    if (try tryMatchSymbolicToSymbolicChildrenSemantic(
        self,
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
    try collectSemanticStepCandidatesSymbolic(self, lhs, &lhs_steps);
    for (lhs_steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToSymbolic(
            self,
            step,
            lhs,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchSymbolicToSymbolicSemanticSearch(
            self,
            next,
            rhs,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }

    var rhs_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer rhs_steps.deinit(self.shared.allocator);
    try collectSemanticStepCandidatesSymbolic(self, rhs, &rhs_steps);
    for (rhs_steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToSymbolic(
            self,
            step,
            rhs,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchSymbolicToSymbolicSemanticSearch(
            self,
            lhs,
            next,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return false;
}

fn tryMatchSymbolicToExprChildrenSemantic(
    self: anytype,
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
        .placeholder => return false,
    };
    if (symbolic_app.term_id != actual_app.term_id) return false;
    if (symbolic_app.args.len != actual_app.args.len) return false;

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    var remaining_budget = budget;
    var used_semantic = false;
    for (symbolic_app.args, actual_app.args) |symbolic_arg, actual_arg| {
        if (try TransparentMatch.tryMatchSymbolicToExprDirect(
            self,
            symbolic_arg,
            actual_arg,
            state,
        )) {
            continue;
        }
        if (remaining_budget == 0) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
        remaining_budget -= 1;
        if (!try matchSymbolicToExprSemanticSearch(
            self,
            symbolic_arg,
            actual_arg,
            state,
            remaining_budget,
            visited,
        )) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
        used_semantic = true;
    }
    if (!used_semantic) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return used_semantic;
}

fn tryMatchExprToSymbolicDirect(
    self: anytype,
    actual: ExprId,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try TransparentMatch.matchExprToSymbolic(
        self,
        actual,
        symbolic,
        state,
        .transparent,
    )) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

fn tryMatchExprToSymbolicChildrenSemantic(
    self: anytype,
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
        .placeholder => return false,
    };
    const symbolic_app = switch (symbolic.*) {
        .app => |app| app,
        else => return false,
    };
    if (actual_app.term_id != symbolic_app.term_id) return false;
    if (actual_app.args.len != symbolic_app.args.len) return false;

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    var remaining_budget = budget;
    var used_semantic = false;
    for (actual_app.args, symbolic_app.args) |actual_arg, symbolic_arg| {
        if (try tryMatchExprToSymbolicDirect(
            self,
            actual_arg,
            symbolic_arg,
            state,
        )) {
            continue;
        }
        if (remaining_budget == 0) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
        remaining_budget -= 1;
        if (!try matchExprToSymbolicSemanticSearch(
            self,
            actual_arg,
            symbolic_arg,
            state,
            remaining_budget,
            visited,
        )) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
        used_semantic = true;
    }
    if (!used_semantic) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return used_semantic;
}

fn tryMatchSymbolicToSymbolicDirect(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try TransparentMatch.matchSymbolicToSymbolicState(
        self,
        lhs,
        rhs,
        state,
    )) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

    if (rhs.* == .fixed) {
        if (try TransparentMatch.matchExprToSymbolic(
            self,
            rhs.fixed,
            lhs,
            state,
            .transparent,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return false;
}

fn tryMatchSymbolicToSymbolicChildrenSemantic(
    self: anytype,
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

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    var remaining_budget = budget;
    var used_semantic = false;
    for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
        if (try tryMatchSymbolicToSymbolicDirect(
            self,
            lhs_arg,
            rhs_arg,
            state,
        )) {
            continue;
        }
        if (remaining_budget == 0) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
        remaining_budget -= 1;
        if (!try matchSymbolicToSymbolicSemanticSearch(
            self,
            lhs_arg,
            rhs_arg,
            state,
            remaining_budget,
            visited,
        )) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
        used_semantic = true;
    }
    if (!used_semantic) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return used_semantic;
}

fn applySemanticStepToExpr(
    self: anytype,
    step: SemanticStepCandidate,
    expr_id: ExprId,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    return switch (step) {
        .unfold_concrete_def => |unfold| if (unfold.expr_id != expr_id)
            null
        else
            try TransparentMatch.expandConcreteDef(self, expr_id, state),
        .unfold_symbolic_def => null,
        .rewrite_rule => |rule| try RewriteApplication.applyRewriteRuleToExpr(
            self,
            rule,
            expr_id,
            state,
        ),
        .acui => |acui| try applyAcuiToExpr(self, acui, expr_id),
    };
}

fn applySemanticStepToSymbolic(
    self: anytype,
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
                break :blk try TransparentMatch.expandConcreteDef(
                    self,
                    expr_id,
                    state,
                );
            },
            else => null,
        },
        .unfold_symbolic_def => |unfold| switch (symbolic.*) {
            .app => |app| if (app.term_id != unfold.term_id)
                null
            else
                try TransparentMatch.expandSymbolicApp(self, app, state),
            .fixed => |expr_id| blk: {
                const node = self.shared.theorem.interner.node(expr_id);
                const app = switch (node.*) {
                    .app => |value| value,
                    .variable => break :blk null,
                    .placeholder => break :blk null,
                };
                if (app.term_id != unfold.term_id) break :blk null;
                break :blk try TransparentMatch.expandConcreteDef(
                    self,
                    expr_id,
                    state,
                );
            },
            else => null,
        },
        .rewrite_rule => |rule| try RewriteApplication.applyRewriteRuleToSymbolic(
            self,
            rule,
            symbolic,
            state,
        ),
        .acui => |acui| try applyAcuiToSymbolic(self, acui, symbolic, state),
    };
}

fn applyAcuiToExpr(
    self: anytype,
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
    self: anytype,
    acui: ResolvedStructuralCombiner,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const plain = switch (symbolic.*) {
        .fixed => |expr_id| expr_id,
        else => (try WitnessState.symbolicToConcreteIfPlain(
            self,
            symbolic,
            state,
        )) orelse {
            return null;
        },
    };
    return try applyAcuiToExpr(self, acui, plain);
}

fn noteSemanticExprSearchState(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: ExprId,
    state: *const MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    return try noteSemanticSearchState(
        self,
        hashSymbolicForSearch(self, lhs),
        hashExprForSearch(rhs),
        state,
        budget,
        visited,
    );
}

fn noteExprSemanticSearchState(
    self: anytype,
    lhs: ExprId,
    rhs: *const SymbolicExpr,
    state: *const MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    return try noteSemanticSearchState(
        self,
        hashExprForSearch(lhs),
        hashSymbolicForSearch(self, rhs),
        state,
        budget,
        visited,
    );
}

fn noteSymbolicSemanticSearchState(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *const MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    return try noteSemanticSearchState(
        self,
        hashSymbolicForSearch(self, lhs),
        hashSymbolicForSearch(self, rhs),
        state,
        budget,
        visited,
    );
}

fn noteSemanticSearchState(
    self: anytype,
    lhs_hash: u64,
    rhs_hash: u64,
    state: *const MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    const key = SemanticSearchKey{
        .lhs_hash = lhs_hash,
        .rhs_hash = rhs_hash,
        .state_hash = try hashMatchSessionForSearch(self, state),
    };
    const entry = try visited.getOrPut(self.shared.allocator, key);
    if (entry.found_existing) {
        if (entry.value_ptr.* >= budget) return false;
    }
    entry.value_ptr.* = budget;
    return true;
}

fn hashExprForSearch(expr_id: ExprId) u64 {
    var hasher = std.hash.Wyhash.init(0x7419ef6a1fd348d1);
    const tag: u8 = 1;
    hasher.update(std.mem.asBytes(&tag));
    hasher.update(std.mem.asBytes(&expr_id));
    return hasher.final();
}

fn hashSymbolicForSearch(
    self: anytype,
    symbolic: *const SymbolicExpr,
) u64 {
    var hasher = std.hash.Wyhash.init(0x4fd443d41d41de49);
    hashSymbolicExprForSearch(self, symbolic, &hasher);
    return hasher.final();
}

fn hashSymbolicExprForSearch(
    self: anytype,
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
                hashSymbolicExprForSearch(self, arg, hasher);
            }
        },
    }
}

fn hashMatchSessionForSearch(
    self: anytype,
    state: *const MatchSession,
) anyerror!u64 {
    var hasher = std.hash.Wyhash.init(0x9ff6116d7c0ed8a3);

    hasher.update(std.mem.asBytes(&state.bindings.len));
    for (state.bindings) |binding_opt| {
        const present: u8 = if (binding_opt == null) 0 else 1;
        hasher.update(std.mem.asBytes(&present));
        if (binding_opt) |binding| {
            try hashBoundValueForSearch(self, binding, &hasher);
        }
    }

    hasher.update(std.mem.asBytes(&state.symbolic_dummy_infos.items.len));
    for (state.symbolic_dummy_infos.items) |info| {
        hasher.update(info.sort_name);
        hasher.update(std.mem.asBytes(&info.bound));
    }

    hashWitnessMapForSearch(state.witnesses, &hasher);
    hashWitnessMapForSearch(state.materialized_witnesses, &hasher);
    hashWitnessSlotMapForSearch(state.materialized_witness_slots, &hasher);
    hashDummyAliasMapForSearch(state.dummy_aliases, &hasher);
    return hasher.final();
}

fn hashBoundValueForSearch(
    self: anytype,
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
            hashSymbolicExprForSearch(self, concrete.repr, hasher);
        },
        .symbolic => |symbolic| {
            const tag: u8 = 7;
            const mode = @intFromEnum(symbolic.mode);
            hasher.update(std.mem.asBytes(&tag));
            hasher.update(std.mem.asBytes(&mode));
            hashSymbolicExprForSearch(self, symbolic.expr, hasher);
        },
    }
}

fn hashWitnessMapForSearch(
    map: WitnessMap,
    hasher: *std.hash.Wyhash,
) void {
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
}

fn hashWitnessSlotMapForSearch(
    map: WitnessSlotMap,
    hasher: *std.hash.Wyhash,
) void {
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
}

fn hashDummyAliasMapForSearch(
    map: DummyAliasMap,
    hasher: *std.hash.Wyhash,
) void {
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
}

pub fn matchTemplateSemantic(
    self: anytype,
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

    if (!try matchTemplateSemanticState(
        self,
        template,
        actual,
        &state,
        budget,
    )) {
        return false;
    }
    try WitnessState.representResolvedBindings(self, &state, bindings);
    return true;
}

pub fn matchSymbolicAcuiLeafToExprSemantic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    head_term_id: u32,
    state: *MatchSession,
    budget: usize,
) anyerror!bool {
    var visited: SemanticSearchVisited = .empty;
    defer visited.deinit(self.shared.allocator);
    return try matchSymbolicAcuiLeafToExprSemanticSearch(
        self,
        symbolic,
        actual,
        head_term_id,
        state,
        budget,
        &visited,
    );
}

fn matchSymbolicAcuiLeafToExprSemanticSearch(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    head_term_id: u32,
    state: *MatchSession,
    budget: usize,
    visited: *SemanticSearchVisited,
) anyerror!bool {
    if (try TransparentMatch.matchSymbolicAcuiLeafToExprState(
        self,
        symbolic,
        actual,
        head_term_id,
        state,
    )) {
        return true;
    }
    if (budget == 0) return false;
    if (!try noteSemanticExprSearchState(
        self,
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
                var snapshot = try WitnessState.saveMatchSnapshot(self, state);
                defer WitnessState.deinitMatchSnapshot(self, &snapshot);

                if (try matchSymbolicAcuiLeafToExprSemanticSearch(
                    self,
                    app.args[0],
                    actual,
                    head_term_id,
                    state,
                    budget,
                    visited,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                if (try matchSymbolicAcuiLeafToExprSemanticSearch(
                    self,
                    app.args[1],
                    actual,
                    head_term_id,
                    state,
                    budget,
                    visited,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
        },
        else => {},
    }

    var steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer steps.deinit(self.shared.allocator);
    try collectSemanticStepCandidatesSymbolic(self, symbolic, &steps);
    for (steps.items) |step| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        const next = try applySemanticStepToSymbolic(
            self,
            step,
            symbolic,
            state,
        ) orelse {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        };
        if (try matchSymbolicAcuiLeafToExprSemanticSearch(
            self,
            next,
            actual,
            head_term_id,
            state,
            budget - 1,
            visited,
        )) {
            return true;
        }
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    }
    return false;
}
