const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch = @import("./transparent_match.zig");
const Root = @import("witness_state.zig");

const SymbolicDummyInfo = Types.SymbolicDummyInfo;
const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const ConcreteBinding = Types.ConcreteBinding;
const BoundValue = Types.BoundValue;
const MatchSession = MatchState.MatchSession;

const assignBinderFromSymbolic = Root.assignBinderFromSymbolic;
const chooseRepresentativeSymbolic = Root.chooseRepresentativeSymbolic;
const symbolicToConcreteIfPlain = Root.symbolicToConcreteIfPlain;
const symbolicExprEql = Root.symbolicExprEql;
const resolveDummySlot = Root.resolveDummySlot;
const putWitnessForDummySlot = Root.putWitnessForDummySlot;
const alignDummySlots = Root.alignDummySlots;
const saveMatchSnapshot = Root.saveMatchSnapshot;
const restoreMatchSnapshot = Root.restoreMatchSnapshot;
const deinitMatchSnapshot = Root.deinitMatchSnapshot;
const materializeRepresentativeSymbolic = Root.materializeRepresentativeSymbolic;
const materializeAssignedSymbolic = Root.materializeAssignedSymbolic;
const materializeResolvedSymbolic = Root.materializeResolvedSymbolic;
const currentWitnessExpr = Root.currentWitnessExpr;
const isProvisionalWitnessExpr = Root.isProvisionalWitnessExpr;
const getConcreteLeafInfo = Root.getConcreteLeafInfo;

pub fn boundValueMatchesExpr(
    self: anytype,
    bound: BoundValue,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    return switch (bound) {
        .concrete => |concrete| {
            return try concreteBindingMatchesExpr(
                self,
                concrete,
                actual,
                state,
            );
        },
        .symbolic => |symbolic| {
            return try matchSymbolicToExprWithConcreteFallback(
                self,
                symbolic.expr,
                actual,
                state,
                symbolic.mode,
            );
        },
    };
}

/// Compare two concrete expressions using the representative relation for the
/// requested mode. This is the common concrete fallback used by normalized
/// matching and by transparent reuse of previously symbolic bindings.
pub fn concreteExprsMatchMode(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!bool {
    if (mode == .exact) return lhs == rhs;

    if (mode == .transparent) {
        // Transparent matching is strictly stronger than representative
        // equality, so try the direct relation first and only then fall back
        // to representative comparison.
        if ((try TransparentMatch.compareTransparent(self, lhs, rhs)) != null) {
            return true;
        }
    }

    const lhs_repr = try chooseRepresentativeSymbolic(
        self,
        lhs,
        state,
        mode,
    );
    const rhs_repr = try chooseRepresentativeSymbolic(
        self,
        rhs,
        state,
        mode,
    );
    if (symbolicExprEql(self, lhs_repr, rhs_repr)) {
        return true;
    }

    if (mode != .normalized) return false;

    const lhs_compare = (try symbolicToConcreteIfPlain(
        self,
        lhs_repr,
        state,
    )) orelse lhs;
    const rhs_compare = (try symbolicToConcreteIfPlain(
        self,
        rhs_repr,
        state,
    )) orelse rhs;
    return (try TransparentMatch.compareTransparent(
        self,
        lhs_compare,
        rhs_compare,
    )) != null;
}

pub fn concreteBindingMatchesExpr(
    self: anytype,
    concrete: ConcreteBinding,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (concrete.mode == .exact) {
        return concrete.raw == actual;
    }

    const concrete_expr = (try concreteBindingMatchExpr(
        self,
        concrete,
        state,
    )) orelse return false;
    if ((concrete.mode == .transparent or concrete.mode == .normalized) and
        (try TransparentMatch.compareTransparent(
            self,
            concrete_expr,
            actual,
        )) != null)
    {
        return true;
    }

    const actual_repr = try chooseRepresentativeSymbolic(
        self,
        actual,
        state,
        concrete.mode,
    );
    return symbolicExprEql(self, concrete.repr, actual_repr);
}

fn matchSymbolicToExprWithConcreteFallback(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!bool {
    var snapshot = try saveMatchSnapshot(self, state);
    defer deinitMatchSnapshot(self, &snapshot);

    if (try TransparentMatch.matchSymbolicToExprState(
        self,
        symbolic,
        actual,
        state,
    )) {
        return true;
    }
    try restoreMatchSnapshot(self, &snapshot, state);

    // If structural replay fails but the symbolic value can already be
    // resolved to a concrete expression, compare representatives instead.
    // This mirrors the extra strength that normalized matching already had.
    const symbolic_expr = try materializeResolvedSymbolic(
        self,
        symbolic,
        state,
    ) orelse return false;
    return try concreteExprsMatchMode(
        self,
        symbolic_expr,
        actual,
        state,
        mode,
    );
}

pub fn boundValueMatchesSymbolic(
    self: anytype,
    bound: BoundValue,
    actual: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    return switch (bound) {
        .concrete => |concrete| {
            const match_expr = (try concreteBindingMatchExpr(
                self,
                concrete,
                state,
            )) orelse return false;
            return try TransparentMatch.matchExprToSymbolic(
                self,
                match_expr,
                actual,
                state,
                concrete.mode,
            );
        },
        .symbolic => |symbolic| {
            return try TransparentMatch.matchSymbolicToSymbolicState(
                self,
                symbolic.expr,
                actual,
                state,
            );
        },
    };
}

pub fn concreteBindingMatchExpr(
    self: anytype,
    concrete: ConcreteBinding,
    state: *MatchSession,
) anyerror!?ExprId {
    if (concrete.mode == .exact) return concrete.raw;
    return try materializeRepresentativeSymbolic(
        self,
        concrete.repr,
        state,
    );
}

pub fn matchSymbolicDummyState(
    self: anytype,
    slot: usize,
    info: SymbolicDummyInfo,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const root = try resolveDummySlot(self, slot, state);
    const root_info = state.symbolic_dummy_infos.items[root];

    // Matching a symbolic dummy against a non-variable is a plain mismatch,
    // not a fatal error.
    const actual_info =
        (try getConcreteLeafInfo(self, actual)) orelse return false;
    if (root_info.bound and !actual_info.bound) return false;
    if (!std.mem.eql(u8, root_info.sort_name, actual_info.sort_name)) {
        return false;
    }
    _ = info;

    if (currentWitnessExpr(self, root, state)) |existing| {
        if (existing == actual) return true;
        if (isProvisionalWitnessExpr(self, existing, state)) {
            try putWitnessForDummySlot(self, root, actual, state);
            return true;
        }
        return false;
    }
    try putWitnessForDummySlot(self, root, actual, state);
    return true;
}

pub fn matchDummyToSymbolic(
    self: anytype,
    slot: usize,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    return switch (rhs.*) {
        .binder => |idx| blk: {
            const symbolic = try self.allocSymbolic(.{ .dummy = slot });
            break :blk try assignBinderFromSymbolic(
                self,
                idx,
                symbolic,
                state,
                .transparent,
            );
        },
        .fixed => |expr_id| {
            const info = state.symbolic_dummy_infos.items[slot];
            return try matchSymbolicDummyState(
                self,
                slot,
                info,
                expr_id,
                state,
            );
        },
        .dummy => |rhs_slot| {
            return try alignDummySlots(self, slot, rhs_slot, state);
        },
        .app => {
            const rhs_expr = try materializeAssignedSymbolic(
                self,
                rhs,
                state,
                .transparent,
            ) orelse return false;
            const info = state.symbolic_dummy_infos.items[slot];
            return try matchSymbolicDummyState(
                self,
                slot,
                info,
                rhs_expr,
                state,
            );
        },
    };
}
