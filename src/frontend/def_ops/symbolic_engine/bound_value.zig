const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Root = @import("witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const BindingSeed = Types.BindingSeed;
const BoundValue = Types.BoundValue;
const MatchSession = MatchState.MatchSession;

const chooseRepresentativeSymbolic = Root.chooseRepresentativeSymbolic;
const resymbolizeBinding = Root.resymbolizeBinding;
const boundValueMatchesExpr = Root.boundValueMatchesExpr;
const boundValueMatchesSymbolic = Root.boundValueMatchesSymbolic;
const concreteBindingMatchExpr = Root.concreteBindingMatchExpr;

pub fn rebuildBoundValue(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    mode: BindingMode,
) anyerror!BoundValue {
    if (try resymbolizeBinding(self, expr_id, state, witness_slots)) |symbolic| {
        return makeSymbolicBoundValue(self, symbolic, mode);
    }
    return try makeConcreteBoundValue(self, expr_id, state, mode);
}

pub fn rebuildBoundValueFromState(
    self: anytype,
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
    return try rebuildBoundValue(
        self,
        expr_id,
        state,
        &witness_slots,
        mode,
    );
}

pub fn makeConcreteBoundValue(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!BoundValue {
    return .{ .concrete = .{
        .raw = expr_id,
        .repr = try chooseRepresentativeSymbolic(
            self,
            expr_id,
            state,
            mode,
        ),
        .mode = mode,
    } };
}

pub fn makeSymbolicBoundValue(
    self: anytype,
    symbolic: *const SymbolicExpr,
    mode: BindingMode,
) BoundValue {
    _ = self;
    return .{ .symbolic = .{
        .expr = symbolic,
        .mode = mode,
    } };
}

pub fn invalidateRepresentativeCaches(state: *MatchSession) void {
    state.transparent_representatives.clearRetainingCapacity();
    state.normalized_representatives.clearRetainingCapacity();
}

pub fn assignBinderFromExpr(
    self: anytype,
    idx: usize,
    actual: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!bool {
    if (idx >= state.bindings.len) return false;
    if (state.bindings[idx]) |existing| {
        if (!try boundValueMatchesExpr(self, existing, actual, state)) {
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
                state.bindings[idx] = try rebuildBoundValueFromState(
                    self,
                    actual,
                    state,
                    mode,
                );
                invalidateRepresentativeCaches(state);
            },
        }
        return true;
    }
    state.bindings[idx] = try rebuildBoundValueFromState(
        self,
        actual,
        state,
        mode,
    );
    invalidateRepresentativeCaches(state);
    return true;
}

pub fn assignBinderFromSymbolic(
    self: anytype,
    idx: usize,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!bool {
    if (idx >= state.bindings.len) return false;
    if (state.bindings[idx]) |existing| {
        return try boundValueMatchesSymbolic(
            self,
            existing,
            symbolic,
            state,
        );
    }
    state.bindings[idx] = makeSymbolicBoundValue(self, symbolic, mode);
    invalidateRepresentativeCaches(state);
    return true;
}

pub fn assignBinderValue(
    self: anytype,
    idx: usize,
    value: BoundValue,
    state: *MatchSession,
) anyerror!bool {
    if (idx >= state.bindings.len) return false;
    if (state.bindings[idx]) |existing| {
        return switch (value) {
            .concrete => |concrete| blk: {
                const actual = (try concreteBindingMatchExpr(
                    self,
                    concrete,
                    state,
                )) orelse break :blk false;
                break :blk try boundValueMatchesExpr(
                    self,
                    existing,
                    actual,
                    state,
                );
            },
            .symbolic => |symbolic| try boundValueMatchesSymbolic(
                self,
                existing,
                symbolic.expr,
                state,
            ),
        };
    }
    state.bindings[idx] = value;
    invalidateRepresentativeCaches(state);
    return true;
}

pub fn boundValueFromSeed(
    self: anytype,
    seed: BindingSeed,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!?BoundValue {
    return switch (seed) {
        .none => null,
        .exact => |expr_id| try rebuildBoundValue(
            self,
            expr_id,
            state,
            witness_slots,
            .exact,
        ),
        .semantic => |semantic| try rebuildBoundValue(
            self,
            semantic.expr_id,
            state,
            witness_slots,
            semantic.mode,
        ),
        .bound => |bv| bv,
    };
}
