const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Root = @import("witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const BoundValue = Types.BoundValue;
const UnresolvedDummyRoot = Types.UnresolvedDummyRoot;
const MatchSession = MatchState.MatchSession;
const ConcreteVarInfo = Types.ConcreteVarInfo;

const chooseRepresentative = Root.chooseRepresentative;
const concreteBindingMatchExpr = Root.concreteBindingMatchExpr;
const resolveDummySlot = Root.resolveDummySlot;

/// Materialize the current binding state, then project each binding
/// through its representative-selection mode.
pub fn representResolvedBindings(
    self: anytype,
    state: *MatchSession,
    bindings: []?ExprId,
) anyerror!void {
    for (state.bindings, 0..) |binding, idx| {
        bindings[idx] = if (binding) |bound| blk: {
            const materialized = try materializeResolvedBoundValue(
                self,
                bound,
                state,
            );
            break :blk try projectMaterializedExpr(
                self,
                materialized,
                switch (bound) {
                    .concrete => |concrete| concrete.mode,
                    .symbolic => |symbolic| symbolic.mode,
                },
            );
        } else null;
    }
}

fn exprDeps(self: anytype, expr_id: ExprId) anyerror!u55 {
    if (try self.shared.theorem.currentLeafInfo(expr_id)) |leaf| {
        return leaf.deps;
    }

    const app = switch (self.shared.theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => unreachable,
    };
    var deps: u55 = 0;
    for (app.args) |arg| {
        deps |= try exprDeps(self, arg);
    }
    return deps;
}

fn collectUnresolvedRootsInSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    out: *std.ArrayListUnmanaged(UnresolvedDummyRoot),
    seen_roots: *std.AutoHashMapUnmanaged(usize, void),
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (symbolic.*) {
        .binder => |idx| {
            const seen = try seen_binders.getOrPut(
                self.shared.allocator,
                idx,
            );
            if (seen.found_existing) return;
            const bound = state.bindings[idx] orelse {
                return error.MissingBinderAssignment;
            };
            try collectUnresolvedRootsInBoundValue(
                self,
                bound,
                state,
                out,
                seen_roots,
                seen_binders,
            );
        },
        .fixed => {},
        .dummy => |slot| {
            const root = try resolveDummySlot(slot, state);
            if (state.witnesses.get(root) != null or
                state.materialized_witnesses.get(root) != null) return;
            const seen = try seen_roots.getOrPut(
                self.shared.allocator,
                root,
            );
            if (seen.found_existing) return;
            const info = state.symbolic_dummy_infos.items[root];
            try out.append(self.shared.allocator, .{
                .root_slot = root,
                .sort_name = info.sort_name,
                .bound = info.bound,
            });
        },
        .app => |app| {
            for (app.args) |arg| {
                try collectUnresolvedRootsInSymbolic(
                    self,
                    arg,
                    state,
                    out,
                    seen_roots,
                    seen_binders,
                );
            }
        },
    }
}

pub fn collectUnresolvedRootsInBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
    out: *std.ArrayListUnmanaged(UnresolvedDummyRoot),
    seen_roots: *std.AutoHashMapUnmanaged(usize, void),
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (bound) {
        .concrete => |concrete| try collectUnresolvedRootsInSymbolic(
            self,
            concrete.repr,
            state,
            out,
            seen_roots,
            seen_binders,
        ),
        .symbolic => |symbolic| try collectUnresolvedRootsInSymbolic(
            self,
            symbolic.expr,
            state,
            out,
            seen_roots,
            seen_binders,
        ),
    }
}

fn collectConcreteDepsInSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    deps: *u55,
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (symbolic.*) {
        .binder => |idx| {
            const seen = try seen_binders.getOrPut(
                self.shared.allocator,
                idx,
            );
            if (seen.found_existing) return;
            const bound = state.bindings[idx] orelse {
                return error.MissingBinderAssignment;
            };
            try collectConcreteDepsInBoundValue(
                self,
                bound,
                state,
                deps,
                seen_binders,
            );
        },
        .fixed => |expr_id| deps.* |= try exprDeps(self, expr_id),
        .dummy => |slot| {
            const root = try resolveDummySlot(slot, state);
            if (state.witnesses.get(root)) |expr_id| {
                deps.* |= try exprDeps(self, expr_id);
            }
            if (state.materialized_witnesses.get(root)) |expr_id| {
                deps.* |= try exprDeps(self, expr_id);
            }
        },
        .app => |app| {
            for (app.args) |arg| {
                try collectConcreteDepsInSymbolic(
                    self,
                    arg,
                    state,
                    deps,
                    seen_binders,
                );
            }
        },
    }
}

pub fn collectConcreteDepsInBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
    deps: *u55,
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (bound) {
        .concrete => |concrete| {
            deps.* |= try exprDeps(self, concrete.raw);
            try collectConcreteDepsInSymbolic(
                self,
                concrete.repr,
                state,
                deps,
                seen_binders,
            );
        },
        .symbolic => |symbolic| try collectConcreteDepsInSymbolic(
            self,
            symbolic.expr,
            state,
            deps,
            seen_binders,
        ),
    }
}

/// Materialize the concrete expression justified by the current match
/// state without applying representative selection.
pub fn materializeResolvedBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (bound) {
        .concrete => |concrete| concrete.raw,
        .symbolic => |symbolic| try materializeResolvedSymbolic(
            self,
            symbolic.expr,
            state,
        ),
    };
}

/// Project a materialized expression through the binding mode's
/// representative-selection semantics.
pub fn projectMaterializedExpr(
    self: anytype,
    expr_id: ?ExprId,
    mode: BindingMode,
) anyerror!?ExprId {
    const materialized = expr_id orelse return null;
    return try chooseRepresentative(self, materialized, mode);
}

// This is the only escape path that turns symbolic match state back into
// main-theorem expressions. Internal matching and representative work
// should stay symbolic until a caller explicitly finalizes bindings.
/// Finalize a BoundValue to a concrete ExprId. Returns
/// error.UnresolvedDummyWitness if any hidden-dummy slot in the
/// symbolic structure lacks a witness.
pub fn finalizeBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!ExprId {
    return switch (bound) {
        .concrete => |concrete| {
            return (try concreteBindingMatchExpr(
                self,
                concrete,
                state,
            )) orelse error.MissingRepresentative;
        },
        .symbolic => |symbolic| {
            const expr_id = try materializeFinalSymbolic(
                self,
                symbolic.expr,
                state,
            );
            return try chooseRepresentative(self, expr_id, symbolic.mode);
        },
    };
}

pub fn materializeAssignedBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (bound) {
        .concrete => |concrete| try concreteBindingMatchExpr(
            self,
            concrete,
            state,
        ),
        .symbolic => |symbolic| {
            return try materializeAssignedSymbolic(
                self,
                symbolic.expr,
                state,
                symbolic.mode,
            );
        },
    };
}

pub fn materializeRepresentativeSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx >= state.bindings.len) break :blk null;
            const bound = state.bindings[idx] orelse break :blk null;
            break :blk try materializeAssignedBoundValue(self, bound, state);
        },
        .fixed => |expr| expr,
        .dummy => |slot| currentWitnessExpr(slot, state),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try materializeRepresentativeSymbolic(
                    self,
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

pub fn materializeAssignedSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!?ExprId {
    const expr_id = try materializeRepresentativeSymbolic(
        self,
        symbolic,
        state,
    ) orelse return null;
    return try chooseRepresentative(self, expr_id, mode);
}

pub fn materializeResolvedSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx >= state.bindings.len) {
                return error.TemplateBinderOutOfRange;
            }
            const bound = state.bindings[idx] orelse break :blk null;
            break :blk try materializeResolvedBoundValue(
                self,
                bound,
                state,
            );
        },
        .fixed => |expr_id| expr_id,
        .dummy => |slot| currentWitnessExpr(slot, state),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try materializeResolvedSymbolic(
                    self,
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
pub fn materializeFinalSymbolic(
    self: anytype,
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
            break :blk try finalizeBoundValue(self, bound, state);
        },
        .fixed => |expr_id| expr_id,
        .dummy => |slot| try resolveWitnessForDummySlot(slot, state),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = try materializeFinalSymbolic(
                    self,
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
    slot: usize,
    state: *const MatchSession,
) ?ExprId {
    const root = resolveDummySlot(slot, state) catch return null;
    return state.witnesses.get(root) orelse
        state.materialized_witnesses.get(root);
}

pub fn isProvisionalWitnessExpr(
    expr_id: ExprId,
    state: *const MatchSession,
) bool {
    return state.provisional_witness_infos.contains(expr_id) or
        state.materialized_witness_infos.contains(expr_id);
}

/// Resolve a hidden-dummy slot to a concrete ExprId. Only succeeds
/// if the slot was previously filled by a witness during matching.
/// Returns error.UnresolvedDummyWitness if the slot has no witness —
/// the user must provide explicit bindings that cover the hidden
/// def structure.
pub fn resolveWitnessForDummySlot(
    slot: usize,
    state: *MatchSession,
) anyerror!ExprId {
    const root = try resolveDummySlot(slot, state);
    if (state.witnesses.get(root)) |existing| return existing;
    if (state.materialized_witnesses.get(root)) |existing| return existing;
    return error.UnresolvedDummyWitness;
}

pub fn getConcreteLeafInfo(
    self: anytype,
    expr_id: ExprId,
) !?ConcreteVarInfo {
    const leaf = (try self.shared.theorem.currentLeafInfo(expr_id)) orelse {
        return null;
    };
    return .{
        .sort_name = leaf.sort_name,
        .bound = leaf.bound,
    };
}
