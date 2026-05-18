const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Root = @import("witness_state.zig");

const SymbolicDummyInfo = Types.SymbolicDummyInfo;
const MatchSession = MatchState.MatchSession;

const invalidateRepresentativeCaches = Root.invalidateRepresentativeCaches;
const currentWitnessExpr = Root.currentWitnessExpr;

pub fn slotForWitness(
    self: anytype,
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
    invalidateRepresentativeCaches(state);
    return slot;
}

pub fn resolveDummySlot(
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
    return current;
}

pub fn putWitnessForDummySlot(
    self: anytype,
    slot: usize,
    actual: ExprId,
    state: *MatchSession,
) anyerror!void {
    const root = try resolveDummySlot(slot, state);
    try state.witnesses.put(self.shared.allocator, root, actual);
    invalidateRepresentativeCaches(state);
}

pub fn alignDummySlots(
    self: anytype,
    lhs_slot: usize,
    rhs_slot: usize,
    state: *MatchSession,
) anyerror!bool {
    const lhs_root = try resolveDummySlot(lhs_slot, state);
    const rhs_root = try resolveDummySlot(rhs_slot, state);
    if (lhs_root == rhs_root) return true;

    const lhs_info = state.symbolic_dummy_infos.items[lhs_root];
    const rhs_info = state.symbolic_dummy_infos.items[rhs_root];
    if (!std.mem.eql(u8, lhs_info.sort_name, rhs_info.sort_name)) {
        return false;
    }
    if (lhs_info.bound != rhs_info.bound) {
        return false;
    }

    const lhs_witness = currentWitnessExpr(lhs_root, state);
    const rhs_witness = currentWitnessExpr(rhs_root, state);
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
    invalidateRepresentativeCaches(state);
    return true;
}
