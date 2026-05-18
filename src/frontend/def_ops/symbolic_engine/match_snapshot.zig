const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Containers = @import("../../containers.zig");

const cloneMap = Containers.cloneMap;

const BoundValue = Types.BoundValue;
const MatchSession = MatchState.MatchSession;
const MatchSnapshot = MatchState.MatchSnapshot;

pub fn saveMatchSnapshot(
    self: anytype,
    state: *const MatchSession,
) anyerror!MatchSnapshot {
    return .{
        .bindings = try self.shared.allocator.dupe(?BoundValue, state.bindings),
        .witnesses = try cloneMap(self.shared.allocator, state.witnesses),
        .materialized_witnesses = try cloneMap(self.shared.allocator, state.materialized_witnesses),
        .materialized_witness_slots = try cloneMap(self.shared.allocator, state.materialized_witness_slots),
        .dummy_aliases = try cloneMap(self.shared.allocator, state.dummy_aliases),
        .provisional_witness_infos = try cloneMap(
            self.shared.allocator,
            state.provisional_witness_infos,
        ),
        .materialized_witness_infos = try cloneMap(
            self.shared.allocator,
            state.materialized_witness_infos,
        ),
        .transparent_representatives = try cloneMap(
            self.shared.allocator,
            state.transparent_representatives,
        ),
        .normalized_representatives = try cloneMap(
            self.shared.allocator,
            state.normalized_representatives,
        ),
        .dummy_info_len = state.symbolic_dummy_infos.items.len,
    };
}

pub fn restoreMatchSnapshot(
    self: anytype,
    snapshot: *const MatchSnapshot,
    state: *MatchSession,
) anyerror!void {
    @memcpy(state.bindings, snapshot.bindings);
    state.witnesses.deinit(self.shared.allocator);
    state.witnesses = try cloneMap(self.shared.allocator, snapshot.witnesses);
    state.materialized_witnesses.deinit(self.shared.allocator);
    state.materialized_witnesses =
        try cloneMap(self.shared.allocator, snapshot.materialized_witnesses);
    state.materialized_witness_slots.deinit(self.shared.allocator);
    state.materialized_witness_slots = try cloneMap(
        self.shared.allocator,
        snapshot.materialized_witness_slots,
    );
    state.dummy_aliases.deinit(self.shared.allocator);
    state.dummy_aliases = try cloneMap(
        self.shared.allocator,
        snapshot.dummy_aliases,
    );
    state.provisional_witness_infos.deinit(self.shared.allocator);
    state.provisional_witness_infos =
        try cloneMap(
            self.shared.allocator,
            snapshot.provisional_witness_infos,
        );
    state.materialized_witness_infos.deinit(self.shared.allocator);
    state.materialized_witness_infos =
        try cloneMap(
            self.shared.allocator,
            snapshot.materialized_witness_infos,
        );
    state.transparent_representatives.deinit(self.shared.allocator);
    state.transparent_representatives =
        try cloneMap(
            self.shared.allocator,
            snapshot.transparent_representatives,
        );
    state.normalized_representatives.deinit(self.shared.allocator);
    state.normalized_representatives =
        try cloneMap(
            self.shared.allocator,
            snapshot.normalized_representatives,
        );
    state.symbolic_dummy_infos.shrinkRetainingCapacity(
        snapshot.dummy_info_len,
    );
}

pub fn deinitMatchSnapshot(
    self: anytype,
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

pub fn cloneRepresentativeState(
    self: anytype,
    source: *const MatchSession,
    binding_len: usize,
) anyerror!MatchSession {
    var clone = try MatchSession.init(self.shared.allocator, binding_len);
    errdefer clone.deinit(self.shared.allocator);

    clone.witnesses = try cloneMap(self.shared.allocator, source.witnesses);
    clone.materialized_witnesses =
        try cloneMap(self.shared.allocator, source.materialized_witnesses);
    clone.materialized_witness_slots =
        try cloneMap(self.shared.allocator, source.materialized_witness_slots);
    clone.dummy_aliases = try cloneMap(self.shared.allocator, source.dummy_aliases);
    clone.provisional_witness_infos =
        try cloneMap(
            self.shared.allocator,
            source.provisional_witness_infos,
        );
    clone.materialized_witness_infos =
        try cloneMap(
            self.shared.allocator,
            source.materialized_witness_infos,
        );
    try clone.symbolic_dummy_infos.appendSlice(
        self.shared.allocator,
        source.symbolic_dummy_infos.items,
    );
    return clone;
}
