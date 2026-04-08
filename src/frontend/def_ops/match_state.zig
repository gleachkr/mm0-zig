const std = @import("std");
const Types = @import("./types.zig");

pub const MatchSession = struct {
    bindings: []?Types.BoundValue,
    witnesses: Types.WitnessMap = .{},
    materialized_witnesses: Types.WitnessMap = .{},
    materialized_witness_slots: Types.WitnessSlotMap = .empty,
    dummy_aliases: Types.DummyAliasMap = .empty,
    provisional_witness_infos: Types.ProvisionalWitnessInfoMap = .empty,
    materialized_witness_infos: Types.MaterializedWitnessInfoMap = .empty,
    transparent_representatives: Types.RepresentativeCache = .empty,
    normalized_representatives: Types.RepresentativeCache = .empty,
    symbolic_dummy_infos: std.ArrayListUnmanaged(Types.SymbolicDummyInfo) = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        binding_len: usize,
    ) !MatchSession {
        const bindings = try allocator.alloc(?Types.BoundValue, binding_len);
        @memset(bindings, null);
        return .{
            .bindings = bindings,
        };
    }

    pub fn deinit(
        self: *MatchSession,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.bindings);
        self.witnesses.deinit(allocator);
        self.materialized_witnesses.deinit(allocator);
        self.materialized_witness_slots.deinit(allocator);
        self.dummy_aliases.deinit(allocator);
        self.provisional_witness_infos.deinit(allocator);
        self.materialized_witness_infos.deinit(allocator);
        self.transparent_representatives.deinit(allocator);
        self.normalized_representatives.deinit(allocator);
        self.symbolic_dummy_infos.deinit(allocator);
    }
};

pub const MatchSnapshot = struct {
    bindings: []?Types.BoundValue,
    witnesses: Types.WitnessMap,
    materialized_witnesses: Types.WitnessMap,
    materialized_witness_slots: Types.WitnessSlotMap,
    dummy_aliases: Types.DummyAliasMap,
    provisional_witness_infos: Types.ProvisionalWitnessInfoMap,
    materialized_witness_infos: Types.MaterializedWitnessInfoMap,
    transparent_representatives: Types.RepresentativeCache,
    normalized_representatives: Types.RepresentativeCache,
    dummy_info_len: usize,
};
