const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;

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

pub const SymbolicDummyInfo = struct {
    sort_name: []const u8,
    bound: bool,
};

pub const SymbolicExpr = union(enum) {
    binder: usize,
    fixed: ExprId,
    dummy: usize,
    app: App,

    pub const App = struct {
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
    /// Carry a pre-built BoundValue (possibly symbolic) from one session
    /// into another without collapsing it to a concrete ExprId first.
    bound: BoundValue,
};

pub const ConcreteBinding = struct {
    raw: ExprId,
    repr: *const SymbolicExpr,
    mode: BindingMode,
};

pub const SymbolicBinding = struct {
    expr: *const SymbolicExpr,
    mode: BindingMode,
};

pub const BoundValue = union(enum) {
    concrete: ConcreteBinding,
    symbolic: SymbolicBinding,
};

pub const WitnessMap = std.AutoHashMapUnmanaged(usize, ExprId);
pub const WitnessSlotMap = std.AutoHashMapUnmanaged(ExprId, usize);
pub const DummyAliasMap = std.AutoHashMapUnmanaged(usize, usize);
pub const ProvisionalWitnessInfoMap = std.AutoHashMapUnmanaged(
    ExprId,
    SymbolicDummyInfo,
);
pub const MaterializedWitnessInfoMap = std.AutoHashMapUnmanaged(
    ExprId,
    SymbolicDummyInfo,
);
pub const RepresentativeCache = std.AutoHashMapUnmanaged(
    ExprId,
    *const SymbolicExpr,
);

pub const MatchSeedState = struct {
    bindings: []BindingSeed,
    symbolic_dummy_infos: []SymbolicDummyInfo,
    witnesses: WitnessMap = .{},
    materialized_witnesses: WitnessMap = .{},
    materialized_witness_slots: WitnessSlotMap = .{},
    dummy_aliases: DummyAliasMap = .{},
    provisional_witness_infos: ProvisionalWitnessInfoMap = .{},
    materialized_witness_infos: MaterializedWitnessInfoMap = .{},

    pub fn deinit(self: *MatchSeedState, allocator: std.mem.Allocator) void {
        allocator.free(self.bindings);
        allocator.free(self.symbolic_dummy_infos);
        self.witnesses.deinit(allocator);
        self.materialized_witnesses.deinit(allocator);
        self.materialized_witness_slots.deinit(allocator);
        self.dummy_aliases.deinit(allocator);
        self.provisional_witness_infos.deinit(allocator);
        self.materialized_witness_infos.deinit(allocator);
    }
};

pub const ConcreteVarInfo = struct {
    sort_name: []const u8,
    bound: bool,
};
