const std = @import("std");
const ExprId = @import("../compiler_expr.zig").ExprId;

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

pub const ConcreteVarInfo = struct {
    sort_name: []const u8,
    bound: bool,
};
