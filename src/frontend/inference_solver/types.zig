const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const ResolvedStructuralCombiner =
    @import("../rewrite_registry.zig").ResolvedStructuralCombiner;

pub const BinderSpace = enum {
    rule,
    view,
};

pub const MatchConstraint = struct {
    template: TemplateExpr,
    actual: ExprId,
};

pub const StructuralFragment = enum {
    au,
    acu,
    aui,
    acui,
};

pub const StructuralProfile = struct {
    combiner: ResolvedStructuralCombiner,
    fragment: StructuralFragment,

    pub fn init(combiner: ResolvedStructuralCombiner) StructuralProfile {
        const fragment: StructuralFragment = if (combiner.comm_id != null) blk: {
            break :blk if (combiner.idem_id != null) .acui else .acu;
        } else blk: {
            break :blk if (combiner.idem_id != null) .aui else .au;
        };
        return .{
            .combiner = combiner,
            .fragment = fragment,
        };
    }

    pub fn headTermId(self: StructuralProfile) u32 {
        return self.combiner.head_term_id;
    }

    pub fn unitTermId(self: StructuralProfile) u32 {
        return self.combiner.unit_term_id;
    }

    pub fn isCommutative(self: StructuralProfile) bool {
        return switch (self.fragment) {
            .acu, .acui => true,
            .au, .aui => false,
        };
    }

    pub fn isIdempotent(self: StructuralProfile) bool {
        return switch (self.fragment) {
            .aui, .acui => true,
            .au, .acu => false,
        };
    }
};

pub const StructuralTemplateItem = union(enum) {
    template: TemplateExpr,
    exact: ExprId,
};

pub const StructuralRemainder = struct {
    binder_idx: usize,
    item_pos: usize,
};

pub const StructuralJointObligation = struct {
    head_term_id: u32,
    unit_term_id: u32,
    lower_expr: ExprId,
    upper_expr: ExprId,
    binder_idxs: []const usize,
};

pub const StructuralInterval = struct {
    // Per-binder structural bounds. For ACUI these are real lower / upper
    // set bounds; for the other fragments Stage 3 still uses exact
    // lower == upper intervals and carries multi-binder obligations
    // separately.
    head_term_id: u32,
    unit_term_id: u32,
    lower_expr: ExprId,
    upper_expr: ExprId,
};

pub const BranchState = struct {
    rule_bindings: []?ExprId,
    view_bindings: ?[]?ExprId,
    rule_structural_intervals: []?StructuralInterval,
    view_structural_intervals: ?[]?StructuralInterval,
    rule_structural_obligations: []StructuralJointObligation,
    view_structural_obligations: ?[]StructuralJointObligation,
};
