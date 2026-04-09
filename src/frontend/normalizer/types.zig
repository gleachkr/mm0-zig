const ExprId = @import("../expr.zig").ExprId;

pub const NormalizeResult = struct {
    result_expr: ExprId,
    /// Index into the lines array of the conversion proof line,
    /// or null if the expression is unchanged (refl).
    conv_line_idx: ?usize,
};

pub const CommonTargetResult = struct {
    target_expr: ExprId,
    lhs_conv_line_idx: ?usize,
    rhs_conv_line_idx: ?usize,
};

pub const AcuiLeaf = struct {
    old_expr: ExprId,
    new_expr: ExprId,
    is_def: bool,
    conv_line_idx: ?usize = null,
};
