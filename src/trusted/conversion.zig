const Expr = @import("./expressions.zig").Expr;

pub const ConvProof = struct {
    left: *const Expr,
    right: *const Expr,
};

pub const ConvObligation = struct {
    left: *const Expr,
    right: *const Expr,
};
