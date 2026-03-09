const Expr = @import("./expressions.zig").Expr;
const ConvProof = @import("./conversion.zig").ConvProof;
const ConvObligation = @import("./conversion.zig").ConvObligation;

pub const Entry = union(enum) {
    expr: *const Expr,
    proof: *const Expr,
    conv: ConvProof,
    conv_obligation: ConvObligation,
};
