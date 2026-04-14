const StructuralMatcher = @import("./structural_matcher.zig");
const StructuralObligationSolver =
    @import("./structural_obligation_solver.zig");
const StructuralStateUpdates =
    @import("./structural_state_updates.zig");

pub const matchExpr = StructuralMatcher.matchExpr;
pub const solveStructuralObligation =
    StructuralObligationSolver.solveStructuralObligation;
pub const appendUniqueStateForSpace =
    StructuralStateUpdates.appendUniqueStateForSpace;
