const std = @import("std");
const mm0_lib = @import("mm0");

const Mmb = mm0_lib.Mmb;
const Verifier = mm0_lib.Verifier;
const CrossChecker = mm0_lib.CrossChecker;

pub fn verifyMmbAgainstMm0(
    allocator: std.mem.Allocator,
    mm0: []const u8,
    mmb: []u8,
) !void {
    const parsed = try Mmb.parse(allocator, mmb);

    const verifier = try Verifier.init(
        allocator,
        mmb,
        parsed.sort_table,
        parsed.term_table,
        parsed.theorem_table,
        &parsed.index,
    );
    defer verifier.deinit(allocator);

    const checker = try CrossChecker.init(mm0, allocator);
    defer checker.deinit(allocator);

    try verifier.verifyProofStream(parsed.header.p_proof, checker);
}
