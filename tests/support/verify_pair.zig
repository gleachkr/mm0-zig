const std = @import("std");
const mm0_lib = @import("mm0");

const Header = mm0_lib.Header;
const Sort = mm0_lib.Sort;
const Term = mm0_lib.Term;
const Theorem = mm0_lib.Theorem;
const Verifier = mm0_lib.Verifier;
const CrossChecker = mm0_lib.CrossChecker;

pub fn verifyMmbAgainstMm0(
    allocator: std.mem.Allocator,
    mm0: []const u8,
    mmb: []u8,
) !void {
    if (mmb.len < @sizeOf(Header)) return error.ShortMmb;

    const header = try Header.fromBytes(mmb[0..@sizeOf(Header)]);

    if (header.num_sorts > 0) {
        const sort_end = @sizeOf(Header) + header.num_sorts;
        if (sort_end > mmb.len) return error.ShortSortTable;
    }

    const sort_bytes = mmb[@sizeOf(Header)..][0..header.num_sorts];
    const sort_table = @as([*]const Sort, @ptrCast(sort_bytes))[0..header.num_sorts];

    const term_start: usize = header.p_terms;
    const term_end = term_start + header.num_terms * @sizeOf(Term);
    if (term_end > mmb.len) return error.ShortTermTable;
    const term_bytes = mmb[term_start..term_end];
    if (header.p_terms % @alignOf(Term) != 0) return error.MisalignedTermTable;
    const term_table =
        @as([*]const Term, @ptrCast(@alignCast(term_bytes)))[0..header.num_terms];

    const thm_start: usize = header.p_thms;
    const thm_end = thm_start + header.num_thms * @sizeOf(Theorem);
    if (thm_end > mmb.len) return error.ShortTheoremTable;
    const theorem_bytes = mmb[thm_start..thm_end];
    if (header.p_thms % @alignOf(Theorem) != 0) {
        return error.MisalignedTheoremTable;
    }
    const theorem_table = @as(
        [*]const Theorem,
        @ptrCast(@alignCast(theorem_bytes)),
    )[0..header.num_thms];

    const verifier = try Verifier.init(
        allocator,
        mmb,
        sort_table,
        term_table,
        theorem_table,
    );
    defer verifier.deinit(allocator);

    const checker = try CrossChecker.init(mm0, allocator);
    defer checker.deinit(allocator);

    try verifier.verifyProofStream(header.p_proof, checker);
}
