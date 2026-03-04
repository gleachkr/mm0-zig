const std = @import("std");
const Header = @import("./headers.zig").Header;
const Sort = @import("./sorts.zig").Sort;
const Term = @import("./terms.zig").Term;
const Theorem = @import("./theorems.zig").Theorem;
const Verifier = @import("./verifier.zig").Verifier;
const CrossChecker = @import("./check.zig").CrossChecker;

pub fn usage() !void {
    var buf: [256]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const stdout = &w.interface;
    try stdout.writeAll("Usage: mm0-zig FILE.mmb < FILE.mm0\n");
    try stdout.flush();
}

pub fn main() !void {
    
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len != 2) {
        try usage();
        std.process.exit(1);
    }

    // XXX Not imposing any file size limit
    const mmb = try std.fs.cwd().readFileAlloc(allocator, args[1], std.math.maxInt(usize));
    defer allocator.free(mmb);

    const mm0 = try std.fs.File.readToEndAlloc(std.fs.File.stdin(), allocator, std.math.maxInt(usize));
    defer allocator.free(mm0);

    const header = try Header.fromBytes(mmb[0..@sizeOf(Header)]);

    const sort_bytes = mmb[@sizeOf(Header)..][0..header.num_sorts];
    const sort_table = @as([*]const Sort, @ptrCast(sort_bytes))[0..header.num_sorts];

    const term_bytes = mmb[header.p_terms..header.p_terms + header.num_terms * @sizeOf(Term)];
    if (header.p_terms % @alignOf(Term) != 0) return error.MisalignedTermTable;
    const term_table = @as([*]const Term, @ptrCast(@alignCast(term_bytes)))[0..header.num_terms];

    const theorem_bytes = mmb[header.p_thms..header.p_thms + header.num_thms * @sizeOf(Theorem)];
    if (header.p_thms % @alignOf(Theorem) != 0) return error.MisalignedTheoremTable;
    const theorem_table = @as([*]const Theorem, @ptrCast(@alignCast(theorem_bytes)))[0..header.num_thms];

    // Create verifier
    const verifier = try Verifier.init(allocator, mmb, sort_table, term_table, theorem_table);
    defer verifier.deinit(allocator);

    // Create crosschecker
    const checker = try CrossChecker.init(mm0, allocator);
    defer checker.deinit(allocator);

    try verifier.verifyProofStream(header.p_proof, checker);

    std.debug.print("Verification successful!\n", .{});
}

