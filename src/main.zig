const std = @import("std");
const Mmb = @import("./mmb.zig").Mmb;
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

    const parsed = Mmb.parse(allocator, mmb) catch |err| {
        std.debug.print("Failed to parse {s}: {s}\n", .{
            args[1],
            @errorName(err),
        });
        std.process.exit(1);
    };

    // Create verifier
    const verifier = try Verifier.init(
        allocator,
        mmb,
        parsed.sort_table,
        parsed.term_table,
        parsed.theorem_table,
        &parsed.index,
    );
    defer verifier.deinit(allocator);

    // Create crosschecker
    const checker = try CrossChecker.init(mm0, allocator);
    defer checker.deinit(allocator);

    verifier.verifyProofStream(parsed.header.p_proof, checker) catch |err| {
        verifier.reportError(err);
        std.process.exit(1);
    };

    std.debug.print("Verification successful!\n", .{});
}
