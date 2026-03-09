const std = @import("std");
const mm0 = @import("mm0");

const UsageError = error{InvalidUsage};

pub fn usage() !void {
    var buf: [256]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const stdout = &w.interface;
    try stdout.writeAll("Usage: mm0-zig FILE.mmb < FILE.mm0\n");
    try stdout.flush();
}

pub fn run(
    allocator: std.mem.Allocator,
    argv: []const []const u8,
) !void {
    if (argv.len != 1) return UsageError.InvalidUsage;

    const mmb_path = argv[0];
    const cwd = std.fs.cwd();

    const mmb_bytes = try cwd.readFileAllocOptions(
        allocator,
        mmb_path,
        std.math.maxInt(usize),
        null,
        std.mem.Alignment.of(mm0.Arg),
        null,
    );
    defer allocator.free(mmb_bytes);

    const mm0_src = try std.fs.File.readToEndAlloc(
        std.fs.File.stdin(),
        allocator,
        std.math.maxInt(usize),
    );
    defer allocator.free(mm0_src);

    const parsed = mm0.Mmb.parse(allocator, mmb_bytes) catch |err| {
        std.debug.print("Failed to parse {s}: {s}\n", .{
            mmb_path,
            @errorName(err),
        });
        return err;
    };

    var session = mm0.VerificationSession.initParsed(
        allocator,
        mm0_src,
        parsed,
    ) catch |err| {
        std.debug.print("Failed to prepare verification: {s}\n", .{
            @errorName(err),
        });
        return err;
    };
    defer session.deinit();

    session.verify() catch |err| {
        session.verifier.reportError(err);
        return err;
    };

    std.debug.print("Verification successful!\n", .{});
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    run(allocator, args[1..]) catch |err| switch (err) {
        UsageError.InvalidUsage => {
            try usage();
            std.process.exit(1);
        },
        else => std.process.exit(1),
    };
}
