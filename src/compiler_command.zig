const std = @import("std");
const mm0 = @import("mm0");

const UsageError = error{InvalidUsage};

const Command = union(enum) {
    compile: Paths,
    join: Paths,
};

const Paths = struct {
    input: []const u8,
    output: []const u8,
};

pub fn usage() !void {
    var buf: [512]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const stdout = &w.interface;

    try stdout.writeAll(
        "Usage:\n" ++
            "  mm0-zigc compile INPUT.mm0 OUTPUT.mmb\n" ++
            "  mm0-zigc join INPUT.mm0 OUTPUT.mm0\n",
    );
    try stdout.flush();
}

fn parseArgs(argv: []const []const u8) !Command {
    if (argv.len != 3) return UsageError.InvalidUsage;

    const paths = Paths{
        .input = argv[1],
        .output = argv[2],
    };

    if (std.mem.eql(u8, argv[0], "compile")) {
        return .{ .compile = paths };
    }
    if (std.mem.eql(u8, argv[0], "join")) {
        return .{ .join = paths };
    }
    return UsageError.InvalidUsage;
}

fn loadSource(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

fn reportUnimplemented(
    kind: []const u8,
    input: []const u8,
    output: []const u8,
) void {
    std.debug.print(
        "{s} {s} -> {s}: emission is not implemented yet\n",
        .{ kind, input, output },
    );
}

pub fn run(
    allocator: std.mem.Allocator,
    argv: []const []const u8,
) !void {
    const command = try parseArgs(argv);
    const paths = switch (command) {
        .compile => |cmd| cmd,
        .join => |cmd| cmd,
    };

    const source = try loadSource(allocator, paths.input);
    defer allocator.free(source);

    var compiler = mm0.Compiler.init(allocator, source);

    switch (command) {
        .compile => |cmd| {
            compiler.writeMmb() catch |err| switch (err) {
                error.Unimplemented => {
                    reportUnimplemented("compile", cmd.input, cmd.output);
                    return err;
                },
                else => {
                    std.debug.print(
                        "Failed to compile {s}: {s}\n",
                        .{ cmd.input, @errorName(err) },
                    );
                    return err;
                },
            };
        },
        .join => |cmd| {
            compiler.writeMm0() catch |err| switch (err) {
                error.Unimplemented => {
                    reportUnimplemented("join", cmd.input, cmd.output);
                    return err;
                },
                else => {
                    std.debug.print(
                        "Failed to join {s}: {s}\n",
                        .{ cmd.input, @errorName(err) },
                    );
                    return err;
                },
            };
        },
    }
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
