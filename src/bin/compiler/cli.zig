const std = @import("std");
const mm0 = @import("mm0");

const UsageError = error{InvalidUsage};

const Command = union(enum) {
    compile: CompilePaths,
    join: JoinPaths,
};

const CompilePaths = struct {
    input: []const u8,
    proof: []const u8,
    output: []const u8,
};

const JoinPaths = struct {
    input: []const u8,
    output: []const u8,
};

pub fn usage() !void {
    var buf: [512]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const stdout = &w.interface;

    try stdout.writeAll(
        "Usage:\n" ++
            "  mm0-zigc compile INPUT.mm0 INPUT.proof OUTPUT.mmb\n" ++
            "  mm0-zigc join INPUT.mm0 OUTPUT.mm0\n",
    );
    try stdout.flush();
}

fn parseArgs(argv: []const []const u8) !Command {
    if (argv.len == 4 and std.mem.eql(u8, argv[0], "compile")) {
        return .{ .compile = .{
            .input = argv[1],
            .proof = argv[2],
            .output = argv[3],
        } };
    }
    if (argv.len == 3 and std.mem.eql(u8, argv[0], "join")) {
        return .{ .join = .{
            .input = argv[1],
            .output = argv[2],
        } };
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

pub fn run(
    allocator: std.mem.Allocator,
    argv: []const []const u8,
) !void {
    const command = try parseArgs(argv);

    switch (command) {
        .compile => |cmd| {
            const source = try loadSource(allocator, cmd.input);
            defer allocator.free(source);

            const proof = try loadSource(allocator, cmd.proof);
            defer allocator.free(proof);

            var compiler = mm0.Compiler.initWithProof(
                allocator,
                source,
                proof,
            );
            const mmb = compiler.compileMmb(allocator) catch |err| {
                std.debug.print("Failed to compile {s}\n", .{cmd.input});
                compiler.reportError(err);
                return err;
            };
            defer allocator.free(mmb);

            try std.fs.cwd().writeFile(.{
                .sub_path = cmd.output,
                .data = mmb,
            });
        },
        .join => |cmd| {
            const source = try loadSource(allocator, cmd.input);
            defer allocator.free(source);

            var compiler = mm0.Compiler.init(allocator, source);
            compiler.writeMm0() catch |err| switch (err) {
                error.Unimplemented => {
                    std.debug.print(
                        "join {s} -> {s}: emission is not implemented yet\n",
                        .{ cmd.input, cmd.output },
                    );
                    return err;
                },
                else => {
                    std.debug.print("Failed to join {s}\n", .{cmd.input});
                    compiler.reportError(err);
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
