const std = @import("std");
const mm0 = @import("mm0");
const DebugConfig = mm0.DebugConfig;

const UsageError = error{InvalidUsage};

const CompilePaths = struct {
    input: []const u8,
    proof: []const u8,
    output: []const u8,
};

const ParsedArgs = struct {
    paths: CompilePaths,
    debug: DebugConfig,
};

pub fn usage() !void {
    var buf: [512]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const stdout = &w.interface;

    try stdout.writeAll(
        "Usage:\n" ++
            "  mm0-zigc compile INPUT.mm0 INPUT.proof OUTPUT.mmb\n" ++
            "\nOptions:\n" ++
            "  --debug SYSTEMS  Enable debug output (comma-separated:\n" ++
            "                   inference,views,unfolding,normalization,emission,check,all)\n",
    );
    try stdout.flush();
}

fn parseArgs(argv: []const []const u8) !ParsedArgs {
    var debug = DebugConfig.none;
    var positional = std.ArrayListUnmanaged([]const u8){};
    // Use a small fixed buffer; we won't allocate.
    var buf: [64][]const u8 = undefined;
    positional.items = buf[0..0];
    positional.capacity = buf.len;

    var i: usize = 0;
    while (i < argv.len) : (i += 1) {
        if (std.mem.eql(u8, argv[i], "--debug")) {
            i += 1;
            if (i >= argv.len) return UsageError.InvalidUsage;
            debug = DebugConfig.parse(argv[i]) catch return UsageError.InvalidUsage;
        } else {
            positional.appendAssumeCapacity(argv[i]);
        }
    }

    const pos = positional.items;
    if (pos.len != 4 or !std.mem.eql(u8, pos[0], "compile")) {
        return UsageError.InvalidUsage;
    }

    return .{
        .paths = .{
            .input = pos[1],
            .proof = pos[2],
            .output = pos[3],
        },
        .debug = debug,
    };
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
    const parsed = try parseArgs(argv);
    const cmd = parsed.paths;

    const source = try loadSource(allocator, cmd.input);
    defer allocator.free(source);

    const proof = try loadSource(allocator, cmd.proof);
    defer allocator.free(proof);

    var compiler = mm0.Compiler.initWithProof(
        allocator,
        source,
        proof,
    );
    compiler.debug = parsed.debug;
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
