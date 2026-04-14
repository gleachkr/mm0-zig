const std = @import("std");
const mm0 = @import("mm0");
const compiler_lsp = @import("./lsp.zig");
const DebugConfig = mm0.DebugConfig;

const UsageError = error{InvalidUsage};

const CompilePaths = struct {
    input: []const u8,
    proof: []const u8,
    output: []const u8,
};

const CompileCommand = struct {
    paths: CompilePaths,
    debug: DebugConfig,
    warnings_as_errors: bool,
};

const Command = union(enum) {
    compile: CompileCommand,
    lsp,
};

pub fn usage() !void {
    var buf: [640]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const stdout = &w.interface;

    try stdout.writeAll(
        "Usage:\n" ++
            "  abc compile INPUT.mm0 INPUT.auf OUTPUT.mmb " ++
            "[--debug SYSTEMS] [-Werror]\n" ++
            "  abc lsp\n" ++
            "\nOptions:\n" ++
            "  --debug SYSTEMS  Enable debug output (comma-separated:\n" ++
            "                   inference,views,unfolding,normalization,emission,check,all)\n" ++
            "  -Werror          Treat compiler warnings as errors\n",
    );
    try stdout.flush();
}

fn parseCompileArgs(argv: []const []const u8) !Command {
    var debug = DebugConfig.none;
    var warnings_as_errors = false;
    var positional = std.ArrayListUnmanaged([]const u8){};
    var buf: [64][]const u8 = undefined;
    positional.items = buf[0..0];
    positional.capacity = buf.len;

    var i: usize = 0;
    while (i < argv.len) : (i += 1) {
        if (std.mem.eql(u8, argv[i], "--debug")) {
            i += 1;
            if (i >= argv.len) return UsageError.InvalidUsage;
            debug = DebugConfig.parse(argv[i]) catch {
                return UsageError.InvalidUsage;
            };
        } else if (std.mem.eql(u8, argv[i], "-Werror")) {
            warnings_as_errors = true;
        } else {
            positional.appendAssumeCapacity(argv[i]);
        }
    }

    const pos = positional.items;
    if (pos.len != 4 or !std.mem.eql(u8, pos[0], "compile")) {
        return UsageError.InvalidUsage;
    }

    return .{ .compile = .{
        .paths = .{
            .input = pos[1],
            .proof = pos[2],
            .output = pos[3],
        },
        .debug = debug,
        .warnings_as_errors = warnings_as_errors,
    } };
}

fn parseArgs(argv: []const []const u8) !Command {
    if (argv.len == 1 and std.mem.eql(u8, argv[0], "lsp")) {
        return .lsp;
    }
    return parseCompileArgs(argv);
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

fn runCompile(
    allocator: std.mem.Allocator,
    cmd: CompileCommand,
) !void {
    const source = try loadSource(allocator, cmd.paths.input);
    defer allocator.free(source);

    const proof = try loadSource(allocator, cmd.paths.proof);
    defer allocator.free(proof);

    var compiler = mm0.Compiler.initWithProof(
        allocator,
        source,
        proof,
    );
    compiler.debug = cmd.debug;
    compiler.warnings_as_errors = cmd.warnings_as_errors;
    const mmb = compiler.compileMmb(allocator) catch |err| {
        std.debug.print("Failed to compile {s}\n", .{cmd.paths.input});
        compiler.reportError(err);
        return err;
    };
    defer allocator.free(mmb);

    compiler.reportWarnings();

    try std.fs.cwd().writeFile(.{
        .sub_path = cmd.paths.output,
        .data = mmb,
    });
}

pub fn run(
    allocator: std.mem.Allocator,
    argv: []const []const u8,
) !void {
    const cmd = try parseArgs(argv);
    switch (cmd) {
        .compile => |compile| try runCompile(allocator, compile),
        .lsp => try compiler_lsp.run(allocator),
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
