const std = @import("std");
const verifyMmbAgainstMm0 =
    @import("./support/verify_pair.zig").verifyMmbAgainstMm0;

const EXAMPLES_DIR = "third_party/mm0/examples";

const ExpectedOutcome = union(enum) {
    pass,
    compile_fail,
    verify_error: anyerror,
};

const ExpectedPair = struct {
    name: []const u8,
    outcome: ExpectedOutcome,
    reason: ?[]const u8 = null,
};

const expected_pairs = [_]ExpectedPair{
    .{ .name = "compiler", .outcome = .pass },
    .{
        .name = "hello_assembler",
        .outcome = .{ .verify_error = error.MM0Mismatch },
        .reason = "mm1 declares theorem hello_terminates without a proof; mm0 does " ++
            "not declare it, so declaration streams diverge.",
    },
    .{ .name = "hello_mmc", .outcome = .pass },
    .{ .name = "hol", .outcome = .pass },
    .{ .name = "mm0", .outcome = .pass },
    .{ .name = "peano", .outcome = .pass },
    .{ .name = "peano_hex", .outcome = .pass },
    .{ .name = "set", .outcome = .pass },
    .{
        .name = "verifier",
        .outcome = .compile_fail,
        .reason = "upstream example is intentionally incomplete and mm0-rs compile " ++
            "fails (missing theorem bodies/placeholders).",
    },
    .{ .name = "x86", .outcome = .pass },
};

const CommandResult = struct {
    term: std.process.Child.Term,
    stdout: []u8,
    stderr: []u8,

    fn deinit(self: *CommandResult, allocator: std.mem.Allocator) void {
        allocator.free(self.stdout);
        allocator.free(self.stderr);
    }
};

fn openExamplesDirOrSkip() !std.fs.Dir {
    std.fs.cwd().access(EXAMPLES_DIR, .{}) catch return error.SkipZigTest;
    return std.fs.cwd().openDir(EXAMPLES_DIR, .{ .iterate = true });
}

fn ensureMm0RsExists(allocator: std.mem.Allocator) !void {
    const result = std.process.Child.run(.{
        .allocator = allocator,
        .argv = &.{ "mm0-rs", "--version" },
        .max_output_bytes = 8 * 1024,
    }) catch |err| switch (err) {
        error.FileNotFound => return error.SkipZigTest,
        else => return err,
    };
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    switch (result.term) {
        .Exited => |code| {
            if (code != 0) return error.SkipZigTest;
        },
        else => return error.SkipZigTest,
    }
}

fn runCommand(
    allocator: std.mem.Allocator,
    cwd_dir: std.fs.Dir,
    argv: []const []const u8,
) !CommandResult {
    const result = try std.process.Child.run(.{
        .allocator = allocator,
        .argv = argv,
        .cwd_dir = cwd_dir,
        .max_output_bytes = 2 * 1024 * 1024,
    });
    return .{
        .term = result.term,
        .stdout = result.stdout,
        .stderr = result.stderr,
    };
}

fn expectCommandSuccess(argv: []const []const u8, result: CommandResult) !void {
    switch (result.term) {
        .Exited => |code| {
            if (code == 0) return;
            std.debug.print("command failed ({d}):\n", .{code});
        },
        else => {
            std.debug.print("command terminated unexpectedly:\n", .{});
        },
    }

    for (argv) |arg| {
        std.debug.print("  {s}\n", .{arg});
    }
    std.debug.print("stdout:\n{s}\n", .{result.stdout});
    std.debug.print("stderr:\n{s}\n", .{result.stderr});
    return error.CommandFailed;
}

fn findExpected(stem: []const u8) ?struct { idx: usize, pair: ExpectedPair } {
    inline for (expected_pairs, 0..) |entry, idx| {
        if (std.mem.eql(u8, stem, entry.name)) {
            return .{ .idx = idx, .pair = entry };
        }
    }
    return null;
}

fn getFilter(allocator: std.mem.Allocator) !?[]u8 {
    return std.process.getEnvVarOwned(
        allocator,
        "MM0_ZIG_EXAMPLE_FILTER",
    ) catch |err| switch (err) {
        error.EnvironmentVariableNotFound => null,
        else => return err,
    };
}

fn matchesFilter(filter: ?[]const u8, rel_mm1_path: []const u8) bool {
    if (filter) |needle| {
        return std.mem.indexOf(u8, rel_mm1_path, needle) != null;
    }
    return true;
}

test "integration: all example mm1/mm0 pairs" {
    const allocator = std.testing.allocator;
    var examples_dir = try openExamplesDirOrSkip();
    defer examples_dir.close();

    try ensureMm0RsExists(allocator);

    const filter = try getFilter(allocator);
    defer if (filter) |f| allocator.free(f);

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const tmp_abs = try tmp.parent_dir.realpathAlloc(allocator, &tmp.sub_path);
    defer allocator.free(tmp_abs);

    const out_mmb_path = try std.fs.path.join(allocator, &.{ tmp_abs, "example.mmb" });
    defer allocator.free(out_mmb_path);

    const joined_mm0_path = try std.fs.path.join(
        allocator,
        &.{ tmp_abs, "example_join.mm0" },
    );
    defer allocator.free(joined_mm0_path);

    var walker = try examples_dir.walk(allocator);
    defer walker.deinit();

    var seen: [expected_pairs.len]bool = .{false} ** expected_pairs.len;
    var paired_count: usize = 0;
    var skipped_no_mm0: usize = 0;
    var skipped_by_filter: usize = 0;

    while (try walker.next()) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.path, ".mm1")) continue;
        if (!matchesFilter(filter, entry.path)) {
            skipped_by_filter += 1;
            continue;
        }

        const mm1_rel = entry.path;
        const stem_rel = mm1_rel[0 .. mm1_rel.len - ".mm1".len];
        const mm0_rel = try std.fmt.allocPrint(allocator, "{s}.mm0", .{stem_rel});
        defer allocator.free(mm0_rel);

        examples_dir.access(mm0_rel, .{}) catch {
            skipped_no_mm0 += 1;
            continue;
        };

        const base = std.fs.path.basename(mm1_rel);
        const stem = base[0 .. base.len - ".mm1".len];
        const matched = findExpected(stem) orelse {
            std.debug.print("unexpected pair with no expectation: {s}\n", .{mm1_rel});
            return error.UnexpectedExamplePair;
        };

        const expected = matched.pair;
        seen[matched.idx] = true;
        paired_count += 1;

        var compile_result = try runCommand(
            allocator,
            examples_dir,
            &.{ "mm0-rs", "compile", mm1_rel, out_mmb_path },
        );
        defer compile_result.deinit(allocator);

        switch (expected.outcome) {
            .compile_fail => {
                switch (compile_result.term) {
                    .Exited => |code| {
                        if (code == 0) {
                            std.debug.print(
                                "expected compile failure but succeeded: {s}\n",
                                .{mm1_rel},
                            );
                            if (expected.reason) |reason| {
                                std.debug.print("reason: {s}\n", .{reason});
                            }
                            return error.ExpectedCompileFailure;
                        }
                    },
                    else => {},
                }
                continue;
            },
            else => try expectCommandSuccess(
                &.{ "mm0-rs", "compile", mm1_rel, out_mmb_path },
                compile_result,
            ),
        }

        var join_result = try runCommand(
            allocator,
            examples_dir,
            &.{ "mm0-rs", "join", mm0_rel, joined_mm0_path },
        );
        defer join_result.deinit(allocator);
        try expectCommandSuccess(
            &.{ "mm0-rs", "join", mm0_rel, joined_mm0_path },
            join_result,
        );

        const mm0 = try std.fs.cwd().readFileAlloc(
            allocator,
            joined_mm0_path,
            std.math.maxInt(usize),
        );
        defer allocator.free(mm0);

        const mmb = try std.fs.cwd().readFileAlloc(
            allocator,
            out_mmb_path,
            std.math.maxInt(usize),
        );
        defer allocator.free(mmb);

        switch (expected.outcome) {
            .pass => {
                verifyMmbAgainstMm0(allocator, mm0, mmb) catch |err| {
                    std.debug.print(
                        "verify failed for {s}: {s}\n",
                        .{ mm1_rel, @errorName(err) },
                    );
                    return err;
                };
            },
            .verify_error => |err| {
                std.testing.expectError(
                    err,
                    verifyMmbAgainstMm0(allocator, mm0, mmb),
                ) catch |got| {
                    std.debug.print(
                        "expected verify error {s} for {s}, got {s}\n",
                        .{ @errorName(err), mm1_rel, @errorName(got) },
                    );
                    if (expected.reason) |reason| {
                        std.debug.print("reason: {s}\n", .{reason});
                    }
                    return got;
                };
            },
            .compile_fail => unreachable,
        }
    }

    if (paired_count == 0 and filter != null) return error.SkipZigTest;
    if (paired_count == 0) return error.NoExamplePairsFound;

    if (filter == null) {
        inline for (expected_pairs, 0..) |entry, idx| {
            if (!seen[idx]) {
                std.debug.print(
                    "expected pair missing from scan: {s}\n",
                    .{entry.name},
                );
                return error.ExpectedPairMissing;
            }
        }
    }

    std.debug.print(
        "integration summary: paired={d} no-mm0={d} filtered={d}\n",
        .{ paired_count, skipped_no_mm0, skipped_by_filter },
    );
}
