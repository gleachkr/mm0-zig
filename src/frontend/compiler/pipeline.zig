const std = @import("std");
const CompilerContext = @import("./context.zig").CompilerContext;
const Common = @import("./pipeline/common.zig");
const Run = @import("./pipeline/run.zig");
const Analyze = @import("./pipeline/analyze.zig");

pub const Output = Common.Output;

pub fn run(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    emit: ?*Output,
) !void {
    return Run.run(self, allocator, emit);
}

pub fn analyze(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
) !void {
    return Analyze.analyze(self, allocator);
}

pub fn analyzeMm0(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
) !void {
    return Analyze.analyzeMm0(self, allocator);
}
