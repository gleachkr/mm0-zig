const std = @import("std");
const MM0Parser = @import("./parse.zig").MM0Parser;

pub const Compiler = struct {
    allocator: std.mem.Allocator,
    source: []const u8,

    pub fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
        };
    }

    pub fn check(self: *Compiler) !void {
        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(self.source, arena.allocator());
        while (try parser.next()) |_| {}
    }

    pub fn writeMmb(self: *Compiler) !void {
        try self.check();
        return error.Unimplemented;
    }

    pub fn writeMm0(self: *Compiler) !void {
        try self.check();
        return error.Unimplemented;
    }
};
