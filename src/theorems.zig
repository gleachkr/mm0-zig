const std = @import("std");
const Arg = @import("./args.zig").Arg;

pub const Theorem = extern struct {
    num_args: u16,
    reserved: u16,
    p_data: u32,

    pub fn getArgs(self: Theorem, file_bytes: []const u8) []const Arg {
        const data = file_bytes[self.p_data..];
        return @as([*]const Arg, @ptrCast(@alignCast(data.ptr)))[0..self.num_args];
    }

pub fn getUnifyPtr(self: Theorem, file_bytes: []const u8) u32 {
    _ = file_bytes;
    return @intCast(self.p_data + self.num_args * @sizeOf(Arg));
}

};
