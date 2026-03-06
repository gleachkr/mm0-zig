const std = @import("std");
const Arg = @import("./args.zig").Arg;

pub const Theorem = extern struct {
    num_args: u16,
    reserved: u16,
    p_data: u32,

    pub fn getArgs(self: Theorem, file_bytes: []const u8) []const Arg {
        return self.getArgsChecked(file_bytes) catch unreachable;
    }

    pub fn getArgsChecked(self: Theorem, file_bytes: []const u8) ![]const Arg {
        const start: usize = self.p_data;
        const byte_len = try std.math.mul(usize, self.num_args, @sizeOf(Arg));
        const end = try std.math.add(usize, start, byte_len);
        if (end > file_bytes.len) return error.ShortTheoremData;
        if (start % @alignOf(Arg) != 0) return error.MisalignedArgTable;

        const data = file_bytes[start..end];
        return @as([*]const Arg, @ptrCast(@alignCast(data.ptr)))[0..self.num_args];
    }

    pub fn getUnifyPtr(self: Theorem, file_bytes: []const u8) u32 {
        return self.getUnifyPtrChecked(file_bytes) catch unreachable;
    }

    pub fn getUnifyPtrChecked(self: Theorem, file_bytes: []const u8) !u32 {
        const offset = try std.math.add(
            usize,
            self.p_data,
            try std.math.mul(usize, self.num_args, @sizeOf(Arg)),
        );
        if (offset > file_bytes.len) return error.ShortTheoremData;
        return @intCast(offset);
    }
};
