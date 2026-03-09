const std = @import("std");
const Arg = @import("./args.zig").Arg;

pub const Term = extern struct {
    /// how many arguments
    num_args: u16,
    /// what's the return sort
    ret_sort: RetSort,
    reserved: u8,
    /// pointer to the term data
    p_data: u32,

    pub fn getArgs(self: Term, file_bytes: []const u8) []const Arg {
        return self.getArgsChecked(file_bytes) catch unreachable;
    }

    pub fn getArgsChecked(
        self: Term,
        file_bytes: []const u8,
    ) ![]const Arg {
        const start: usize = self.p_data;
        const byte_len = try std.math.mul(usize, self.num_args, @sizeOf(Arg));
        const end = try std.math.add(usize, start, byte_len);
        if (end > file_bytes.len) return error.ShortTermData;
        if (self.num_args == 0) return &.{};
        if (start % @alignOf(Arg) != 0) return error.MisalignedArgTable;
        if (@intFromPtr(file_bytes.ptr) % @alignOf(Arg) != 0) {
            return error.MisalignedArgTable;
        }

        const data = file_bytes[start..end];
        const args_ptr: [*]const Arg = @ptrCast(@alignCast(data.ptr));
        return args_ptr[0..self.num_args];
    }

    pub fn getRetArg(self: Term, file_bytes: []const u8) Arg {
        return self.getRetArgChecked(file_bytes) catch unreachable;
    }

    pub fn getRetArgChecked(self: Term, file_bytes: []const u8) !Arg {
        const offset = try std.math.add(
            usize,
            self.p_data,
            try std.math.mul(usize, self.num_args, @sizeOf(Arg)),
        );
        const end = try std.math.add(usize, offset, @sizeOf(Arg));
        if (end > file_bytes.len) return error.ShortTermData;
        if (offset % @alignOf(Arg) != 0) return error.MisalignedArgTable;
        if (@intFromPtr(file_bytes.ptr) % @alignOf(Arg) != 0) {
            return error.MisalignedArgTable;
        }

        return @as(
            *const Arg,
            @ptrCast(@alignCast(file_bytes[offset..end].ptr)),
        ).*;
    }

    pub fn getUnifyPtr(self: Term, file_bytes: []const u8) ?u32 {
        return self.getUnifyPtrChecked(file_bytes) catch unreachable;
    }

    pub fn getUnifyPtrChecked(self: Term, file_bytes: []const u8) !?u32 {
        if (!self.ret_sort.is_def) return null;

        const offset = try std.math.add(
            usize,
            self.p_data,
            try std.math.mul(usize, self.num_args + 1, @sizeOf(Arg)),
        );
        if (offset > file_bytes.len) return error.ShortTermData;
        return @intCast(offset);
    }
};

pub const RetSort = packed struct {
    /// index into the sort table
    sort: u7,
    /// is this a definition
    is_def: bool,
};
