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
        const data = file_bytes[self.p_data..];
        return @as([*]const Arg, @ptrCast(@alignCast(data.ptr)))[0..self.num_args];
    }

    pub fn getRetArg(self: Term, file_bytes: []const u8) Arg {
        const offset = self.p_data + self.num_args * @sizeOf(Arg);
        return @as(*const Arg, @ptrCast(@alignCast(file_bytes[offset..].ptr))).*;
    }

    pub fn getUnifyPtr(self: Term, file_bytes: []const u8) ?u32 {
        if (!self.ret_sort.is_def) return null;
        _ = file_bytes;
        return @intCast(self.p_data + (self.num_args + 1) * @sizeOf(Arg));
    }

};

pub const RetSort = packed struct {
    /// index into the sort table
    sort: u7,
    /// is this a definition
    is_def: bool,
};
