const std = @import("std");
const Expr = @import("./expressions.zig").Expr;

const MAX_HYP = 256; // or whatever bound makes sense

pub const HypList = struct {
    entries: [MAX_HYP]*const Expr = undefined,
    len: usize = 0,

    pub fn append(self: *HypList, expr: *const Expr) !void {
        if (self.len >= MAX_HYP) return error.TooManyHyps;
        self.entries[self.len] = expr;
        self.len += 1;
    }

    pub fn get(self: *HypList, index: usize) !*const Expr {
        if (index >= self.len) return error.HypOutOfBounds;
        return self.entries[index];
    }

    pub fn reset(self: *HypList) void {
        self.len = 0;
    }
};
