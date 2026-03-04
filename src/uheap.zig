const UHEAP_SIZE = @import("./constants.zig").UHEAP_SIZE;
const Expr = @import("./expressions.zig").Expr;

pub const UHeap = struct {
    entries: [UHEAP_SIZE]*const Expr = undefined,
    len: usize = 0,

    pub fn push(self: *UHeap, expr: *const Expr) !void {
        if (self.len >= UHEAP_SIZE) return error.UHeapOverflow;
        self.entries[self.len] = expr;
        self.len += 1;
    }

    pub fn get(self: *UHeap, index: u32) !*const Expr {
        if (index >= self.len) return error.UHeapOutOfBounds;
        return self.entries[index];
    }

    pub fn reset(self: *UHeap) void {
        self.len = 0;
    }
};
