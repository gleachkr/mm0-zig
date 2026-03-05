const UHEAP_SIZE = @import("./constants.zig").UHEAP_SIZE;
const Expr = @import("./expressions.zig").Expr;

pub const UHeapEntry = struct {
    expr: *const Expr,
    saved: bool,
};

pub const UHeap = struct {
    entries: [UHEAP_SIZE]UHeapEntry = undefined,
    len: usize = 0,

    pub fn push(self: *UHeap, expr: *const Expr) !void {
        return self.pushWithTag(expr, false);
    }

    pub fn pushSaved(self: *UHeap, expr: *const Expr) !void {
        return self.pushWithTag(expr, true);
    }

    fn pushWithTag(self: *UHeap, expr: *const Expr, saved: bool) !void {
        if (self.len >= UHEAP_SIZE) return error.UHeapOverflow;
        self.entries[self.len] = .{ .expr = expr, .saved = saved };
        self.len += 1;
    }

    pub fn get(self: *UHeap, index: u32) !*const Expr {
        if (index >= self.len) return error.UHeapOutOfBounds;
        return self.entries[index].expr;
    }

    pub fn reset(self: *UHeap) void {
        self.len = 0;
    }
};
