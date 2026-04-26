const USTACK_SIZE = @import("./constants.zig").USTACK_SIZE;
const Expr = @import("./expressions.zig").Expr;

pub const UStack = struct {
    entries: [USTACK_SIZE]*const Expr = undefined,
    top: usize = 0,

    pub fn push(self: *UStack, expr: *const Expr) !void {
        if (self.top >= USTACK_SIZE) return error.UStackOverflow;
        self.entries[self.top] = expr;
        self.top += 1;
    }

    pub fn pop(self: *UStack) !*const Expr {
        if (self.top == 0) return error.UStackUnderflow;
        self.top -= 1;
        const entries = &self.entries;
        return entries[self.top];
    }

    pub fn reset(self: *UStack) void {
        self.top = 0;
    }
};
