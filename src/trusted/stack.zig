const Entry = @import("./entry.zig").Entry;
const STACK_SIZE = @import("./constants.zig").STACK_SIZE;

pub const Stack = struct {
    entries: [STACK_SIZE]Entry = undefined,
    top: usize = 0,

    pub fn push(self: *Stack, entry: Entry) !void {
        if (self.top >= STACK_SIZE) return error.StackOverflow;
        self.entries[self.top] = entry;
        self.top += 1;
    }

    pub fn pop(self: *Stack) !Entry {
        if (self.top == 0) return error.StackUnderflow;
        self.top -= 1;
        const entries = &self.entries;
        return entries[self.top];
    }

    pub fn peek(self: *Stack) !Entry {
        if (self.top == 0) return error.StackUnderflow;
        const entries = &self.entries;
        return entries[self.top - 1];
    }
};
