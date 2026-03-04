const Entry = @import("./entry.zig").Entry;
const HEAP_SIZE = @import("./constants.zig").HEAP_SIZE;

pub const Heap = struct {
    entries: [HEAP_SIZE]Entry = undefined,
    len: usize = 0,

    pub fn push(self: *Heap, entry: Entry) !void {
        if (self.len >= HEAP_SIZE) return error.HeapOverflow;
        self.entries[self.len] = entry;
        self.len += 1;
    }

    pub fn get(self: *Heap, index: u32) !Entry {
        if (index >= self.len) return error.HeapOutOfBounds;
        return self.entries[index];
    }
};
