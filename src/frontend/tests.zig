const mm0 = @import("mm0");

comptime {
    _ = @import("./tests/root.zig");
    _ = mm0.DefOpsTests;
}
