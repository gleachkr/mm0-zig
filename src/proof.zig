const std = @import("std");

pub const ProofCmd = enum(u6) {
    End = 0x00,
    Term = 0x10,
    TermSave = 0x11,
    Ref = 0x12,
    Dummy = 0x13,
    Thm = 0x14,
    ThmSave = 0x15,
    Hyp = 0x16,
    Conv = 0x17,
    Refl = 0x18,
    Symm = 0x19,
    Cong = 0x1A,
    Unfold = 0x1B,
    ConvCut = 0x1C,
    ConvSave = 0x1E,
    Save = 0x1F,
    Sorry = 0x20,
    _, // allow unknown values without safety panic
};

pub const StmtCmd = enum(u6) {
    End = 0x00,
    Axiom = 0x02,
    Sort = 0x04,
    TermDef = 0x05,
    Thm = 0x06,
    LocalDef = 0x0D,
    LocalThm = 0x0E,
    _,
};

pub const UnifyCmd = enum(u6) {
    End = 0x00,
    UTerm = 0x30,
    UTermSave = 0x31,
    URef = 0x32,
    UDummy = 0x33,
    UHyp = 0x36,
    _,
};

pub const Cmd = struct {
    op: u6,
    data: u32,
    size: usize,

    pub fn read(bytes: []const u8, pos: usize, limit: usize) !Cmd {
        if (pos >= bytes.len or pos >= limit) return error.TruncatedCommand;

        const first = bytes[pos];
        const op: u6 = @truncate(first & 0x3F);
        const size: usize = switch (first >> 6) {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 5,
            else => unreachable,
        };
        const end = try std.math.add(usize, pos, size);
        if (end > bytes.len or end > limit) return error.TruncatedCommand;

        return switch (first >> 6) {
            0 => .{ .op = op, .data = 0, .size = 1 },
            1 => .{ .op = op, .data = bytes[pos + 1], .size = 2 },
            2 => .{
                .op = op,
                .data = @as(u32, bytes[pos + 1]) |
                    (@as(u32, bytes[pos + 2]) << 8),
                .size = 3,
            },
            3 => .{
                .op = op,
                .data = @as(u32, bytes[pos + 1]) |
                    (@as(u32, bytes[pos + 2]) << 8) |
                    (@as(u32, bytes[pos + 3]) << 16) |
                    (@as(u32, bytes[pos + 4]) << 24),
                .size = 5,
            },
            else => unreachable,
        };
    }
};
