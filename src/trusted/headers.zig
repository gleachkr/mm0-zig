const std = @import("std");

pub const MAGIC = 0x42304D4D;

pub const Header = extern struct {
    /// 0x42304D4D ("MM0B" in ASCII)
    magic: u32,
    /// 1
    version: u8,
    /// how many sorts
    num_sorts: u8,
    /// 0
    reserved0: u16,
    /// how many terms and defs
    num_terms: u32,
    /// how many axioms and theorems
    num_thms: u32,
    /// pointer to term table
    p_terms: u32,
    /// pointer to theorem table
    p_thms: u32,
    /// pointer to proof stream
    p_proof: u32,
    /// 0
    reserved1: u32,
    /// pointer to index
    p_index: u64,

    pub fn fromBytes(bytes: []const u8) !Header {
        if (bytes.len != @sizeOf(Header)) return error.BadHeaderSize;

        var header: Header = undefined;
        @memcpy(std.mem.asBytes(&header), bytes);
        if (header.magic != MAGIC) return error.BadMagic;
        if (header.version != 1) return error.BadVersion;
        if (header.reserved0 != 0) return error.BadReserved;
        if (header.reserved1 != 0) return error.BadReserved;
        return header;
    }
};
