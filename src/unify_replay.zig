const Proof = @import("./proof.zig");

// Shared opcode walker for unify streams.
//
// The stream format and traversal order are identical in the verifier,
// the cross-checker, and compiler-side argument inference. The only thing
// that changes between these uses is the meaning of the individual opcodes,
// so this helper owns only decoding and dispatch.
//
// Contexts passed here must provide these methods:
// - `uopTerm(term_id, save)`
// - `uopRef(heap_id)`
// - `uopDummy(sort_id)`
// - `uopHyp()`
pub fn run(
    file_bytes: []const u8,
    start_pos: u32,
    context: anytype,
) !void {
    var pos: usize = start_pos;
    while (true) {
        const cmd = try Proof.Cmd.read(file_bytes, pos, file_bytes.len);
        pos += cmd.size;
        switch (@as(Proof.UnifyCmd, @enumFromInt(cmd.op))) {
            .End => break,
            .UTerm => try context.uopTerm(cmd.data, false),
            .UTermSave => try context.uopTerm(cmd.data, true),
            .URef => try context.uopRef(cmd.data),
            .UDummy => try context.uopDummy(cmd.data),
            .UHyp => try context.uopHyp(),
            _ => return error.UnknownUnifyCmd,
        }
    }
}
