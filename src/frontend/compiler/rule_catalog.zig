const std = @import("std");
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const CompilerDiag = @import("./diag.zig");
const Span = @import("../proof_script.zig").Span;

pub const Entry = struct {
    ordinal: u32,
    name_span: Span,
};

pub const Catalog = std.StringHashMap(Entry);

pub fn build(
    allocator: std.mem.Allocator,
    src: []const u8,
) !Catalog {
    var parser = MM0Parser.init(src, allocator);
    var catalog = Catalog.init(allocator);
    var ordinal: u32 = 0;

    while (try parser.next()) |stmt| {
        switch (stmt) {
            .assertion => |assertion| {
                try recordAssertion(
                    &catalog,
                    assertion,
                    ordinal,
                );
                ordinal += 1;
            },
            else => {},
        }
    }

    return catalog;
}

fn recordAssertion(
    catalog: *Catalog,
    assertion: AssertionStmt,
    ordinal: u32,
) !void {
    const gop = try catalog.getOrPut(assertion.name);
    if (gop.found_existing) return;
    gop.value_ptr.* = .{
        .ordinal = ordinal,
        .name_span = CompilerDiag.mathSpanToSpan(assertion.name_span),
    };
}
