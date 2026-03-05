const std = @import("std");
const mm0 = @import("mm0");

const Arg = mm0.Arg;
const Expr = mm0.Expr;
const Header = mm0.Header;
const MAGIC = mm0.MAGIC;
const Heap = mm0.Heap;
const MM0Parser = mm0.MM0Parser;
const Proof = mm0.Proof;
const Sort = mm0.Sort;
const Stack = mm0.Stack;
const Term = mm0.Term;
const Theorem = mm0.Theorem;

fn fillHeaderBytes(
    out: *align(@alignOf(Header)) [@sizeOf(Header)]u8,
    header: Header,
) void {
    @memcpy(out[0..], std.mem.asBytes(&header));
}

fn writeArg(buf: []u8, offset: usize, arg: Arg) void {
    @memcpy(buf[offset..][0..@sizeOf(Arg)], std.mem.asBytes(&arg));
}

test "header parsing accepts valid header" {
    const header = Header{
        .magic = MAGIC,
        .version = 1,
        .num_sorts = 2,
        .reserved0 = 0,
        .num_terms = 3,
        .num_thms = 4,
        .p_terms = 32,
        .p_thms = 64,
        .p_proof = 96,
        .reserved1 = 0,
        .p_index = 128,
    };

    var bytes: [@sizeOf(Header)]u8 align(@alignOf(Header)) = undefined;
    fillHeaderBytes(&bytes, header);
    const parsed = try Header.fromBytes(&bytes);
    try std.testing.expectEqual(header.magic, parsed.magic);
    try std.testing.expectEqual(header.num_terms, parsed.num_terms);
    try std.testing.expectEqual(header.p_index, parsed.p_index);
}

test "header parsing rejects invalid fields" {
    const base = Header{
        .magic = MAGIC,
        .version = 1,
        .num_sorts = 0,
        .reserved0 = 0,
        .num_terms = 0,
        .num_thms = 0,
        .p_terms = 0,
        .p_thms = 0,
        .p_proof = 0,
        .reserved1 = 0,
        .p_index = 0,
    };

    var bad_magic: [@sizeOf(Header)]u8 align(@alignOf(Header)) = undefined;
    fillHeaderBytes(&bad_magic, Header{
        .magic = 0,
        .version = base.version,
        .num_sorts = base.num_sorts,
        .reserved0 = base.reserved0,
        .num_terms = base.num_terms,
        .num_thms = base.num_thms,
        .p_terms = base.p_terms,
        .p_thms = base.p_thms,
        .p_proof = base.p_proof,
        .reserved1 = base.reserved1,
        .p_index = base.p_index,
    });
    try std.testing.expectError(error.BadMagic, Header.fromBytes(&bad_magic));

    var bad_version: [@sizeOf(Header)]u8 align(@alignOf(Header)) = undefined;
    fillHeaderBytes(&bad_version, Header{
        .magic = base.magic,
        .version = 7,
        .num_sorts = base.num_sorts,
        .reserved0 = base.reserved0,
        .num_terms = base.num_terms,
        .num_thms = base.num_thms,
        .p_terms = base.p_terms,
        .p_thms = base.p_thms,
        .p_proof = base.p_proof,
        .reserved1 = base.reserved1,
        .p_index = base.p_index,
    });
    try std.testing.expectError(error.BadVersion, Header.fromBytes(&bad_version));

    var bad_reserved: [@sizeOf(Header)]u8 align(@alignOf(Header)) = undefined;
    fillHeaderBytes(&bad_reserved, Header{
        .magic = base.magic,
        .version = base.version,
        .num_sorts = base.num_sorts,
        .reserved0 = 1,
        .num_terms = base.num_terms,
        .num_thms = base.num_thms,
        .p_terms = base.p_terms,
        .p_thms = base.p_thms,
        .p_proof = base.p_proof,
        .reserved1 = base.reserved1,
        .p_index = base.p_index,
    });
    try std.testing.expectError(error.BadReserved, Header.fromBytes(&bad_reserved));
}

test "Arg dependency helpers" {
    const arg = Arg{
        .deps = 0b1010,
        .reserved = 0,
        .sort = 3,
        .bound = false,
    };

    try std.testing.expect(!arg.dependsOn(0));
    try std.testing.expect(arg.dependsOn(1));
    try std.testing.expect(arg.dependsOn(3));
    try std.testing.expect(arg.depsOverlap(0b1000));
    try std.testing.expect(!arg.depsOverlap(0b0100));
}

test "proof command decoding handles all payload sizes" {
    const cmd1 = Proof.Cmd.read(&[_]u8{0x1A}, 0);
    try std.testing.expectEqual(@as(u6, 0x1A), cmd1.op);
    try std.testing.expectEqual(@as(u32, 0), cmd1.data);
    try std.testing.expectEqual(@as(usize, 1), cmd1.size);

    const cmd2 = Proof.Cmd.read(&[_]u8{ 0x45, 0x7F }, 0);
    try std.testing.expectEqual(@as(u6, 0x05), cmd2.op);
    try std.testing.expectEqual(@as(u32, 0x7F), cmd2.data);
    try std.testing.expectEqual(@as(usize, 2), cmd2.size);

    const cmd3 = Proof.Cmd.read(&[_]u8{ 0x91, 0xCD, 0xAB }, 0);
    try std.testing.expectEqual(@as(u6, 0x11), cmd3.op);
    try std.testing.expectEqual(@as(u32, 0xABCD), cmd3.data);
    try std.testing.expectEqual(@as(usize, 3), cmd3.size);

    const cmd4 = Proof.Cmd.read(&[_]u8{ 0xE2, 0x44, 0x33, 0x22, 0x11 }, 0);
    try std.testing.expectEqual(@as(u6, 0x22), cmd4.op);
    try std.testing.expectEqual(@as(u32, 0x11223344), cmd4.data);
    try std.testing.expectEqual(@as(usize, 5), cmd4.size);
}

test "MM0 parser parses sort modifiers" {
    const src =
        \\-- comment
        \\pure strict provable free sort wff;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    const stmt = (try parser.next()).?;

    switch (stmt) {
        .sort => |sort_stmt| {
            try std.testing.expectEqualStrings("wff", sort_stmt.name);
            try std.testing.expect(sort_stmt.modifiers.pure);
            try std.testing.expect(sort_stmt.modifiers.strict);
            try std.testing.expect(sort_stmt.modifiers.provable);
            try std.testing.expect(sort_stmt.modifiers.free);
        },
        else => return error.UnexpectedStatementKind,
    }

    try std.testing.expect((try parser.next()) == null);
}

test "MM0 parser handles binders and dependencies" {
    const src =
        \\term app {x: wff} (h: wff x) (.d: wff x) : wff;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    const stmt = (try parser.next()).?;

    switch (stmt) {
        .term => |term_stmt| {
            try std.testing.expectEqualStrings("app", term_stmt.name);
            try std.testing.expectEqualStrings("wff", term_stmt.ret_sort_name);
            try std.testing.expectEqual(@as(usize, 2), term_stmt.args.len);

            const bound_arg = term_stmt.args[0];
            try std.testing.expect(bound_arg.bound);
            try std.testing.expectEqual(@as(u55, 1), bound_arg.deps);
            try std.testing.expectEqualStrings("wff", bound_arg.sort_name);

            const regular_arg = term_stmt.args[1];
            try std.testing.expect(!regular_arg.bound);
            try std.testing.expectEqual(@as(u55, 1), regular_arg.deps);
            try std.testing.expectEqualStrings("wff", regular_arg.sort_name);
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser handles arrow-style term signatures" {
    const src =
        \\term ch: hex > hex > char;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    const stmt = (try parser.next()).?;

    switch (stmt) {
        .term => |term_stmt| {
            try std.testing.expectEqualStrings("ch", term_stmt.name);
            try std.testing.expectEqualStrings("char", term_stmt.ret_sort_name);
            try std.testing.expectEqual(@as(usize, 2), term_stmt.args.len);
            try std.testing.expectEqualStrings("hex", term_stmt.args[0].sort_name);
            try std.testing.expectEqualStrings("hex", term_stmt.args[1].sort_name);
            try std.testing.expect(!term_stmt.args[0].bound);
            try std.testing.expect(!term_stmt.args[1].bound);
            try std.testing.expectEqual(@as(u55, 0), term_stmt.args[0].deps);
            try std.testing.expectEqual(@as(u55, 0), term_stmt.args[1].deps);
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser handles dependent args in arrow signatures" {
    const src =
        \\term lam {x: term}: type > term x > term;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    const stmt = (try parser.next()).?;

    switch (stmt) {
        .term => |term_stmt| {
            try std.testing.expectEqualStrings("lam", term_stmt.name);
            try std.testing.expectEqualStrings("term", term_stmt.ret_sort_name);
            try std.testing.expectEqual(@as(usize, 3), term_stmt.args.len);

            try std.testing.expect(term_stmt.args[0].bound);
            try std.testing.expectEqual(@as(u55, 1), term_stmt.args[0].deps);
            try std.testing.expectEqualStrings("term", term_stmt.args[0].sort_name);

            try std.testing.expect(!term_stmt.args[1].bound);
            try std.testing.expectEqual(@as(u55, 0), term_stmt.args[1].deps);
            try std.testing.expectEqualStrings("type", term_stmt.args[1].sort_name);

            try std.testing.expect(!term_stmt.args[2].bound);
            try std.testing.expectEqual(@as(u55, 1), term_stmt.args[2].deps);
            try std.testing.expectEqualStrings("term", term_stmt.args[2].sort_name);
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser skips local theorems and unknown declarations" {
    const src =
        \\notation "|-";
        \\theorem visible0 {x: wff}: $ |- x $;
        \\local theorem hidden {x: wff}: $ |- x $;
        \\pub theorem visible1 {x: wff}: $ |- x $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    const stmt0 = (try parser.next()).?;
    switch (stmt0) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("visible0", assert_stmt.name);
            try std.testing.expectEqual(@as(usize, 1), assert_stmt.args.len);
            try std.testing.expect(assert_stmt.args[0].bound);
        },
        else => return error.UnexpectedStatementKind,
    }

    const stmt1 = (try parser.next()).?;
    switch (stmt1) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("visible1", assert_stmt.name);
            try std.testing.expectEqual(@as(usize, 1), assert_stmt.args.len);
            try std.testing.expect(assert_stmt.args[0].bound);
        },
        else => return error.UnexpectedStatementKind,
    }

    try std.testing.expect((try parser.next()) == null);
}

test "stack and heap basic behavior" {
    var expr = Expr{ .variable = .{ .sort = 1, .bound = false, .deps = 0 } };

    var stack = Stack{};
    try stack.push(.{ .expr = &expr });
    const top = try stack.peek();
    try std.testing.expect(top == .expr);
    try std.testing.expect(top.expr == &expr);

    const popped = try stack.pop();
    try std.testing.expect(popped == .expr);
    try std.testing.expect(popped.expr == &expr);
    try std.testing.expectError(error.StackUnderflow, stack.pop());

    var heap = Heap{};
    try heap.push(.{ .expr = &expr });
    const got = try heap.get(0);
    try std.testing.expect(got == .expr);
    try std.testing.expect(got.expr == &expr);
    try std.testing.expectError(error.HeapOutOfBounds, heap.get(1));
}

test "term and theorem accessors read packed argument tables" {
    var bytes: [128]u8 align(@alignOf(Arg)) = std.mem.zeroes([128]u8);
    const p_data: usize = 16;

    const arg0 = Arg{ .deps = 1, .reserved = 0, .sort = 2, .bound = true };
    const arg1 = Arg{ .deps = 3, .reserved = 0, .sort = 4, .bound = false };
    const ret = Arg{ .deps = 0, .reserved = 0, .sort = 5, .bound = false };

    writeArg(bytes[0..], p_data, arg0);
    writeArg(bytes[0..], p_data + @sizeOf(Arg), arg1);
    writeArg(bytes[0..], p_data + 2 * @sizeOf(Arg), ret);

    const term = Term{
        .num_args = 2,
        .ret_sort = .{ .sort = 6, .is_def = true },
        .reserved = 0,
        .p_data = @intCast(p_data),
    };

    const term_args = term.getArgs(bytes[0..]);
    try std.testing.expectEqual(@as(usize, 2), term_args.len);
    try std.testing.expect(term_args[0].bound);
    try std.testing.expectEqual(@as(u55, 3), term_args[1].deps);

    const ret_arg = term.getRetArg(bytes[0..]);
    try std.testing.expectEqual(@as(u7, 5), ret_arg.sort);
    try std.testing.expectEqual(
        @as(u32, @intCast(p_data + 3 * @sizeOf(Arg))),
        term.getUnifyPtr(bytes[0..]).?,
    );

    const theorem = Theorem{
        .num_args = 2,
        .reserved = 0,
        .p_data = @intCast(p_data),
    };

    const thm_args = theorem.getArgs(bytes[0..]);
    try std.testing.expectEqual(@as(usize, 2), thm_args.len);
    try std.testing.expectEqual(
        @as(u32, @intCast(p_data + 2 * @sizeOf(Arg))),
        theorem.getUnifyPtr(bytes[0..]),
    );
}

test "expression helper methods" {
    var child = Expr{ .variable = .{ .sort = 3, .bound = true, .deps = 0b10 } };
    const children = [_]*const Expr{&child};

    const var_expr = Expr{ .variable = .{ .sort = 4, .bound = false, .deps = 5 } };
    try std.testing.expectEqual(@as(u7, 4), var_expr.sort());
    try std.testing.expectEqual(@as(u55, 5), var_expr.deps());
    try std.testing.expect(!var_expr.bound());

    const term_expr = Expr{ .term = .{
        .sort = 6,
        .deps = 0b10,
        .id = 9,
        .args = &children,
    } };
    try std.testing.expectEqual(@as(u7, 6), term_expr.sort());
    try std.testing.expectEqual(@as(u55, 0b10), term_expr.deps());
    try std.testing.expect(!term_expr.bound());
}

test "sort packed fields round-trip" {
    const sort = Sort{
        .pure = true,
        .strict = false,
        .provable = true,
        .free = false,
        ._padding = 0,
    };

    const bytes = std.mem.asBytes(&sort);
    const parsed = @as(*const Sort, @ptrCast(bytes.ptr)).*;
    try std.testing.expect(parsed.pure);
    try std.testing.expect(!parsed.strict);
    try std.testing.expect(parsed.provable);
    try std.testing.expect(!parsed.free);
}
