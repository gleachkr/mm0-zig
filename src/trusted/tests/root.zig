const std = @import("std");
const mm0 = @import("mm0");

const Arg = mm0.Arg;
const Compiler = mm0.Compiler;
const FrontendEnv = mm0.Frontend.Env;
const FrontendExpr = mm0.Frontend.Expr;
const Expr = mm0.Expr;
const Header = mm0.Header;
const MAGIC = mm0.MAGIC;
const Heap = mm0.Heap;
const MM0Parser = mm0.MM0Parser;
const Mmb = mm0.Mmb;
const DefOps = mm0.DefOps;
const CompilerInference = mm0.CompilerSupport.Inference;
const CrossChecker = mm0.CrossChecker;
const Proof = mm0.Proof;
const ProofScript = mm0.ProofScript;
const Sort = mm0.Sort;
const Stack = mm0.Stack;
const Term = mm0.Term;
const Theorem = mm0.Theorem;
const Verifier = mm0.Verifier;

fn fillHeaderBytes(
    out: *align(@alignOf(Header)) [@sizeOf(Header)]u8,
    header: Header,
) void {
    @memcpy(out[0..], std.mem.asBytes(&header));
}

fn writeArg(buf: []u8, offset: usize, arg: Arg) void {
    @memcpy(buf[offset..][0..@sizeOf(Arg)], std.mem.asBytes(&arg));
}

fn writeValue(buf: []u8, offset: usize, value: anytype) void {
    const bytes = std.mem.asBytes(&value);
    @memcpy(buf[offset..][0..bytes.len], bytes);
}

const IndexEntryWire = extern struct {
    id: [4]u8,
    data: u32,
    ptr: u64,
};

const NameEntryWire = extern struct {
    proof: u64,
    name: u64,
};

fn buildIndexedMmb() [256]u8 {
    var bytes: [256]u8 align(8) = std.mem.zeroes([256]u8);

    const header = Header{
        .magic = MAGIC,
        .version = 1,
        .num_sorts = 1,
        .reserved0 = 0,
        .num_terms = 1,
        .num_thms = 1,
        .p_terms = 48,
        .p_thms = 56,
        .p_proof = 80,
        .reserved1 = 0,
        .p_index = 88,
    };
    writeValue(bytes[0..], 0, header);

    const sort = Sort{};
    writeValue(bytes[0..], 40, sort);

    const term = Term{
        .num_args = 0,
        .ret_sort = .{ .sort = 0, .is_def = false },
        .reserved = 0,
        .p_data = 64,
    };
    writeValue(bytes[0..], 48, term);

    const theorem = Theorem{
        .num_args = 0,
        .reserved = 0,
        .p_data = 72,
    };
    writeValue(bytes[0..], 56, theorem);

    writeArg(
        bytes[0..],
        64,
        .{ .deps = 0, .reserved = 0, .sort = 0, .bound = false },
    );

    bytes[80] = 0x44;
    bytes[81] = 0x02;
    bytes[82] = 0x45;
    bytes[83] = 0x02;
    bytes[84] = 0x42;
    bytes[85] = 0x03;
    bytes[86] = 0x00;
    bytes[87] = 0x00;

    writeValue(bytes[0..], 88, @as(u64, 3));
    writeValue(
        bytes[0..],
        96,
        IndexEntryWire{ .id = .{ 'N', 'a', 'm', 'e' }, .data = 0, .ptr = 144 },
    );
    writeValue(
        bytes[0..],
        112,
        IndexEntryWire{ .id = .{ 'V', 'a', 'r', 'N' }, .data = 0, .ptr = 192 },
    );
    writeValue(
        bytes[0..],
        128,
        IndexEntryWire{ .id = .{ 'H', 'y', 'p', 'N' }, .data = 0, .ptr = 208 },
    );

    writeValue(bytes[0..], 144, NameEntryWire{ .proof = 80, .name = 224 });
    writeValue(bytes[0..], 160, NameEntryWire{ .proof = 82, .name = 228 });
    writeValue(bytes[0..], 176, NameEntryWire{ .proof = 84, .name = 232 });

    writeValue(bytes[0..], 192, @as(u64, 216));
    writeValue(bytes[0..], 200, @as(u64, 216));
    writeValue(bytes[0..], 208, @as(u64, 216));
    writeValue(bytes[0..], 216, @as(u64, 0));

    @memcpy(bytes[224..228], "wff\x00");
    @memcpy(bytes[228..232], "app\x00");
    @memcpy(bytes[232..235], "ax\x00");

    return bytes;
}

fn buildRemapCrossCheckBytes() [128]u8 {
    var bytes: [128]u8 align(@alignOf(Arg)) = std.mem.zeroes([128]u8);

    const term_p_data: usize = 16;
    writeArg(
        bytes[0..],
        term_p_data,
        .{ .deps = 0, .reserved = 0, .sort = 1, .bound = false },
    );
    writeArg(
        bytes[0..],
        term_p_data + @sizeOf(Arg),
        .{ .deps = 0, .reserved = 0, .sort = 1, .bound = false },
    );

    const thm_p_data: usize = 48;
    writeArg(
        bytes[0..],
        thm_p_data,
        .{ .deps = 0, .reserved = 0, .sort = 1, .bound = false },
    );

    const unify = thm_p_data + @sizeOf(Arg);
    bytes[unify + 0] = 0x70;
    bytes[unify + 1] = 0x01;
    bytes[unify + 2] = 0x72;
    bytes[unify + 3] = 0x00;
    bytes[unify + 4] = 0x72;
    bytes[unify + 5] = 0x00;
    bytes[unify + 6] = 0x00;

    return bytes;
}

fn buildTheoremHypOrderCrossCheckBytes() [128]u8 {
    var bytes: [128]u8 align(@alignOf(Arg)) = std.mem.zeroes([128]u8);

    const term_p_data: usize = 16;
    writeArg(
        bytes[0..],
        term_p_data,
        .{ .deps = 0, .reserved = 0, .sort = 0, .bound = false },
    );
    writeArg(
        bytes[0..],
        term_p_data + @sizeOf(Arg),
        .{ .deps = 0, .reserved = 0, .sort = 0, .bound = false },
    );

    const thm_p_data: usize = 48;
    writeArg(
        bytes[0..],
        thm_p_data,
        .{ .deps = 0, .reserved = 0, .sort = 0, .bound = false },
    );
    writeArg(
        bytes[0..],
        thm_p_data + @sizeOf(Arg),
        .{ .deps = 0, .reserved = 0, .sort = 0, .bound = false },
    );

    const unify = thm_p_data + 2 * @sizeOf(Arg);
    bytes[unify + 0] = 0x72;
    bytes[unify + 1] = 0x01;
    bytes[unify + 2] = 0x36;
    bytes[unify + 3] = 0x72;
    bytes[unify + 4] = 0x00;
    bytes[unify + 5] = 0x36;
    bytes[unify + 6] = 0x70;
    bytes[unify + 7] = 0x00;
    bytes[unify + 8] = 0x72;
    bytes[unify + 9] = 0x00;
    bytes[unify + 10] = 0x72;
    bytes[unify + 11] = 0x01;
    bytes[unify + 12] = 0x00;

    return bytes;
}

fn buildLocalDefDummyProof() [16]u8 {
    var bytes: [16]u8 = std.mem.zeroes([16]u8);
    bytes[0] = 0x44;
    bytes[1] = 0x02;
    bytes[2] = 0x4D;
    bytes[3] = 0x05;
    bytes[4] = 0x53;
    bytes[5] = 0x00;
    bytes[6] = 0x00;
    bytes[7] = 0x00;
    return bytes;
}

const NoopChecker = struct {
    pub fn checkSort(_: @This(), _: u32, _: Sort) !void {}

    pub fn checkTerm(
        _: @This(),
        _: u32,
        _: Term,
        _: []const u8,
    ) !void {}

    pub fn checkAssertion(
        _: @This(),
        _: Theorem,
        _: []const u8,
    ) !void {}
};

fn buildSingleStmtProof(stmt_op: u8, body: []const u8) [32]u8 {
    var bytes: [32]u8 = std.mem.zeroes([32]u8);
    bytes[0] = 0x40 | stmt_op;
    bytes[1] = @intCast(2 + body.len + 1);
    @memcpy(bytes[2 .. 2 + body.len], body);
    bytes[2 + body.len] = 0x00;
    bytes[3 + body.len] = 0x00;
    return bytes;
}

fn collectStatementCmds(
    allocator: std.mem.Allocator,
    mmb: Mmb,
) ![]Proof.StmtCmd {
    var cmds = std.ArrayListUnmanaged(Proof.StmtCmd){};
    var pos: usize = @intCast(mmb.header.p_proof);

    while (true) {
        const stmt_start = pos;
        const cmd = try Proof.Cmd.read(
            mmb.file_bytes,
            pos,
            mmb.file_bytes.len,
        );
        const stmt_cmd: Proof.StmtCmd = @enumFromInt(cmd.op);
        try cmds.append(allocator, stmt_cmd);
        if (stmt_cmd == .End) break;
        if (cmd.data == 0) return error.BadStatementLength;
        pos = stmt_start + cmd.data;
    }

    return try cmds.toOwnedSlice(allocator);
}

fn buildAssertionFixture(
    stmt_op: u8,
    args: []const Arg,
    body: []const u8,
) align(@alignOf(Arg)) [128]u8 {
    var bytes: [128]u8 align(@alignOf(Arg)) = std.mem.zeroes([128]u8);
    const proof = buildSingleStmtProof(stmt_op, body);
    @memcpy(bytes[0..proof.len], proof[0..]);

    const p_data: usize = 32;
    for (args, 0..) |arg, i| {
        writeArg(bytes[0..], p_data + i * @sizeOf(Arg), arg);
    }
    return bytes;
}

fn buildLocalDefFixture(
    args: []const Arg,
    ret: Arg,
    unify: []const u8,
    body: []const u8,
) align(@alignOf(Arg)) [128]u8 {
    var bytes: [128]u8 align(@alignOf(Arg)) = std.mem.zeroes([128]u8);
    const proof = buildSingleStmtProof(0x0D, body);
    @memcpy(bytes[0..proof.len], proof[0..]);

    const p_data: usize = 32;
    for (args, 0..) |arg, i| {
        writeArg(bytes[0..], p_data + i * @sizeOf(Arg), arg);
    }

    const ret_offset = p_data + args.len * @sizeOf(Arg);
    writeArg(bytes[0..], ret_offset, ret);
    @memcpy(
        bytes[ret_offset + @sizeOf(Arg) ..][0..unify.len],
        unify,
    );
    return bytes;
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
    const parsed = try Header.fromBytes(bytes[0..]);
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
    try std.testing.expectError(error.BadMagic, Header.fromBytes(bad_magic[0..]));

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
    try std.testing.expectError(error.BadVersion, Header.fromBytes(bad_version[0..]));

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
    try std.testing.expectError(error.BadReserved, Header.fromBytes(bad_reserved[0..]));
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
    const cmd1 = try Proof.Cmd.read(&[_]u8{0x1A}, 0, 1);
    try std.testing.expectEqual(@as(u6, 0x1A), cmd1.op);
    try std.testing.expectEqual(@as(u32, 0), cmd1.data);
    try std.testing.expectEqual(@as(usize, 1), cmd1.size);

    const cmd2 = try Proof.Cmd.read(&[_]u8{ 0x45, 0x7F }, 0, 2);
    try std.testing.expectEqual(@as(u6, 0x05), cmd2.op);
    try std.testing.expectEqual(@as(u32, 0x7F), cmd2.data);
    try std.testing.expectEqual(@as(usize, 2), cmd2.size);

    const cmd3 = try Proof.Cmd.read(&[_]u8{ 0x91, 0xCD, 0xAB }, 0, 3);
    try std.testing.expectEqual(@as(u6, 0x11), cmd3.op);
    try std.testing.expectEqual(@as(u32, 0xABCD), cmd3.data);
    try std.testing.expectEqual(@as(usize, 3), cmd3.size);

    const cmd4 = try Proof.Cmd.read(
        &[_]u8{ 0xE2, 0x44, 0x33, 0x22, 0x11 },
        0,
        5,
    );
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
        \\sort wff;
        \\term app {x: wff} (h: wff x) (.d: wff x) : wff;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
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

test "MM0 parser treats parenthesized dot binders as bound dummies" {
    const src =
        \\sort nat;
        \\provable sort wff;
        \\term all {x: nat} (p: wff x): wff;
        \\prefix all: $A.$ prec 41;
        \\def subset (.x: nat) (p: wff x): wff = $ A. x p $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;

    switch (stmt) {
        .term => |term_stmt| {
            try std.testing.expectEqualStrings("subset", term_stmt.name);
            try std.testing.expectEqual(@as(usize, 1), term_stmt.args.len);
            try std.testing.expectEqual(@as(usize, 1), term_stmt.dummy_args.len);
            try std.testing.expect(term_stmt.dummy_args[0].bound);
            try std.testing.expectEqual(
                @as(u55, 1),
                term_stmt.dummy_args[0].deps,
            );
            try std.testing.expect(term_stmt.dummy_exprs[0].bound());
            try std.testing.expectEqual(
                @as(u55, 1),
                term_stmt.dummy_exprs[0].deps(),
            );
            try std.testing.expectEqual(@as(u55, 1), term_stmt.args[0].deps);

            const body = term_stmt.body orelse return error.ExpectedDefinitionBody;
            switch (body.*) {
                .term => |app| {
                    try std.testing.expectEqual(@as(usize, 2), app.args.len);
                    try std.testing.expect(
                        app.args[0] == term_stmt.dummy_exprs[0],
                    );
                    try std.testing.expect(app.args[0].bound());
                },
                else => return error.ExpectedTermApp,
            }
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser handles arrow-style term signatures" {
    const src =
        \\sort hex;
        \\sort char;
        \\term ch: hex > hex > char;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
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
        \\sort term;
        \\sort type;
        \\term lam {x: term}: type > term x > term;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
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
        \\provable sort wff;
        \\notation "|-";
        \\theorem visible0 {x: wff}: $ |- x $;
        \\local theorem hidden {x: wff}: $ |- x $;
        \\pub theorem visible1 {x: wff}: $ |- x $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
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

test "MM0 parser rejects unknown sorts in term signatures" {
    {
        const src =
            \\sort nat;
            \\term bad: foo > nat;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        try std.testing.expectError(error.UnknownSort, parser.next());
    }

    {
        const src =
            \\sort nat;
            \\term bad: nat > foo;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        try std.testing.expectError(error.UnknownSort, parser.next());
    }
}

test "MM0 parser rejects unknown sorts in theorem binders" {
    const src =
        \\provable sort wff;
        \\theorem bad (x: foo): $ x $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    try std.testing.expectError(error.UnknownSort, parser.next());
}

test "MM0 parser rejects unknown sorts in defs and coercions" {
    {
        const src =
            \\sort nat;
            \\term z: nat;
            \\def bad: foo = $ z $;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(error.UnknownSort, parser.next());
    }

    {
        const src =
            \\sort a;
            \\term aa: a > a;
            \\coercion aa: a > b;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(error.UnknownSort, parser.next());
    }
}

test "MM0 parser rejects notation tokens using parentheses" {
    {
        const src =
            \\sort wff;
            \\term p: wff > wff;
            \\prefix p: $($ prec 5;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(error.InvalidNotationToken, parser.next());
    }

    {
        const src =
            \\sort wff;
            \\term p: wff > wff;
            \\notation p (x: wff): wff = ($)$: 5) x;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(error.InvalidNotationToken, parser.next());
    }
}

test "MM0 parser rejects infix precedence max" {
    const src =
        \\sort wff;
        \\term imp: wff > wff > wff;
        \\infixr imp: $->$ prec max;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.InfixPrecOutOfRange, parser.next());
}

test "MM0 parser rejects notation precedence conflicts" {
    {
        const src =
            \\sort wff;
            \\term p: wff > wff;
            \\prefix p: $~$ prec 5;
            \\prefix p: $~$ prec 6;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(error.PrecedenceMismatch, parser.next());
    }

    {
        const src =
            \\sort wff;
            \\term l: wff > wff > wff;
            \\term r: wff > wff > wff;
            \\infixl l: $*$ prec 7;
            \\infixr r: $+$ prec 7;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(error.PrecedenceAssocMismatch, parser.next());
    }
}

test "MM0 parser rejects notation first-token conflicts" {
    const src =
        \\sort wff;
        \\term p: wff > wff;
        \\term q: wff > wff;
        \\prefix p: $~$ prec 5;
        \\notation q (x: wff): wff = ($~$: 5) x;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(
        error.NotationFirstTokenConflict,
        parser.next(),
    );
}

test "MM0 parser rejects notation first-token vs infixy conflicts" {
    {
        const src =
            \\sort wff;
            \\term mix: wff > wff > wff;
            \\term p: wff > wff;
            \\notation mix (x y: wff): wff = ($[$: 20) x ($->$: 5) y;
            \\prefix p: $->$ prec 5;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(
            error.NotationFirstTokenConflict,
            parser.next(),
        );
    }

    {
        const src =
            \\sort wff;
            \\term mix: wff > wff > wff;
            \\term p: wff > wff;
            \\prefix p: $->$ prec 5;
            \\notation mix (x y: wff): wff = ($[$: 20) x ($->$: 5) y;
        ;

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();

        var parser = MM0Parser.init(src, arena.allocator());
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        _ = (try parser.next()).?;
        try std.testing.expectError(
            error.NotationFirstTokenConflict,
            parser.next(),
        );
    }
}

test "MM0 parser rejects coercion cycles" {
    const src =
        \\sort a;
        \\sort b;
        \\term ab: a > b;
        \\term ba: b > a;
        \\coercion ab: a > b;
        \\coercion ba: b > a;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.CoercionCycle, parser.next());
}

test "MM0 parser rejects coercion diamonds" {
    const src =
        \\sort a;
        \\sort b;
        \\sort c;
        \\term ab: a > b;
        \\term bc: b > c;
        \\term ac: a > c;
        \\coercion ab: a > b;
        \\coercion bc: b > c;
        \\coercion ac: a > c;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.CoercionDiamond, parser.next());
}

test "MM0 parser rejects coercion diamonds to provable" {
    const src =
        \\sort a;
        \\provable sort b;
        \\provable sort c;
        \\term ab: a > b;
        \\term ac: a > c;
        \\coercion ab: a > b;
        \\coercion ac: a > c;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.CoercionDiamondToProvable, parser.next());
}

test "MM0 parser coerces formulas to provable sorts" {
    const src =
        \\sort nat;
        \\provable sort wff;
        \\term box: nat > wff;
        \\coercion box: nat > wff;
        \\theorem t (x: nat): $ x $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;

    const stmt = (try parser.next()).?;
    switch (stmt) {
        .assertion => |assert_stmt| switch (assert_stmt.concl.*) {
            .term => |term_app| {
                try std.testing.expectEqual(@as(u32, 0), term_app.id);
                try std.testing.expectEqual(@as(usize, 1), term_app.args.len);
                try std.testing.expect(term_app.args[0] == assert_stmt.arg_exprs[0]);
            },
            else => return error.ExpectedTermApp,
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser handles nullary terms in applications" {
    const src =
        \\provable sort wff;
        \\sort nat;
        \\term z: nat;
        \\term p: nat > nat > wff;
        \\theorem t: $ p z z $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;

    const stmt = (try parser.next()).?;
    switch (stmt) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("t", assert_stmt.name);
            try std.testing.expectEqual(@as(usize, 0), assert_stmt.args.len);
            try std.testing.expectEqual(@as(usize, 0), assert_stmt.hyps.len);
            switch (assert_stmt.concl.*) {
                .term => |concl| {
                    try std.testing.expectEqual(@as(u32, 1), concl.id);
                    try std.testing.expectEqual(@as(usize, 2), concl.args.len);
                    switch (concl.args[0].*) {
                        .term => |arg0| {
                            try std.testing.expectEqual(@as(u32, 0), arg0.id);
                            try std.testing.expectEqual(@as(usize, 0), arg0.args.len);
                        },
                        else => return error.ExpectedTermApp,
                    }
                    switch (concl.args[1].*) {
                        .term => |arg1| {
                            try std.testing.expectEqual(@as(u32, 0), arg1.id);
                            try std.testing.expectEqual(@as(usize, 0), arg1.args.len);
                        },
                        else => return error.ExpectedTermApp,
                    }
                },
                else => return error.ExpectedTermApp,
            }
        },
        else => return error.UnexpectedStatementKind,
    }
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

test "CrossChecker remaps parser term ids to MMB ids" {
    const mm0_src =
        \\provable sort wff;
        \\sort nat;
        \\term eq: nat > nat > wff;
        \\axiom refl (a: nat): $ eq a a $;
    ;

    var bytes: [128]u8 align(@alignOf(Arg)) =
        buildRemapCrossCheckBytes();
    const file_bytes = bytes[0..];

    const checker = try CrossChecker.init(mm0_src, std.testing.allocator);
    defer checker.deinit(std.testing.allocator);

    try checker.checkSort(0, .{ .provable = true });
    try checker.checkSort(1, .{});

    const eq_term = Term{
        .num_args = 2,
        .ret_sort = .{ .sort = 0, .is_def = false },
        .reserved = 0,
        .p_data = 16,
    };
    try checker.checkTerm(1, eq_term, file_bytes);

    const refl = Theorem{
        .num_args = 1,
        .reserved = 0,
        .p_data = 48,
    };
    try checker.checkAssertion(refl, file_bytes);
}

test "CrossChecker consumes theorem hypotheses in unify order" {
    const mm0_src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    ;

    var bytes: [128]u8 align(@alignOf(Arg)) =
        buildTheoremHypOrderCrossCheckBytes();
    const file_bytes = bytes[0..];

    var checker = try CrossChecker.init(mm0_src, std.testing.allocator);
    defer checker.deinit(std.testing.allocator);

    try checker.checkSort(0, .{ .provable = true });

    const imp_term = Term{
        .num_args = 2,
        .ret_sort = .{ .sort = 0, .is_def = false },
        .reserved = 0,
        .p_data = 16,
    };
    try checker.checkTerm(0, imp_term, file_bytes);

    const ax_mp = Theorem{
        .num_args = 2,
        .reserved = 0,
        .p_data = 48,
    };
    try checker.checkAssertion(ax_mp, file_bytes);
}

test "Verifier rejects dummy variables in free sorts" {
    const mm0_src =
        \\provable free sort foo;
    ;

    var checker = try CrossChecker.init(mm0_src, std.testing.allocator);
    defer checker.deinit(std.testing.allocator);

    const sorts = [_]Sort{.{ .provable = true, .free = true }};
    const terms = [_]Term{.{
        .num_args = 0,
        .ret_sort = .{ .sort = 0, .is_def = true },
        .reserved = 0,
        .p_data = 0,
    }};
    const theorems = [_]Theorem{};
    var proof = buildLocalDefDummyProof();

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.FreeSort,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier requires bound variables for UDummy" {
    const sorts = [_]Sort{.{}};
    const verifier = try Verifier.init(
        std.testing.allocator,
        "",
        &sorts,
        &.{},
        &.{},
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    verifier.available_sorts = 1;
    verifier.unify_context = .defn;

    const expr = try verifier.arena.allocator().create(Expr);
    expr.* = .{ .variable = .{
        .sort = 0,
        .bound = false,
        .deps = 0,
    } };
    try verifier.ustack.push(expr);

    try std.testing.expectError(error.ExpectedBoundVar, verifier.uopDummy(0));
}

test "CrossChecker requires bound variables for UDummy" {
    var checker = try CrossChecker.init("", std.testing.allocator);
    defer checker.deinit(std.testing.allocator);

    checker.unify_mode = .definition;

    const expr = try checker.arena.allocator().create(Expr);
    expr.* = .{ .variable = .{
        .sort = 0,
        .bound = false,
        .deps = 0,
    } };
    checker.ustack[0] = expr;
    checker.ustack_top = 1;

    try std.testing.expectError(error.ExpectedBoundVar, checker.uopDummy(0));
}

test "Verifier rejects aliasing UDummy witnesses" {
    const sorts = [_]Sort{.{}};
    const verifier = try Verifier.init(
        std.testing.allocator,
        "",
        &sorts,
        &.{},
        &.{},
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    verifier.available_sorts = 1;
    verifier.unify_context = .defn;

    const expr = try verifier.arena.allocator().create(Expr);
    expr.* = .{ .variable = .{
        .sort = 0,
        .bound = true,
        .deps = 1,
    } };
    try verifier.uheap.push(expr);
    try verifier.ustack.push(expr);

    try std.testing.expectError(error.DepViolation, verifier.uopDummy(0));
}

test "CrossChecker rejects aliasing UDummy witnesses" {
    var checker = try CrossChecker.init("", std.testing.allocator);
    defer checker.deinit(std.testing.allocator);

    checker.unify_mode = .definition;

    const expr = try checker.arena.allocator().create(Expr);
    expr.* = .{ .variable = .{
        .sort = 0,
        .bound = true,
        .deps = 1,
    } };
    checker.uheap[0] = expr;
    checker.uheap_saved[0] = false;
    checker.uheap_len = 1;
    checker.ustack[0] = expr;
    checker.ustack_top = 1;

    try std.testing.expectError(error.DepViolation, checker.uopDummy(0));
}

test "Verifier rejects strict bound theorem arguments" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{ .strict = true, .provable = true }};
    const args = [_]Arg{.{
        .deps = 1,
        .reserved = 0,
        .sort = 0,
        .bound = true,
    }};
    var proof: [128]u8 align(@alignOf(Arg)) =
        buildAssertionFixture(0x0E, &args, &.{});
    const terms = [_]Term{};
    const theorems = [_]Theorem{.{
        .num_args = 1,
        .reserved = 0,
        .p_data = 32,
    }};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.StrictSort,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier rejects strict bound definition arguments" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{ .strict = true }};
    const args = [_]Arg{.{
        .deps = 1,
        .reserved = 0,
        .sort = 0,
        .bound = true,
    }};
    const ret = Arg{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    };
    var proof: [128]u8 align(@alignOf(Arg)) =
        buildLocalDefFixture(&args, ret, &.{ 0x72, 0x00, 0x00 }, &.{});
    const terms = [_]Term{.{
        .num_args = 1,
        .ret_sort = .{ .sort = 0, .is_def = true },
        .reserved = 0,
        .p_data = 32,
    }};
    const theorems = [_]Theorem{};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.StrictSort,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier rejects pure return sorts in local defs" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{ .pure = true }};
    const ret = Arg{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    };
    var proof = buildLocalDefFixture(&.{}, ret, &.{0x00}, &.{});
    const terms = [_]Term{.{
        .num_args = 0,
        .ret_sort = .{ .sort = 0, .is_def = true },
        .reserved = 0,
        .p_data = 32,
    }};
    const theorems = [_]Theorem{};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.PureSort,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier rejects non-provable axiom conclusions" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{}};
    const args = [_]Arg{.{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    }};
    var proof: [128]u8 align(@alignOf(Arg)) =
        buildAssertionFixture(0x02, &args, &.{ 0x52, 0x00 });
    const terms = [_]Term{};
    const theorems = [_]Theorem{.{
        .num_args = 1,
        .reserved = 0,
        .p_data = 32,
    }};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.NotProvable,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier rejects non-provable theorem conclusions" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{}};
    const args = [_]Arg{.{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    }};
    var proof: [128]u8 align(@alignOf(Arg)) = buildAssertionFixture(
        0x0E,
        &args,
        &.{ 0x52, 0x00, 0x20 },
    );
    const terms = [_]Term{};
    const theorems = [_]Theorem{.{
        .num_args = 1,
        .reserved = 0,
        .p_data = 32,
    }};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.NotProvable,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier checks definition return sorts" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{ .{}, .{} };
    const args = [_]Arg{.{
        .deps = 0,
        .reserved = 0,
        .sort = 1,
        .bound = false,
    }};
    const ret = Arg{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    };
    var proof: [128]u8 align(@alignOf(Arg)) = buildLocalDefFixture(
        &args,
        ret,
        &.{ 0x72, 0x00, 0x00 },
        &.{ 0x52, 0x00 },
    );
    const terms = [_]Term{.{
        .num_args = 1,
        .ret_sort = .{ .sort = 0, .is_def = true },
        .reserved = 0,
        .p_data = 32,
    }};
    const theorems = [_]Theorem{};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.SortMismatch,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier checks definition return dependencies" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{}};
    const args = [_]Arg{.{
        .deps = 1,
        .reserved = 0,
        .sort = 0,
        .bound = true,
    }};
    const ret = Arg{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    };
    var proof: [128]u8 align(@alignOf(Arg)) = buildLocalDefFixture(
        &args,
        ret,
        &.{ 0x72, 0x00, 0x00 },
        &.{ 0x52, 0x00 },
    );
    const terms = [_]Term{.{
        .num_args = 1,
        .ret_sort = .{ .sort = 0, .is_def = true },
        .reserved = 0,
        .p_data = 32,
    }};
    const theorems = [_]Theorem{};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.DepViolation,
        verifier.verifyProofStream(0, checker),
    );
}

test "Verifier replays definition unify streams" {
    const checker = NoopChecker{};
    const sorts = [_]Sort{.{}};
    const args = [_]Arg{.{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    }};
    const ret = Arg{
        .deps = 0,
        .reserved = 0,
        .sort = 0,
        .bound = false,
    };
    var proof: [128]u8 align(@alignOf(Arg)) = buildLocalDefFixture(
        &args,
        ret,
        &.{ 0x70, 0x00, 0x00 },
        &.{ 0x52, 0x00 },
    );
    const terms = [_]Term{.{
        .num_args = 1,
        .ret_sort = .{ .sort = 0, .is_def = true },
        .reserved = 0,
        .p_data = 32,
    }};
    const theorems = [_]Theorem{};

    const verifier = try Verifier.init(
        std.testing.allocator,
        proof[0..],
        &sorts,
        &terms,
        &theorems,
        null,
    );
    defer verifier.deinit(std.testing.allocator);

    try std.testing.expectError(
        error.ExpectedTermApp,
        verifier.verifyProofStream(0, checker),
    );
}

test "proof command decoding detects truncation" {
    try std.testing.expectError(
        error.TruncatedCommand,
        Proof.Cmd.read(&[_]u8{0x45}, 0, 1),
    );
}

test "MMB parser reads index names and string lists" {
    var bytes: [256]u8 align(8) = buildIndexedMmb();
    const mmb = try Mmb.parse(std.testing.allocator, bytes[0..235]);

    try std.testing.expectEqualStrings("wff", (try mmb.sortName(0)).?);
    try std.testing.expectEqualStrings("app", (try mmb.termName(0)).?);
    try std.testing.expectEqualStrings("ax", (try mmb.theoremName(0)).?);

    const term_vars = (try mmb.termVarNames(0)).?;
    const thm_vars = (try mmb.theoremVarNames(0)).?;
    const thm_hyps = (try mmb.theoremHypNames(0)).?;
    try std.testing.expectEqual(@as(usize, 0), term_vars.len());
    try std.testing.expectEqual(@as(usize, 0), thm_vars.len());
    try std.testing.expectEqual(@as(usize, 0), thm_hyps.len());
}

test "MMB parser rejects misaligned backing bytes" {
    const bytes = buildIndexedMmb();
    var backing: [257]u8 align(8) = std.mem.zeroes([257]u8);
    @memcpy(backing[1..236], bytes[0..235]);

    try std.testing.expectError(
        error.MisalignedTermTable,
        Mmb.parse(std.testing.allocator, backing[1..236]),
    );
}

test "MMB parser rejects duplicate index tables" {
    var bytes: [256]u8 align(8) = buildIndexedMmb();
    writeValue(
        bytes[0..],
        112,
        IndexEntryWire{ .id = .{ 'N', 'a', 'm', 'e' }, .data = 0, .ptr = 192 },
    );

    try std.testing.expectError(
        error.DuplicateIndexTable,
        Mmb.parse(std.testing.allocator, bytes[0..235]),
    );
}

test "MMB index validates proof pointer in name table" {
    var bytes: [256]u8 align(8) = buildIndexedMmb();
    writeValue(bytes[0..], 144, NameEntryWire{ .proof = 81, .name = 224 });

    const mmb = try Mmb.parse(std.testing.allocator, bytes[0..235]);
    try std.testing.expectError(
        error.BadIndexLookup,
        mmb.index.validateSortProof(0, 80),
    );
}

test "MM0 parser preserves binder names and assertion kind" {
    const src =
        \\provable sort wff;
        \\term pair (left _: wff) {x: wff}: wff;
        \\theorem thm (a _: wff) {x: wff}: $ a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;

    const term_stmt = (try parser.next()).?;
    switch (term_stmt) {
        .term => |term| {
            try std.testing.expectEqual(@as(usize, 3), term.arg_names.len);
            try std.testing.expectEqualStrings("left", term.arg_names[0].?);
            try std.testing.expect(term.arg_names[1] == null);
            try std.testing.expectEqualStrings("x", term.arg_names[2].?);
        },
        else => return error.UnexpectedStatementKind,
    }

    const assertion_stmt = (try parser.next()).?;
    switch (assertion_stmt) {
        .assertion => |assertion| {
            try std.testing.expectEqual(@as(usize, 3), assertion.arg_names.len);
            try std.testing.expectEqualStrings("a", assertion.arg_names[0].?);
            try std.testing.expect(assertion.arg_names[1] == null);
            try std.testing.expectEqualStrings("x", assertion.arg_names[2].?);
            try std.testing.expect(assertion.kind == .theorem);
        },
        else => return error.UnexpectedStatementKind,
    }
}
