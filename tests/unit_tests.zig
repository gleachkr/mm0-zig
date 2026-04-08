const std = @import("std");
const mm0 = @import("mm0");

const Arg = mm0.Arg;
const Compiler = mm0.Compiler;
const CompilerEnv = mm0.CompilerEnv;
const CompilerExpr = mm0.CompilerExpr;
const TermAnnotations = mm0.TermAnnotations;
const Expr = mm0.Expr;
const Header = mm0.Header;
const MAGIC = mm0.MAGIC;
const Heap = mm0.Heap;
const MM0Parser = mm0.MM0Parser;
const Mmb = mm0.Mmb;
const DefOps = mm0.DefOps;
const CompilerInference = mm0.CompilerInference;
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

test "proof script parser reads theorem blocks and proof lines" {
    const src =
        \\id
        \\--
        \\l1: $ a -> a $ by ax_1 (a := $ a $, b := $ a $) []
        \\l2: $ a $ by ax_mp (a := $ a $, b := $ a $) [#1, l1]
        \\
        \\other
        \\l1: $ b $ by ax_b []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const first = (try parser.nextBlock()).?;
    try std.testing.expect(first.kind == .theorem);
    try std.testing.expectEqualStrings("id", first.name);
    try std.testing.expect(first.underline_span != null);
    try std.testing.expectEqual(@as(usize, 2), first.lines.len);
    try std.testing.expectEqualStrings("l1", first.lines[0].label);
    try std.testing.expectEqualStrings(" a -> a ", first.lines[0].assertion.text);
    try std.testing.expectEqualStrings("ax_mp", first.lines[1].rule_name);
    try std.testing.expectEqual(@as(usize, 2), first.lines[1].arg_bindings.len);
    try std.testing.expectEqualStrings(
        "a",
        first.lines[1].arg_bindings[0].name,
    );
    try std.testing.expectEqual(@as(usize, 2), first.lines[1].refs.len);
    switch (first.lines[1].refs[0]) {
        .hyp => |hyp| try std.testing.expectEqual(@as(usize, 1), hyp.index),
        else => return error.UnexpectedRefKind,
    }
    switch (first.lines[1].refs[1]) {
        .line => |line| try std.testing.expectEqualStrings("l1", line.label),
        else => return error.UnexpectedRefKind,
    }

    const second = (try parser.nextBlock()).?;
    try std.testing.expect(second.kind == .theorem);
    try std.testing.expectEqualStrings("other", second.name);
    try std.testing.expect(second.underline_span == null);
    try std.testing.expectEqual(@as(usize, 1), second.lines.len);
    try std.testing.expectEqual(
        @as(usize, 0),
        second.lines[0].arg_bindings.len,
    );
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser reads lemma blocks" {
    const src =
        \\lemma id (a: wff): $ a -> a $
        \\---------------------------
        \\l1: $ a -> a $ by ax_id (a := $ a $) []
        \\
        \\main
        \\----
        \\l1: $ a -> a $ by id (a := $ a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const lemma = (try parser.nextBlock()).?;
    try std.testing.expect(lemma.kind == .lemma);
    try std.testing.expectEqualStrings("id", lemma.name);
    try std.testing.expectEqualStrings(
        "(a: wff): $ a -> a $",
        lemma.header_tail,
    );
    try std.testing.expectEqual(@as(usize, 1), lemma.lines.len);

    const theorem = (try parser.nextBlock()).?;
    try std.testing.expect(theorem.kind == .theorem);
    try std.testing.expectEqualStrings("main", theorem.name);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser allows newlines inside math strings" {
    const src =
        \\demo
        \\----
        \\l1: $ a ->
        \\  a $ by ax_id (a := $ a ->
        \\  a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expectEqualStrings(
        " a ->\n  a ",
        block.lines[0].assertion.text,
    );
    try std.testing.expectEqual(@as(usize, 1), block.lines[0].arg_bindings.len);
    try std.testing.expectEqualStrings(
        " a ->\n  a ",
        block.lines[0].arg_bindings[0].formula.text,
    );
}

test "compiler env retains def dummy metadata" {
    const src = try readProofCaseFile(
        std.testing.allocator,
        "pass_def_dummy",
        "mm0",
    );
    defer std.testing.allocator.free(src);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    const term_id = env.term_names.get("injective") orelse {
        return error.MissingTerm;
    };
    const term = env.terms.items[term_id];
    try std.testing.expect(term.is_def);
    try std.testing.expectEqual(@as(usize, 2), term.dummy_args.len);
    try std.testing.expectEqualStrings("obj", term.dummy_args[0].sort_name);
    try std.testing.expectEqualStrings("obj", term.dummy_args[1].sort_name);
}

test "compiler ignores legacy @abbrev annotations on defs" {
    const src =
        \\sort nat;
        \\term plus (a b: nat): nat;
        \\--| @abbrev
        \\def double (a: nat): nat = $ plus a a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .term => |term| try TermAnnotations.processTermAnnotations(
                &env,
                term,
                parser.last_annotations,
            ),
            else => {},
        }
    }

    try std.testing.expectEqual(@as(usize, 2), env.terms.items.len);
    try std.testing.expect(env.terms.items[1].is_def);
    try std.testing.expect(env.terms.items[1].body != null);
}

fn expectCompareTransparent(
    src: []const u8,
    lhs_text: []const u8,
    rhs_text: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const lhs_expr = try parser.parseFormulaText(lhs_text, &theorem_vars);
    const rhs_expr = try parser.parseFormulaText(rhs_text, &theorem_vars);
    const lhs = try theorem.internParsedExpr(lhs_expr);
    const rhs = try theorem.internParsedExpr(rhs_expr);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    try std.testing.expect((try def_ops.compareTransparent(lhs, rhs)) != null);
    try std.testing.expect((try def_ops.compareTransparent(rhs, lhs)) != null);
}

test "targeted def module has no standalone opening API" {
    try std.testing.expect(!@hasDecl(DefOps.Context, "openConcreteDef"));
}

fn exprContainsExprId(
    theorem: *const CompilerExpr.TheoremContext,
    root: CompilerExpr.ExprId,
    needle: CompilerExpr.ExprId,
) bool {
    if (root == needle) return true;
    return switch (theorem.interner.node(root).*) {
        .variable => false,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (exprContainsExprId(theorem, arg, needle)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

test "def matcher binds quantified templates through hidden dummies" {
    const allocator = std.testing.allocator;
    const src = try readProofCaseFile(
        allocator,
        "pass_def_all_elim_free_param",
        "mm0",
    );
    defer allocator.free(src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const rule_id = env.getRuleId("all_elim") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    const parsed_actual = try parser.parseFormulaText(" mono f ", &theorem_vars);
    const actual = try theorem.internParsedExpr(parsed_actual);

    const bindings = try allocator.alloc(?CompilerExpr.ExprId, rule.args.len);
    defer allocator.free(bindings);
    @memset(bindings, null);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    try std.testing.expect(try def_ops.matchTemplateTransparent(
        rule.hyps[0],
        actual,
        bindings,
    ));

    // Public template matching now stays on the resolved, non-escaping path.
    // Hidden def dummies therefore remain unresolved here instead of being
    // materialized into fresh theorem-local dummy vars.
    try std.testing.expect(bindings[0] == null);
    try std.testing.expect(bindings[1] == null);
    try std.testing.expect(bindings[2] == null);
    try std.testing.expectEqual(@as(usize, 0), theorem.theorem_dummies.items.len);
}

test "def matcher opens nested user-side defs under matching heads" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ (a -> a) -> (a -> a) $;
    ;

    try expectCompareTransparent(
        src,
        " (a -> double a) -> (a -> a) ",
        " (a -> (a -> a)) -> (a -> a) ",
    );
}

test "def matcher opens nested user-side defs on both sides" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\def alias (a: wff): wff = $ double a $;
        \\def wrap (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ (a -> a) -> (a -> a) $;
    ;

    try expectCompareTransparent(
        src,
        " (a -> alias a) -> (a -> a) ",
        " (a -> wrap a) -> (a -> a) ",
    );
}

test "def matcher opens nested user-side defs through repeated heads" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\def alias (a: wff): wff = $ double a $;
        \\def wrap (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ ((a -> a) -> (a -> a)) -> (a -> a) $;
    ;

    try expectCompareTransparent(
        src,
        " ((a -> alias a) -> (a -> a)) -> (a -> a) ",
        " ((a -> wrap a) -> (a -> a)) -> (a -> a) ",
    );
}

test "def conversion plan unfolds to an exact target" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\theorem demo (a: wff): $ a -> a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const lhs_expr = try parser.parseFormulaText(" double a ", &theorem_vars);
    const rhs_expr = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const lhs = try theorem.internParsedExpr(lhs_expr);
    const rhs = try theorem.internParsedExpr(rhs_expr);

    var def_ops = DefOps.Context.init(
        arena.allocator(),
        &theorem,
        &env,
    );
    defer def_ops.deinit();

    const plan = try def_ops.compareTransparent(lhs, rhs);
    const step = plan orelse return error.ExpectedConversionPlan;
    switch (step.*) {
        .unfold_lhs => |unfold| {
            try std.testing.expectEqual(rhs, unfold.witness);
            try std.testing.expect(unfold.next.* == .refl);
        },
        else => return error.UnexpectedConversionPlan,
    }
}

test "semantic seeds finalize to representatives while exact seeds stay raw" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\axiom keep (p: wff): $ p $;
        \\theorem host (a: wff): $ double a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const rule_id = env.getRuleId("keep") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const raw_expr = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const raw = try theorem.internParsedExpr(raw_expr);
    const folded_expr = try parser.parseFormulaText(" double a ", &theorem_vars);
    const folded = try theorem.internParsedExpr(folded_expr);

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var semantic_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .semantic = .{
            .expr_id = raw,
            .mode = .transparent,
        } }},
    );
    defer semantic_session.deinit();
    const semantic_bindings = try semantic_session.finalizeConcreteBindings();
    try std.testing.expectEqual(@as(usize, 1), semantic_bindings.len);
    try std.testing.expectEqual(folded, semantic_bindings[0]);

    var exact_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .exact = raw }},
    );
    defer exact_session.deinit();
    const exact_bindings = try exact_session.finalizeConcreteBindings();
    try std.testing.expectEqual(@as(usize, 1), exact_bindings.len);
    try std.testing.expectEqual(raw, exact_bindings[0]);
}

test "semantic seeds reuse representative-aware matches" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def double (a: wff): wff = $ a -> a $;
        \\axiom dup (p: wff): $ p -> p $;
        \\theorem host (a: wff): $ double a -> double a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const rule_id = env.getRuleId("dup") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];
    const raw_expr = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const raw = try theorem.internParsedExpr(raw_expr);
    const folded_expr = try parser.parseFormulaText(" double a ", &theorem_vars);
    const folded = try theorem.internParsedExpr(folded_expr);
    const actual_expr =
        try parser.parseFormulaText(" double a -> double a ", &theorem_vars);
    const actual = try theorem.internParsedExpr(actual_expr);

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var semantic_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .semantic = .{
            .expr_id = raw,
            .mode = .transparent,
        } }},
    );
    defer semantic_session.deinit();
    try std.testing.expect(
        try semantic_session.matchTransparent(rule.concl, actual),
    );
    const semantic_bindings = try semantic_session.finalizeConcreteBindings();
    try std.testing.expectEqual(@as(usize, 1), semantic_bindings.len);
    try std.testing.expectEqual(folded, semantic_bindings[0]);

    var exact_session = try def_ops.beginRuleMatch(
        rule.args,
        &.{DefOps.BindingSeed{ .exact = raw }},
    );
    defer exact_session.deinit();
    try std.testing.expect(
        !(try exact_session.matchTransparent(rule.concl, actual)),
    );
}

test "compiler emits a valid hidden-dummy targeted unfold proof" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_def_unfold_dummy",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_def_unfold_dummy",
        "proof",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler handles normalize-plus-unfold hidden-dummy proof" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_def_hidden_dummy_all_elim_ctx_unfold",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_def_hidden_dummy_all_elim_ctx_unfold",
        "proof",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler ignores legacy @abbrev on non-def terms" {
    const mm0_src =
        \\sort nat;
        \\--| @abbrev
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler env converts rules into binder-indexed templates" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    try std.testing.expectEqual(@as(usize, 1), env.rules.items.len);
    const rule = env.rules.items[0];
    try std.testing.expect(rule.kind == .axiom);
    try std.testing.expectEqual(@as(usize, 2), rule.arg_names.len);
    try std.testing.expectEqualStrings("a", rule.arg_names[0].?);
    try std.testing.expectEqualStrings("b", rule.arg_names[1].?);
    try std.testing.expectEqual(@as(usize, 2), rule.hyps.len);
    switch (rule.hyps[0]) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 0), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            switch (app.args[0]) {
                .binder => |idx| try std.testing.expectEqual(@as(usize, 0), idx),
                else => return error.UnexpectedTemplateExpr,
            }
            switch (app.args[1]) {
                .binder => |idx| try std.testing.expectEqual(@as(usize, 1), idx),
                else => return error.UnexpectedTemplateExpr,
            }
        },
        else => return error.UnexpectedTemplateExpr,
    }
    switch (rule.hyps[1]) {
        .binder => |idx| try std.testing.expectEqual(@as(usize, 0), idx),
        else => return error.UnexpectedTemplateExpr,
    }
    switch (rule.concl) {
        .binder => |idx| try std.testing.expectEqual(@as(usize, 1), idx),
        else => return error.UnexpectedTemplateExpr,
    }
}

test "compiler checks proof blocks in theorem order" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.check();
}

test "compiler compiles lemma proof blocks" {
    const allocator = std.testing.allocator;
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_1 (a b: wff): $ a -> b -> a $;
        \\axiom ax_2 (a b c: wff):
        \\$ (a -> b -> c) -> (a -> b) -> a -> c $;
        \\axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
        \\theorem main (a: wff): $ a -> a $;
    ;
    const proof_src =
        \\lemma id (a: wff): $ a -> a $
        \\---------------------------
        \\l1: $ a -> ((a -> a) -> a) $ by ax_1 []
        \\l2: $ a -> (a -> a) $ by ax_1 []
        \\l3: $ (a -> ((a -> a) -> a)) -> ((a -> (a -> a)) -> (a -> a)) $ by ax_2 []
        \\l4: $ (a -> (a -> a)) -> (a -> a) $ by ax_mp (a := $ a -> ((a -> a) -> a) $, b := $ (a -> (a -> a)) -> (a -> a) $) [l3, l1]
        \\l5: $ a -> a $ by ax_mp (a := $ a -> (a -> a) $, b := $ a -> a $) [l4, l2]
        \\
        \\main
        \\----
        \\l1: $ a -> a $ by id (a := $ a $) []
    ;

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler interleaves LocalThm and Thm statements in MMB order" {
    const allocator = std.testing.allocator;
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
        \\theorem third: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\lemma helper0: $ top $
        \\--------------------
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by helper0 []
        \\
        \\lemma helper1: $ top $
        \\--------------------
        \\l1: $ top $ by helper0 []
        \\
        \\third
        \\-----
        \\l1: $ top $ by helper1 []
    ;

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    try mm0.verifyPair(allocator, mm0_src, mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    const cmds = try collectStatementCmds(allocator, mmb);
    defer allocator.free(cmds);

    const expected_cmds = [_]Proof.StmtCmd{
        .Sort,
        .TermDef,
        .Axiom,
        .Thm,
        .LocalThm,
        .Thm,
        .LocalThm,
        .Thm,
        .End,
    };
    try std.testing.expectEqual(expected_cmds.len, cmds.len);
    for (expected_cmds, cmds) |expected, actual| {
        try std.testing.expectEqual(expected, actual);
    }

    try std.testing.expectEqualStrings("top_i", (try mmb.theoremName(0)).?);
    try std.testing.expectEqualStrings("first", (try mmb.theoremName(1)).?);
    try std.testing.expectEqualStrings("helper0", (try mmb.theoremName(2)).?);
    try std.testing.expectEqualStrings("second", (try mmb.theoremName(3)).?);
    try std.testing.expectEqualStrings("helper1", (try mmb.theoremName(4)).?);
    try std.testing.expectEqualStrings("third", (try mmb.theoremName(5)).?);
}

test "compiler rejects lemma names that collide with earlier rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\lemma first: $ top $
        \\------------------
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqualStrings("first", diag.name.?);
    try std.testing.expect(diag.span != null);
}

test "compiler rejects theorem names that collide with earlier lemmas" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem helper: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
        \\
        \\helper
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqualStrings("helper", diag.name.?);
}

test "compiler rejects out-of-order and extra proof blocks" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
    ;

    var mismatch = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\second
        \\------
    );
    try std.testing.expectError(error.TheoremNameMismatch, mismatch.check());

    var extra = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
    );
    try std.testing.expectError(error.ExtraProofBlock, extra.check());
}

test "compiler records proof diagnostics for failing proof lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_label (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_label
        \\----------
        \\l1: $ a -> b -> a $ by ax_keep (a := $ a $, b := $ b $) [missing]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownLabel, compiler.compileMmb(
        std.testing.allocator,
    ));
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownLabel, diag.err);
    try std.testing.expectEqualStrings("keep_label", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing", diag.name.?);
    try std.testing.expect(diag.span != null);
}

test "compiler records inference diagnostics for omitted arguments" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_bad (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_bad
        \\--------
        \\l1: $ b -> a -> b $ by ax_keep [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnifyMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));
    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnifyMismatch, diag.err);
    try std.testing.expectEqualStrings(
        "could not infer omitted rule arguments from the line and refs",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expectEqualStrings("keep_bad", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("ax_keep", diag.rule_name.?);
    try std.testing.expect(diag.span != null);
}

test "compiler reports dependency slot exhaustion clearly" {
    const allocator = std.testing.allocator;

    var mm0_buf = std.ArrayListUnmanaged(u8){};
    defer mm0_buf.deinit(allocator);
    try mm0_buf.appendSlice(allocator,
        \\--| @vars y
        \\provable sort wff;
        \\term top: wff;
        \\--| @fresh y
        \\axiom use_fresh {y: wff}: $ top $;
        \\theorem overflow
    );
    for (0..CompilerExpr.tracked_bound_dep_limit) |idx| {
        try mm0_buf.writer(allocator).print(" {{x{d}: wff}}", .{idx});
    }
    try mm0_buf.appendSlice(allocator, ": $ top $;\n");

    const proof_src =
        \\overflow
        \\--------
        \\l1: $ top $ by use_fresh []
    ;

    var compiler = Compiler.initWithProof(
        allocator,
        mm0_buf.items,
        proof_src,
    );
    try std.testing.expectError(
        error.DependencySlotExhausted,
        compiler.compileMmb(allocator),
    );

    const diag = compiler.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DependencySlotExhausted, diag.err);
    try std.testing.expectEqualStrings("overflow", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("use_fresh", diag.rule_name.?);
    try std.testing.expectEqualStrings("y", diag.name.?);
    try std.testing.expectEqualStrings(
        "theorem exceeded the 55 tracked bound-variable dependency slots",
        mm0.compilerDiagnosticSummary(diag),
    );
}

test "strict replay still infers exact omitted binders" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_exact (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_exact
        \\----------
        \\l1: $ a -> b -> a $ by ax_keep [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);

    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
}

test "strict replay does not open defs during omitted inference" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def id (a: wff): wff = $ a -> a $;
        \\axiom ax_id (a: wff): $ id a $;
        \\theorem strict_infer_expected (a: wff): $ a -> a $;
    ;
    const proof_src =
        \\strict_infer_expected
        \\---------------------
        \\l1: $ a -> a $ by ax_id []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(mm0_src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();

    const assertion = blk: {
        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |value| {
                    if (value.kind != .theorem) continue;
                    if (!std.mem.eql(
                        u8,
                        value.name,
                        "strict_infer_expected",
                    )) continue;
                    break :blk value;
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };
    const rule_id = env.getRuleId("ax_id") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    try theorem.seedAssertion(assertion);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try theorem_vars.put(actual_name, expr);
        }
    }

    const parsed_line = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const line_expr = try theorem.internParsedExpr(parsed_line);
    const partial_bindings = [_]?CompilerExpr.ExprId{null};
    const ref_exprs = [_]CompilerExpr.ExprId{};
    const line = ProofScript.ProofLine{
        .label = "l1",
        .assertion = .{
            .text = " a -> a ",
            .span = .{ .start = 0, .end = 0 },
        },
        .rule_name = "ax_id",
        .arg_bindings = &.{},
        .refs = &.{},
        .span = .{ .start = 0, .end = 0 },
    };

    try std.testing.expectError(
        error.TermMismatch,
        CompilerInference.strictInferBindings(
            {},
            arena.allocator(),
            &env,
            &theorem,
            assertion,
            rule,
            line,
            &partial_bindings,
            &ref_exprs,
            line_expr,
        ),
    );
}

test "compiler normalizes conclusions then transports through defs" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_normalize_def_transport_concl",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_normalize_def_transport_concl",
        "proof",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "theorem context preserves theorem var identity" {
    const src =
        \\provable sort wff;
        \\theorem thm (a b: wff): $ a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    var ctx = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(assertion);
    try std.testing.expectEqual(@as(usize, 2), ctx.theorem_vars.items.len);

    const first = ctx.theorem_vars.items[0];
    const second = ctx.theorem_vars.items[1];
    try std.testing.expect(first != second);

    const first_node = ctx.interner.node(first);
    const first_value = first_node.*;
    switch (first_value) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try std.testing.expectEqual(@as(u32, 0), idx);
            },
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }

    const second_node = ctx.interner.node(second);
    const second_value = second_node.*;
    switch (second_value) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try std.testing.expectEqual(@as(u32, 1), idx);
            },
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }
}

test "theorem context rejects dummy dependency slot overflow" {
    var ctx = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const limit = CompilerExpr.tracked_bound_dep_limit;
    try ctx.seedBinderCount(limit - 1);
    ctx.next_dummy_dep = limit - 1;

    const last_dummy = try ctx.addDummyVarResolved("wff", 0);
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_dummies.items.len);
    try std.testing.expectEqual(
        @as(u55, 1) << @intCast(limit - 1),
        ctx.theorem_dummies.items[0].deps,
    );
    try std.testing.expectEqual(limit, ctx.next_dummy_dep);

    const node = ctx.interner.node(last_dummy);
    switch (node.*) {
        .variable => |var_id| switch (var_id) {
            .dummy_var => |idx| try std.testing.expectEqual(@as(u32, 0), idx),
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }

    try std.testing.expectError(
        error.DependencySlotExhausted,
        ctx.addDummyVarResolved("wff", 0),
    );
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_dummies.items.len);
    try std.testing.expectEqual(limit, ctx.next_dummy_dep);
}

test "theorem context interns parsed expressions with sharing" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\theorem thm (a b: wff): $ imp a b $ > $ imp a b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    var ctx = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(assertion);
    const concl_id = try ctx.internParsedExpr(assertion.concl);

    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_hyps.items.len);
    try std.testing.expectEqual(ctx.theorem_hyps.items[0], concl_id);
    try std.testing.expectEqual(@as(usize, 3), ctx.interner.count());
}

test "template instantiation shares repeated substitutions" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom dup (a: wff): $ imp a a $;
        \\theorem host (p q: wff): $ imp p q $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());

    const sort_stmt = (try parser.next()).?;
    try env.addStmt(sort_stmt);
    const term_stmt = (try parser.next()).?;
    try env.addStmt(term_stmt);
    const axiom_stmt = (try parser.next()).?;
    try env.addStmt(axiom_stmt);
    const host_stmt = (try parser.next()).?;
    try env.addStmt(host_stmt);

    const host = switch (host_stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };
    const rule = env.rules.items[0];

    var ctx = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(host);
    const subst = try ctx.internParsedExpr(host.concl);
    const inst = try ctx.instantiateTemplate(rule.concl, &.{subst});

    const inst_node = ctx.interner.node(inst);
    const inst_value = inst_node.*;
    switch (inst_value) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 0), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            try std.testing.expectEqual(subst, app.args[0]);
            try std.testing.expectEqual(subst, app.args[1]);
        },
        else => return error.UnexpectedExprNode,
    }
}

const ProofCaseOutcome = union(enum) {
    pass,
    fail: anyerror,
    // Expected-failure cases for known frontend bugs.
    known_fail,
    // Explicitly unsupported cases whose semantics need a broader design.
    unsupported,
};

const ProofCase = struct {
    stem: []const u8,
    outcome: ProofCaseOutcome,
};

const ProofCaseMetadata = struct {
    stem: []const u8,
    reason: []const u8,
};

const known_proof_case_failures = [_]ProofCaseMetadata{};

const unsupported_proof_cases = [_]ProofCaseMetadata{
    .{
        .stem = "unsupported_def_unfold_then_rewrite_concl",
        .reason = "requires inventing an erased hidden def witness after " ++
            "unfold then rewrite; treating that as out of scope",
    },
};

fn lookupProofCaseReason(
    entries: []const ProofCaseMetadata,
    stem: []const u8,
) ?[]const u8 {
    for (entries) |entry| {
        if (std.mem.eql(u8, entry.stem, stem)) return entry.reason;
    }
    return null;
}

fn knownFailReason(stem: []const u8) ?[]const u8 {
    return lookupProofCaseReason(&known_proof_case_failures, stem);
}

fn unsupportedReason(stem: []const u8) ?[]const u8 {
    return lookupProofCaseReason(&unsupported_proof_cases, stem);
}

const proof_cases = [_]ProofCase{
    .{ .stem = "pass_keep", .outcome = .pass },
    .{ .stem = "pass_label", .outcome = .pass },
    .{ .stem = "pass_gen", .outcome = .pass },
    .{ .stem = "pass_dup", .outcome = .pass },
    .{ .stem = "pass_def", .outcome = .pass },
    .{ .stem = "pass_def_dummy", .outcome = .pass },
    .{ .stem = "pass_def_transport", .outcome = .pass },
    .{ .stem = "pass_def_unfold_line", .outcome = .pass },
    .{ .stem = "pass_def_unfold_ref", .outcome = .pass },
    .{ .stem = "pass_def_unfold_final", .outcome = .pass },
    .{ .stem = "pass_def_unfold_final_reverse", .outcome = .pass },
    .{ .stem = "pass_def_unfold_dummy", .outcome = .pass },
    .{ .stem = "pass_def_view_basic", .outcome = .pass },
    .{ .stem = "pass_def_rewrite_concl", .outcome = .pass },
    .{ .stem = "pass_def_rewrite_hyp", .outcome = .pass },
    // Strict replay stays exact, but omitted binders can fall back to
    // shared targeted transparency when needed.
    .{ .stem = "pass_def_infer_expected", .outcome = .pass },
    .{ .stem = "pass_def_infer_actual", .outcome = .pass },
    .{ .stem = "pass_def_infer_hyp", .outcome = .pass },
    .{ .stem = "pass_def_infer_dummy", .outcome = .pass },
    .{ .stem = "pass_def_infer_user_side", .outcome = .pass },
    .{ .stem = "pass_def_infer_user_side_hyp", .outcome = .pass },
    .{ .stem = "pass_def_infer_user_side_final", .outcome = .pass },
    .{ .stem = "pass_def_all_elim_free_param", .outcome = .pass },
    .{ .stem = "pass_category_defs_direct", .outcome = .pass },
    .{ .stem = "pass_infer_normalized_conclusion", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_explicit", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_infer", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_and_elim", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_reorder", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_unfold", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_fold", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_twostep", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_imp_elim_ctx_mixed", .outcome = .pass },
    .{ .stem = "pass_def_acui_assoc", .outcome = .pass },
    .{
        .stem = "fail_def_unfold_then_rewrite",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{ .stem = "fail_nested_def_unfold_then_acui", .outcome = .pass },
    .{
        .stem = "unsupported_def_unfold_then_rewrite_concl",
        .outcome = .unsupported,
    },
    .{ .stem = "unsupported_epi_comp", .outcome = .pass },
    .{ .stem = "pass_epi_cancel_right", .outcome = .pass },
    .{ .stem = "pass_epi_mono_cancel_right", .outcome = .pass },
    .{ .stem = "pass_epi_comp_assign", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_hyp", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_view", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_recover", .outcome = .pass, },
    .{ .stem = "pass_def_unfold_then_acui_concl", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_acui_hyp", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_abstract", .outcome = .pass, },
    .{ .stem = "pass_def_unfold_then_rewrite_abstract_hyp", .outcome = .pass, },
    .{ .stem = "pass_def_unfold_then_full_acui_concl", .outcome = .pass, },
    .{ .stem = "pass_def_unfold_then_full_acui_hyp", .outcome = .pass, },
    .{ .stem = "pass_def_unfold_then_full_acui_abstract", .outcome = .pass, },
    .{ .stem = "pass_def_unfold_then_full_acui_abstract_hyp", .outcome = .pass, },
    .{ .stem = "pass_normalize", .outcome = .pass },
    .{ .stem = "pass_normalize_nested", .outcome = .pass },
    .{ .stem = "pass_normalize_identity", .outcome = .pass },
    .{ .stem = "pass_normalize_hyp", .outcome = .pass },
    .{ .stem = "pass_normalize_repeat_ref", .outcome = .pass },
    .{ .stem = "pass_normalize_noop", .outcome = .pass },
    .{ .stem = "pass_normalize_def_transport_concl", .outcome = .pass },
    .{ .stem = "hilbert", .outcome = .pass },
    .{ .stem = "hilbert_quant", .outcome = .pass },
    .{ .stem = "hilbert_russell", .outcome = .pass },
    .{ .stem = "pass_view_basic", .outcome = .pass },
    .{ .stem = "pass_view_explicit", .outcome = .pass },
    .{ .stem = "pass_recover_basic", .outcome = .pass },
    .{ .stem = "pass_abstract_basic", .outcome = .pass },
    .{ .stem = "pass_abstract_repeated", .outcome = .pass },
    .{ .stem = "pass_abstract_view_phantoms", .outcome = .pass },
    .{ .stem = "pass_abstract_explicit_target", .outcome = .pass },
    .{ .stem = "pass_abstract_chain_recover", .outcome = .pass },
    .{ .stem = "pass_abstract_normalize", .outcome = .pass },
    .{ .stem = "pass_fresh_hole", .outcome = .pass },
    .{ .stem = "pass_fresh_explicit_override", .outcome = .pass },
    .{ .stem = "pass_fresh_reuse", .outcome = .pass },
    .{ .stem = "demo_prop_cnf", .outcome = .pass },
    .{ .stem = "demo_nd_excluded_middle", .outcome = .pass },
    .{ .stem = "demo_seq_peirce", .outcome = .pass },
    .{ .stem = "demo_lk_exists_mono", .outcome = .pass },
    .{ .stem = "demo_calculus_product_rule", .outcome = .pass },
    .{ .stem = "demo_category_pullback", .outcome = .pass },
    .{ .stem = "demo_category_pullback_legacy_abbrev_mono", .outcome = .pass },
    .{ .stem = "demo_category_pullback_legacy_abbrev_pullback", .outcome = .pass },
    .{ .stem = "demo_category_pullback_legacy_abbrev_both", .outcome = .pass },
    .{ .stem = "demo_category_pullback_unfold", .outcome = .pass },
    .{ .stem = "demo_category_pullback_unfold_2", .outcome = .pass },
    .{ .stem = "demo_category_pullback_unfold_3", .outcome = .pass },
    .{ .stem = "demo_category_pullback_unfold_4", .outcome = .pass },
    .{ .stem = "pass_acui_remainder_overlap", .outcome = .pass },
    .{ .stem = "pass_acui_order_independent_overlap", .outcome = .pass },
    .{ .stem = "pass_acui_repeated_explicit_item", .outcome = .pass },
    .{ .stem = "pass_acui_duplicate_binders_same_item", .outcome = .pass },
    .{ .stem = "pass_acui_principal_remainder", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_absorb", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_absorb_commuted", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_duplicate_def", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_absorb_infer", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_absorb", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_cancel", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_cancel_then_absorb", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_structural_def_leftover", .outcome = .pass },
    .{ .stem = "pass_au_category", .outcome = .pass },
    .{ .stem = "pass_struct_nd_imp_intro", .outcome = .pass },
    .{ .stem = "pass_struct_nd_forall_elim", .outcome = .pass },
    .{ .stem = "pass_view_infer_ctx_raw", .outcome = .pass },
    .{ .stem = "pass_struct_seq_forall_left", .outcome = .pass },
    .{ .stem = "quant_nd", .outcome = .pass },
    .{
        .stem = "fail_missing_binding",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_def_unfold_mismatch",
        .outcome = .{ .fail = error.HypothesisMismatch },
    },
    .{
        .stem = "fail_def_view_mismatch",
        .outcome = .{ .fail = error.ViewHypothesisMismatch },
    },
    .{
        .stem = "fail_def_infer_ambiguous",
        .outcome = .{ .fail = error.AmbiguousAcuiMatch },
    },
    .{
        .stem = "fail_def_hidden_dummy_all_elim_ctx_uncovered",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{
        .stem = "fail_acui_same_side_uncovered",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{
        .stem = "fail_acui_same_side_leftover_def",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{
        .stem = "fail_acui_cross_side_uncovered",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{ .stem = "fail_acui_cross_side_leftover_def", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_ax", .outcome = .pass },
    .{ .stem = "pass_legacy_abbrev_on_nondef", .outcome = .pass },
    .{
        .stem = "fail_infer_mismatch",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{
        .stem = "fail_hyp_mismatch",
        .outcome = .{ .fail = error.HypothesisMismatch },
    },
    .{
        .stem = "fail_duplicate_label",
        .outcome = .{ .fail = error.DuplicateLabel },
    },
    .{
        .stem = "fail_boundness",
        .outcome = .{ .fail = error.BoundnessMismatch },
    },
    .{
        .stem = "fail_view_boundness",
        .outcome = .{ .fail = error.BoundnessMismatch },
    },
    .{
        .stem = "fail_unknown_label",
        .outcome = .{ .fail = error.UnknownLabel },
    },
    .{
        .stem = "fail_normalize_mismatch",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{
        .stem = "fail_abstract_no_occurrence",
        .outcome = .{ .fail = error.AbstractNoPlugOccurrence },
    },
    .{
        .stem = "fail_abstract_structure_mismatch",
        .outcome = .{ .fail = error.AbstractStructureMismatch },
    },
    .{
        .stem = "fail_abstract_sort_mismatch",
        .outcome = .{ .fail = error.AbstractPlugSortMismatch },
    },
    .{
        .stem = "fail_abstract_conflict",
        .outcome = .{ .fail = error.AbstractConflict },
    },
    .{
        .stem = "fail_abstract_unknown_binder",
        .outcome = .{ .fail = error.UnknownAbstractBinder },
    },
    .{
        .stem = "fail_abstract_without_view",
        .outcome = .{ .fail = error.AbstractWithoutView },
    },
    .{
        .stem = "fail_fresh_unknown_binder",
        .outcome = .{ .fail = error.UnknownFreshBinder },
    },
    .{
        .stem = "fail_fresh_duplicate",
        .outcome = .{ .fail = error.DuplicateFreshBinder },
    },
    .{
        .stem = "fail_fresh_nonbound_binder",
        .outcome = .{ .fail = error.FreshRequiresBoundBinder },
    },
    .{
        .stem = "fail_fresh_sort_restriction",
        .outcome = .{ .fail = error.FreshFreeSort },
    },
    .{
        .stem = "fail_fresh_exhausted",
        .outcome = .{ .fail = error.FreshNoAvailableVar },
    },
    .{
        .stem = "fail_var_conclusion_mismatch",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{ .stem = "pass_comment_trailing", .outcome = .pass },
    .{ .stem = "pass_comment_standalone", .outcome = .pass },
    .{ .stem = "pass_comment_only_lines", .outcome = .pass },
    .{ .stem = "pass_vars_basic", .outcome = .pass },
    .{ .stem = "pass_vars_unicode", .outcome = .pass },
    .{ .stem = "pass_vars_lazy", .outcome = .pass },
    .{ .stem = "pass_vars_tab_ws", .outcome = .pass },
    .{
        .stem = "fail_vars_duplicate_token",
        .outcome = .{ .fail = error.DuplicateVarsToken },
    },
    .{
        .stem = "fail_vars_collision",
        .outcome = .{ .fail = error.VarsTokenCollision },
    },
    .{
        .stem = "fail_vars_later_collision",
        .outcome = .{ .fail = error.VarsTokenCollision },
    },
    .{
        .stem = "fail_vars_invalid_annotation",
        .outcome = .{ .fail = error.InvalidVarsAnnotation },
    },
    .{
        .stem = "fail_vars_strict_sort",
        .outcome = .{ .fail = error.VarsStrictSort },
    },
    .{
        .stem = "fail_vars_free_sort",
        .outcome = .{ .fail = error.VarsFreeSort },
    },
};

fn readProofCaseFile(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

const mm0c_cache_dir = ".zig-cache-local/mm0c-test";

fn mm0cExists() bool {
    const result = std.process.Child.run(.{
        .allocator = std.testing.allocator,
        .argv = &.{"mm0-c"},
        .max_output_bytes = 8 * 1024,
    }) catch return false;
    std.testing.allocator.free(result.stdout);
    std.testing.allocator.free(result.stderr);
    // mm0-c with no args prints usage and exits 1
    return switch (result.term) {
        .Exited => true,
        else => false,
    };
}

fn verifyWithMm0c(mm0_src: []const u8, mmb: []const u8, stem: []const u8) !void {
    var path_buf: [256]u8 = undefined;
    const mmb_path = std.fmt.bufPrint(&path_buf, mm0c_cache_dir ++ "/{s}.mmb", .{stem}) catch mm0c_cache_dir ++ "/out.mmb";
    std.fs.cwd().makePath(mm0c_cache_dir) catch |err| {
        std.debug.print("FAIL (mm0-c) could not create cache dir: {}\n", .{err});
        return err;
    };
    std.fs.cwd().writeFile(.{ .sub_path = mmb_path, .data = mmb }) catch |err| {
        std.debug.print("FAIL (mm0-c) could not write temp mmb: {}\n", .{err});
        return err;
    };
    defer std.fs.cwd().deleteFile(mmb_path) catch {};

    var child = std.process.Child.init(&.{ "mm0-c", mmb_path }, std.testing.allocator);
    child.stdin_behavior = .Pipe;
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;

    child.spawn() catch |err| {
        std.debug.print("FAIL (mm0-c) could not spawn: {}\n", .{err});
        return err;
    };

    child.stdin.?.writeAll(mm0_src) catch {};
    child.stdin.?.close();
    child.stdin = null;

    // Read stderr before wait to avoid pipe buffer deadlock
    var stderr_buf: [4096]u8 = undefined;
    const stderr_len = child.stderr.?.readAll(&stderr_buf) catch 0;
    const stderr = stderr_buf[0..stderr_len];

    const term = child.wait() catch |err| {
        std.debug.print("FAIL (mm0-c) wait failed: {}\n", .{err});
        return err;
    };

    switch (term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("FAIL (mm0-c) exit code {d}\n{s}\n", .{ code, stderr });
                return error.Mm0cVerificationFailed;
            }
        },
        else => {
            std.debug.print("FAIL (mm0-c) abnormal termination\n", .{});
            return error.Mm0cVerificationFailed;
        },
    }
}

test "non-pass proof case metadata stays in sync" {
    var known_fail_count: usize = 0;
    var unsupported_count: usize = 0;

    for (proof_cases) |case| {
        switch (case.outcome) {
            .known_fail => {
                known_fail_count += 1;
                try std.testing.expect(knownFailReason(case.stem) != null);
                try std.testing.expect(unsupportedReason(case.stem) == null);
            },
            .unsupported => {
                unsupported_count += 1;
                try std.testing.expect(unsupportedReason(case.stem) != null);
                try std.testing.expect(knownFailReason(case.stem) == null);
            },
            else => {
                try std.testing.expect(knownFailReason(case.stem) == null);
                try std.testing.expect(unsupportedReason(case.stem) == null);
            },
        }
    }

    try std.testing.expectEqual(
        known_proof_case_failures.len,
        known_fail_count,
    );
    try std.testing.expectEqual(
        unsupported_proof_cases.len,
        unsupported_count,
    );

    for (known_proof_case_failures, 0..) |entry, idx| {
        for (known_proof_case_failures[idx + 1 ..]) |other| {
            try std.testing.expect(!std.mem.eql(u8, entry.stem, other.stem));
        }
    }
    for (unsupported_proof_cases, 0..) |entry, idx| {
        for (unsupported_proof_cases[idx + 1 ..]) |other| {
            try std.testing.expect(!std.mem.eql(u8, entry.stem, other.stem));
        }
    }
    for (known_proof_case_failures) |entry| {
        try std.testing.expect(unsupportedReason(entry.stem) == null);
    }
    for (unsupported_proof_cases) |entry| {
        try std.testing.expect(knownFailReason(entry.stem) == null);
    }
}

test "compiler proof cases from files" {
    const allocator = std.testing.allocator;
    const have_mm0c = mm0cExists();

    var failure_count: usize = 0;
    var failed_cases: [proof_cases.len][]const u8 = undefined;

    for (proof_cases) |case| {
        const mm0_src = try readProofCaseFile(allocator, case.stem, "mm0");
        defer allocator.free(mm0_src);

        const proof_src = try readProofCaseFile(allocator, case.stem, "proof");
        defer allocator.free(proof_src);

        var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
        switch (case.outcome) {
            .pass => {
                const mmb = compiler.compileMmb(allocator) catch |err| {
                    std.debug.print("FAIL (compile) case={s} err={}\n", .{ case.stem, err });
                    if (compiler.last_diagnostic) |diag| {
                        std.debug.print(
                            "  diag: kind={} theorem={s} line={s} rule={s}\n",
                            .{
                                diag.kind,
                                diag.theorem_name orelse "?",
                                diag.line_label orelse "?",
                                diag.rule_name orelse "?",
                            },
                        );
                    }
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                    continue;
                };
                defer allocator.free(mmb);
                mm0.verifyPair(allocator, mm0_src, mmb) catch |err| {
                    std.debug.print("FAIL (verify) case={s} err={}\n", .{ case.stem, err });
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                    continue;
                };
                if (have_mm0c) {
                    verifyWithMm0c(mm0_src, mmb, case.stem) catch {
                        std.debug.print("FAIL (mm0-c) case={s}\n", .{case.stem});
                        failed_cases[failure_count] = case.stem;
                        failure_count += 1;
                        continue;
                    };
                }
            },
            .fail => |err| {
                try std.testing.expectError(err, compiler.compileMmb(allocator));
            },
            .known_fail => {
                if (compiler.compileMmb(allocator)) |mmb| {
                    allocator.free(mmb);
                    std.debug.print(
                        "XPASS (known_fail) case={s}: {s}\n",
                        .{
                            case.stem,
                            knownFailReason(case.stem) orelse "missing reason",
                        },
                    );
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                } else |_| {}
            },
            .unsupported => {
                if (compiler.compileMmb(allocator)) |mmb| {
                    allocator.free(mmb);
                    std.debug.print(
                        "XPASS (unsupported) case={s}: {s}\n",
                        .{
                            case.stem,
                            unsupportedReason(case.stem) orelse
                                "missing reason",
                        },
                    );
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                } else |_| {}
            },
        }
    }

    if (failure_count > 0) {
        std.debug.print("\n{d} test case(s) failed:\n", .{failure_count});
        for (failed_cases[0..failure_count]) |stem| {
            std.debug.print("  - {s}\n", .{stem});
        }
        return error.TestCasesFailed;
    }
}

test "compiler emits name, var, and hyp index tables" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(allocator, "hilbert", "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(allocator, "hilbert", "proof");
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    try std.testing.expect(mmb.header.p_index != 0);
    try std.testing.expectEqualStrings("wff", (try mmb.sortName(0)).?);
    try std.testing.expectEqualStrings("imp", (try mmb.termName(0)).?);
    try std.testing.expectEqualStrings("not", (try mmb.termName(1)).?);
    try std.testing.expectEqualStrings("h1", (try mmb.theoremName(0)).?);
    try std.testing.expectEqualStrings("mp", (try mmb.theoremName(3)).?);
    try std.testing.expectEqualStrings("imp_refl", (try mmb.theoremName(4)).?);
    try std.testing.expectEqualStrings("hs", (try mmb.theoremName(5)).?);

    const imp_vars = (try mmb.termVarNames(0)).?;
    try std.testing.expectEqual(@as(usize, 2), imp_vars.len());
    try std.testing.expectEqualStrings("a", (try imp_vars.get(0)).?);
    try std.testing.expectEqualStrings("b", (try imp_vars.get(1)).?);

    const mp_vars = (try mmb.theoremVarNames(3)).?;
    try std.testing.expectEqual(@as(usize, 2), mp_vars.len());
    try std.testing.expectEqualStrings("a", (try mp_vars.get(0)).?);
    try std.testing.expectEqualStrings("b", (try mp_vars.get(1)).?);

    const mp_hyps = (try mmb.theoremHypNames(3)).?;
    try std.testing.expectEqual(@as(usize, 2), mp_hyps.len());
    try std.testing.expectEqualStrings("#1", (try mp_hyps.get(0)).?);
    try std.testing.expectEqualStrings("#2", (try mp_hyps.get(1)).?);

    const refl_hyps = (try mmb.theoremHypNames(4)).?;
    try std.testing.expectEqual(@as(usize, 0), refl_hyps.len());

    const hs_hyps = (try mmb.theoremHypNames(5)).?;
    try std.testing.expectEqual(@as(usize, 2), hs_hyps.len());
    try std.testing.expectEqualStrings("#1", (try hs_hyps.get(0)).?);
    try std.testing.expectEqualStrings("#2", (try hs_hyps.get(1)).?);
}

test "compiler records theorem-local fresh vars in theorem var table" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(allocator, "pass_fresh_hole", "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_fresh_hole",
        "proof",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    var theorem_id: ?u32 = null;
    var idx: u32 = 0;
    while (idx < mmb.header.num_thms) : (idx += 1) {
        const maybe_name = try mmb.theoremName(idx);
        if (maybe_name) |name| {
            if (std.mem.eql(u8, name, "fresh_hole")) {
                theorem_id = idx;
                break;
            }
        }
    }

    const fresh_hole_id = theorem_id orelse return error.MissingTheorem;
    const vars = (try mmb.theoremVarNames(fresh_hole_id)).?;
    try std.testing.expectEqual(@as(usize, 3), vars.len());
    try std.testing.expectEqualStrings("a", (try vars.get(0)).?);
    try std.testing.expectEqualStrings("b", (try vars.get(1)).?);
    try std.testing.expectEqual(@as(?[]const u8, null), try vars.get(2));
}

test "compiler reuses @fresh pool vars across proof lines" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_fresh_reuse",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_fresh_reuse",
        "proof",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    var theorem_id: ?u32 = null;
    var idx: u32 = 0;
    while (idx < mmb.header.num_thms) : (idx += 1) {
        const maybe_name = try mmb.theoremName(idx);
        if (maybe_name) |name| {
            if (std.mem.eql(u8, name, "fresh_reuse")) {
                theorem_id = idx;
                break;
            }
        }
    }

    const fresh_reuse_id = theorem_id orelse return error.MissingTheorem;
    const vars = (try mmb.theoremVarNames(fresh_reuse_id)).?;
    try std.testing.expectEqual(@as(usize, 1), vars.len());
    try std.testing.expectEqual(@as(?[]const u8, null), try vars.get(0));
}

// ---------- Phase 0: dummy allocation classification tests ----------

test "explicit source dummy allocation is allowed and tracks dependency slots" {
    // Explicit user/source dummies (seedTerm, applyDummyBindings) are
    // legitimate and must keep working. This test verifies the low-level
    // addDummyVarResolved API that those paths use.
    var ctx = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    // Allocate two explicit dummies — simulates what seedTerm does for
    // dummies declared in .mm0 source.
    const d0 = try ctx.addDummyVarResolved("wff", 0);
    const d1 = try ctx.addDummyVarResolved("wff", 0);

    // Each allocation should produce a distinct ExprId.
    try std.testing.expect(d0 != d1);

    // Both should be tracked in theorem_dummies.
    try std.testing.expectEqual(@as(usize, 2), ctx.theorem_dummies.items.len);

    // Each should consume a distinct dependency slot (one-hot bit).
    try std.testing.expect(ctx.theorem_dummies.items[0].deps != ctx.theorem_dummies.items[1].deps);

    // The dependency counter should advance by 2.
    try std.testing.expectEqual(@as(u32, 2), ctx.next_dummy_dep);
}

test "mirror-only dummy allocation does not affect source theorem context" {
    // Mirror-only allocations (mirror_support.zig, normalized_match.zig)
    // create dummies in a temporary TheoremContext. This test verifies that
    // allocating dummies in a separate "mirror" context leaves the original
    // source context's dummy count untouched.
    var source = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer source.deinit();

    // Allocate one explicit dummy in the source context.
    _ = try source.addDummyVarResolved("wff", 0);
    try std.testing.expectEqual(@as(usize, 1), source.theorem_dummies.items.len);
    const source_dep_after = source.next_dummy_dep;

    // Create a separate "mirror" context (simulates MirroredTheoremContext).
    var mirror = CompilerExpr.TheoremContext.init(std.testing.allocator);
    defer mirror.deinit();

    // Allocate several dummies in the mirror context.
    _ = try mirror.addDummyVarResolved("wff", 0);
    _ = try mirror.addDummyVarResolved("wff", 0);
    _ = try mirror.addDummyVarResolved("wff", 0);

    // Mirror allocations should not have touched the source context.
    try std.testing.expectEqual(@as(usize, 1), source.theorem_dummies.items.len);
    try std.testing.expectEqual(source_dep_after, source.next_dummy_dep);

    // Mirror context should have its own independent count.
    try std.testing.expectEqual(@as(usize, 3), mirror.theorem_dummies.items.len);
}

test "finalization rejects unresolved hidden-dummy witnesses" {
    // When matching through a def with hidden dummies produces symbolic
    // bindings containing unresolved dummy structure, finalization
    // returns error.UnresolvedDummyWitness. The user must provide
    // explicit bindings that cover the hidden def structure.
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const parsed_actual = try parser.parseFormulaText(" mono f ", &theorem_vars);
    const actual = try theorem.internParsedExpr(parsed_actual);

    // keep_all has binders {x: obj} (p: wff x), hyp = $ ∀ x p $.
    // Matching hyp against "mono f" forces unfolding of mono and
    // produces symbolic bindings with hidden-dummy structure.
    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, &.{ .none, .none });
    defer session.deinit();

    // Match hyp (∀ x p) against "mono f". The symbolic engine unfolds mono
    // and binds x → hidden dummy .a, p → ∀ b (...) symbolically.
    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));

    const dummies_before = theorem.theorem_dummies.items.len;

    // Finalization rejects unresolved hidden-dummy witnesses.
    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session.finalizeConcreteBindings(),
    );

    // No dummies should have been allocated.
    try std.testing.expectEqual(dummies_before, theorem.theorem_dummies.items.len);
}

test "exact hidden-binder seeds match repeated def expansions" {
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const actual = try theorem.internParsedExpr(
        try parser.parseFormulaText(" mono f ", &theorem_vars),
    );
    const exact_x = try theorem.addDummyVarResolved("obj", 0);

    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(
        rule.args,
        &.{ .{ .exact = exact_x }, .none },
    );
    defer session.deinit();

    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));
}

test "resolveBindingSeeds preserves symbolic state through view reuse" {
    // Same setup as the strict finalization test: matching "mono f" against
    // keep_all's ∀ x p produces symbolic bindings with hidden-dummy structure.
    // resolveBindingSeeds should return .bound seeds (preserving symbolic
    // BoundValues) where resolveOptionalBindings would lose the info.
    const src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term all {x: obj} (p: wff x): wff; prefix all: $A.$ prec 41;
        \\term eq (a b: obj): wff; infixl eq: $=$ prec 35;
        \\term pair (a b: obj): obj;
        \\axiom keep_all {x: obj} (p: wff x): $ A. x p $ > $ A. x p $;
        \\def mono {.a .b: obj} (f: obj): wff =
        \\  $ A. a A. b ((pair f a = pair f b) -> (a = b)) $;
        \\theorem test (f: obj): $ mono f $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = CompilerEnv.GlobalEnv.init(arena.allocator());
    var theorem = CompilerExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(arena.allocator());
    defer theorem_vars.deinit();
    var found_theorem = false;

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .assertion => |value| {
                if (value.kind != .theorem or found_theorem) continue;
                try theorem.seedAssertion(value);
                for (value.arg_names, value.arg_exprs) |name, expr| {
                    if (name) |actual_name| {
                        try theorem_vars.put(actual_name, expr);
                    }
                }
                found_theorem = true;
            },
            else => {},
        }
    }
    if (!found_theorem) return error.MissingAssertion;

    const parsed_actual = try parser.parseFormulaText(" mono f ", &theorem_vars);
    const actual = try theorem.internParsedExpr(parsed_actual);

    const rule_id = env.getRuleId("keep_all") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    var def_ops = DefOps.Context.init(arena.allocator(), &theorem, &env);
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(rule.args, &.{ .none, .none });
    defer session.deinit();

    // Match hyp (∀ x p) against "mono f" — produces symbolic bindings.
    try std.testing.expect(try session.matchTransparent(rule.hyps[0], actual));

    // materializeOptionalBindings collapses symbolic bindings to null where
    // the symbolic structure contains unresolved hidden dummies.
    const optional = try session.materializeOptionalBindings();
    defer arena.allocator().free(optional);

    // resolveBindingSeeds should preserve symbolic state as .bound seeds.
    const binding_seeds = try session.resolveBindingSeeds();

    // At least one seed should be .bound (symbolic), not .none.
    var has_bound_seed = false;
    for (binding_seeds) |seed| {
        switch (seed) {
            .bound => {
                has_bound_seed = true;
            },
            else => {},
        }
    }
    try std.testing.expect(has_bound_seed);

    var seed_state = try session.exportMatchSeedState(binding_seeds);
    defer seed_state.deinit(arena.allocator());

    // The exported state should be usable in a new session without any
    // side-channel import step, and without allocating theorem dummies.
    const dummies_before = theorem.theorem_dummies.items.len;

    var session2 = try def_ops.beginRuleMatchFromSeedState(
        rule.args,
        &seed_state,
    );
    defer session2.deinit();

    try std.testing.expectError(
        error.UnresolvedDummyWitness,
        session2.finalizeConcreteBindings(),
    );
    try std.testing.expectEqual(
        dummies_before,
        theorem.theorem_dummies.items.len,
    );
}
