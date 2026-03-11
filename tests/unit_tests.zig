const std = @import("std");
const mm0 = @import("mm0");

const Arg = mm0.Arg;
const Compiler = mm0.Compiler;
const CompilerEnv = mm0.CompilerEnv;
const CompilerExpr = mm0.CompilerExpr;
const Expr = mm0.Expr;
const Header = mm0.Header;
const MAGIC = mm0.MAGIC;
const Heap = mm0.Heap;
const MM0Parser = mm0.MM0Parser;
const Mmb = mm0.Mmb;
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
    try std.testing.expectEqualStrings("other", second.name);
    try std.testing.expect(second.underline_span == null);
    try std.testing.expectEqual(@as(usize, 1), second.lines.len);
    try std.testing.expectEqual(
        @as(usize, 0),
        second.lines[0].arg_bindings.len,
    );
    try std.testing.expect((try parser.nextBlock()) == null);
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
};

const ProofCase = struct {
    stem: []const u8,
    outcome: ProofCaseOutcome,
};

const proof_cases = [_]ProofCase{
    .{ .stem = "pass_keep", .outcome = .pass },
    .{ .stem = "pass_label", .outcome = .pass },
    .{ .stem = "pass_gen", .outcome = .pass },
    .{ .stem = "pass_dup", .outcome = .pass },
    .{ .stem = "pass_def", .outcome = .pass },
    .{ .stem = "pass_normalize", .outcome = .pass },
    .{ .stem = "pass_normalize_nested", .outcome = .pass },
    .{ .stem = "pass_normalize_identity", .outcome = .pass },
    .{ .stem = "pass_normalize_hyp", .outcome = .pass },
    .{ .stem = "pass_normalize_noop", .outcome = .pass },
    .{ .stem = "hilbert", .outcome = .pass },
    .{ .stem = "hilbert_quant", .outcome = .pass },
    .{ .stem = "hilbert_russell", .outcome = .pass },
    .{ .stem = "pass_view_basic", .outcome = .pass },
    .{ .stem = "pass_view_explicit", .outcome = .pass },
    .{ .stem = "pass_recover_basic", .outcome = .pass },
    .{ .stem = "pass_struct_nd_imp_intro", .outcome = .pass },
    .{ .stem = "pass_struct_nd_forall_elim", .outcome = .pass },
    .{ .stem = "pass_struct_seq_forall_left", .outcome = .pass },
    .{
        .stem = "fail_missing_binding",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
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

test "compiler proof cases from files" {
    const allocator = std.testing.allocator;

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
                        std.debug.print("  diag: kind={} theorem={s} line={s} rule={s} name={s}\n", .{
                            diag.kind,
                            diag.theorem_name orelse "?",
                            diag.line_label orelse "?",
                            diag.rule_name orelse "?",
                            diag.name orelse "?",
                        });
                    }
                    return err;
                };
                defer allocator.free(mmb);
                mm0.verifyPair(allocator, mm0_src, mmb) catch |err| {
                    std.debug.print("FAIL (verify) case={s} err={}\n", .{ case.stem, err });
                    return err;
                };
            },
            .fail => |err| {
                try std.testing.expectError(err, compiler.compileMmb(allocator));
            },
        }
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
