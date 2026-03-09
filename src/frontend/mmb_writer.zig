const std = @import("std");
const Arg = @import("../trusted/args.zig").Arg;
const Header = @import("../trusted/headers.zig").Header;
const MAGIC = @import("../trusted/headers.zig").MAGIC;
const IndexEntry = @import("../trusted/mmb.zig").IndexEntry;
const NameEntry = @import("../trusted/mmb.zig").NameEntry;
const Sort = @import("../trusted/sorts.zig").Sort;
const Term = @import("../trusted/terms.zig").Term;
const Theorem = @import("../trusted/theorems.zig").Theorem;
const StmtCmd = @import("../trusted/proof.zig").StmtCmd;

const NAME_ID = [4]u8{ 'N', 'a', 'm', 'e' };
const VAR_ID = [4]u8{ 'V', 'a', 'r', 'N' };
const HYP_ID = [4]u8{ 'H', 'y', 'p', 'N' };

pub const TermRecord = struct {
    args: []const Arg,
    ret_sort: u7,
    is_def: bool,
    unify: []const u8,
    name: ?[]const u8 = null,
    var_names: []const ?[]const u8 = &.{},
};

pub const TheoremRecord = struct {
    args: []const Arg,
    unify: []const u8,
    name: ?[]const u8 = null,
    var_names: []const ?[]const u8 = &.{},
    hyp_names: []const ?[]const u8 = &.{},
};

pub const Statement = struct {
    cmd: StmtCmd,
    body: []const u8,
};

pub fn appendCmd(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    op: anytype,
    data: u32,
) !void {
    const op_int: u8 = switch (@typeInfo(@TypeOf(op))) {
        .@"enum" => @intFromEnum(op),
        .comptime_int, .int => @intCast(op),
        else => @compileError("unsupported opcode type"),
    };

    if (data == 0) {
        try bytes.append(allocator, @intCast(op_int));
        return;
    }
    if (data <= std.math.maxInt(u8)) {
        try bytes.append(allocator, 0x40 | @as(u8, @intCast(op_int)));
        try bytes.append(allocator, @intCast(data));
        return;
    }
    if (data <= std.math.maxInt(u16)) {
        try bytes.append(allocator, 0x80 | @as(u8, @intCast(op_int)));
        try bytes.append(allocator, @intCast(data & 0xFF));
        try bytes.append(allocator, @intCast((data >> 8) & 0xFF));
        return;
    }
    try bytes.append(allocator, 0xC0 | @as(u8, @intCast(op_int)));
    try bytes.append(allocator, @intCast(data & 0xFF));
    try bytes.append(allocator, @intCast((data >> 8) & 0xFF));
    try bytes.append(allocator, @intCast((data >> 16) & 0xFF));
    try bytes.append(allocator, @intCast((data >> 24) & 0xFF));
}

pub fn appendStmt(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    cmd: StmtCmd,
    body: []const u8,
) !void {
    if (body.len + 2 <= std.math.maxInt(u8)) {
        try appendCmd(bytes, allocator, cmd, @intCast(body.len + 2));
    } else if (body.len + 3 <= std.math.maxInt(u16)) {
        try appendCmd(bytes, allocator, cmd, @intCast(body.len + 3));
    } else {
        const total = try std.math.add(u32, @intCast(body.len), 5);
        try appendCmd(bytes, allocator, cmd, total);
    }
    try bytes.appendSlice(allocator, body);
}

pub fn buildFile(
    allocator: std.mem.Allocator,
    sort_names: []const []const u8,
    sorts: []const Sort,
    terms: []const TermRecord,
    theorems: []const TheoremRecord,
    statements: []const Statement,
) ![]u8 {
    var bytes = std.ArrayListUnmanaged(u8){};
    errdefer bytes.deinit(allocator);

    try bytes.resize(allocator, @sizeOf(Header));
    @memset(bytes.items[0..@sizeOf(Header)], 0);

    for (sorts) |sort| {
        try appendValue(&bytes, allocator, sort);
    }

    try appendAlign(&bytes, allocator, @alignOf(Term));
    const p_terms = bytes.items.len;
    const term_table_offset = bytes.items.len;
    try bytes.resize(
        allocator,
        bytes.items.len + terms.len * @sizeOf(Term),
    );
    @memset(bytes.items[term_table_offset..][0 .. terms.len * @sizeOf(Term)], 0);

    try appendAlign(&bytes, allocator, @alignOf(Theorem));
    const p_thms = bytes.items.len;
    const theorem_table_offset = bytes.items.len;
    try bytes.resize(
        allocator,
        bytes.items.len + theorems.len * @sizeOf(Theorem),
    );
    @memset(
        bytes.items[theorem_table_offset..][0 .. theorems.len * @sizeOf(Theorem)],
        0,
    );

    var term_table = try allocator.alloc(Term, terms.len);
    defer allocator.free(term_table);
    for (terms, 0..) |record, idx| {
        try appendAlign(&bytes, allocator, @alignOf(Arg));
        const p_data = bytes.items.len;
        for (record.args) |arg| {
            try appendValue(&bytes, allocator, arg);
        }
        try appendValue(&bytes, allocator, Arg{
            .deps = 0,
            .reserved = 0,
            .sort = record.ret_sort,
            .bound = false,
        });
        try bytes.appendSlice(allocator, record.unify);

        term_table[idx] = .{
            .num_args = std.math.cast(u16, record.args.len) orelse {
                return error.TooManyTermArgs;
            },
            .ret_sort = .{
                .sort = record.ret_sort,
                .is_def = record.is_def,
            },
            .reserved = 0,
            .p_data = std.math.cast(u32, p_data) orelse {
                return error.MmbTooLarge;
            },
        };
    }

    var theorem_table = try allocator.alloc(Theorem, theorems.len);
    defer allocator.free(theorem_table);
    for (theorems, 0..) |record, idx| {
        try appendAlign(&bytes, allocator, @alignOf(Arg));
        const p_data = bytes.items.len;
        for (record.args) |arg| {
            try appendValue(&bytes, allocator, arg);
        }
        try bytes.appendSlice(allocator, record.unify);

        theorem_table[idx] = .{
            .num_args = std.math.cast(u16, record.args.len) orelse {
                return error.TooManyTheoremArgs;
            },
            .reserved = 0,
            .p_data = std.math.cast(u32, p_data) orelse {
                return error.MmbTooLarge;
            },
        };
    }

    const p_proof = bytes.items.len;
    var sort_proofs = try allocator.alloc(u64, sort_names.len);
    defer allocator.free(sort_proofs);
    var term_proofs = try allocator.alloc(u64, terms.len);
    defer allocator.free(term_proofs);
    var theorem_proofs = try allocator.alloc(u64, theorems.len);
    defer allocator.free(theorem_proofs);

    var sort_count: usize = 0;
    var term_count: usize = 0;
    var theorem_count: usize = 0;
    for (statements) |stmt| {
        const stmt_start = try castU64(bytes.items.len);
        try appendStmt(&bytes, allocator, stmt.cmd, stmt.body);
        switch (stmt.cmd) {
            .Sort => {
                if (sort_count >= sort_proofs.len) return error.StatementCountMismatch;
                sort_proofs[sort_count] = stmt_start;
                sort_count += 1;
            },
            .TermDef, .LocalDef => {
                if (term_count >= term_proofs.len) return error.StatementCountMismatch;
                term_proofs[term_count] = stmt_start;
                term_count += 1;
            },
            .Axiom, .Thm, .LocalThm => {
                if (theorem_count >= theorem_proofs.len) {
                    return error.StatementCountMismatch;
                }
                theorem_proofs[theorem_count] = stmt_start;
                theorem_count += 1;
            },
            .End => unreachable,
            else => {},
        }
    }
    try appendCmd(&bytes, allocator, StmtCmd.End, 0);

    if (sort_count != sort_names.len or
        term_count != terms.len or
        theorem_count != theorems.len)
    {
        return error.StatementCountMismatch;
    }

    for (term_table, 0..) |term, idx| {
        writeValueAt(
            bytes.items,
            term_table_offset + idx * @sizeOf(Term),
            term,
        );
    }
    for (theorem_table, 0..) |theorem, idx| {
        writeValueAt(
            bytes.items,
            theorem_table_offset + idx * @sizeOf(Theorem),
            theorem,
        );
    }

    const p_index = try appendIndex(
        &bytes,
        allocator,
        sort_names,
        terms,
        theorems,
        sort_proofs,
        term_proofs,
        theorem_proofs,
    );

    const header = Header{
        .magic = MAGIC,
        .version = 1,
        .num_sorts = std.math.cast(u8, sorts.len) orelse {
            return error.TooManySorts;
        },
        .reserved0 = 0,
        .num_terms = std.math.cast(u32, terms.len) orelse {
            return error.TooManyTerms;
        },
        .num_thms = std.math.cast(u32, theorems.len) orelse {
            return error.TooManyTheorems;
        },
        .p_terms = std.math.cast(u32, p_terms) orelse {
            return error.MmbTooLarge;
        },
        .p_thms = std.math.cast(u32, p_thms) orelse {
            return error.MmbTooLarge;
        },
        .p_proof = std.math.cast(u32, p_proof) orelse {
            return error.MmbTooLarge;
        },
        .reserved1 = 0,
        .p_index = p_index,
    };
    writeValueAt(bytes.items, 0, header);

    return try bytes.toOwnedSlice(allocator);
}

fn appendIndex(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    sort_names: []const []const u8,
    terms: []const TermRecord,
    theorems: []const TheoremRecord,
    sort_proofs: []const u64,
    term_proofs: []const u64,
    theorem_proofs: []const u64,
) !u64 {
    try appendAlign(bytes, allocator, @alignOf(u64));
    const p_index = try castU64(bytes.items.len);
    try appendValue(bytes, allocator, @as(u64, 3));

    const index_entry_offset = bytes.items.len;
    try bytes.resize(
        allocator,
        bytes.items.len + 3 * @sizeOf(IndexEntry),
    );
    @memset(bytes.items[index_entry_offset..][0 .. 3 * @sizeOf(IndexEntry)], 0);

    try appendAlign(bytes, allocator, @alignOf(NameEntry));
    const name_table_offset = bytes.items.len;
    const name_entry_count = sort_names.len + terms.len + theorems.len;
    try bytes.resize(
        allocator,
        bytes.items.len + name_entry_count * @sizeOf(NameEntry),
    );
    @memset(bytes.items[name_table_offset..][0 .. name_entry_count * @sizeOf(NameEntry)], 0);

    try appendAlign(bytes, allocator, @alignOf(u64));
    const var_table_offset = bytes.items.len;
    const var_ptr_count = terms.len + theorems.len;
    try bytes.resize(
        allocator,
        bytes.items.len + var_ptr_count * @sizeOf(u64),
    );
    @memset(bytes.items[var_table_offset..][0 .. var_ptr_count * @sizeOf(u64)], 0);

    try appendAlign(bytes, allocator, @alignOf(u64));
    const hyp_table_offset = bytes.items.len;
    try bytes.resize(
        allocator,
        bytes.items.len + theorems.len * @sizeOf(u64),
    );
    @memset(bytes.items[hyp_table_offset..][0 .. theorems.len * @sizeOf(u64)], 0);

    var name_entries = try allocator.alloc(NameEntry, name_entry_count);
    defer allocator.free(name_entries);

    var name_idx: usize = 0;
    for (sort_names, sort_proofs) |name, proof| {
        name_entries[name_idx] = .{
            .proof = proof,
            .name = try appendCString(bytes, allocator, name),
        };
        name_idx += 1;
    }
    for (terms, term_proofs) |record, proof| {
        name_entries[name_idx] = .{
            .proof = proof,
            .name = try appendCStringMaybe(bytes, allocator, record.name),
        };
        name_idx += 1;
    }
    for (theorems, theorem_proofs) |record, proof| {
        name_entries[name_idx] = .{
            .proof = proof,
            .name = try appendCStringMaybe(bytes, allocator, record.name),
        };
        name_idx += 1;
    }

    for (name_entries, 0..) |entry, idx| {
        writeValueAt(
            bytes.items,
            name_table_offset + idx * @sizeOf(NameEntry),
            entry,
        );
    }

    var var_ptrs = try allocator.alloc(u64, var_ptr_count);
    defer allocator.free(var_ptrs);
    var var_idx: usize = 0;
    for (terms) |record| {
        var_ptrs[var_idx] = try appendStringList(
            bytes,
            allocator,
            record.var_names,
        );
        var_idx += 1;
    }
    for (theorems) |record| {
        var_ptrs[var_idx] = try appendStringList(
            bytes,
            allocator,
            record.var_names,
        );
        var_idx += 1;
    }
    for (var_ptrs, 0..) |ptr, idx| {
        writeValueAt(
            bytes.items,
            var_table_offset + idx * @sizeOf(u64),
            ptr,
        );
    }

    for (theorems, 0..) |record, idx| {
        const ptr = try appendStringList(bytes, allocator, record.hyp_names);
        writeValueAt(
            bytes.items,
            hyp_table_offset + idx * @sizeOf(u64),
            ptr,
        );
    }

    const entries = [_]IndexEntry{
        .{
            .id = NAME_ID,
            .data = 0,
            .ptr = try castU64(name_table_offset),
        },
        .{
            .id = VAR_ID,
            .data = 0,
            .ptr = try castU64(var_table_offset),
        },
        .{
            .id = HYP_ID,
            .data = 0,
            .ptr = try castU64(hyp_table_offset),
        },
    };
    for (entries, 0..) |entry, idx| {
        writeValueAt(
            bytes.items,
            index_entry_offset + idx * @sizeOf(IndexEntry),
            entry,
        );
    }

    return p_index;
}

fn appendStringList(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    names: []const ?[]const u8,
) !u64 {
    try appendAlign(bytes, allocator, @alignOf(u64));
    const offset = bytes.items.len;
    try appendValue(bytes, allocator, try castU64(names.len));

    const ptr_offset = bytes.items.len;
    try bytes.resize(
        allocator,
        bytes.items.len + names.len * @sizeOf(u64),
    );
    @memset(bytes.items[ptr_offset..][0 .. names.len * @sizeOf(u64)], 0);

    for (names, 0..) |name, idx| {
        const ptr = try appendCStringMaybe(bytes, allocator, name);
        writeValueAt(
            bytes.items,
            ptr_offset + idx * @sizeOf(u64),
            ptr,
        );
    }

    return try castU64(offset);
}

fn appendCStringMaybe(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    text: ?[]const u8,
) !u64 {
    if (text) |value| {
        return try appendCString(bytes, allocator, value);
    }
    return 0;
}

fn appendCString(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    text: []const u8,
) !u64 {
    const offset = bytes.items.len;
    try bytes.appendSlice(allocator, text);
    try bytes.append(allocator, 0);
    return try castU64(offset);
}

fn castU64(value: usize) !u64 {
    return std.math.cast(u64, value) orelse error.MmbTooLarge;
}

fn appendAlign(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    align_to: usize,
) !void {
    const misalignment = bytes.items.len % align_to;
    if (misalignment == 0) return;
    const padding = align_to - misalignment;
    try bytes.appendNTimes(allocator, 0, padding);
}

fn appendValue(
    bytes: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    value: anytype,
) !void {
    try bytes.appendSlice(allocator, std.mem.asBytes(&value));
}

fn writeValueAt(buf: []u8, offset: usize, value: anytype) void {
    const raw = std.mem.asBytes(&value);
    @memcpy(buf[offset..][0..raw.len], raw);
}
