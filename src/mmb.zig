const std = @import("std");
const Header = @import("./headers.zig").Header;
const Sort = @import("./sorts.zig").Sort;
const Term = @import("./terms.zig").Term;
const Theorem = @import("./theorems.zig").Theorem;
const Arg = @import("./args.zig").Arg;

const NAME_ID = [4]u8{ 'N', 'a', 'm', 'e' };
const VAR_ID = [4]u8{ 'V', 'a', 'r', 'N' };
const HYP_ID = [4]u8{ 'H', 'y', 'p', 'N' };

pub const IndexEntry = extern struct {
    id: [4]u8,
    data: u32,
    ptr: u64,
};

pub const NameEntry = extern struct {
    proof: u64,
    name: u64,
};

pub const StringList = struct {
    file_bytes: []const u8,
    ptrs: []const u64,

    pub fn len(self: StringList) usize {
        return self.ptrs.len;
    }

    pub fn get(self: StringList, idx: usize) !?[]const u8 {
        if (idx >= self.ptrs.len) return null;
        return try readOptionalCString(self.file_bytes, self.ptrs[idx]);
    }
};

pub const NameIndex = struct {
    sorts: []const NameEntry,
    terms: []const NameEntry,
    thms: []const NameEntry,
};

pub const VarIndex = struct {
    term_vars: []const u64,
    thm_vars: []const u64,
};

pub const HypIndex = struct {
    thm_hyps: []const u64,
};

pub const Index = struct {
    names: ?NameIndex = null,
    vars: ?VarIndex = null,
    hyps: ?HypIndex = null,

    pub fn sortName(
        self: Index,
        file_bytes: []const u8,
        sort_id: usize,
    ) !?[]const u8 {
        const names = self.names orelse return null;
        if (sort_id >= names.sorts.len) return error.InvalidSort;
        return try readOptionalCString(file_bytes, names.sorts[sort_id].name);
    }

    pub fn termName(
        self: Index,
        file_bytes: []const u8,
        term_id: usize,
    ) !?[]const u8 {
        const names = self.names orelse return null;
        if (term_id >= names.terms.len) return error.InvalidTerm;
        return try readOptionalCString(file_bytes, names.terms[term_id].name);
    }

    pub fn theoremName(
        self: Index,
        file_bytes: []const u8,
        theorem_id: usize,
    ) !?[]const u8 {
        const names = self.names orelse return null;
        if (theorem_id >= names.thms.len) return error.InvalidTheorem;
        return try readOptionalCString(file_bytes, names.thms[theorem_id].name);
    }

    pub fn validateSortProof(
        self: Index,
        sort_id: usize,
        stmt_start: usize,
    ) !void {
        const names = self.names orelse return;
        if (sort_id >= names.sorts.len) return error.BadIndexLookup;
        try validateNameProof(names.sorts[sort_id], stmt_start);
    }

    pub fn validateTermProof(
        self: Index,
        term_id: usize,
        stmt_start: usize,
    ) !void {
        const names = self.names orelse return;
        if (term_id >= names.terms.len) return error.BadIndexLookup;
        try validateNameProof(names.terms[term_id], stmt_start);
    }

    pub fn validateTheoremProof(
        self: Index,
        theorem_id: usize,
        stmt_start: usize,
    ) !void {
        const names = self.names orelse return;
        if (theorem_id >= names.thms.len) return error.BadIndexLookup;
        try validateNameProof(names.thms[theorem_id], stmt_start);
    }

    pub fn termVarNames(
        self: Index,
        file_bytes: []const u8,
        term_id: usize,
    ) !?StringList {
        const vars = self.vars orelse return null;
        if (term_id >= vars.term_vars.len) return error.InvalidTerm;
        return try readOptionalStringList(file_bytes, vars.term_vars[term_id]);
    }

    pub fn theoremVarNames(
        self: Index,
        file_bytes: []const u8,
        theorem_id: usize,
    ) !?StringList {
        const vars = self.vars orelse return null;
        if (theorem_id >= vars.thm_vars.len) return error.InvalidTheorem;
        return try readOptionalStringList(file_bytes, vars.thm_vars[theorem_id]);
    }

    pub fn theoremHypNames(
        self: Index,
        file_bytes: []const u8,
        theorem_id: usize,
    ) !?StringList {
        const hyps = self.hyps orelse return null;
        if (theorem_id >= hyps.thm_hyps.len) return error.InvalidTheorem;
        return try readOptionalStringList(file_bytes, hyps.thm_hyps[theorem_id]);
    }
};

pub const Mmb = struct {
    file_bytes: []const u8,
    header: Header,
    sort_table: []const Sort,
    term_table: []const Term,
    theorem_table: []const Theorem,
    index: Index,

    pub fn parse(
        _: std.mem.Allocator,
        file_bytes: []const u8,
    ) !Mmb {
        if (file_bytes.len < @sizeOf(Header)) return error.ShortMmb;

        const header = try Header.fromBytes(file_bytes[0..@sizeOf(Header)]);
        try validateHeaderLayout(header, file_bytes.len);

        const sort_table = try readTableSlice(
            Sort,
            file_bytes,
            @sizeOf(Header),
            header.num_sorts,
            error.ShortSortTable,
            null,
        );
        try validateSortTable(sort_table);

        const term_table = try readTableSlice(
            Term,
            file_bytes,
            header.p_terms,
            header.num_terms,
            error.ShortTermTable,
            error.MisalignedTermTable,
        );
        try validateTermTable(term_table, file_bytes, header.num_sorts);

        const theorem_table = try readTableSlice(
            Theorem,
            file_bytes,
            header.p_thms,
            header.num_thms,
            error.ShortTheoremTable,
            error.MisalignedTheoremTable,
        );
        try validateTheoremTable(theorem_table, file_bytes, header.num_sorts);

        const index = try parseIndex(file_bytes, header);

        return .{
            .file_bytes = file_bytes,
            .header = header,
            .sort_table = sort_table,
            .term_table = term_table,
            .theorem_table = theorem_table,
            .index = index,
        };
    }

    pub fn sortName(self: Mmb, sort_id: usize) !?[]const u8 {
        return try self.index.sortName(self.file_bytes, sort_id);
    }

    pub fn termName(self: Mmb, term_id: usize) !?[]const u8 {
        return try self.index.termName(self.file_bytes, term_id);
    }

    pub fn theoremName(self: Mmb, theorem_id: usize) !?[]const u8 {
        return try self.index.theoremName(self.file_bytes, theorem_id);
    }

    pub fn termVarNames(self: Mmb, term_id: usize) !?StringList {
        return try self.index.termVarNames(self.file_bytes, term_id);
    }

    pub fn theoremVarNames(self: Mmb, theorem_id: usize) !?StringList {
        return try self.index.theoremVarNames(self.file_bytes, theorem_id);
    }

    pub fn theoremHypNames(self: Mmb, theorem_id: usize) !?StringList {
        return try self.index.theoremHypNames(self.file_bytes, theorem_id);
    }
};

fn validateHeaderLayout(header: Header, file_len: usize) !void {
    const header_end = @sizeOf(Header) + header.num_sorts;
    const p_terms = try usizeFromU32(header.p_terms);
    const p_thms = try usizeFromU32(header.p_thms);
    const p_proof = try usizeFromU32(header.p_proof);
    const p_index = try usizeFromU64(header.p_index);

    if (header_end > p_terms) return error.SuspectHeader;
    if (p_terms > p_thms) return error.SuspectHeader;
    if (p_thms > p_proof) return error.SuspectHeader;
    if (p_proof > file_len) return error.SuspectHeader;
    if (p_index != 0 and p_index < p_proof) return error.SuspectHeader;
    if (p_index > file_len) return error.SuspectHeader;
}

fn validateSortTable(sort_table: []const Sort) !void {
    for (sort_table) |sort| {
        if (sort._padding != 0) return error.BadSortPadding;
    }
}

fn validateTermTable(
    term_table: []const Term,
    file_bytes: []const u8,
    num_sorts: u8,
) !void {
    for (term_table) |term| {
        if (term.reserved != 0) return error.BadReserved;
        if (term.ret_sort.sort >= num_sorts) return error.InvalidSort;

        const args = try term.getArgsChecked(file_bytes);
        for (args) |arg| {
            try validateArg(arg, num_sorts);
        }

        const ret = try term.getRetArgChecked(file_bytes);
        try validateArg(ret, num_sorts);
    }
}

fn validateTheoremTable(
    theorem_table: []const Theorem,
    file_bytes: []const u8,
    num_sorts: u8,
) !void {
    for (theorem_table) |theorem| {
        if (theorem.reserved != 0) return error.BadReserved;

        const args = try theorem.getArgsChecked(file_bytes);
        for (args) |arg| {
            try validateArg(arg, num_sorts);
        }
    }
}

fn validateArg(arg: Arg, num_sorts: u8) !void {
    if (arg.reserved != 0) return error.BadReserved;
    if (arg.sort >= num_sorts) return error.InvalidSort;
}

fn parseIndex(
    file_bytes: []const u8,
    header: Header,
) !Index {
    if (header.p_index == 0) return .{};

    const p_index = try usizeFromU64(header.p_index);
    if (p_index % @alignOf(u64) != 0) return error.MisalignedIndex;

    const count = try readScalar(u64, file_bytes, p_index, error.ShortIndex);
    const entry_offset = p_index + @sizeOf(u64);
    const entry_count = try usizeFromU64(count);
    const entries = try readTableSlice(
        IndexEntry,
        file_bytes,
        entry_offset,
        entry_count,
        error.ShortIndex,
        error.MisalignedIndex,
    );

    var index = Index{};
    for (entries) |entry| {
        if (std.mem.eql(u8, &entry.id, &NAME_ID)) {
            if (entry.data != 0) return error.BadIndexData;
            if (index.names != null) return error.DuplicateIndexTable;
            index.names = try parseNameTable(file_bytes, entry.ptr, header);
        } else if (std.mem.eql(u8, &entry.id, &VAR_ID)) {
            if (entry.data != 0) return error.BadIndexData;
            if (index.vars != null) return error.DuplicateIndexTable;
            index.vars = try parseVarTable(file_bytes, entry.ptr, header);
        } else if (std.mem.eql(u8, &entry.id, &HYP_ID)) {
            if (entry.data != 0) return error.BadIndexData;
            if (index.hyps != null) return error.DuplicateIndexTable;
            index.hyps = try parseHypTable(file_bytes, entry.ptr, header);
        }
    }

    return index;
}

fn parseNameTable(
    file_bytes: []const u8,
    ptr: u64,
    header: Header,
) !NameIndex {
    const offset = try usizeFromU64(ptr);
    const sorts = try readTableSlice(
        NameEntry,
        file_bytes,
        offset,
        header.num_sorts,
        error.BadIndexParse,
        error.MisalignedIndex,
    );
    const terms_offset = offset + header.num_sorts * @sizeOf(NameEntry);
    const terms = try readTableSlice(
        NameEntry,
        file_bytes,
        terms_offset,
        header.num_terms,
        error.BadIndexParse,
        error.MisalignedIndex,
    );
    const thms_offset = terms_offset + header.num_terms * @sizeOf(NameEntry);
    const thms = try readTableSlice(
        NameEntry,
        file_bytes,
        thms_offset,
        header.num_thms,
        error.BadIndexParse,
        error.MisalignedIndex,
    );

    for (sorts) |entry| {
        try validateNameEntry(file_bytes, entry);
    }
    for (terms) |entry| {
        try validateNameEntry(file_bytes, entry);
    }
    for (thms) |entry| {
        try validateNameEntry(file_bytes, entry);
    }

    return .{ .sorts = sorts, .terms = terms, .thms = thms };
}

fn parseVarTable(
    file_bytes: []const u8,
    ptr: u64,
    header: Header,
) !VarIndex {
    const offset = try usizeFromU64(ptr);
    const term_vars = try readTableSlice(
        u64,
        file_bytes,
        offset,
        header.num_terms,
        error.BadIndexParse,
        error.MisalignedIndex,
    );
    const thms_offset = offset + header.num_terms * @sizeOf(u64);
    const thm_vars = try readTableSlice(
        u64,
        file_bytes,
        thms_offset,
        header.num_thms,
        error.BadIndexParse,
        error.MisalignedIndex,
    );

    for (term_vars) |list_ptr| {
        _ = try readOptionalStringList(file_bytes, list_ptr);
    }
    for (thm_vars) |list_ptr| {
        _ = try readOptionalStringList(file_bytes, list_ptr);
    }

    return .{ .term_vars = term_vars, .thm_vars = thm_vars };
}

fn parseHypTable(
    file_bytes: []const u8,
    ptr: u64,
    header: Header,
) !HypIndex {
    const offset = try usizeFromU64(ptr);
    const thm_hyps = try readTableSlice(
        u64,
        file_bytes,
        offset,
        header.num_thms,
        error.BadIndexParse,
        error.MisalignedIndex,
    );

    for (thm_hyps) |list_ptr| {
        _ = try readOptionalStringList(file_bytes, list_ptr);
    }

    return .{ .thm_hyps = thm_hyps };
}

fn validateNameEntry(file_bytes: []const u8, entry: NameEntry) !void {
    _ = try readOptionalCString(file_bytes, entry.name);
}

fn validateNameProof(entry: NameEntry, stmt_start: usize) !void {
    if (entry.proof != 0 and entry.proof != stmt_start) {
        return error.BadIndexLookup;
    }
}

fn readOptionalStringList(
    file_bytes: []const u8,
    ptr: u64,
) !?StringList {
    if (ptr == 0) return null;

    const offset = try usizeFromU64(ptr);
    const count = try readScalar(u64, file_bytes, offset, error.BadIndexParse);
    const len = try usizeFromU64(count);
    const ptrs = try readTableSlice(
        u64,
        file_bytes,
        offset + @sizeOf(u64),
        len,
        error.BadIndexParse,
        error.MisalignedIndex,
    );

    for (ptrs) |name_ptr| {
        _ = try readOptionalCString(file_bytes, name_ptr);
    }

    return .{ .file_bytes = file_bytes, .ptrs = ptrs };
}

fn readOptionalCString(
    file_bytes: []const u8,
    ptr: u64,
) !?[]const u8 {
    if (ptr == 0) return null;

    const offset = try usizeFromU64(ptr);
    if (offset >= file_bytes.len) return error.BadIndexLookup;

    const suffix = file_bytes[offset..];
    const nul = std.mem.indexOfScalar(u8, suffix, 0) orelse
        return error.BadIndexLookup;
    const value = suffix[0..nul];
    if (!std.unicode.utf8ValidateSlice(value)) return error.BadIndexLookup;
    return value;
}

fn readScalar(
    comptime T: type,
    file_bytes: []const u8,
    offset: usize,
    short_err: anyerror,
) !T {
    const end = try std.math.add(usize, offset, @sizeOf(T));
    if (end > file_bytes.len) return short_err;

    var value: T = undefined;
    @memcpy(std.mem.asBytes(&value), file_bytes[offset..end]);
    return value;
}

fn readTableSlice(
    comptime T: type,
    file_bytes: []const u8,
    offset_raw: anytype,
    len_raw: anytype,
    short_err: anyerror,
    misaligned_err: ?anyerror,
) ![]const T {
    const offset = try toUsize(offset_raw);
    const len = try toUsize(len_raw);
    const size = try std.math.mul(usize, len, @sizeOf(T));
    const end = try std.math.add(usize, offset, size);
    if (end > file_bytes.len) return short_err;

    if (len == 0) return &.{};
    if (misaligned_err) |err| {
        if (offset % @alignOf(T) != 0) return err;
    }

    const bytes = file_bytes[offset..end];
    return @as([*]const T, @ptrCast(@alignCast(bytes.ptr)))[0..len];
}

fn usizeFromU32(value: u32) !usize {
    return std.math.cast(usize, value) orelse error.IntegerOverflow;
}

fn usizeFromU64(value: u64) !usize {
    return std.math.cast(usize, value) orelse error.IntegerOverflow;
}

fn toUsize(value: anytype) !usize {
    return switch (@TypeOf(value)) {
        usize => value,
        u64 => try usizeFromU64(value),
        u32 => try usizeFromU32(value),
        u16 => value,
        u8 => value,
        comptime_int => value,
        else => @compileError("unsupported integer type"),
    };
}
