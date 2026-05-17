const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const Types = @import("types.zig");
const completion = @import("completion.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const DeclarationKind = Types.DeclarationKind;
const BinderDecl = Types.BinderDecl;
const Declaration = Types.Declaration;

const StatementIterator = source.StatementIterator;
const sourceRangeFromSlice = source.sourceRangeFromSlice;
const findIdentIn = source.findIdentIn;

const completionSortText = completion.completionSortText;
const sort_group_local_binder = completion.sort_group_local_binder;

pub fn nextStatementRangeForMm0Stmt(
    iter: *StatementIterator,
    parsed: parse.MM0Stmt,
) SourceRange {
    const name_range = mm0StmtNameRange(parsed);
    while (iter.next()) |stmt| {
        if (stmt.start <= name_range.start and stmt.end >= name_range.end) {
            return .{
                .document = .mm0,
                .start = stmt.start,
                .end = stmt.end,
            };
        }
    }
    return name_range;
}

fn mm0StmtNameRange(stmt: parse.MM0Stmt) SourceRange {
    return switch (stmt) {
        .sort => |sort| mathSpanRange(sort.name_span),
        .term => |term| mathSpanRange(term.name_span),
        .assertion => |assertion| mathSpanRange(assertion.name_span),
    };
}

pub fn proofBlockDeclarationKind(kind: proof_script.BlockKind) DeclarationKind {
    return switch (kind) {
        .theorem => .theorem,
        .lemma => .lemma,
    };
}

pub fn mathSpanRange(span: parse.MathSpan) SourceRange {
    return .{
        .document = .mm0,
        .start = span.start,
        .end = span.end,
    };
}

pub fn proofSpanRange(span: proof_script.Span) SourceRange {
    return .{
        .document = .proof,
        .start = span.start,
        .end = span.end,
    };
}

pub fn proofMathTextSpan(span: proof_script.Span) parse.MathSpan {
    return .{
        .start = @min(span.start + 1, span.end),
        .end = if (span.end > span.start) span.end - 1 else span.end,
    };
}

fn rangeContains(range: SourceRange, document: DocumentId, offset: usize) bool {
    return range.document == document and offset >= range.start and
        offset < range.end;
}

pub fn targetRangeIfAvailable(decl: Declaration, use_start: usize) ?SourceRange {
    if (decl.name_range.start <= use_start) return decl.name_range;
    return null;
}

pub fn targetRangeForUse(
    decl: Declaration,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
) ?SourceRange {
    return switch (document) {
        .mm0 => targetRangeIfAvailable(decl, use_start),
        .proof => {
            if (decl.name_range.document == .proof) {
                if (decl.name_range.start <= use_start) return decl.name_range;
                return null;
            }
            const before = available_before orelse return decl.name_range;
            if (decl.name_range.start < before) return decl.name_range;
            return null;
        },
    };
}

pub fn isFatalIndexError(err: anyerror) bool {
    return switch (err) {
        error.OutOfMemory => true,
        else => false,
    };
}

pub fn findBinder(decl: Declaration, name: []const u8) ?BinderDecl {
    for (decl.binders) |binder| {
        if (std.mem.eql(u8, binder.name, name)) return binder;
    }
    return null;
}

pub fn bindersFromTerm(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    term: parse.TermStmt,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    try appendBindersFromArgs(
        allocator,
        &binders,
        document,
        text,
        term.arg_names,
        term.args,
        0,
    );
    try appendBindersFromArgs(
        allocator,
        &binders,
        document,
        text,
        term.dummy_names,
        term.dummy_args,
        term.args.len,
    );
    return try binders.toOwnedSlice(allocator);
}

fn appendBindersFromArgs(
    allocator: std.mem.Allocator,
    binders: *std.ArrayListUnmanaged(BinderDecl),
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    ordinal_base: usize,
) !void {
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = sourceRangeFromSlice(document, text, name),
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                ordinal_base + i,
                name,
            ),
        });
    }
}

const ScannedProofBinder = struct {
    name: []const u8,
    range: SourceRange,
    is_dummy: bool,
};

pub fn bindersFromProofDef(
    allocator: std.mem.Allocator,
    def: proof_script.DefItem,
    term: parse.TermStmt,
) ![]const BinderDecl {
    const header_tail = def.header_tail orelse return &.{};
    const header_span = def.header_tail_span orelse return &.{};
    const scanned = try scanProofDefBinders(
        allocator,
        header_tail,
        header_span.start,
    );

    var binders = std.ArrayListUnmanaged(BinderDecl){};
    var arg_index: usize = 0;
    var dummy_index: usize = 0;
    var ordinal: usize = 0;
    for (scanned) |item| {
        const arg = if (item.is_dummy) blk: {
            if (dummy_index >= term.dummy_args.len) continue;
            const arg = term.dummy_args[dummy_index];
            dummy_index += 1;
            break :blk arg;
        } else blk: {
            if (arg_index >= term.args.len) continue;
            const arg = term.args[arg_index];
            arg_index += 1;
            break :blk arg;
        };
        const maybe_name = if (item.is_dummy)
            term.dummy_names[dummy_index - 1]
        else
            term.arg_names[arg_index - 1];
        const name = maybe_name orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = item.range,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                ordinal,
                name,
            ),
        });
        ordinal += 1;
    }
    return try binders.toOwnedSlice(allocator);
}

fn scanProofDefBinders(
    allocator: std.mem.Allocator,
    header_tail: []const u8,
    base: usize,
) ![]const ScannedProofBinder {
    var result = std.ArrayListUnmanaged(ScannedProofBinder){};
    var pos: usize = 0;
    while (pos < header_tail.len) : (pos += 1) {
        const open = header_tail[pos];
        if (open != '(' and open != '{') continue;
        pos += 1;
        while (pos < header_tail.len) {
            skipProofDefHeaderSpace(header_tail, &pos);
            if (pos >= header_tail.len or header_tail[pos] == ':') break;
            const is_dummy = header_tail[pos] == '.';
            if (is_dummy) pos += 1;
            if (pos >= header_tail.len or !isProofIdentStart(header_tail[pos])) {
                break;
            }
            const start = pos;
            pos += 1;
            while (pos < header_tail.len and isProofIdentChar(header_tail[pos])) {
                pos += 1;
            }
            try result.append(allocator, .{
                .name = header_tail[start..pos],
                .range = .{
                    .document = .proof,
                    .start = base + start,
                    .end = base + pos,
                },
                .is_dummy = is_dummy,
            });
        }
    }
    return try result.toOwnedSlice(allocator);
}

fn skipProofDefHeaderSpace(text: []const u8, pos: *usize) void {
    while (pos.* < text.len) {
        switch (text[pos.*]) {
            ' ', '\t', '\r', '\n' => pos.* += 1,
            else => return,
        }
    }
}

fn isProofIdentStart(ch: u8) bool {
    return std.ascii.isAlphabetic(ch) or ch == '_';
}

fn isProofIdentChar(ch: u8) bool {
    return isProofIdentStart(ch) or std.ascii.isDigit(ch);
}

pub fn bindersFromArgs(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = sourceRangeFromSlice(document, text, name),
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                name,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}

pub fn completionArgsFromArgs(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    for (args, 0..) |arg, i| {
        const name = if (i < names.len) names[i] else null;
        const label = if (name) |actual|
            actual
        else
            try std.fmt.allocPrint(allocator, "arg{d}", .{i + 1});
        try binders.append(allocator, .{
            .name = label,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = if (name) |actual|
                sourceRangeFromSlice(document, text, actual)
            else
                null,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                label,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}

pub fn bindersFromLemma(
    allocator: std.mem.Allocator,
    block: proof_script.ProofBlock,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl){};
    var search_start: usize = 0;
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        const maybe_rel = findIdentIn(block.header_tail, name, search_start);
        const range = if (maybe_rel) |rel| blk: {
            search_start = rel + name.len;
            break :blk SourceRange{
                .document = .proof,
                .start = block.header_tail_span.start + rel,
                .end = block.header_tail_span.start + rel + name.len,
            };
        } else null;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = range,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                name,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}
