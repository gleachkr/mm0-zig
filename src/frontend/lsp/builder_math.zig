const std = @import("std");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const support = @import("builder_support.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;

const SourceSpan = source.SourceSpan;
const StatementIterator = source.StatementIterator;
const MathTokenCursor = source.MathTokenCursor;
const statementHeader = source.statementHeader;
const nextMathStringIn = source.nextMathStringIn;

const binderMarkdown = markdown.binderMarkdown;

const findBinder = support.findBinder;
const targetRangeForUse = support.targetRangeForUse;

pub fn indexMm0Math(self: anytype, text: []const u8) !void {
    var iter = StatementIterator.init(text);
    while (iter.next()) |stmt| {
        const decl_index = self.declIndexForStatement(text, stmt);
        var pos = stmt.start;
        while (nextMathStringIn(text, stmt.end, &pos)) |math| {
            try self.indexMathString(
                .mm0,
                math.text,
                math.inner_start,
                decl_index,
                false,
                null,
            );
        }
    }
}

pub fn declIndexForStatement(
    self: anytype,
    text: []const u8,
    stmt: SourceSpan,
) ?usize {
    const header = statementHeader(text, stmt) orelse return null;
    if (header.name == null) return null;
    if (std.mem.eql(u8, header.keyword, "sort") or
        std.mem.eql(u8, header.keyword, "term") or
        std.mem.eql(u8, header.keyword, "def") or
        std.mem.eql(u8, header.keyword, "axiom") or
        std.mem.eql(u8, header.keyword, "theorem"))
    {
        return self.decl_by_name.get(header.name.?);
    }
    return null;
}

pub fn indexLemmaHeaderMath(
    self: anytype,
    block: proof_script.ProofBlock,
    decl_index: usize,
    available_before: ?usize,
) !void {
    var pos: usize = 0;
    while (nextMathStringIn(
        block.header_tail,
        block.header_tail.len,
        &pos,
    )) |math| {
        try self.indexMathString(
            .proof,
            math.text,
            block.header_tail_span.start + math.inner_start,
            decl_index,
            false,
            available_before,
        );
    }
}

pub fn indexProofMathString(
    self: anytype,
    block_index: usize,
    math: proof_script.MathString,
) !void {
    const block = self.proof_blocks.items[block_index];
    try self.indexMathString(
        .proof,
        math.text,
        math.span.start + 1,
        block.decl_index,
        true,
        block.global_available_before,
    );
}

pub fn indexRuleApplicationMath(
    self: anytype,
    block_index: usize,
    app: proof_script.RuleApplication,
) !void {
    for (app.arg_bindings) |binding| {
        try self.indexProofMathString(block_index, binding.formula);
    }
}

pub fn indexMathString(
    self: anytype,
    document: DocumentId,
    math: []const u8,
    base: usize,
    decl_index: ?usize,
    allow_sort_vars: bool,
    available_before: ?usize,
) !void {
    var cursor = MathTokenCursor{
        .src = math,
        .left_delims = self.left_delims,
        .right_delims = self.right_delims,
    };
    while (cursor.next()) |token| {
        if (token.text.len == 0) continue;
        const range = SourceRange{
            .document = document,
            .start = base + token.start,
            .end = base + token.end,
        };
        if (decl_index) |idx| {
            const decl = self.declarations.items[idx];
            if (findBinder(decl, token.text)) |binder| {
                try self.addSymbol(.{
                    .source_range = range,
                    .target_range = binder.range orelse decl.name_range,
                    .markdown = try binderMarkdown(
                        self.allocator,
                        decl,
                        binder,
                    ),
                });
                continue;
            }
        }
        if (self.notation_by_token.get(token.text)) |idx| {
            const decl = self.declarations.items[idx];
            try self.addSymbol(.{
                .source_range = range,
                .target_range = targetRangeForUse(
                    decl,
                    document,
                    range.start,
                    available_before,
                ),
                .markdown = decl.markdown,
            });
            continue;
        }
        if (self.decl_by_name.get(token.text)) |idx| {
            const decl = self.declarations.items[idx];
            if (decl.kind == .term or decl.kind == .def) {
                try self.addSymbol(.{
                    .source_range = range,
                    .target_range = targetRangeForUse(
                        decl,
                        document,
                        range.start,
                        available_before,
                    ),
                    .markdown = decl.markdown,
                });
                continue;
            }
        }
        if (allow_sort_vars) {
            if (self.sort_var_by_token.get(token.text)) |idx| {
                const decl = self.declarations.items[idx];
                try self.addSymbol(.{
                    .source_range = range,
                    .target_range = targetRangeForUse(
                        decl,
                        document,
                        range.start,
                        available_before,
                    ),
                    .markdown = decl.markdown,
                });
            }
        }
    }
}
