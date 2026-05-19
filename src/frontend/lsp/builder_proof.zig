const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");

const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const model = @import("model.zig");
const completion = @import("completion.zig");
const support = @import("builder_support.zig");

const Declaration = Types.Declaration;

const ProofRuleDecl = model.ProofRuleDecl;
const ProofLineDecl = model.ProofLineDecl;
const RuleResolution = model.RuleResolution;

const completionSortText = completion.completionSortText;
const sort_group_proof_lemma = completion.sort_group_proof_lemma;
const sort_group_proof_reference = completion.sort_group_proof_reference;

const binderMarkdown = markdown.binderMarkdown;
const hypRefMarkdown = markdown.hypRefMarkdown;
const lemmaMarkdown = markdown.lemmaMarkdown;
const proofLineMarkdown = markdown.proofLineMarkdown;
const unknownBindingMarkdown = markdown.unknownBindingMarkdown;
const unknownHypMarkdown = markdown.unknownHypMarkdown;
const unknownLineMarkdown = markdown.unknownLineMarkdown;
const unknownRuleMarkdown = markdown.unknownRuleMarkdown;
const unresolvedBindingMarkdown = markdown.unresolvedBindingMarkdown;

const bindersFromLemma = support.bindersFromLemma;
const findBinder = support.findBinder;
const hypothesesFromLemma = support.hypothesesFromLemma;
const isFatalIndexError = support.isFatalIndexError;
const proofBlockDeclarationKind = support.proofBlockDeclarationKind;
const proofSpanRange = support.proofSpanRange;

pub fn addProofBlock(
    self: anytype,
    block: proof_script.ProofBlock,
    global_available_before: ?usize,
) !void {
    const block_index = self.proof_blocks.items.len;
    try self.proof_blocks.append(self.allocator, .{
        .kind = block.kind,
        .name = block.name,
        .name_range = proofSpanRange(block.name_span),
        .span = proofSpanRange(block.span),
        .global_available_before = global_available_before,
    });
    try self.addProofOutline(.{
        .name = block.name,
        .kind = proofBlockDeclarationKind(block.kind),
        .range = proofSpanRange(block.span),
        .selection_range = proofSpanRange(block.name_span),
    });

    switch (block.kind) {
        .theorem => try self.addTheoremBlockHeader(block_index, block),
        .lemma => try self.addLemmaBlockHeader(block_index, block),
    }

    for (block.lines) |line| {
        try self.addProofLine(block_index, line);
    }

    const info = self.proof_blocks.items[block_index];
    if (block.kind == .lemma) {
        if (info.decl_index) |decl_index| {
            try self.proof_rules.append(self.allocator, .{
                .name = block.name,
                .decl_index = decl_index,
                .available_start = block.span.end,
                .sort_text = try completionSortText(
                    self.allocator,
                    sort_group_proof_lemma,
                    block.span.end,
                    block.name,
                ),
            });
        }
    }
}

pub fn addTheoremBlockHeader(
    self: anytype,
    block_index: usize,
    block: proof_script.ProofBlock,
) !void {
    const decl_index = self.theoremDeclIndex(block.name) orelse return;
    const decl = self.declarations.items[decl_index];
    self.proof_blocks.items[block_index].decl_index = decl_index;
    self.proof_blocks.items[block_index].hyp_count = decl.hyp_count;
    self.proof_blocks.items[block_index].hyp_count_known = true;
    try self.addSymbol(.{
        .source_range = proofSpanRange(block.name_span),
        .target_range = decl.name_range,
        .markdown = decl.markdown,
    });
}

pub fn addLemmaBlockHeader(
    self: anytype,
    block_index: usize,
    block: proof_script.ProofBlock,
) !void {
    const maybe_assertion = try self.parseLemmaAssertion(block);
    const hyp_count = if (maybe_assertion) |assertion|
        assertion.hyps.len
    else
        0;
    const binders = if (maybe_assertion) |assertion|
        try bindersFromLemma(
            self.allocator,
            block,
            assertion.arg_names,
            assertion.args,
        )
    else
        &.{};
    const decl: Declaration = .{
        .name = block.name,
        .kind = .lemma,
        .name_range = proofSpanRange(block.name_span),
        .markdown = try lemmaMarkdown(
            self.allocator,
            block,
            hyp_count,
            maybe_assertion != null,
        ),
        .binders = binders,
        .hyp_count = hyp_count,
        .hypotheses = try hypothesesFromLemma(
            self.allocator,
            block,
            hyp_count,
        ),
    };
    const decl_index = try self.addDeclaration(decl);
    self.proof_blocks.items[block_index].decl_index = decl_index;
    self.proof_blocks.items[block_index].hyp_count = hyp_count;
    self.proof_blocks.items[block_index].hyp_count_known =
        maybe_assertion != null;
    try self.indexLemmaHeaderMath(
        block,
        decl_index,
        self.proof_blocks.items[block_index].global_available_before,
    );
}

pub fn parseLemmaAssertion(
    self: anytype,
    block: proof_script.ProofBlock,
) !?parse.AssertionStmt {
    const parser = self.mm0_parser orelse return null;
    const src = try std.fmt.allocPrint(
        self.allocator,
        "theorem {s}{s};",
        .{ block.name, block.header_tail },
    );
    return parser.parseAssertionText(src, .theorem, true) catch |err| {
        if (isFatalIndexError(err)) return err;
        return null;
    };
}

pub fn addProofLine(
    self: anytype,
    block_index: usize,
    line: proof_script.ProofLine,
) !void {
    const decl: Declaration = .{
        .name = line.label,
        .kind = .proof_line,
        .name_range = proofSpanRange(line.label_span),
        .markdown = try proofLineMarkdown(self.allocator, line),
    };
    const decl_index = try self.addDeclaration(decl);
    try self.indexRuleApplication(block_index, line.application, line.span.start);
    try self.indexProofMathString(block_index, line.assertion);
    try self.proof_lines.append(self.allocator, .{
        .block_index = block_index,
        .name = line.label,
        .decl_index = decl_index,
        .line_start = line.span.start,
        .sort_text = try completionSortText(
            self.allocator,
            sort_group_proof_reference,
            line.span.start,
            line.label,
        ),
    });
}

pub fn indexRuleApplication(
    self: anytype,
    block_index: usize,
    app: proof_script.RuleApplication,
    line_start: usize,
) !void {
    try self.proof_applications.append(self.allocator, .{
        .block_index = block_index,
        .rule_name = app.rule_name,
        .rule_span = proofSpanRange(app.rule_span),
        .binding_list_span = if (app.binding_list_span) |span|
            proofSpanRange(span)
        else
            null,
        .refs_span = if (app.refs_span) |span| proofSpanRange(span) else null,
        .span = proofSpanRange(app.span),
        .use_start = app.rule_span.start,
        .line_start = line_start,
    });
    const maybe_rule = self.resolveRule(
        block_index,
        app.rule_name,
        app.rule_span.start,
    );
    if (maybe_rule) |rule| {
        const decl = self.declarations.items[rule.decl_index];
        try self.addSymbol(.{
            .source_range = proofSpanRange(app.rule_span),
            .target_range = if (rule.available) decl.name_range else null,
            .markdown = decl.markdown,
        });
        try self.indexArgBindings(app, rule.decl_index, rule.available);
    } else {
        try self.addSymbol(.{
            .source_range = proofSpanRange(app.rule_span),
            .target_range = null,
            .markdown = try unknownRuleMarkdown(
                self.allocator,
                app.rule_name,
            ),
        });
        try self.indexUnknownArgBindings(app);
    }

    try self.indexRuleApplicationMath(block_index, app);

    for (app.refs) |ref| {
        switch (ref) {
            .hyp => |hyp| try self.addHypRef(block_index, hyp),
            .line => |line| try self.addLineRef(block_index, line, line_start),
            .application => |child| {
                try self.indexRuleApplication(block_index, child, line_start);
            },
        }
    }
}

pub fn indexArgBindings(
    self: anytype,
    app: proof_script.RuleApplication,
    decl_index: usize,
    rule_available: bool,
) !void {
    const decl = self.declarations.items[decl_index];
    for (app.arg_bindings) |binding| {
        const binder = findBinder(decl, binding.name) orelse {
            try self.addSymbol(.{
                .source_range = proofSpanRange(binding.name_span),
                .target_range = null,
                .markdown = try unknownBindingMarkdown(
                    self.allocator,
                    binding.name,
                    decl.name,
                ),
            });
            continue;
        };
        try self.addSymbol(.{
            .source_range = proofSpanRange(binding.name_span),
            .target_range = if (rule_available)
                binder.range orelse decl.name_range
            else
                null,
            .markdown = try binderMarkdown(
                self.allocator,
                decl,
                binder,
            ),
        });
    }
}

pub fn indexUnknownArgBindings(
    self: anytype,
    app: proof_script.RuleApplication,
) !void {
    for (app.arg_bindings) |binding| {
        try self.addSymbol(.{
            .source_range = proofSpanRange(binding.name_span),
            .target_range = null,
            .markdown = try unresolvedBindingMarkdown(
                self.allocator,
                binding.name,
                app.rule_name,
            ),
        });
    }
}

pub fn addHypRef(
    self: anytype,
    block_index: usize,
    hyp: proof_script.HypRef,
) !void {
    const block = self.proof_blocks.items[block_index];
    if (hyp.index == 0 or
        (block.hyp_count_known and hyp.index > block.hyp_count))
    {
        try self.addSymbol(.{
            .source_range = proofSpanRange(hyp.span),
            .target_range = null,
            .markdown = try unknownHypMarkdown(
                self.allocator,
                block.name,
                hyp.index,
            ),
        });
        return;
    }
    const decl_index = block.decl_index orelse {
        try self.addSymbol(.{
            .source_range = proofSpanRange(hyp.span),
            .target_range = null,
            .markdown = try unknownHypMarkdown(
                self.allocator,
                block.name,
                hyp.index,
            ),
        });
        return;
    };
    const decl = self.declarations.items[decl_index];
    const hyp_decl = if (hyp.index <= decl.hypotheses.len)
        decl.hypotheses[hyp.index - 1]
    else
        null;
    try self.addSymbol(.{
        .source_range = proofSpanRange(hyp.span),
        .target_range = if (hyp_decl) |item| item.range else decl.name_range,
        .markdown = try hypRefMarkdown(
            self.allocator,
            block.name,
            hyp.index,
            block.hyp_count,
            block.hyp_count_known,
            if (hyp_decl) |item| item.text else null,
        ),
    });
}

pub fn addLineRef(
    self: anytype,
    block_index: usize,
    ref: proof_script.LineRef,
    line_start: usize,
) !void {
    const decl_index = self.resolveLine(block_index, ref.label, line_start) orelse {
        try self.addSymbol(.{
            .source_range = proofSpanRange(ref.span),
            .target_range = null,
            .markdown = try unknownLineMarkdown(self.allocator, ref.label),
        });
        return;
    };
    const decl = self.declarations.items[decl_index];
    try self.addSymbol(.{
        .source_range = proofSpanRange(ref.span),
        .target_range = decl.name_range,
        .markdown = decl.markdown,
    });
}

pub fn resolveRule(
    self: anytype,
    block_index: usize,
    name: []const u8,
    use_start: usize,
) ?RuleResolution {
    var best: ?ProofRuleDecl = null;
    for (self.proof_rules.items) |rule| {
        if (!std.mem.eql(u8, rule.name, name)) continue;
        if (rule.available_start > use_start) continue;
        if (best == null or rule.available_start > best.?.available_start) {
            best = rule;
        }
    }
    if (best) |rule| {
        return .{ .decl_index = rule.decl_index, .available = true };
    }
    return self.globalRuleResolution(block_index, name);
}

pub fn globalRuleResolution(
    self: anytype,
    block_index: usize,
    name: []const u8,
) ?RuleResolution {
    const decl_index = self.decl_by_name.get(name) orelse return null;
    const decl = self.declarations.items[decl_index];
    switch (decl.kind) {
        .axiom, .theorem => {},
        else => return null,
    }
    const bound = self.proof_blocks.items[block_index].global_available_before;
    const available = if (bound) |before|
        decl.name_range.start < before
    else
        true;
    return .{ .decl_index = decl_index, .available = available };
}

pub fn sortNameForId(self: anytype, id: u7) ?[]const u8 {
    const idx: usize = id;
    if (idx >= self.sort_names.items.len) return null;
    return self.sort_names.items[idx];
}

pub fn theoremDeclIndex(self: anytype, name: []const u8) ?usize {
    const decl_index = self.decl_by_name.get(name) orelse return null;
    const decl = self.declarations.items[decl_index];
    if (decl.kind != .theorem) return null;
    return decl_index;
}

pub fn sortDeclIndex(self: anytype, name: []const u8) ?usize {
    const decl_index = self.decl_by_name.get(name) orelse return null;
    const decl = self.declarations.items[decl_index];
    if (decl.kind != .sort) return null;
    return decl_index;
}

pub fn resolveLine(
    self: anytype,
    block_index: usize,
    label: []const u8,
    line_start: usize,
) ?usize {
    var best: ?ProofLineDecl = null;
    for (self.proof_lines.items) |line| {
        if (line.block_index != block_index) continue;
        if (!std.mem.eql(u8, line.name, label)) continue;
        if (line.line_start >= line_start) continue;
        if (best == null or line.line_start > best.?.line_start) {
            best = line;
        }
    }
    if (best) |line| return line.decl_index;
    return null;
}
