pub const DocumentId = enum {
    mm0,
    proof,
};

pub const SnapshotInput = struct {
    mm0_uri: []const u8,
    mm0_text: []const u8,
    proof_uri: ?[]const u8 = null,
    proof_text: ?[]const u8 = null,
};

pub const SourceRange = struct {
    document: DocumentId,
    start: usize,
    end: usize,
};

pub const DefinitionResult = struct {
    uri: []const u8,
    range: SourceRange,
    selection_range: SourceRange,
};

pub const HoverResult = struct {
    range: SourceRange,
    markdown: []const u8,
};

pub const CompletionOptions = struct {
    snippet_support: bool = false,
};

pub const CompletionKind = enum {
    keyword,
    modifier,
    sort,
    term,
    def,
    axiom,
    theorem,
    lemma,
    proof_line,
    hypothesis,
    binder,
    annotation,
    notation,
    snippet,
};

pub const CompletionItem = struct {
    label: []const u8,
    kind: CompletionKind,
    detail: []const u8,
    documentation_markdown: ?[]const u8 = null,
    replacement: SourceRange,
    replacement_text: []const u8,
    snippet_replacement_text: ?[]const u8 = null,
    filter_text: ?[]const u8 = null,
    sort_text: []const u8,
};

pub const OutlineSymbol = struct {
    name: []const u8,
    kind: DeclarationKind,
    range: SourceRange,
    selection_range: SourceRange,
    children: []const OutlineSymbol = &.{},
};

pub const DeclarationKind = enum {
    sort,
    term,
    def,
    axiom,
    theorem,
    lemma,
    proof_line,
    sort_var,

    pub fn label(self: DeclarationKind) []const u8 {
        return switch (self) {
            .sort => "sort",
            .term => "term",
            .def => "def",
            .axiom => "axiom",
            .theorem => "theorem",
            .lemma => "lemma",
            .proof_line => "proof line",
            .sort_var => "@vars token",
        };
    }
};

pub const BinderDecl = struct {
    name: []const u8,
    sort_name: []const u8,
    bound: bool,
    range: ?SourceRange = null,
    sort_text: []const u8 = "",
};

pub const HypothesisDecl = struct {
    text: []const u8,
    range: SourceRange,
};

pub const Declaration = struct {
    name: []const u8,
    kind: DeclarationKind,
    name_range: SourceRange,
    markdown: []const u8,
    binders: []const BinderDecl = &.{},
    completion_args: []const BinderDecl = &.{},
    sort_text: []const u8 = "",
    hyp_count: usize = 0,
    hypotheses: []const HypothesisDecl = &.{},
};
