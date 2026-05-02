const proof_script = @import("../proof_script.zig");
const Types = @import("types.zig");

pub const SourceRange = Types.SourceRange;
pub const Declaration = Types.Declaration;

pub const LookupHit = struct {
    source_range: SourceRange,
    target_range: ?SourceRange,
    markdown: []const u8,
};

pub const NavigationSymbol = struct {
    source_range: SourceRange,
    target_range: ?SourceRange,
    markdown: []const u8,
};

pub const ProofBlockInfo = struct {
    kind: proof_script.BlockKind,
    name: []const u8,
    name_range: SourceRange,
    span: SourceRange,
    global_available_before: ?usize = null,
    decl_index: ?usize = null,
    hyp_count: usize = 0,
    hyp_count_known: bool = false,
};

pub const ProofRuleDecl = struct {
    name: []const u8,
    decl_index: usize,
    available_start: usize,
    sort_text: []const u8,
};

pub const ProofLineDecl = struct {
    name: []const u8,
    decl_index: usize,
    block_index: usize,
    line_start: usize,
    sort_text: []const u8,
};

pub const ProofApplicationInfo = struct {
    block_index: usize,
    rule_name: []const u8,
    rule_span: SourceRange,
    binding_list_span: ?SourceRange = null,
    refs_span: ?SourceRange = null,
    span: SourceRange,
    use_start: usize,
    line_start: usize,
};

pub const RuleResolution = struct {
    decl_index: usize,
    available: bool,
};
