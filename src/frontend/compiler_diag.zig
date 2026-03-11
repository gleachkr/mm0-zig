const Span = @import("./proof_script.zig").Span;

pub const DiagnosticKind = enum {
    generic,
    missing_proof_block,
    extra_proof_block,
    theorem_name_mismatch,
    parse_assertion,
    parse_binding,
    inference_failed,
    unknown_rule,
    unknown_binder_name,
    duplicate_binder_assignment,
    missing_binder_assignment,
    ref_count_mismatch,
    unknown_hypothesis_ref,
    unknown_label,
    hypothesis_mismatch,
    conclusion_mismatch,
    duplicate_label,
    empty_proof_block,
    final_line_mismatch,
};

pub const Diagnostic = struct {
    kind: DiagnosticKind,
    err: anyerror,
    theorem_name: ?[]const u8 = null,
    block_name: ?[]const u8 = null,
    line_label: ?[]const u8 = null,
    rule_name: ?[]const u8 = null,
    name: ?[]const u8 = null,
    expected_name: ?[]const u8 = null,
    span: ?Span = null,
};

pub fn diagnosticSummary(diag: Diagnostic) []const u8 {
    return switch (diag.kind) {
        .generic => compilerErrorSummary(diag.err),
        .missing_proof_block => "missing proof block for theorem",
        .extra_proof_block => "extra proof block with no matching theorem",
        .theorem_name_mismatch => "proof block name does not match the theorem",
        .parse_assertion => "could not parse proof line assertion",
        .parse_binding => "could not parse binder assignment",
        .inference_failed => compilerErrorSummary(diag.err),
        .unknown_rule => "unknown rule in proof line",
        .unknown_binder_name => "unknown binder name in rule application",
        .duplicate_binder_assignment => "duplicate binder assignment in rule application",
        .missing_binder_assignment => "missing binder assignment in rule application",
        .ref_count_mismatch => "wrong number of references for rule application",
        .unknown_hypothesis_ref => "unknown theorem hypothesis reference",
        .unknown_label => "unknown proof line label",
        .hypothesis_mismatch => "rule reference does not match the expected hypothesis",
        .conclusion_mismatch => "proof line assertion does not match the rule conclusion",
        .duplicate_label => "duplicate proof line label",
        .empty_proof_block => "proof block is empty",
        .final_line_mismatch => "last proof line does not prove the theorem conclusion",
    };
}

fn compilerErrorSummary(err: anyerror) []const u8 {
    return switch (err) {
        error.BoundnessMismatch => "binding does not satisfy the rule's " ++
            "bound-variable constraint",
        error.SortMismatch => "binding does not satisfy the rule's sort constraint",
        error.UnifyMismatch, error.TermMismatch, error.ExpectedTermApp, error.UnifyStackNotEmpty, error.HypCountMismatch => "could not infer omitted rule arguments from the line and refs",
        error.DuplicateViewAnnotation => "multiple @view annotations were attached to one rule",
        error.InvalidViewAnnotation => "could not parse @view annotation",
        error.ViewHypCountMismatch => "@view hypothesis count does not match the rule",
        error.ViewConclusionMismatch => "@view conclusion does not match the proof line assertion",
        error.ViewHypothesisMismatch => "@view hypotheses do not match the cited refs",
        error.ViewBindingConflict => "@view inference conflicts with an explicit binding",
        error.RecoverWithoutView => "@recover requires a preceding @view on the same rule",
        error.InvalidRecoverAnnotation => "@recover expects four binder names: target source " ++
            "pattern hole",
        error.UnknownRecoverBinder => "@recover refers to a binder name not present in the view",
        error.RecoverTargetNotRuleBinder => "@recover target must be a real rule binder",
        error.RecoverSortMismatch => "@recover target and hole binders must have the same sort",
        error.RecoverSourceUnsolved => "@recover source binder was not solved by the view",
        error.RecoverPatternUnsolved => "@recover pattern binder was not solved by the view",
        error.RecoverHoleUnsolved => "@recover hole binder was not solved by the view",
        error.RecoverHoleNotFound => "@recover could not find the hole binder in the pattern expr",
        error.RecoverConflict => "@recover found inconsistent candidates for the target " ++
            "binder",
        error.RecoverStructureMismatch => "@recover source expr does not match the pattern structure",
        else => @errorName(err),
    };
}
