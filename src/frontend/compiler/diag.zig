const Span = @import("../proof_script.zig").Span;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const DiagScratch = @import("../diag_scratch.zig");

pub const DiagnosticKind = enum {
    generic,
    missing_proof_block,
    extra_proof_block,
    theorem_name_mismatch,
    duplicate_rule_name,
    parse_assertion,
    parse_binding,
    parse_fresh,
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

pub const Scratch = DiagScratch.Scratch;
pub const MissingCongruenceReason = DiagScratch.MissingCongruenceReason;

pub const MissingCongruenceRuleDetail = struct {
    reason: MissingCongruenceReason,
    term_name: ?[]const u8 = null,
    sort_name: ?[]const u8 = null,
    arg_index: ?usize = null,
};

pub const DiagnosticDetail = union(enum) {
    none,
    unknown_math_token: struct {
        token: []const u8,
    },
    missing_binder_assignment: struct {
        binder_name: []const u8,
    },
    missing_congruence_rule: MissingCongruenceRuleDetail,
    hypothesis_ref: struct {
        index: usize,
    },
};

pub const DiagnosticSource = enum {
    mm0,
    proof,
};

pub const Diagnostic = struct {
    kind: DiagnosticKind,
    err: anyerror,
    source: DiagnosticSource = .mm0,
    theorem_name: ?[]const u8 = null,
    block_name: ?[]const u8 = null,
    line_label: ?[]const u8 = null,
    rule_name: ?[]const u8 = null,
    name: ?[]const u8 = null,
    expected_name: ?[]const u8 = null,
    span: ?Span = null,
    detail: DiagnosticDetail = .none,
};

pub fn diagnosticSummary(diag: Diagnostic) []const u8 {
    return switch (diag.kind) {
        .generic => compilerErrorSummary(diag.err),
        .missing_proof_block => "missing proof block for theorem",
        .extra_proof_block => "extra proof block with no matching theorem",
        .theorem_name_mismatch => "proof block name does not match the theorem",
        .duplicate_rule_name => "duplicate rule name",
        .parse_assertion => "could not parse proof line assertion",
        .parse_binding => "could not parse binder assignment",
        .parse_fresh => compilerErrorSummary(diag.err),
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
        error.UnifyMismatch,
        error.TermMismatch,
        error.ExpectedTermApp,
        error.UnifyStackNotEmpty,
        error.HypCountMismatch,
        => "could not infer omitted rule arguments from the line and refs",
        error.AmbiguousAcuiMatch => "omitted rule arguments are ambiguous after structural " ++
            "or def-aware matching",
        error.UnknownTheoremVariable => "binding refers to a theorem variable that is not in scope",
        error.DuplicateRuleName => "duplicate rule name",
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
        error.RecoverHoleNotFound => "@recover could not find the hole binder in the pattern expr",
        error.RecoverConflict => "@recover found inconsistent candidates for the target " ++
            "binder",
        error.RecoverStructureMismatch => "@recover source expr does not match the pattern structure",
        error.AbstractWithoutView => "@abstract requires a preceding @view on the same rule",
        error.InvalidAbstractAnnotation => "@abstract expects six binder names: target left " ++
            "right hole left_plug right_plug",
        error.UnknownAbstractBinder => "@abstract refers to a binder name not present in the view",
        error.AbstractTargetNotRuleBinder => "@abstract target must be a real rule binder",
        error.AbstractHoleSortMismatch => "@abstract target and hole binders must have the same sort",
        error.AbstractPlugSortMismatch => "@abstract hole and plug binders must have the same sort",
        error.AbstractNoPlugOccurrence => "@abstract could not find the plug pair in the source exprs",
        error.AbstractConflict => "@abstract found a context that conflicts with the target binder",
        error.AbstractStructureMismatch => "@abstract source exprs do not match outside the plug pair",
        error.UnknownTermAnnotation => "unknown term-level annotation",
        error.DummyAnnotationRemoved => "@dummy was removed; use @fresh instead",
        error.InvalidFreshAnnotation => "@fresh expects exactly one real rule binder name",
        error.UnknownFreshBinder => "@fresh target must be a real rule binder",
        error.DuplicateFreshBinder => "multiple @fresh annotations were attached to one rule binder",
        error.FreshRequiresBoundBinder => "@fresh target must be a bound rule binder",
        error.FreshStrictSort => "@fresh cannot target a binder in a strict sort",
        error.FreshFreeSort => "@fresh cannot target a binder in a free sort",
        error.FreshNoAvailableVar => "@fresh could not find an available @vars token",
        error.HiddenWitnessNoAvailableVar =>
            "hidden def witness needed a fresh @vars token, but none was " ++
            "available",
        error.InvalidVarsAnnotation => "@vars expects one or more raw math tokens",
        error.VarsStrictSort => "@vars cannot be used on a strict sort",
        error.VarsFreeSort => "@vars cannot be used on a free sort",
        error.DuplicateVarsToken => "duplicate @vars token across sorts",
        error.VarsTokenCollision => "@vars token collides with an existing term, notation, " ++
            "or formula marker",
        error.DependencySlotExhausted => "theorem exceeded the 55 tracked bound-variable dependency slots",
        error.UnresolvedDummyWitness => "matched rule through hidden def structure, but omitted " ++
            "binders contain unresolved hidden-dummy witnesses",
        error.MissingCongruenceRule => "missing congruence rule needed for normalization",
        else => @errorName(err),
    };
}

pub fn writeMissingCongruenceRuleSummary(
    writer: anytype,
    info: MissingCongruenceRuleDetail,
) !void {
    switch (info.reason) {
        .missing_rule => {
            if (info.term_name) |term_name| {
                try writer.print(
                    "missing @congr for term {s}",
                    .{term_name},
                );
            } else {
                try writer.writeAll("missing @congr rule");
            }
        },
        .changed_bound_arg => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try writer.print(
                        "bound argument {d} of term {s} changed " ++
                            "during normalization",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try writer.print(
                        "bound argument {d} changed during normalization",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(
                    "bound argument changed during normalization",
                );
            }
        },
        .missing_child_relation => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try writer.print(
                        "missing relation for argument {d} of term {s}",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try writer.print(
                        "missing relation for argument {d}",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll("missing child relation");
            }
        },
        .missing_child_proof => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try writer.print(
                        "argument {d} of term {s} changed without " ++
                            "a congruence proof",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try writer.print(
                        "argument {d} changed without a congruence proof",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(
                    "argument changed without a congruence proof",
                );
            }
        },
        .missing_parent_relation => {
            if (info.term_name) |term_name| {
                try writer.print(
                    "missing parent relation for term {s}",
                    .{term_name},
                );
            } else {
                try writer.writeAll("missing parent relation");
            }
        },
        .malformed_rule => {
            if (info.term_name) |term_name| {
                try writer.print(
                    "malformed @congr rule for term {s}",
                    .{term_name},
                );
            } else {
                try writer.writeAll("malformed @congr rule");
            }
        },
        .unknown_term => {
            try writer.writeAll("normalization used an unknown term");
        },
    }
}

pub fn buildCapturedDiagnosticDetail(
    env: *const GlobalEnv,
    detail: DiagScratch.CapturedDetail,
) DiagnosticDetail {
    return switch (detail) {
        .missing_congruence_rule => |info| .{
            .missing_congruence_rule = .{
                .reason = info.reason,
                .term_name = if (info.term_id) |term_id|
                    if (term_id < env.terms.items.len)
                        env.terms.items[term_id].name
                    else
                        null
                else
                    null,
                .sort_name = info.sort_name,
                .arg_index = info.arg_index,
            },
        },
    };
}

pub fn takeScratchDetail(
    scratch: *Scratch,
    mark: Scratch.Mark,
    env: *const GlobalEnv,
    err: anyerror,
) ?DiagnosticDetail {
    const detail = scratch.takeSince(mark, err) orelse return null;
    return buildCapturedDiagnosticDetail(env, detail);
}
