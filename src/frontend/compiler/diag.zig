const std = @import("std");
const Span = @import("../proof_script.zig").Span;
const ProofScriptParser = @import("../proof_script.zig").Parser;
const ProofLine = @import("../proof_script.zig").ProofLine;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const DiagScratch = @import("../diag_scratch.zig");
const MathParseError = @import("../../trusted/parse.zig").MathParseError;
const MathSpan = @import("../../trusted/parse.zig").MathSpan;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const MM0Stmt = @import("../../trusted/parse.zig").MM0Stmt;

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

pub const DiagnosticSeverity = enum {
    @"error",
    warning,
};

pub const Diagnostic = struct {
    severity: DiagnosticSeverity = .@"error",
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

pub fn setIfMissing(self: anytype, diag: Diagnostic) void {
    if (self.last_diagnostic != null) return;
    self.setDiagnostic(diag);
}

pub fn setProof(self: anytype, diag: Diagnostic) void {
    var proof_diag = diag;
    proof_diag.source = .proof;
    self.setDiagnostic(proof_diag);
}

pub fn maybeSetProof(self: anytype, diag: Diagnostic) void {
    const T = @TypeOf(self);
    switch (@typeInfo(T)) {
        .pointer => |ptr| {
            if (@hasDecl(ptr.child, "setDiagnostic")) {
                setProof(self, diag);
            }
        },
        .@"struct" => {
            if (@hasDecl(T, "setDiagnostic")) {
                setProof(self, diag);
            }
        },
        else => {},
    }
}

pub fn mathSpanToSpan(span: MathSpan) Span {
    return .{ .start = span.start, .end = span.end };
}

pub fn mathSpanToSpanOpt(span: ?MathSpan) ?Span {
    return if (span) |value| mathSpanToSpan(value) else null;
}

pub fn mm0ParserDiagnostic(
    parser: *const MM0Parser,
    err: anyerror,
) Diagnostic {
    const diag = Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .mm0,
        .name = parser.diagnosticName(),
        .span = mathSpanToSpanOpt(parser.diagnosticSpan()),
    };
    return mathErrorDiagnostic(diag, err, parser.last_math_error);
}

pub fn mm0StatementDiagnostic(
    parser: *const MM0Parser,
    stmt: MM0Stmt,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .mm0,
        .name = mm0StmtName(stmt),
        .span = annotationDiagnosticSpan(parser, stmt, err) orelse
            mm0StmtNameSpan(stmt),
    };
}

pub fn proofParserDiagnostic(
    proofs: *const ProofScriptParser,
    fallback_theorem_name: ?[]const u8,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .theorem_name = proofs.diagnosticBlockName() orelse
            fallback_theorem_name,
        .block_name = proofs.diagnosticBlockName(),
        .span = proofs.diagnosticSpan(),
    };
}

pub fn extraProofBlockDiagnostic(
    block_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .extra_proof_block,
        .err = error.ExtraProofBlock,
        .source = .proof,
        .block_name = block_name,
        .span = span,
    };
}

pub fn missingProofBlockDiagnostic(
    theorem_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .missing_proof_block,
        .err = error.MissingProofBlock,
        .source = .mm0,
        .theorem_name = theorem_name,
        .span = span,
    };
}

pub fn theoremNameMismatchDiagnostic(
    theorem_name: []const u8,
    block_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .theorem_name_mismatch,
        .err = error.TheoremNameMismatch,
        .source = .proof,
        .theorem_name = theorem_name,
        .block_name = block_name,
        .expected_name = theorem_name,
        .span = span,
    };
}

pub fn duplicateRuleNameDiagnostic(
    name: []const u8,
    span: ?Span,
    source: DiagnosticSource,
) Diagnostic {
    return .{
        .kind = .duplicate_rule_name,
        .err = error.DuplicateRuleName,
        .source = source,
        .name = name,
        .span = span,
    };
}

pub fn theoremDiagnostic(
    theorem_name: []const u8,
    span: Span,
    source: DiagnosticSource,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = source,
        .theorem_name = theorem_name,
        .span = span,
    };
}

pub fn proofBlockDiagnostic(
    block_name: []const u8,
    span: Span,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .theorem_name = block_name,
        .block_name = block_name,
        .span = span,
    };
}

pub fn proofMathTokenSpan(math_span: Span, token_span: MathSpan) Span {
    const inner_start = math_span.start + 1;
    return .{
        .start = inner_start + token_span.start,
        .end = inner_start + token_span.end,
    };
}

pub fn proofMathParseDiagnostic(
    parser: *MM0Parser,
    kind: DiagnosticKind,
    err: anyerror,
    theorem_name: []const u8,
    line_label: []const u8,
    rule_name: []const u8,
    name: ?[]const u8,
    math_span: Span,
) Diagnostic {
    const diag = Diagnostic{
        .kind = kind,
        .err = err,
        .source = .proof,
        .theorem_name = theorem_name,
        .line_label = line_label,
        .rule_name = rule_name,
        .name = name,
        .span = math_span,
    };
    const math_err = parser.last_math_error orelse return diag;
    return proofMathErrorDiagnostic(diag, math_err, math_span);
}

pub fn proofBindingDiagnosticSpan(
    line: ProofLine,
    binder_name: ?[]const u8,
) Span {
    return line.bindingSpan(binder_name) orelse line.ruleApplicationSpan();
}

pub fn setProofScratchDiagnosticIfPresent(
    self: anytype,
    scratch: *Scratch,
    mark: Scratch.Mark,
    env: *const GlobalEnv,
    kind: DiagnosticKind,
    err: anyerror,
    theorem_name: []const u8,
    line_label: ?[]const u8,
    rule_name: ?[]const u8,
    span: ?Span,
) bool {
    const detail = takeScratchDetail(
        scratch,
        mark,
        env,
        err,
    ) orelse {
        return false;
    };
    maybeSetProof(self, .{
        .kind = kind,
        .err = err,
        .theorem_name = theorem_name,
        .line_label = line_label,
        .rule_name = rule_name,
        .span = span,
        .detail = detail,
    });
    return true;
}

fn proofMathErrorDiagnostic(
    diag: Diagnostic,
    math_err: MathParseError,
    math_span: Span,
) Diagnostic {
    var result = mathErrorDiagnostic(diag, diag.err, math_err);
    switch (math_err) {
        .unknown_token, .unexpected_token => |token| {
            result.span = proofMathTokenSpan(math_span, token.span);
        },
        .unexpected_end => |pos| {
            const start = @min(math_span.start + pos, math_span.end);
            result.span = .{ .start = start, .end = start };
        },
    }
    return result;
}

fn mathErrorDiagnostic(
    diag: Diagnostic,
    err: anyerror,
    math_err: ?MathParseError,
) Diagnostic {
    if (err != error.UnknownMathToken) return diag;
    const actual = math_err orelse return diag;

    var result = diag;
    switch (actual) {
        .unknown_token => |token| {
            result.detail = .{
                .unknown_math_token = .{
                    .token = token.text,
                },
            };
        },
        .unexpected_token,
        .unexpected_end,
        => {},
    }
    return result;
}

fn mm0StmtName(stmt: MM0Stmt) ?[]const u8 {
    return switch (stmt) {
        .sort => |sort_stmt| sort_stmt.name,
        .term => |term_stmt| term_stmt.name,
        .assertion => |assertion| assertion.name,
    };
}

fn mm0StmtNameSpan(stmt: MM0Stmt) Span {
    return switch (stmt) {
        .sort => |sort_stmt| mathSpanToSpan(sort_stmt.name_span),
        .term => |term_stmt| mathSpanToSpan(term_stmt.name_span),
        .assertion => |assertion| mathSpanToSpan(assertion.name_span),
    };
}

fn firstAnnotationSpan(parser: *const MM0Parser) ?Span {
    if (parser.last_annotation_spans.len == 0) return null;
    return mathSpanToSpan(parser.last_annotation_spans[0]);
}

fn annotationDirective(ann: []const u8) ?[]const u8 {
    if (ann.len == 0 or ann[0] != '@') return null;

    var iter = std.mem.tokenizeAny(u8, ann, " \t\r\n");
    return iter.next();
}

fn unknownTermAnnotationSpan(parser: *const MM0Parser) ?Span {
    for (parser.last_annotations, parser.last_annotation_spans) |ann, span| {
        const directive = annotationDirective(ann) orelse continue;
        if (std.mem.eql(u8, directive, "@acui")) continue;
        return mathSpanToSpan(span);
    }
    return firstAnnotationSpan(parser);
}

fn annotationDiagnosticSpan(
    parser: *const MM0Parser,
    stmt: MM0Stmt,
    err: anyerror,
) ?Span {
    return switch (err) {
        error.UnknownTermAnnotation => switch (stmt) {
            .term => unknownTermAnnotationSpan(parser),
            else => firstAnnotationSpan(parser),
        },
        error.DummyAnnotationRemoved,
        error.InvalidFreshAnnotation,
        error.InvalidFallbackAnnotation,
        error.DuplicateFallbackAnnotation,
        error.UnknownFallbackRule,
        error.UnknownFreshBinder,
        error.DuplicateFreshBinder,
        error.FreshRequiresBoundBinder,
        error.FreshStrictSort,
        error.FreshFreeSort,
        error.FreshNoAvailableVar,
        error.HiddenWitnessNoAvailableVar,
        error.DuplicateViewAnnotation,
        error.InvalidViewAnnotation,
        error.ViewHypCountMismatch,
        error.RecoverWithoutView,
        error.InvalidRecoverAnnotation,
        error.UnknownRecoverBinder,
        error.RecoverTargetNotRuleBinder,
        error.RecoverSortMismatch,
        error.AbstractWithoutView,
        error.InvalidAbstractAnnotation,
        error.UnknownAbstractBinder,
        error.AbstractTargetNotRuleBinder,
        error.AbstractHoleSortMismatch,
        error.AbstractPlugSortMismatch,
        error.InvalidVarsAnnotation,
        error.VarsStrictSort,
        error.VarsFreeSort,
        error.DuplicateVarsToken,
        error.VarsTokenCollision,
        => firstAnnotationSpan(parser),
        else => null,
    };
}

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
        // Legacy public error name. The repaired structural solver uses
        // this for ambiguity across AU, ACU, AUI, and ACUI matching.
        error.AmbiguousAcuiMatch => "omitted rule arguments remain ambiguous after structural " ++
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
        error.InvalidFallbackAnnotation => "@fallback expects exactly one rule name",
        error.DuplicateFallbackAnnotation => "multiple @fallback annotations were attached to one rule",
        error.UnknownFallbackRule => "@fallback refers to a rule that is not available here",
        error.FallbackCycle => "@fallback chain contains a cycle",
        error.UnknownFreshBinder => "@fresh target must be a real rule binder",
        error.DuplicateFreshBinder => "multiple @fresh annotations were attached to one rule binder",
        error.FreshRequiresBoundBinder => "@fresh target must be a bound rule binder",
        error.FreshStrictSort => "@fresh cannot target a binder in a strict sort",
        error.FreshFreeSort => "@fresh cannot target a binder in a free sort",
        error.FreshNoAvailableVar => "@fresh could not find an available @vars token",
        error.HiddenWitnessNoAvailableVar => "hidden def witness needed a fresh @vars token, but none was " ++
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
        error.ExpectedIdentifier,
        error.ExpectedIdent,
        => "expected identifier",
        error.ExpectedNumber => "expected number",
        error.UnknownMathToken => "unknown token in math string",
        error.ExpectedMathToken => "expected token in math string",
        error.ExpectedCloseParen => "expected closing parenthesis in math string",
        error.TrailingMathTokens => "unexpected trailing tokens in math string",
        error.NotationMismatch => "token sequence does not match declared notation",
        error.PrecMismatch => "operator precedence does not allow this parse",
        error.NotProvable => "math string does not have a provable sort",
        error.ExpectedMathString,
        error.ExpectedMathStr,
        => "expected $...$ math string",
        error.ExpectedKeyword => "expected keyword",
        error.ExpectedString => "expected quoted string",
        error.UnknownTerm => "unknown term",
        error.UnknownSort => "unknown sort",
        error.UnknownVariable => "unknown variable",
        error.UnexpectedKeyword => "unexpected keyword",
        error.UnexpectedCharacter,
        error.UnexpectedChar,
        => "unexpected character",
        error.ExpectedLineEnd => "expected end of line",
        error.UnterminatedMathString,
        error.UnterminatedMathStr,
        => "unterminated $...$ math string",
        error.UnterminatedString => "unterminated string",
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
