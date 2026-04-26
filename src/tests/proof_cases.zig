const std = @import("std");
const mm0 = @import("../lib.zig");

const Compiler = mm0.Compiler;
const Mmb = mm0.Mmb;

const ProofCaseOutcome = union(enum) {
    pass,
    fail: anyerror,
    // Expected-failure cases for known frontend bugs.
    known_fail,
    // Explicitly unsupported cases whose semantics need a broader design.
    unsupported,
};

const ProofCase = struct {
    stem: []const u8,
    outcome: ProofCaseOutcome,
};

const ProofCaseMetadata = struct {
    stem: []const u8,
    reason: []const u8,
};

const known_proof_case_failures = [_]ProofCaseMetadata{};

const unsupported_proof_cases = [_]ProofCaseMetadata{
    .{
        .stem = "unsupported_def_unfold_then_rewrite_concl",
        .reason = "requires inventing an erased hidden def witness after " ++
            "unfold then rewrite; treating that as out of scope",
    },
};

fn lookupProofCaseReason(
    entries: []const ProofCaseMetadata,
    stem: []const u8,
) ?[]const u8 {
    for (entries) |entry| {
        if (std.mem.eql(u8, entry.stem, stem)) return entry.reason;
    }
    return null;
}

fn knownFailReason(stem: []const u8) ?[]const u8 {
    return lookupProofCaseReason(&known_proof_case_failures, stem);
}

fn unsupportedReason(stem: []const u8) ?[]const u8 {
    return lookupProofCaseReason(&unsupported_proof_cases, stem);
}

const proof_case_ext = "auf";

const proof_cases = [_]ProofCase{
    .{ .stem = "pass_keep", .outcome = .pass },
    .{ .stem = "pass_label", .outcome = .pass },
    .{ .stem = "pass_gen", .outcome = .pass },
    .{ .stem = "pass_dup", .outcome = .pass },
    .{ .stem = "pass_def", .outcome = .pass },
    .{ .stem = "pass_def_dummy", .outcome = .pass },
    .{ .stem = "pass_def_transport", .outcome = .pass },
    .{ .stem = "pass_def_unfold_line", .outcome = .pass },
    .{ .stem = "pass_def_unfold_ref", .outcome = .pass },
    .{ .stem = "pass_def_unfold_final", .outcome = .pass },
    .{ .stem = "pass_def_unfold_final_reverse", .outcome = .pass },
    .{ .stem = "pass_def_unfold_dummy", .outcome = .pass },
    .{ .stem = "pass_def_view_basic", .outcome = .pass },
    .{ .stem = "pass_def_rewrite_concl", .outcome = .pass },
    .{ .stem = "pass_def_rewrite_hyp", .outcome = .pass },
    // Strict replay stays exact, but omitted binders can fall back to
    // shared targeted transparency when needed.
    .{ .stem = "pass_def_infer_expected", .outcome = .pass },
    .{ .stem = "pass_def_infer_actual", .outcome = .pass },
    .{ .stem = "pass_def_infer_hyp", .outcome = .pass },
    .{ .stem = "pass_def_infer_dummy", .outcome = .pass },
    .{ .stem = "pass_def_infer_user_side", .outcome = .pass },
    .{ .stem = "pass_def_infer_user_side_hyp", .outcome = .pass },
    .{ .stem = "pass_def_infer_user_side_final", .outcome = .pass },
    .{ .stem = "pass_def_all_elim_free_param", .outcome = .pass },
    .{ .stem = "pass_category_defs_direct", .outcome = .pass },
    .{ .stem = "pass_infer_normalized_conclusion", .outcome = .pass },
    .{ .stem = "pass_alleq_normalized_inference", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_explicit", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_infer", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_and_elim", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_auto", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_reorder", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_unfold", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_fold", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_all_elim_ctx_twostep", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_imp_elim_ctx_mixed", .outcome = .pass },
    .{
        .stem = "fail_verify_hidden_dummy_dep",
        .outcome = .{ .fail = error.DepViolation },
    },
    .{
        .stem = "fail_def_body_free_hidden_binder",
        .outcome = .{ .fail = error.DepViolation },
    },
    .{ .stem = "pass_def_acui_assoc", .outcome = .pass },
    .{
        .stem = "fail_def_unfold_then_rewrite",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{ .stem = "fail_nested_def_unfold_then_acui", .outcome = .pass },
    .{
        .stem = "unsupported_def_unfold_then_rewrite_concl",
        .outcome = .unsupported,
    },
    .{ .stem = "pass_alleq_transparent_inference", .outcome = .pass },
    .{ .stem = "pass_alleq_surface_inference", .outcome = .pass },
    .{ .stem = "unsupported_epi_comp", .outcome = .pass },
    .{ .stem = "pass_epi_cancel_right", .outcome = .pass },
    .{ .stem = "pass_epi_mono_cancel_right", .outcome = .pass },
    .{ .stem = "pass_epi_comp_assign", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_hyp", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_view", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_rewrite_view_auto", .outcome = .pass },
    .{
        .stem = "pass_def_unfold_then_rewrite_recover",
        .outcome = .pass,
    },
    .{ .stem = "pass_def_unfold_then_acui_concl", .outcome = .pass },
    .{ .stem = "pass_def_unfold_then_acui_hyp", .outcome = .pass },
    .{
        .stem = "pass_def_unfold_then_rewrite_abstract",
        .outcome = .pass,
    },
    .{
        .stem = "pass_def_unfold_then_rewrite_abstract_hyp",
        .outcome = .pass,
    },
    .{
        .stem = "pass_def_unfold_then_full_acui_concl",
        .outcome = .pass,
    },
    .{
        .stem = "pass_def_unfold_then_full_acui_hyp",
        .outcome = .pass,
    },
    .{
        .stem = "pass_def_unfold_then_full_acui_abstract",
        .outcome = .pass,
    },
    .{
        .stem = "pass_def_unfold_then_full_acui_abstract_hyp",
        .outcome = .pass,
    },
    .{ .stem = "pass_normalize", .outcome = .pass },
    .{ .stem = "pass_normalize_nested", .outcome = .pass },
    .{ .stem = "pass_normalize_identity", .outcome = .pass },
    .{ .stem = "pass_normalize_hyp", .outcome = .pass },
    .{ .stem = "pass_normalize_repeat_ref", .outcome = .pass },
    .{ .stem = "pass_normalize_noop", .outcome = .pass },
    .{ .stem = "pass_normalize_def_transport_concl", .outcome = .pass },
    .{ .stem = "hilbert", .outcome = .pass },
    .{ .stem = "hilbert_quant", .outcome = .pass },
    .{ .stem = "russell", .outcome = .pass },
    .{ .stem = "pass_view_basic", .outcome = .pass },
    .{ .stem = "pass_view_explicit", .outcome = .pass },
    .{ .stem = "pass_recover_basic", .outcome = .pass },
    .{ .stem = "pass_abstract_basic", .outcome = .pass },
    .{ .stem = "pass_abstract_repeated", .outcome = .pass },
    .{ .stem = "pass_abstract_view_phantoms", .outcome = .pass },
    .{ .stem = "pass_abstract_explicit_target", .outcome = .pass },
    .{ .stem = "pass_abstract_chain_recover", .outcome = .pass },
    .{ .stem = "pass_abstract_normalize", .outcome = .pass },
    .{ .stem = "pass_fresh_hole", .outcome = .pass },
    .{ .stem = "pass_fresh_explicit_override", .outcome = .pass },
    .{ .stem = "pass_fresh_reuse", .outcome = .pass },
    .{ .stem = "pass_holes", .outcome = .pass },
    .{ .stem = "pass_hole_fallback", .outcome = .pass },
    .{ .stem = "pass_hole_normalize", .outcome = .pass },
    .{ .stem = "pass_hole_view", .outcome = .pass },
    .{ .stem = "pass_hole_recover", .outcome = .pass },
    .{ .stem = "pass_hole_recover_ctx", .outcome = .pass },
    .{ .stem = "pass_hole_view_recover_explicit", .outcome = .pass },
    .{ .stem = "pass_hole_view_recover_matrix", .outcome = .pass },
    .{ .stem = "pass_hole_acui_min_ctx", .outcome = .pass },
    .{ .stem = "pass_hole_acui_disambiguate", .outcome = .pass },
    .{ .stem = "pass_hole_acui_ambiguous", .outcome = .pass },
    .{ .stem = "pass_hole_final_reconcile", .outcome = .pass },
    .{ .stem = "pass_hole_semantic_match", .outcome = .pass },
    .{ .stem = "pass_hole_under_binder", .outcome = .pass },
    .{ .stem = "pass_hole_under_binder_irrel", .outcome = .pass },
    .{ .stem = "pass_hole_abstract", .outcome = .pass },
    .{ .stem = "pass_hole_abstract_matrix", .outcome = .pass },
    .{ .stem = "pass_prawitz_holes", .outcome = .pass },
    .{
        .stem = "fail_hole_mm0_not_allowed",
        .outcome = .{ .fail = error.UnknownMathToken },
    },
    .{
        .stem = "fail_hole_unknown_sort",
        .outcome = .{ .fail = error.UnknownMathToken },
    },
    .{
        .stem = "fail_hole_sort_mismatch",
        .outcome = .{ .fail = error.HoleConclusionMismatch },
    },
    .{
        .stem = "fail_hole_structure_mismatch",
        .outcome = .{ .fail = error.HoleConclusionMismatch },
    },
    .{
        .stem = "fail_hole_missing_binder",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_hole_fresh_postfill",
        .outcome = .{ .fail = error.FreshNoAvailableVar },
    },
    .{
        .stem = "fail_hole_bound_arg",
        .outcome = .{ .fail = error.BoundnessMismatch },
    },
    .{
        .stem = "fail_hole_under_binder_sort_mismatch",
        .outcome = .{ .fail = error.SortMismatch },
    },
    .{
        .stem = "fail_hole_underdetermined_ctx",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_hole_underdetermined_multi_ctx",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_hole_underdetermined_wff",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_hole_view_recover_missing_t",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_hole_view_recover_ctx_missing_t",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_hole_abstract_hidden_target",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{
        .stem = "fail_hole_fallback_first_diag",
        .outcome = .{ .fail = error.HoleConclusionMismatch },
    },
    .{ .stem = "tseitin", .outcome = .pass },
    .{ .stem = "robinson", .outcome = .pass },
    .{ .stem = "aristotle", .outcome = .pass },
    .{ .stem = "peirce", .outcome = .pass },
    .{ .stem = "gentzen", .outcome = .pass },
    .{ .stem = "pass_alpha_freshen", .outcome = .pass },
    .{
        .stem = "fail_alpha_freshen_opaque_theorem_arg",
        .outcome = .{ .fail = error.AlphaRewriteSearchFailed },
    },
    .{
        .stem = "fail_hole_alpha_freshen_opaque",
        .outcome = .{ .fail = error.AlphaRewriteSearchFailed },
    },
    .{ .stem = "leibniz", .outcome = .pass },
    .{ .stem = "smullyan", .outcome = .pass },
    .{ .stem = "mac_lane", .outcome = .pass },
    .{ .stem = "pass_mac_lane_holes", .outcome = .pass },
    .{ .stem = "mac_lane_unfold", .outcome = .pass },
    .{ .stem = "mac_lane_unfold_2", .outcome = .pass },
    .{ .stem = "mac_lane_unfold_3", .outcome = .pass },
    .{ .stem = "mac_lane_unfold_4", .outcome = .pass },
    .{ .stem = "pass_acui_remainder_overlap", .outcome = .pass },
    .{ .stem = "pass_acui_order_independent_overlap", .outcome = .pass },
    .{ .stem = "pass_acui_repeated_explicit_item", .outcome = .pass },
    .{ .stem = "pass_acui_duplicate_binders_same_item", .outcome = .pass },
    .{ .stem = "pass_acui_repeated_joint_binder", .outcome = .pass },
    .{ .stem = "pass_acui_principal_remainder", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_absorb", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_absorb_commuted", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_duplicate_def", .outcome = .pass },
    .{ .stem = "pass_acui_same_side_absorb_infer", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_absorb", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_cancel", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_cancel_then_absorb", .outcome = .pass },
    .{ .stem = "pass_acui_cross_side_structural_def_leftover", .outcome = .pass },
    .{ .stem = "pass_acui_fragment_baseline", .outcome = .pass },
    .{ .stem = "pass_au_category", .outcome = .pass },
    .{
        .stem = "fail_au_right_unit_unsupported",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{ .stem = "pass_au_right_unit_direct", .outcome = .pass },
    .{ .stem = "pass_au_right_unit_reversed", .outcome = .pass },
    .{ .stem = "pass_acu_right_unit_via_comm", .outcome = .pass },
    .{
        .stem = "fail_au_ambiguous_right_unit",
        .outcome = .{ .fail = error.AmbiguousStructuralUnitRule },
    },
    .{ .stem = "pass_au_order_sensitive", .outcome = .pass },
    .{ .stem = "fail_au_order_sensitive", .outcome = .{ .fail = error.UnifyMismatch } },
    .{ .stem = "pass_acu_multiplicity_sensitive", .outcome = .pass },
    .{ .stem = "fail_acu_multiplicity_sensitive", .outcome = .{ .fail = error.UnifyMismatch } },
    .{ .stem = "pass_aui_ordered_idempotent", .outcome = .pass },
    .{ .stem = "fail_aui_nonadjacent_idempotent", .outcome = .{ .fail = error.UnifyMismatch } },
    .{ .stem = "pass_au_multi_remainder_infer", .outcome = .pass },
    .{ .stem = "pass_acu_multi_remainder_infer", .outcome = .pass },
    .{ .stem = "pass_aui_multi_remainder_infer", .outcome = .pass },
    .{ .stem = "pass_acui_multi_remainder_infer", .outcome = .pass },
    .{ .stem = "pass_acui_transparent_ctx_reuse", .outcome = .pass },
    .{ .stem = "pass_acui_four_way_cut_stress", .outcome = .pass },
    .{
        .stem = "fail_acui_joint_cover_conflict",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{ .stem = "pass_acui_multi_remainder_ambiguous", .outcome = .pass },
    .{
        .stem = "fail_acui_multi_remainder_impossible",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{ .stem = "pass_struct_nd_imp_intro", .outcome = .pass },
    .{ .stem = "pass_struct_exchange_ctx", .outcome = .pass },
    .{
        .stem = "fail_struct_exchange_bad_B_dep",
        .outcome = .{ .fail = error.DepViolation },
    },
    .{ .stem = "pass_struct_nd_forall_elim", .outcome = .pass },
    .{ .stem = "pass_view_infer_ctx_raw", .outcome = .pass },
    .{ .stem = "pass_view_materialized_nonderived", .outcome = .pass },
    .{ .stem = "pass_view_recover_free_hole_auto", .outcome = .pass },
    .{ .stem = "pass_view_recover_symbolic_hole", .outcome = .pass },
    .{ .stem = "pass_view_acui_joint_cover", .outcome = .pass },
    .{ .stem = "pass_struct_seq_forall_left", .outcome = .pass },
    .{ .stem = "prawitz", .outcome = .pass },
    .{ .stem = "barcan", .outcome = .pass },
    .{ .stem = "church", .outcome = .pass },
    .{ .stem = "pass_church_holes", .outcome = .pass },
    .{ .stem = "pass_church_holes_hard", .outcome = .pass },
    .{ .stem = "mltt_min", .outcome = .pass },
    .{ .stem = "mltt", .outcome = .pass },
    .{ .stem = "martin_lof", .outcome = .pass },
    .{ .stem = "peano", .outcome = .pass },
    .{
        .stem = "fail_missing_binding",
        .outcome = .{ .fail = error.MissingBinderAssignment },
    },
    .{
        .stem = "fail_def_unfold_mismatch",
        .outcome = .{ .fail = error.HypothesisMismatch },
    },
    .{
        .stem = "fail_def_view_mismatch",
        .outcome = .{ .fail = error.ViewHypothesisMismatch },
    },
    .{
        .stem = "pass_def_infer_ambiguous",
        .outcome = .pass,
    },
    .{
        .stem = "fail_def_hidden_dummy_all_elim_ctx_uncovered",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{
        .stem = "fail_def_hidden_dummy_all_elim_ctx_no_vars",
        .outcome = .{ .fail = error.UnresolvedDummyWitness },
    },
    .{
        .stem = "fail_def_hidden_dummy_all_elim_ctx_pool_exhausted",
        .outcome = .{ .fail = error.HiddenWitnessNoAvailableVar },
    },
    .{
        .stem = "fail_acui_same_side_uncovered",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{
        .stem = "fail_acui_same_side_leftover_def",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{
        .stem = "fail_acui_cross_side_uncovered",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{ .stem = "fail_acui_cross_side_leftover_def", .outcome = .pass },
    .{ .stem = "pass_def_hidden_dummy_ax", .outcome = .pass },
    .{
        .stem = "fail_infer_mismatch",
        .outcome = .{ .fail = error.UnifyMismatch },
    },
    .{
        .stem = "fail_hyp_mismatch",
        .outcome = .{ .fail = error.HypothesisMismatch },
    },
    .{
        .stem = "fail_duplicate_label",
        .outcome = .{ .fail = error.DuplicateLabel },
    },
    .{
        .stem = "fail_boundness",
        .outcome = .{ .fail = error.BoundnessMismatch },
    },
    .{
        .stem = "fail_statement_boundness",
        .outcome = .{ .fail = error.BoundnessMismatch },
    },
    .{
        .stem = "fail_view_boundness",
        .outcome = .{ .fail = error.BoundnessMismatch },
    },
    .{
        .stem = "fail_unknown_label",
        .outcome = .{ .fail = error.UnknownLabel },
    },
    .{
        .stem = "fail_normalize_mismatch",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{
        .stem = "fail_abstract_no_occurrence",
        .outcome = .{ .fail = error.AbstractNoPlugOccurrence },
    },
    .{
        .stem = "fail_abstract_structure_mismatch",
        .outcome = .{ .fail = error.AbstractStructureMismatch },
    },
    .{
        .stem = "fail_abstract_sort_mismatch",
        .outcome = .{ .fail = error.AbstractPlugSortMismatch },
    },
    .{
        .stem = "fail_abstract_conflict",
        .outcome = .{ .fail = error.AbstractConflict },
    },
    .{
        .stem = "fail_abstract_unknown_binder",
        .outcome = .{ .fail = error.UnknownAbstractBinder },
    },
    .{
        .stem = "fail_abstract_without_view",
        .outcome = .{ .fail = error.AbstractWithoutView },
    },
    .{
        .stem = "fail_fresh_unknown_binder",
        .outcome = .{ .fail = error.UnknownFreshBinder },
    },
    .{
        .stem = "fail_fresh_duplicate",
        .outcome = .{ .fail = error.DuplicateFreshBinder },
    },
    .{
        .stem = "fail_fresh_nonbound_binder",
        .outcome = .{ .fail = error.FreshRequiresBoundBinder },
    },
    .{
        .stem = "fail_fresh_sort_restriction",
        .outcome = .{ .fail = error.FreshFreeSort },
    },
    .{
        .stem = "fail_fresh_exhausted",
        .outcome = .{ .fail = error.FreshNoAvailableVar },
    },
    .{
        .stem = "fail_var_conclusion_mismatch",
        .outcome = .{ .fail = error.ConclusionMismatch },
    },
    .{ .stem = "pass_comment_trailing", .outcome = .pass },
    .{ .stem = "pass_comment_standalone", .outcome = .pass },
    .{ .stem = "pass_comment_only_lines", .outcome = .pass },
    .{ .stem = "pass_vars_basic", .outcome = .pass },
    .{ .stem = "pass_vars_unicode", .outcome = .pass },
    .{ .stem = "pass_vars_lazy", .outcome = .pass },
    .{ .stem = "pass_vars_tab_ws", .outcome = .pass },
    .{
        .stem = "fail_vars_duplicate_token",
        .outcome = .{ .fail = error.DuplicateVarsToken },
    },
    .{
        .stem = "fail_vars_collision",
        .outcome = .{ .fail = error.VarsTokenCollision },
    },
    .{
        .stem = "fail_vars_later_collision",
        .outcome = .{ .fail = error.VarsTokenCollision },
    },
    .{
        .stem = "fail_vars_invalid_annotation",
        .outcome = .{ .fail = error.InvalidVarsAnnotation },
    },
    .{
        .stem = "fail_vars_strict_sort",
        .outcome = .{ .fail = error.VarsStrictSort },
    },
    .{
        .stem = "fail_vars_free_sort",
        .outcome = .{ .fail = error.VarsFreeSort },
    },
};

fn readProofCaseFile(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

const mm0c_cache_dir = ".zig-cache-local/mm0c-test";

fn mm0cExists() bool {
    const result = std.process.Child.run(.{
        .allocator = std.testing.allocator,
        .argv = &.{"mm0-c"},
        .max_output_bytes = 8 * 1024,
    }) catch return false;
    std.testing.allocator.free(result.stdout);
    std.testing.allocator.free(result.stderr);
    // mm0-c with no args prints usage and exits 1
    return switch (result.term) {
        .Exited => true,
        else => false,
    };
}

fn verifyWithMm0c(mm0_src: []const u8, mmb: []const u8, stem: []const u8) !void {
    var path_buf: [256]u8 = undefined;
    const mmb_path = std.fmt.bufPrint(&path_buf, mm0c_cache_dir ++ "/{s}.mmb", .{stem}) catch mm0c_cache_dir ++ "/out.mmb";
    std.fs.cwd().makePath(mm0c_cache_dir) catch |err| {
        std.debug.print("FAIL (mm0-c) could not create cache dir: {}\n", .{err});
        return err;
    };
    std.fs.cwd().writeFile(.{ .sub_path = mmb_path, .data = mmb }) catch |err| {
        std.debug.print("FAIL (mm0-c) could not write temp mmb: {}\n", .{err});
        return err;
    };
    defer std.fs.cwd().deleteFile(mmb_path) catch {};

    var child = std.process.Child.init(&.{ "mm0-c", mmb_path }, std.testing.allocator);
    child.stdin_behavior = .Pipe;
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;

    child.spawn() catch |err| {
        std.debug.print("FAIL (mm0-c) could not spawn: {}\n", .{err});
        return err;
    };

    child.stdin.?.writeAll(mm0_src) catch {};
    child.stdin.?.close();
    child.stdin = null;

    // Read stderr before wait to avoid pipe buffer deadlock
    var stderr_buf: [4096]u8 = undefined;
    const stderr_len = child.stderr.?.readAll(&stderr_buf) catch 0;
    const stderr = stderr_buf[0..stderr_len];

    const term = child.wait() catch |err| {
        std.debug.print("FAIL (mm0-c) wait failed: {}\n", .{err});
        return err;
    };

    switch (term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("FAIL (mm0-c) exit code {d}\n{s}\n", .{ code, stderr });
                return error.Mm0cVerificationFailed;
            }
        },
        else => {
            std.debug.print("FAIL (mm0-c) abnormal termination\n", .{});
            return error.Mm0cVerificationFailed;
        },
    }
}

test "non-pass proof case metadata stays in sync" {
    var known_fail_count: usize = 0;
    var unsupported_count: usize = 0;

    for (proof_cases) |case| {
        switch (case.outcome) {
            .known_fail => {
                known_fail_count += 1;
                try std.testing.expect(knownFailReason(case.stem) != null);
                try std.testing.expect(unsupportedReason(case.stem) == null);
            },
            .unsupported => {
                unsupported_count += 1;
                try std.testing.expect(unsupportedReason(case.stem) != null);
                try std.testing.expect(knownFailReason(case.stem) == null);
            },
            else => {
                try std.testing.expect(knownFailReason(case.stem) == null);
                try std.testing.expect(unsupportedReason(case.stem) == null);
            },
        }
    }

    try std.testing.expectEqual(
        known_proof_case_failures.len,
        known_fail_count,
    );
    try std.testing.expectEqual(
        unsupported_proof_cases.len,
        unsupported_count,
    );

    for (known_proof_case_failures, 0..) |entry, idx| {
        for (known_proof_case_failures[idx + 1 ..]) |other| {
            try std.testing.expect(!std.mem.eql(u8, entry.stem, other.stem));
        }
    }
    for (unsupported_proof_cases, 0..) |entry, idx| {
        for (unsupported_proof_cases[idx + 1 ..]) |other| {
            try std.testing.expect(!std.mem.eql(u8, entry.stem, other.stem));
        }
    }
    for (known_proof_case_failures) |entry| {
        try std.testing.expect(unsupportedReason(entry.stem) == null);
    }
    for (unsupported_proof_cases) |entry| {
        try std.testing.expect(knownFailReason(entry.stem) == null);
    }
}

test "compiler proof cases from files" {
    const allocator = std.testing.allocator;
    const have_mm0c = mm0cExists();

    var failure_count: usize = 0;
    var failed_cases: [proof_cases.len][]const u8 = undefined;

    for (proof_cases) |case| {
        const mm0_src = try readProofCaseFile(allocator, case.stem, "mm0");
        defer allocator.free(mm0_src);

        const proof_src = try readProofCaseFile(
            allocator,
            case.stem,
            proof_case_ext,
        );
        defer allocator.free(proof_src);

        var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
        switch (case.outcome) {
            .pass => {
                const mmb = compiler.compileMmb(allocator) catch |err| {
                    std.debug.print("FAIL (compile) case={s} err={}\n", .{ case.stem, err });
                    if (compiler.last_diagnostic) |diag| {
                        std.debug.print(
                            "  diag: kind={} theorem={s} line={s} rule={s}\n",
                            .{
                                diag.kind,
                                diag.theorem_name orelse "?",
                                diag.line_label orelse "?",
                                diag.rule_name orelse "?",
                            },
                        );
                    }
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                    continue;
                };
                defer allocator.free(mmb);
                mm0.verifyPair(allocator, mm0_src, mmb) catch |err| {
                    std.debug.print("FAIL (verify) case={s} err={}\n", .{ case.stem, err });
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                    continue;
                };
                if (have_mm0c) {
                    verifyWithMm0c(mm0_src, mmb, case.stem) catch {
                        std.debug.print("FAIL (mm0-c) case={s}\n", .{case.stem});
                        failed_cases[failure_count] = case.stem;
                        failure_count += 1;
                        continue;
                    };
                }
            },
            .fail => |err| {
                try std.testing.expectError(err, compiler.compileMmb(allocator));
            },
            .known_fail => {
                if (compiler.compileMmb(allocator)) |mmb| {
                    allocator.free(mmb);
                    std.debug.print(
                        "XPASS (known_fail) case={s}: {s}\n",
                        .{
                            case.stem,
                            knownFailReason(case.stem) orelse "missing reason",
                        },
                    );
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                } else |_| {}
            },
            .unsupported => {
                if (compiler.compileMmb(allocator)) |mmb| {
                    allocator.free(mmb);
                    std.debug.print(
                        "XPASS (unsupported) case={s}: {s}\n",
                        .{
                            case.stem,
                            unsupportedReason(case.stem) orelse
                                "missing reason",
                        },
                    );
                    failed_cases[failure_count] = case.stem;
                    failure_count += 1;
                } else |_| {}
            },
        }
    }

    if (failure_count > 0) {
        std.debug.print("\n{d} test case(s) failed:\n", .{failure_count});
        for (failed_cases[0..failure_count]) |stem| {
            std.debug.print("  - {s}\n", .{stem});
        }
        return error.TestCasesFailed;
    }
}

test "compiler emits name, var, and hyp index tables" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(allocator, "hilbert", "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "hilbert",
        proof_case_ext,
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    try std.testing.expect(mmb.header.p_index != 0);
    try std.testing.expectEqualStrings("wff", (try mmb.sortName(0)).?);
    try std.testing.expectEqualStrings("imp", (try mmb.termName(0)).?);
    try std.testing.expectEqualStrings("not", (try mmb.termName(1)).?);
    try std.testing.expectEqualStrings("h1", (try mmb.theoremName(0)).?);
    try std.testing.expectEqualStrings("con2", (try mmb.theoremName(3)).?);
    try std.testing.expectEqualStrings("inot", (try mmb.theoremName(4)).?);
    try std.testing.expectEqualStrings("mp", (try mmb.theoremName(5)).?);
    try std.testing.expectEqualStrings("imp_refl", (try mmb.theoremName(6)).?);
    try std.testing.expectEqualStrings("hs", (try mmb.theoremName(7)).?);
    try std.testing.expectEqualStrings("notnot1", (try mmb.theoremName(8)).?);
    try std.testing.expectEqualStrings("dne", (try mmb.theoremName(9)).?);

    const imp_vars = (try mmb.termVarNames(0)).?;
    try std.testing.expectEqual(@as(usize, 2), imp_vars.len());
    try std.testing.expectEqualStrings("a", (try imp_vars.get(0)).?);
    try std.testing.expectEqualStrings("b", (try imp_vars.get(1)).?);

    const mp_vars = (try mmb.theoremVarNames(5)).?;
    try std.testing.expectEqual(@as(usize, 2), mp_vars.len());
    try std.testing.expectEqualStrings("a", (try mp_vars.get(0)).?);
    try std.testing.expectEqualStrings("b", (try mp_vars.get(1)).?);

    const mp_hyps = (try mmb.theoremHypNames(5)).?;
    try std.testing.expectEqual(@as(usize, 2), mp_hyps.len());
    try std.testing.expectEqualStrings("#1", (try mp_hyps.get(0)).?);
    try std.testing.expectEqualStrings("#2", (try mp_hyps.get(1)).?);

    const refl_hyps = (try mmb.theoremHypNames(6)).?;
    try std.testing.expectEqual(@as(usize, 0), refl_hyps.len());

    const hs_hyps = (try mmb.theoremHypNames(7)).?;
    try std.testing.expectEqual(@as(usize, 2), hs_hyps.len());
    try std.testing.expectEqualStrings("#1", (try hs_hyps.get(0)).?);
    try std.testing.expectEqualStrings("#2", (try hs_hyps.get(1)).?);
}

test "compiler records theorem-local fresh vars in theorem var table" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(allocator, "pass_fresh_hole", "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_fresh_hole",
        proof_case_ext,
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    var theorem_id: ?u32 = null;
    var idx: u32 = 0;
    while (idx < mmb.header.num_thms) : (idx += 1) {
        const maybe_name = try mmb.theoremName(idx);
        if (maybe_name) |name| {
            if (std.mem.eql(u8, name, "fresh_hole")) {
                theorem_id = idx;
                break;
            }
        }
    }

    const fresh_hole_id = theorem_id orelse return error.MissingTheorem;
    const vars = (try mmb.theoremVarNames(fresh_hole_id)).?;
    try std.testing.expectEqual(@as(usize, 3), vars.len());
    try std.testing.expectEqualStrings("a", (try vars.get(0)).?);
    try std.testing.expectEqualStrings("b", (try vars.get(1)).?);
    try std.testing.expectEqual(@as(?[]const u8, null), try vars.get(2));
}

test "compiler reuses @fresh pool vars across proof lines" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_fresh_reuse",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_fresh_reuse",
        proof_case_ext,
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb_bytes = try compiler.compileMmb(allocator);
    defer allocator.free(mmb_bytes);

    const mmb = try Mmb.parse(allocator, mmb_bytes);
    var theorem_id: ?u32 = null;
    var idx: u32 = 0;
    while (idx < mmb.header.num_thms) : (idx += 1) {
        const maybe_name = try mmb.theoremName(idx);
        if (maybe_name) |name| {
            if (std.mem.eql(u8, name, "fresh_reuse")) {
                theorem_id = idx;
                break;
            }
        }
    }

    const fresh_reuse_id = theorem_id orelse return error.MissingTheorem;
    const vars = (try mmb.theoremVarNames(fresh_reuse_id)).?;
    try std.testing.expectEqual(@as(usize, 1), vars.len());
    try std.testing.expectEqual(@as(?[]const u8, null), try vars.get(0));
}
