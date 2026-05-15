const std = @import("std");
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const DefOps = @import("../def_ops.zig");
const DerivedBindings = @import("../derived_bindings.zig");
const BindingValidation = @import("../binding_validation.zig");
const Expr = @import("../../trusted/expressions.zig").Expr;
const SurfaceExpr = @import("../surface_expr.zig");
const ArgInfo = @import("../parse_recovery.zig").ArgInfo;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const ViewTrace = @import("../view_trace.zig");

const recover_guidance_match_budget: usize = 8;

const ViewSignature = struct {
    arg_names: []const ?[]const u8,
    arg_infos: []const ArgInfo,
    arg_exprs: []const *const Expr,
    hyps: []const *const Expr,
    concl: *const Expr,
};

pub const RecoverDecl = DerivedBindings.RecoverDecl;
pub const AbstractDecl = DerivedBindings.AbstractDecl;
pub const DerivedBinding = DerivedBindings.DerivedBinding;

pub const ViewDecl = struct {
    hyps: []const TemplateExpr,
    concl: TemplateExpr,
    num_binders: usize,
    arg_names: []const ?[]const u8,
    arg_infos: []const ArgInfo,
    /// Maps view binder index -> rule arg index, null for phantom binders.
    binder_map: []const ?usize,
    derived_bindings: []const DerivedBinding,
};

pub fn processViewAnnotations(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    assertion: AssertionStmt,
    annotations: []const []const u8,
    views: *std.AutoHashMap(u32, ViewDecl),
) !void {
    const rule_id = env.getRuleId(assertion.name) orelse return;
    const rule = &env.rules.items[rule_id];
    const view_prefix = "@view ";
    const recover_prefix = "@recover ";
    const abstract_prefix = "@abstract ";

    var maybe_view: ?ViewDecl = null;
    var view_sig: ?ViewSignature = null;
    var derived_bindings = std.ArrayListUnmanaged(DerivedBinding){};
    defer derived_bindings.deinit(allocator);

    for (annotations) |ann| {
        if (std.mem.startsWith(u8, ann, view_prefix)) {
            if (maybe_view != null) return error.DuplicateViewAnnotation;

            const sig = try parseViewSignature(
                allocator,
                parser,
                ann[view_prefix.len..],
            );
            if (sig.hyps.len != rule.hyps.len) {
                return error.ViewHypCountMismatch;
            }

            const binder_map = try allocator.alloc(?usize, sig.arg_names.len);
            for (sig.arg_names, 0..) |view_name, vi| {
                binder_map[vi] = if (view_name) |name|
                    findRuleArgIndex(rule, name)
                else
                    null;
            }

            const view_hyps = try allocator.alloc(TemplateExpr, sig.hyps.len);
            for (sig.hyps, 0..) |hyp, idx| {
                view_hyps[idx] = try TemplateExpr.fromExpr(
                    allocator,
                    hyp,
                    sig.arg_exprs,
                );
            }
            const view_concl = try TemplateExpr.fromExpr(
                allocator,
                sig.concl,
                sig.arg_exprs,
            );

            maybe_view = .{
                .hyps = view_hyps,
                .concl = view_concl,
                .num_binders = sig.arg_names.len,
                .arg_names = sig.arg_names,
                .arg_infos = sig.arg_infos,
                .binder_map = binder_map,
                .derived_bindings = &.{},
            };
            view_sig = sig;
            continue;
        }

        if (std.mem.startsWith(u8, ann, recover_prefix)) {
            const sig = view_sig orelse return error.RecoverWithoutView;
            const view = maybe_view orelse return error.RecoverWithoutView;
            try derived_bindings.append(
                allocator,
                .{ .recover = try parseRecoverAnnotation(
                    ann[recover_prefix.len..],
                    sig,
                    view.binder_map,
                ) },
            );
            continue;
        }

        if (std.mem.startsWith(u8, ann, abstract_prefix)) {
            const sig = view_sig orelse return error.AbstractWithoutView;
            const view = maybe_view orelse return error.AbstractWithoutView;
            try derived_bindings.append(
                allocator,
                .{ .abstract = try parseAbstractAnnotation(
                    ann[abstract_prefix.len..],
                    sig,
                    view.binder_map,
                ) },
            );
        }
    }

    if (maybe_view) |*view| {
        view.derived_bindings = try derived_bindings.toOwnedSlice(allocator);
        try views.put(rule_id, view.*);
    }
}

const ViewConclusion = union(enum) {
    concrete: ExprId,
    surface: *const Expr,
};

pub fn applyViewBindings(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view: *const ViewDecl,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    partial_bindings: []?ExprId,
    seed_overrides: ?[]const DefOps.BindingSeed,
    exported_state: ?*?DefOps.MatchSeedState,
    debug_views: bool,
) !void {
    return applyViewBindingsWithConclusion(
        allocator,
        theorem,
        env,
        registry,
        view,
        .{ .concrete = line_expr },
        ref_exprs,
        partial_bindings,
        seed_overrides,
        exported_state,
        debug_views,
    );
}

pub fn applyViewBindingsSurfaceConclusion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view: *const ViewDecl,
    surface_concl: *const Expr,
    ref_exprs: []const ExprId,
    partial_bindings: []?ExprId,
    seed_overrides: ?[]const DefOps.BindingSeed,
    exported_state: ?*?DefOps.MatchSeedState,
    debug_views: bool,
) !void {
    return applyViewBindingsWithConclusion(
        allocator,
        theorem,
        env,
        registry,
        view,
        .{ .surface = surface_concl },
        ref_exprs,
        partial_bindings,
        seed_overrides,
        exported_state,
        debug_views,
    );
}

pub fn applyViewBindingsRefsOnly(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view: *const ViewDecl,
    ref_exprs: []const ExprId,
    partial_bindings: []?ExprId,
    seed_overrides: ?[]const DefOps.BindingSeed,
    exported_state: ?*?DefOps.MatchSeedState,
    debug_views: bool,
) !void {
    return applyViewBindingsWithConclusion(
        allocator,
        theorem,
        env,
        registry,
        view,
        null,
        ref_exprs,
        partial_bindings,
        seed_overrides,
        exported_state,
        debug_views,
    );
}

fn applyViewBindingsWithConclusion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view: *const ViewDecl,
    conclusion: ?ViewConclusion,
    ref_exprs: []const ExprId,
    partial_bindings: []?ExprId,
    seed_overrides: ?[]const DefOps.BindingSeed,
    exported_state: ?*?DefOps.MatchSeedState,
    debug_views: bool,
) !void {
    const seeds = try allocator.alloc(DefOps.BindingSeed, view.num_binders);
    defer allocator.free(seeds);
    for (view.binder_map, 0..) |mapping, vi| {
        seeds[vi] = if (mapping) |rule_idx|
            if (partial_bindings[rule_idx]) |expr_id|
                .{ .exact = expr_id }
            else
                .none
        else
            .none;
    }
    if (seed_overrides) |overrides| {
        std.debug.assert(overrides.len == view.num_binders);
        for (overrides, 0..) |seed, vi| {
            switch (seed) {
                .none => {},
                else => if (seeds[vi] == .none) {
                    seeds[vi] = seed;
                },
            }
        }
    }

    var def_ops = DefOps.Context.initWithRegistry(
        allocator,
        theorem,
        env,
        registry,
    );
    defer def_ops.deinit();

    var session = try def_ops.beginRuleMatch(view.arg_infos, seeds);
    defer session.deinit();

    var surface_bindings: ?[]?*const Expr = null;
    defer if (surface_bindings) |bindings| allocator.free(bindings);
    if (conclusion) |actual_conclusion| {
        switch (actual_conclusion) {
            .surface => {
                const bindings = try allocator.alloc(
                    ?*const Expr,
                    view.num_binders,
                );
                @memset(bindings, null);
                surface_bindings = bindings;
            },
            .concrete => {},
        }
    }

    if (debug_views) {
        try matchViewAgainstConclusionDebug(
            allocator,
            theorem,
            env,
            &session,
            view,
            conclusion,
            surface_bindings,
            ref_exprs,
        );
    } else {
        try matchViewAgainstConclusion(
            env,
            &session,
            view,
            conclusion,
            surface_bindings,
            ref_exprs,
        );
    }
    if (debug_views) {
        const initial_bindings = try session.materializeOptionalBindings();
        defer allocator.free(initial_bindings);
        const initial_seeds = try session.resolveBindingSeeds();
        defer allocator.free(initial_seeds);
        try ViewTrace.printViewBindings(
            allocator,
            theorem,
            env,
            view.arg_names,
            "after initial view match",
            initial_bindings,
            initial_seeds,
        );
    }

    // Keep view reuse on the resolved path, then replay only the cited refs
    // once more so symbolic witnesses prefer the concrete proof shapes
    // before @recover / @abstract try to read them back out.
    if (debug_views) {
        try matchViewHypsAgainstConcreteExprsDebug(
            allocator,
            theorem,
            env,
            &session,
            view,
            ref_exprs,
            "ref replay",
        );
    } else {
        try matchViewHypsAgainstConcreteExprs(
            &session,
            view,
            ref_exprs,
        );
    }
    if (debug_views) {
        const replay_bindings = try session.materializeOptionalBindings();
        defer allocator.free(replay_bindings);
        const replay_seeds = try session.resolveBindingSeeds();
        defer allocator.free(replay_seeds);
        try ViewTrace.printViewBindings(
            allocator,
            theorem,
            env,
            view.arg_names,
            "after ref replay",
            replay_bindings,
            replay_seeds,
        );
    }

    // Derived bindings must inspect the current resolved structure before any
    // representative projection rewrites or canonicalizes it. Symbolic
    // recover also needs the live dummy witnesses from this same state.
    var view_snapshot = DerivedBindings.MatchSnapshot{
        .view_bindings = try session.materializeOptionalBindings(),
        .view_seeds = try session.resolveBindingSeeds(),
        .dummy_witnesses = try session.materializeDummyWitnesses(),
    };
    defer allocator.free(view_snapshot.view_bindings);
    defer allocator.free(view_snapshot.view_seeds.?);
    defer allocator.free(view_snapshot.dummy_witnesses.?);

    if (surface_bindings) |bindings| {
        try applySurfaceDerivedBindings(
            theorem,
            env,
            view,
            bindings,
            view_snapshot.view_bindings,
        );
    }

    var guide_passes: usize = 0;
    while (true) {
        if (debug_views) {
            const label = try std.fmt.allocPrint(
                allocator,
                "before derived pass {d}",
                .{guide_passes},
            );
            defer allocator.free(label);
            try ViewTrace.printViewBindings(
                allocator,
                theorem,
                env,
                view.arg_names,
                label,
                view_snapshot.view_bindings,
                view_snapshot.view_seeds,
            );
        }
        try DerivedBindings.applyDerivedBindings(
            theorem,
            env,
            registry,
            view_snapshot,
            view.derived_bindings,
            view.arg_names,
            debug_views,
        );
        if (guide_passes >= view.derived_bindings.len) break;
        if (!try guideRecoverBindingsTowardSources(
            allocator,
            theorem,
            env,
            &session,
            view,
            view_snapshot.view_bindings,
            view_snapshot.view_seeds.?,
            debug_views,
        )) break;

        const next_view_bindings = try session.materializeOptionalBindings();
        errdefer allocator.free(next_view_bindings);
        const next_view_seeds = try session.resolveBindingSeeds();
        errdefer allocator.free(next_view_seeds);
        const next_dummy_witnesses = try session.materializeDummyWitnesses();
        errdefer allocator.free(next_dummy_witnesses);

        allocator.free(view_snapshot.view_bindings);
        allocator.free(view_snapshot.view_seeds.?);
        allocator.free(view_snapshot.dummy_witnesses.?);
        view_snapshot = .{
            .view_bindings = next_view_bindings,
            .view_seeds = next_view_seeds,
            .dummy_witnesses = next_dummy_witnesses,
        };
        guide_passes += 1;
    }
    if (debug_views) {
        try ViewTrace.printViewBindings(
            allocator,
            theorem,
            env,
            view.arg_names,
            "after derived loop",
            view_snapshot.view_bindings,
            view_snapshot.view_seeds,
        );
    }
    const materialized_projected_bindings =
        try session.materializeOptionalBindings();
    defer allocator.free(materialized_projected_bindings);
    const project_view_binding = try allocator.alloc(bool, view.num_binders);
    defer allocator.free(project_view_binding);
    @memset(project_view_binding, false);
    for (view.binder_map, 0..) |mapping, vi| {
        project_view_binding[vi] = mapping != null;
    }
    const projected_view_bindings =
        try session.representSelectedOptionalBindingsOrRaw(
            materialized_projected_bindings,
            project_view_binding,
        );
    defer allocator.free(projected_view_bindings);

    for (view.derived_bindings) |binding| {
        const target_view_idx = switch (binding) {
            .recover => |recover| recover.target_view_idx,
            .abstract => |abstract| abstract.target_view_idx,
        };
        if (view_snapshot.view_bindings[target_view_idx]) |binding_expr| {
            projected_view_bindings[target_view_idx] = binding_expr;
        }
    }

    // Export symbolic-preserving state in rule-binder space if requested.
    // Only derived targets need symbolic carry-through. Non-derived view
    // binders should be re-inferred by ordinary rule matching unless they
    // already became concrete in partial_bindings.
    if (exported_state) |out_state| {
        const derived_targets = try allocator.alloc(bool, view.num_binders);
        defer allocator.free(derived_targets);
        @memset(derived_targets, false);
        for (view.derived_bindings) |binding| {
            const target_view_idx = switch (binding) {
                .recover => |recover| recover.target_view_idx,
                .abstract => |abstract| abstract.target_view_idx,
            };
            derived_targets[target_view_idx] = true;
        }

        const rule_seeds = try allocator.alloc(
            DefOps.BindingSeed,
            partial_bindings.len,
        );
        @memset(rule_seeds, .none);
        errdefer allocator.free(rule_seeds);

        const export_view_seeds = try session.resolveBindingSeeds();
        defer allocator.free(export_view_seeds);
        var has_symbolic_seed = false;
        for (view.binder_map, 0..) |mapping, vi| {
            const rule_idx = mapping orelse continue;
            if (!derived_targets[vi]) continue;
            switch (export_view_seeds[vi]) {
                .bound => {
                    rule_seeds[rule_idx] = export_view_seeds[vi];
                    has_symbolic_seed = true;
                },
                else => {},
            }
        }
        if (has_symbolic_seed) {
            out_state.* = try session.exportMatchSeedState(rule_seeds);
        } else {
            allocator.free(rule_seeds);
            out_state.* = null;
        }
    }

    for (view.binder_map, 0..) |mapping, vi| {
        const rule_idx = mapping orelse continue;
        const binding = projected_view_bindings[vi] orelse continue;
        if (partial_bindings[rule_idx]) |existing| {
            if (existing != binding) return error.ViewBindingConflict;
        } else {
            partial_bindings[rule_idx] = binding;
        }
    }
}

fn guideRecoverBindingsTowardSources(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    view_bindings: []const ?ExprId,
    view_seeds: []const DefOps.BindingSeed,
    debug_views: bool,
) !bool {
    var guided = false;
    for (view.derived_bindings) |binding| {
        const recover = switch (binding) {
            .recover => |recover| recover,
            .abstract => continue,
        };
        if (view_bindings[recover.target_view_idx] != null and
            view_bindings[recover.pattern_view_idx] != null)
        {
            continue;
        }
        const source_expr = view_bindings[recover.source_view_idx] orelse {
            continue;
        };
        if (debug_views) {
            try ViewTrace.printRecoverState(
                allocator,
                theorem,
                env,
                view.arg_names,
                recover.target_view_idx,
                recover.source_view_idx,
                recover.pattern_view_idx,
                recover.hole_view_idx,
                view_bindings,
                view_seeds,
            );
        }
        const made_progress = if (view_bindings[recover.target_view_idx] != null and
            view_bindings[recover.pattern_view_idx] == null)
            try session.guideBindingTowardExprReplacingHole(
                recover.pattern_view_idx,
                source_expr,
                recover.hole_view_idx,
                recover.target_view_idx,
                recover_guidance_match_budget,
            )
        else
            try session.guideBindingTowardExpr(
                recover.pattern_view_idx,
                source_expr,
                recover_guidance_match_budget,
            );
        if (made_progress) {
            if (debug_views) {
                ViewTrace.printMessage(
                    "guidance for {s}#{d} succeeded",
                    .{
                        ViewTrace.binderLabel(
                            view.arg_names,
                            recover.pattern_view_idx,
                        ),
                        recover.pattern_view_idx,
                    },
                );
            }
            guided = true;
        } else if (debug_views) {
            ViewTrace.printMessage(
                "guidance for {s}#{d} made no progress",
                .{
                    ViewTrace.binderLabel(
                        view.arg_names,
                        recover.pattern_view_idx,
                    ),
                    recover.pattern_view_idx,
                },
            );
        }
    }
    return guided;
}

fn matchViewAgainstConclusion(
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    conclusion: ?ViewConclusion,
    surface_bindings: ?[]?*const Expr,
    ref_exprs: []const ExprId,
) !void {
    var initial_state: ?DefOps.MatchSeedState = null;
    defer if (initial_state) |*state| {
        state.deinit(session.shared.allocator);
    };
    if (conclusion != null and ref_exprs.len != 0 and surface_bindings == null) {
        initial_state = try saveViewMatchState(session);
    }

    if (conclusion) |actual_conclusion| {
        const matched = try matchViewConclusion(
            env,
            session,
            view,
            actual_conclusion,
            surface_bindings,
        );
        if (!matched) return error.ViewConclusionMismatch;
    }
    matchViewHypsAgainstConcreteExprs(session, view, ref_exprs) catch |err| {
        if (err != error.ViewHypothesisMismatch) return err;
        const state = initial_state orelse return err;
        try session.restoreFromSeedState(&state);
        if (try matchViewHypsBeforeConclusion(
            env,
            session,
            view,
            conclusion.?,
            ref_exprs,
        )) return;
        return err;
    };
}

fn saveViewMatchState(
    session: *DefOps.RuleMatchSession,
) !DefOps.MatchSeedState {
    const seeds = try session.resolveBindingSeeds();
    errdefer session.shared.allocator.free(seeds);
    return try session.exportMatchSeedState(seeds);
}

fn matchViewHypsBeforeConclusion(
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    conclusion: ViewConclusion,
    ref_exprs: []const ExprId,
) !bool {
    matchViewHypsAgainstConcreteExprs(session, view, ref_exprs) catch |err| {
        if (err == error.ViewHypothesisMismatch) return false;
        return err;
    };
    return try matchViewConclusion(env, session, view, conclusion, null);
}

fn matchViewConclusion(
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    conclusion: ViewConclusion,
    surface_bindings: ?[]?*const Expr,
) !bool {
    return switch (conclusion) {
        .concrete => |line_expr| try matchConcreteViewConclusion(
            session,
            view,
            line_expr,
        ),
        .surface => |surface| try matchSurfaceViewConclusion(
            env,
            session,
            view,
            surface,
            surface_bindings,
        ),
    };
}

fn matchViewAgainstConclusionDebug(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    conclusion: ?ViewConclusion,
    surface_bindings: ?[]?*const Expr,
    ref_exprs: []const ExprId,
) !void {
    var initial_state: ?DefOps.MatchSeedState = null;
    defer if (initial_state) |*state| {
        state.deinit(session.shared.allocator);
    };
    if (conclusion != null and ref_exprs.len != 0 and surface_bindings == null) {
        initial_state = try saveViewMatchState(session);
    }

    if (conclusion) |actual_conclusion| {
        if (!try matchViewConclusionDebug(
            allocator,
            theorem,
            env,
            session,
            view,
            actual_conclusion,
            surface_bindings,
        )) {
            return error.ViewConclusionMismatch;
        }
    } else {
        ViewTrace.printMessage(
            "view conclusion skipped for implicit application",
            .{},
        );
    }

    matchViewHypsAgainstConcreteExprsDebug(
        allocator,
        theorem,
        env,
        session,
        view,
        ref_exprs,
        "initial hypothesis match",
    ) catch |err| {
        if (err != error.ViewHypothesisMismatch) return err;
        const state = initial_state orelse return err;
        ViewTrace.printMessage(
            "hypothesis match failed; retrying hypotheses before conclusion",
            .{},
        );
        try session.restoreFromSeedState(&state);
        matchViewHypsAgainstConcreteExprsDebug(
            allocator,
            theorem,
            env,
            session,
            view,
            ref_exprs,
            "hypothesis-first retry",
        ) catch |retry_err| {
            if (retry_err == error.ViewHypothesisMismatch) return err;
            return retry_err;
        };
        const actual_conclusion = conclusion orelse return err;
        if (try matchViewConclusionDebug(
            allocator,
            theorem,
            env,
            session,
            view,
            actual_conclusion,
            null,
        )) return;
        return err;
    };
}

fn matchViewConclusionDebug(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    conclusion: ViewConclusion,
    surface_bindings: ?[]?*const Expr,
) !bool {
    switch (conclusion) {
        .concrete => |line_expr| {
            const concl_text = try ViewTrace.formatExpr(
                allocator,
                theorem,
                env,
                line_expr,
            );
            defer allocator.free(concl_text);
            if (try session.matchTransparent(view.concl, line_expr)) {
                ViewTrace.printMessage(
                    "view conclusion matched transparently: {s}",
                    .{concl_text},
                );
                return true;
            }
            if (try session.matchSemantic(
                view.concl,
                line_expr,
                DefOps.default_semantic_match_budget,
            )) {
                ViewTrace.printMessage(
                    "view conclusion matched semantically: {s}",
                    .{concl_text},
                );
                return true;
            }
            ViewTrace.printMessage(
                "view conclusion mismatch: {s}",
                .{concl_text},
            );
            return false;
        },
        .surface => |surface| {
            if (try matchSurfaceViewConclusion(
                env,
                session,
                view,
                surface,
                surface_bindings,
            )) {
                ViewTrace.printMessage(
                    "view conclusion matched holey surface assertion",
                    .{},
                );
                return true;
            }
            ViewTrace.printMessage(
                "view conclusion mismatch with holey surface assertion",
                .{},
            );
            return false;
        },
    }
}

fn matchConcreteViewConclusion(
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    line_expr: ExprId,
) !bool {
    return try session.matchTransparentOrSemantic(view.concl, line_expr);
}

fn matchSurfaceViewConclusion(
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    surface: *const Expr,
    surface_bindings: ?[]?*const Expr,
) !bool {
    if (SurfaceExpr.containsHole(surface)) {
        if (view.concl == .binder) {
            if (surface_bindings) |bindings| {
                bindings[view.concl.binder] = surface;
            }
            return true;
        }
    }

    var comparison = try session.beginNormalizedSurfaceComparison(
        env,
        view.concl,
        surface,
    );
    defer comparison.deinit();
    return try comparison.finish(
        comparison.expected_expr,
        comparison.actual_expr,
    );
}

fn applySurfaceDerivedBindings(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    view: *const ViewDecl,
    surface_bindings: []const ?*const Expr,
    view_bindings: []?ExprId,
) !void {
    for (view.derived_bindings) |binding| {
        const abstract = switch (binding) {
            .abstract => |value| value,
            .recover => continue,
        };
        if (view_bindings[abstract.target_view_idx] != null) continue;
        const right_surface =
            surface_bindings[abstract.right_view_idx] orelse continue;
        const left_expr = view_bindings[abstract.left_view_idx] orelse {
            continue;
        };
        const hole_expr = view_bindings[abstract.hole_view_idx] orelse {
            continue;
        };
        const left_plug = view_bindings[abstract.left_plug_view_idx] orelse {
            continue;
        };
        const right_plug = view_bindings[abstract.right_plug_view_idx] orelse {
            continue;
        };

        var found_plug = false;
        const candidate = abstractContextSurface(
            theorem,
            env,
            left_expr,
            right_surface,
            hole_expr,
            left_plug,
            right_plug,
            &found_plug,
        ) catch |err| switch (err) {
            error.AbstractStructureMismatch => continue,
            else => return err,
        };
        if (!found_plug) continue;
        view_bindings[abstract.target_view_idx] = candidate;
    }
}

fn abstractContextSurface(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    left_expr: ExprId,
    right_surface: *const Expr,
    hole_expr: ExprId,
    left_plug: ExprId,
    right_plug: ExprId,
    found_plug: *bool,
) !ExprId {
    if (left_expr == left_plug and
        try surfaceMatchesConcrete(theorem, env, right_surface, right_plug))
    {
        found_plug.* = true;
        return hole_expr;
    }

    if (right_surface.* == .hole) {
        if (!try surfaceMatchesConcrete(
            theorem,
            env,
            right_surface,
            left_expr,
        )) return error.AbstractStructureMismatch;
        return left_expr;
    }

    const left_node = theorem.interner.node(left_expr);
    return switch (left_node.*) {
        .variable, .placeholder => blk: {
            if (!try surfaceMatchesConcrete(
                theorem,
                env,
                right_surface,
                left_expr,
            )) return error.AbstractStructureMismatch;
            break :blk left_expr;
        },
        .app => |left_app| blk: {
            const right_term = switch (right_surface.*) {
                .term => |term| term,
                .variable, .hole => return error.AbstractStructureMismatch,
            };
            if (left_app.term_id != right_term.id) {
                return error.AbstractStructureMismatch;
            }
            if (left_app.args.len != right_term.args.len) {
                return error.AbstractStructureMismatch;
            }
            const args = try theorem.allocator.alloc(ExprId, left_app.args.len);
            errdefer theorem.allocator.free(args);
            for (left_app.args, right_term.args, 0..) |
                left_arg,
                right_arg,
                idx,
            | {
                args[idx] = try abstractContextSurface(
                    theorem,
                    env,
                    left_arg,
                    right_arg,
                    hole_expr,
                    left_plug,
                    right_plug,
                    found_plug,
                );
            }
            break :blk try theorem.interner.internAppOwned(
                left_app.term_id,
                args,
            );
        },
    };
}

fn surfaceMatchesConcrete(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    surface: *const Expr,
    expr_id: ExprId,
) !bool {
    if (surface.* == .hole) {
        const hole_sort = SurfaceExpr.sortNameById(env, surface.hole.sort) orelse {
            return error.UnknownSort;
        };
        const info = try BindingValidation.currentExprInfo(
            env,
            theorem,
            expr_id,
        );
        return std.mem.eql(u8, hole_sort, info.sort_name);
    }
    if (SurfaceExpr.containsHole(surface)) return false;
    return (try theorem.internParsedExpr(surface)) == expr_id;
}

fn matchViewHypsAgainstConcreteExprs(
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    ref_exprs: []const ExprId,
) !void {
    for (view.hyps, ref_exprs) |hyp_template, ref_expr| {
        if (!try session.matchTransparentOrSemantic(
            hyp_template,
            ref_expr,
        )) {
            return error.ViewHypothesisMismatch;
        }
    }
}

fn matchViewHypsAgainstConcreteExprsDebug(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    session: *DefOps.RuleMatchSession,
    view: *const ViewDecl,
    ref_exprs: []const ExprId,
    phase: []const u8,
) !void {
    for (view.hyps, ref_exprs, 0..) |hyp_template, ref_expr, hyp_idx| {
        const ref_text = try ViewTrace.formatExpr(
            allocator,
            theorem,
            env,
            ref_expr,
        );
        defer allocator.free(ref_text);
        if (try session.matchTransparent(hyp_template, ref_expr)) {
            ViewTrace.printMessage(
                "{s}: hyp {d} matched transparently: {s}",
                .{ phase, hyp_idx, ref_text },
            );
            continue;
        }
        if (try session.matchSemantic(
            hyp_template,
            ref_expr,
            DefOps.default_semantic_match_budget,
        )) {
            ViewTrace.printMessage(
                "{s}: hyp {d} matched semantically: {s}",
                .{ phase, hyp_idx, ref_text },
            );
            continue;
        }
        ViewTrace.printMessage(
            "{s}: hyp {d} mismatch: {s}",
            .{ phase, hyp_idx, ref_text },
        );
        return error.ViewHypothesisMismatch;
    }
}

fn parseViewSignature(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    text: []const u8,
) !ViewSignature {
    const trimmed = std.mem.trimRight(u8, text, " \t\r\n;");
    const wrapped = try std.fmt.allocPrint(
        allocator,
        "axiom __view {s};",
        .{trimmed},
    );

    var view_parser = MM0Parser.init(wrapped, allocator);
    cloneParserEnv(&view_parser, parser);

    const stmt = try view_parser.next() orelse return error.InvalidViewAnnotation;
    if (try view_parser.next() != null) return error.InvalidViewAnnotation;

    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.InvalidViewAnnotation,
    };
    return .{
        .arg_names = assertion.arg_names,
        .arg_infos = assertion.args,
        .arg_exprs = assertion.arg_exprs,
        .hyps = assertion.hyps,
        .concl = assertion.concl,
    };
}

fn cloneParserEnv(dst: *MM0Parser, src: *const MM0Parser) void {
    dst.core.sort_names = src.core.sort_names;
    dst.core.term_names = src.core.term_names;
    dst.core.sort_infos = src.core.sort_infos;
    dst.core.terms = src.core.terms;
    dst.core.prefix_notations = src.core.prefix_notations;
    dst.core.infix_notations = src.core.infix_notations;
    dst.core.formula_markers = src.core.formula_markers;
    dst.core.token_precs = src.core.token_precs;
    dst.core.infix_assoc = src.core.infix_assoc;
    dst.core.leading_tokens = src.core.leading_tokens;
    dst.core.infixy_tokens = src.core.infixy_tokens;
    dst.core.coercion_table = src.core.coercion_table;
    dst.core.left_delims = src.core.left_delims;
    dst.core.right_delims = src.core.right_delims;
}

fn parseRecoverAnnotation(
    text: []const u8,
    sig: ViewSignature,
    binder_map: []const ?usize,
) !RecoverDecl {
    var it = std.mem.tokenizeAny(
        u8,
        std.mem.trimRight(u8, text, " \t\r\n;"),
        " \t\r\n",
    );
    const target_name = it.next() orelse return error.InvalidRecoverAnnotation;
    const source_name = it.next() orelse return error.InvalidRecoverAnnotation;
    const pattern_name = it.next() orelse return error.InvalidRecoverAnnotation;
    const hole_name = it.next() orelse return error.InvalidRecoverAnnotation;
    if (it.next() != null) return error.InvalidRecoverAnnotation;

    const target_view_idx = findViewBinderIndex(sig, target_name) orelse {
        return error.UnknownRecoverBinder;
    };
    const source_view_idx = findViewBinderIndex(sig, source_name) orelse {
        return error.UnknownRecoverBinder;
    };
    const pattern_view_idx = findViewBinderIndex(sig, pattern_name) orelse {
        return error.UnknownRecoverBinder;
    };
    const hole_view_idx = findViewBinderIndex(sig, hole_name) orelse {
        return error.UnknownRecoverBinder;
    };

    if (binder_map[target_view_idx] == null) {
        return error.RecoverTargetNotRuleBinder;
    }
    if (!std.mem.eql(
        u8,
        sig.arg_infos[target_view_idx].sort_name,
        sig.arg_infos[hole_view_idx].sort_name,
    )) {
        return error.RecoverSortMismatch;
    }

    return .{
        .target_view_idx = target_view_idx,
        .source_view_idx = source_view_idx,
        .pattern_view_idx = pattern_view_idx,
        .hole_view_idx = hole_view_idx,
    };
}

fn parseAbstractAnnotation(
    text: []const u8,
    sig: ViewSignature,
    binder_map: []const ?usize,
) !AbstractDecl {
    var it = std.mem.tokenizeAny(
        u8,
        std.mem.trimRight(u8, text, " \t\r\n;"),
        " \t\r\n",
    );
    const target_name = it.next() orelse return error.InvalidAbstractAnnotation;
    const left_name = it.next() orelse return error.InvalidAbstractAnnotation;
    const right_name = it.next() orelse return error.InvalidAbstractAnnotation;
    const hole_name = it.next() orelse return error.InvalidAbstractAnnotation;
    const left_plug_name = it.next() orelse return error.InvalidAbstractAnnotation;
    const right_plug_name = it.next() orelse return error.InvalidAbstractAnnotation;
    if (it.next() != null) return error.InvalidAbstractAnnotation;

    const target_view_idx = findViewBinderIndex(sig, target_name) orelse {
        return error.UnknownAbstractBinder;
    };
    const left_view_idx = findViewBinderIndex(sig, left_name) orelse {
        return error.UnknownAbstractBinder;
    };
    const right_view_idx = findViewBinderIndex(sig, right_name) orelse {
        return error.UnknownAbstractBinder;
    };
    const hole_view_idx = findViewBinderIndex(sig, hole_name) orelse {
        return error.UnknownAbstractBinder;
    };
    const left_plug_view_idx = findViewBinderIndex(sig, left_plug_name) orelse {
        return error.UnknownAbstractBinder;
    };
    const right_plug_view_idx = findViewBinderIndex(sig, right_plug_name) orelse {
        return error.UnknownAbstractBinder;
    };

    if (binder_map[target_view_idx] == null) {
        return error.AbstractTargetNotRuleBinder;
    }
    if (!std.mem.eql(
        u8,
        sig.arg_infos[hole_view_idx].sort_name,
        sig.arg_infos[left_plug_view_idx].sort_name,
    ) or !std.mem.eql(
        u8,
        sig.arg_infos[hole_view_idx].sort_name,
        sig.arg_infos[right_plug_view_idx].sort_name,
    )) {
        return error.AbstractPlugSortMismatch;
    }

    return .{
        .target_view_idx = target_view_idx,
        .left_view_idx = left_view_idx,
        .right_view_idx = right_view_idx,
        .hole_view_idx = hole_view_idx,
        .left_plug_view_idx = left_plug_view_idx,
        .right_plug_view_idx = right_plug_view_idx,
    };
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}

fn findViewBinderIndex(sig: ViewSignature, name: []const u8) ?usize {
    for (sig.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}
