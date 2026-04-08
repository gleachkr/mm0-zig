const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const DefOps = @import("./def_ops.zig");
const BindingSeed = DefOps.BindingSeed;
const BoundValue = @import("./def_ops/types.zig").BoundValue;
const SymbolicExpr = @import("./def_ops/types.zig").SymbolicExpr;
const ViewTrace = @import("./view_trace.zig");

pub const RecoverDecl = struct {
    target_view_idx: usize,
    source_view_idx: usize,
    pattern_view_idx: usize,
    hole_view_idx: usize,
};

pub const AbstractDecl = struct {
    target_view_idx: usize,
    left_view_idx: usize,
    right_view_idx: usize,
    hole_view_idx: usize,
    left_plug_view_idx: usize,
    right_plug_view_idx: usize,
};

pub const DerivedBinding = union(enum) {
    recover: RecoverDecl,
    abstract: AbstractDecl,
};

const ApplyResult = enum {
    no_progress,
    progress,
};

/// Immutable view-match state consumed by @recover / @abstract.
/// This captures the currently resolved structure before representative
/// projection rewrites it into semantic representatives.
pub const MatchSnapshot = struct {
    dummy_witnesses: ?[]const ?ExprId = null,
    view_bindings: []?ExprId,
    view_seeds: ?[]const BindingSeed = null,
};

const preprocess_max_depth: usize = 32;

pub fn applyDerivedBindings(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    snapshot: MatchSnapshot,
    derived_bindings: []const DerivedBinding,
    view_arg_names: []const ?[]const u8,
    debug_views: bool,
) !void {
    var changed = true;
    while (changed) {
        changed = false;
        for (derived_bindings) |binding| {
            switch (try applyDerivedBinding(
                theorem,
                env,
                registry,
                snapshot,
                binding,
                view_arg_names,
                debug_views,
            )) {
                .no_progress => {},
                .progress => changed = true,
            }
        }
    }
}

fn applyDerivedBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    snapshot: MatchSnapshot,
    binding: DerivedBinding,
    view_arg_names: []const ?[]const u8,
    debug_views: bool,
) !ApplyResult {
    return switch (binding) {
        .recover => |recover| try applyRecoverBinding(
            theorem,
            env,
            registry,
            snapshot,
            recover,
            view_arg_names,
            debug_views,
        ),
        .abstract => |abstract| try applyAbstractBinding(
            theorem,
            env,
            registry,
            snapshot.view_bindings,
            abstract,
        ),
    };
}

fn applyRecoverBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    snapshot: MatchSnapshot,
    recover: RecoverDecl,
    view_arg_names: []const ?[]const u8,
    debug_views: bool,
) !ApplyResult {
    const view_bindings = snapshot.view_bindings;
    const view_seeds = snapshot.view_seeds;

    if (view_bindings[recover.target_view_idx] != null) {
        return .no_progress;
    }
    if (debug_views) {
        try ViewTrace.printRecoverState(
            theorem.allocator,
            theorem,
            env,
            view_arg_names,
            recover.target_view_idx,
            recover.source_view_idx,
            recover.pattern_view_idx,
            recover.hole_view_idx,
            view_bindings,
            view_seeds,
        );
    }

    const source_expr = view_bindings[recover.source_view_idx] orelse {
        return .no_progress;
    };
    const hole_expr = view_bindings[recover.hole_view_idx] orelse {
        return .no_progress;
    };

    if (view_bindings[recover.pattern_view_idx]) |pattern_expr| {
        var candidate: ?ExprId = null;
        const found = recoverBindingCandidate(
            theorem,
            source_expr,
            pattern_expr,
            hole_expr,
            &candidate,
        ) catch |err| switch (err) {
            error.RecoverStructureMismatch => false,
            else => return err,
        };
        if (found) {
            if (debug_views) {
                ViewTrace.printMessage(
                    "raw recover matched concrete pattern",
                    .{},
                );
            }
            view_bindings[recover.target_view_idx] = candidate;
            return .progress;
        }

        const aligned_source = try preprocessDerivedExpr(
            theorem,
            env,
            registry,
            source_expr,
        );
        const aligned_pattern = try preprocessDerivedExpr(
            theorem,
            env,
            registry,
            pattern_expr,
        );

        candidate = null;
        const aligned_found = try recoverBindingCandidate(
            theorem,
            aligned_source,
            aligned_pattern,
            hole_expr,
            &candidate,
        );
        if (!aligned_found) {
            if (debug_views) {
                ViewTrace.printMessage(
                    "aligned recover did not find hole",
                    .{},
                );
            }
            return error.RecoverHoleNotFound;
        }

        if (debug_views) {
            ViewTrace.printMessage(
                "aligned recover matched concrete pattern",
                .{},
            );
        }
        view_bindings[recover.target_view_idx] = candidate;
        return .progress;
    }

    const seeds = view_seeds orelse return .no_progress;
    if (recover.pattern_view_idx >= seeds.len) return .no_progress;

    var candidate: ?ExprId = null;
    var dummy_bindings = std.AutoHashMapUnmanaged(usize, ExprId){};
    defer dummy_bindings.deinit(theorem.allocator);

    const found = recoverBindingCandidateFromSeed(
        theorem,
        snapshot.dummy_witnesses,
        source_expr,
        seeds[recover.pattern_view_idx],
        recover.hole_view_idx,
        hole_expr,
        view_bindings,
        seeds,
        &dummy_bindings,
        &candidate,
    ) catch |err| switch (err) {
        error.RecoverStructureMismatch => false,
        else => return err,
    };
    if (!found) {
        if (debug_views) {
            ViewTrace.printMessage(
                "symbolic recover did not find hole",
                .{},
            );
        }
        return error.RecoverHoleNotFound;
    }

    if (debug_views) {
        ViewTrace.printMessage(
            "symbolic recover found hole",
            .{},
        );
    }
    view_bindings[recover.target_view_idx] = candidate;
    return .progress;
}

fn recoverBindingCandidateFromSeed(
    theorem: *const TheoremContext,
    dummy_witnesses: ?[]const ?ExprId,
    source_expr: ExprId,
    seed: BindingSeed,
    hole_view_idx: usize,
    hole_expr: ExprId,
    view_bindings: []const ?ExprId,
    view_seeds: []const BindingSeed,
    dummy_bindings: *std.AutoHashMapUnmanaged(usize, ExprId),
    candidate: *?ExprId,
) anyerror!bool {
    return switch (seed) {
        .none => false,
        .exact => |expr_id| try recoverBindingCandidate(
            theorem,
            source_expr,
            expr_id,
            hole_expr,
            candidate,
        ),
        .semantic => |semantic| try recoverBindingCandidate(
            theorem,
            source_expr,
            semantic.expr_id,
            hole_expr,
            candidate,
        ),
        .bound => |bound| try recoverBindingCandidateFromBoundValue(
            theorem,
            dummy_witnesses,
            source_expr,
            bound,
            hole_view_idx,
            hole_expr,
            view_bindings,
            view_seeds,
            dummy_bindings,
            candidate,
        ),
    };
}

fn recoverBindingCandidateFromBoundValue(
    theorem: *const TheoremContext,
    dummy_witnesses: ?[]const ?ExprId,
    source_expr: ExprId,
    bound: BoundValue,
    hole_view_idx: usize,
    hole_expr: ExprId,
    view_bindings: []const ?ExprId,
    view_seeds: []const BindingSeed,
    dummy_bindings: *std.AutoHashMapUnmanaged(usize, ExprId),
    candidate: *?ExprId,
) anyerror!bool {
    return switch (bound) {
        .concrete => |concrete| try recoverBindingCandidate(
            theorem,
            source_expr,
            concrete.raw,
            hole_expr,
            candidate,
        ),
        .symbolic => |symbolic| try recoverBindingCandidateSymbolic(
            theorem,
            dummy_witnesses,
            source_expr,
            symbolic.expr,
            hole_view_idx,
            hole_expr,
            view_bindings,
            view_seeds,
            dummy_bindings,
            candidate,
        ),
    };
}

fn recoverBindingCandidateSymbolic(
    theorem: *const TheoremContext,
    dummy_witnesses: ?[]const ?ExprId,
    source_expr: ExprId,
    symbolic: *const SymbolicExpr,
    hole_view_idx: usize,
    hole_expr: ExprId,
    view_bindings: []const ?ExprId,
    view_seeds: []const BindingSeed,
    dummy_bindings: *std.AutoHashMapUnmanaged(usize, ExprId),
    candidate: *?ExprId,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx == hole_view_idx) {
                if (candidate.*) |existing| {
                    if (existing != source_expr) return error.RecoverConflict;
                } else {
                    candidate.* = source_expr;
                }
                break :blk true;
            }
            if (idx < view_bindings.len) {
                if (view_bindings[idx]) |expr_id| {
                    break :blk try recoverBindingCandidate(
                        theorem,
                        source_expr,
                        expr_id,
                        hole_expr,
                        candidate,
                    );
                }
            }
            if (idx >= view_seeds.len) return error.TemplateBinderOutOfRange;
            break :blk try recoverBindingCandidateFromSeed(
                theorem,
                dummy_witnesses,
                source_expr,
                view_seeds[idx],
                hole_view_idx,
                hole_expr,
                view_bindings,
                view_seeds,
                dummy_bindings,
                candidate,
            );
        },
        .fixed => |expr_id| try recoverBindingCandidate(
            theorem,
            source_expr,
            expr_id,
            hole_expr,
            candidate,
        ),
        .dummy => |slot| blk: {
            // Symbolic recover must consult the current dummy witnesses from
            // the live view-match state. Repeated def expansion can allocate
            // fresh dummy slots for the same hidden binder, so slot identity
            // alone is not stable enough to recognize the recover hole.
            if (dummy_witnesses) |witnesses| {
                if (slot < witnesses.len) {
                    if (witnesses[slot]) |witness| {
                        if (witness == hole_expr) {
                            if (candidate.*) |existing| {
                                if (existing != source_expr) {
                                    return error.RecoverConflict;
                                }
                            } else {
                                candidate.* = source_expr;
                            }
                            break :blk true;
                        }
                    }
                }
            }
            if (dummy_bindings.get(slot)) |existing| {
                if (existing != source_expr) return error.RecoverStructureMismatch;
            } else {
                try dummy_bindings.put(theorem.allocator, slot, source_expr);
            }
            break :blk false;
        },
        .app => |pattern_app| blk: {
            const source_node = theorem.interner.node(source_expr);
            const source_app = switch (source_node.*) {
                .variable => return error.RecoverStructureMismatch,
                .app => |app| app,
            };
            if (source_app.term_id != pattern_app.term_id) {
                return error.RecoverStructureMismatch;
            }
            if (source_app.args.len != pattern_app.args.len) {
                return error.RecoverStructureMismatch;
            }
            var found = false;
            for (source_app.args, pattern_app.args) |source_arg, pattern_arg| {
                found = (try recoverBindingCandidateSymbolic(
                    theorem,
                    dummy_witnesses,
                    source_arg,
                    pattern_arg,
                    hole_view_idx,
                    hole_expr,
                    view_bindings,
                    view_seeds,
                    dummy_bindings,
                    candidate,
                )) or found;
            }
            break :blk found;
        },
    };
}

fn recoverBindingCandidate(
    theorem: *const TheoremContext,
    source_expr: ExprId,
    pattern_expr: ExprId,
    hole_expr: ExprId,
    candidate: *?ExprId,
) !bool {
    if (pattern_expr == hole_expr) {
        if (candidate.*) |existing| {
            if (existing != source_expr) return error.RecoverConflict;
        } else {
            candidate.* = source_expr;
        }
        return true;
    }

    const source_node = theorem.interner.node(source_expr);
    const pattern_node = theorem.interner.node(pattern_expr);
    return switch (pattern_node.*) {
        .variable => switch (source_node.*) {
            .variable => return false,
            .app => return error.RecoverStructureMismatch,
        },
        .app => |pattern_app| switch (source_node.*) {
            .variable => return error.RecoverStructureMismatch,
            .app => |source_app| blk: {
                if (source_app.term_id != pattern_app.term_id) {
                    return error.RecoverStructureMismatch;
                }
                if (source_app.args.len != pattern_app.args.len) {
                    return error.RecoverStructureMismatch;
                }
                var found = false;
                for (source_app.args, pattern_app.args) |source_arg, pattern_arg| {
                    found = (try recoverBindingCandidate(
                        theorem,
                        source_arg,
                        pattern_arg,
                        hole_expr,
                        candidate,
                    )) or found;
                }
                break :blk found;
            },
        },
    };
}

fn applyAbstractBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view_bindings: []?ExprId,
    abstract: AbstractDecl,
) !ApplyResult {
    const left_expr = view_bindings[abstract.left_view_idx] orelse {
        return .no_progress;
    };
    const right_expr = view_bindings[abstract.right_view_idx] orelse {
        return .no_progress;
    };
    const hole_expr = view_bindings[abstract.hole_view_idx] orelse {
        return .no_progress;
    };
    const left_plug = view_bindings[abstract.left_plug_view_idx] orelse {
        return .no_progress;
    };
    const right_plug = view_bindings[abstract.right_plug_view_idx] orelse {
        return .no_progress;
    };

    var found_plug = false;
    const raw_candidate = abstractContextExpr(
        theorem,
        left_expr,
        right_expr,
        hole_expr,
        left_plug,
        right_plug,
        &found_plug,
    ) catch |err| switch (err) {
        error.AbstractStructureMismatch => null,
        else => return err,
    };
    if (raw_candidate) |candidate| {
        if (found_plug) {
            if (view_bindings[abstract.target_view_idx]) |existing| {
                if (existing != candidate) return error.AbstractConflict;
                return .no_progress;
            }
            view_bindings[abstract.target_view_idx] = candidate;
            return .progress;
        }
    }

    const aligned_left = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        left_expr,
    );
    const aligned_right = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        right_expr,
    );
    const aligned_left_plug = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        left_plug,
    );
    const aligned_right_plug = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        right_plug,
    );

    found_plug = false;
    const candidate = try abstractContextExpr(
        theorem,
        aligned_left,
        aligned_right,
        hole_expr,
        aligned_left_plug,
        aligned_right_plug,
        &found_plug,
    );
    if (!found_plug) return error.AbstractNoPlugOccurrence;

    if (view_bindings[abstract.target_view_idx]) |existing| {
        if (existing != candidate) return error.AbstractConflict;
        return .no_progress;
    }
    view_bindings[abstract.target_view_idx] = candidate;
    return .progress;
}

fn abstractContextExpr(
    theorem: *TheoremContext,
    left_expr: ExprId,
    right_expr: ExprId,
    hole_expr: ExprId,
    left_plug: ExprId,
    right_plug: ExprId,
    found_plug: *bool,
) !ExprId {
    if (left_expr == left_plug and right_expr == right_plug) {
        found_plug.* = true;
        return hole_expr;
    }

    const left_node = theorem.interner.node(left_expr);
    const right_node = theorem.interner.node(right_expr);
    return switch (left_node.*) {
        .variable => switch (right_node.*) {
            .variable => {
                if (left_expr != right_expr) return error.AbstractStructureMismatch;
                return left_expr;
            },
            .app => return error.AbstractStructureMismatch,
        },
        .app => |left_app| switch (right_node.*) {
            .variable => return error.AbstractStructureMismatch,
            .app => |right_app| blk: {
                if (left_app.term_id != right_app.term_id) {
                    return error.AbstractStructureMismatch;
                }
                if (left_app.args.len != right_app.args.len) {
                    return error.AbstractStructureMismatch;
                }
                const args = try theorem.allocator.alloc(ExprId, left_app.args.len);
                errdefer theorem.allocator.free(args);
                for (left_app.args, right_app.args, 0..) |left_arg, right_arg, idx| {
                    args[idx] = try abstractContextExpr(
                        theorem,
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
        },
    };
}

fn preprocessDerivedExpr(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    expr_id: ExprId,
) !ExprId {
    var arena = std.heap.ArenaAllocator.init(theorem.allocator);
    defer arena.deinit();

    var canonicalizer = Canonicalizer.init(
        arena.allocator(),
        theorem,
        registry,
        env,
    );
    return try preprocessDerivedExprInner(
        &canonicalizer,
        theorem,
        env,
        expr_id,
        0,
    );
}

fn preprocessDerivedExprInner(
    canonicalizer: *Canonicalizer,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
    depth: usize,
) !ExprId {
    if (depth >= preprocess_max_depth) return expr_id;

    if (try expandConcreteDefForDerived(theorem, env, expr_id)) |expanded| {
        if (expanded != expr_id) {
            return try preprocessDerivedExprInner(
                canonicalizer,
                theorem,
                env,
                expanded,
                depth + 1,
            );
        }
    }

    var current = expr_id;
    const node = theorem.interner.node(current);
    switch (node.*) {
        .variable => {},
        .app => |app| {
            const args = try canonicalizer.allocator.alloc(ExprId, app.args.len);
            var any_changed = false;
            for (app.args, 0..) |arg, idx| {
                const aligned_arg = try preprocessDerivedExprInner(
                    canonicalizer,
                    theorem,
                    env,
                    arg,
                    depth + 1,
                );
                args[idx] = aligned_arg;
                any_changed = any_changed or aligned_arg != arg;
            }
            if (any_changed) {
                current = try theorem.interner.internApp(app.term_id, args);
            }
        },
    }

    current = try canonicalizer.canonicalize(current);
    if (try expandConcreteDefForDerived(theorem, env, current)) |expanded| {
        if (expanded != current) {
            return try preprocessDerivedExprInner(
                canonicalizer,
                theorem,
                env,
                expanded,
                depth + 1,
            );
        }
    }
    return current;
}

fn expandConcreteDefForDerived(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) !?ExprId {
    const node = theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
    };
    if (app.term_id >= env.terms.items.len) return null;

    const term = &env.terms.items[app.term_id];
    if (!term.is_def or term.body == null) return null;
    if (term.dummy_args.len != 0) return null;
    if (term.args.len != app.args.len) return null;

    return try theorem.instantiateTemplate(term.body.?, app.args);
}
