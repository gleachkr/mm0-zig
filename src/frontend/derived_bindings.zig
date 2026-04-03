const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;

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

const preprocess_max_depth: usize = 32;

pub fn applyDerivedBindings(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view_bindings: []?ExprId,
    derived_bindings: []const DerivedBinding,
) !void {
    var changed = true;
    while (changed) {
        changed = false;
        for (derived_bindings) |binding| {
            switch (try applyDerivedBinding(
                theorem,
                env,
                registry,
                view_bindings,
                binding,
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
    view_bindings: []?ExprId,
    binding: DerivedBinding,
) !ApplyResult {
    return switch (binding) {
        .recover => |recover| try applyRecoverBinding(
            theorem,
            env,
            registry,
            view_bindings,
            recover,
        ),
        .abstract => |abstract| try applyAbstractBinding(
            theorem,
            env,
            registry,
            view_bindings,
            abstract,
        ),
    };
}

fn applyRecoverBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view_bindings: []?ExprId,
    recover: RecoverDecl,
) !ApplyResult {
    if (view_bindings[recover.target_view_idx] != null) {
        return .no_progress;
    }

    const source_expr = view_bindings[recover.source_view_idx] orelse {
        return .no_progress;
    };
    const pattern_expr = view_bindings[recover.pattern_view_idx] orelse {
        return .no_progress;
    };
    const hole_expr = view_bindings[recover.hole_view_idx] orelse {
        return .no_progress;
    };

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
    if (!aligned_found) return error.RecoverHoleNotFound;

    view_bindings[recover.target_view_idx] = candidate;
    return .progress;
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
