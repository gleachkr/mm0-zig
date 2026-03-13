const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;

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

pub fn applyDerivedBindings(
    theorem: *TheoremContext,
    view_bindings: []?ExprId,
    derived_bindings: []const DerivedBinding,
) !void {
    var changed = true;
    while (changed) {
        changed = false;
        for (derived_bindings) |binding| {
            switch (try applyDerivedBinding(theorem, view_bindings, binding)) {
                .no_progress => {},
                .progress => changed = true,
            }
        }
    }
}

fn applyDerivedBinding(
    theorem: *TheoremContext,
    view_bindings: []?ExprId,
    binding: DerivedBinding,
) !ApplyResult {
    return switch (binding) {
        .recover => |recover| try applyRecoverBinding(
            theorem,
            view_bindings,
            recover,
        ),
        .abstract => |abstract| try applyAbstractBinding(
            theorem,
            view_bindings,
            abstract,
        ),
    };
}

fn applyRecoverBinding(
    theorem: *TheoremContext,
    view_bindings: []?ExprId,
    recover: RecoverDecl,
) !ApplyResult {
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
    const found = try recoverBindingCandidate(
        theorem,
        source_expr,
        pattern_expr,
        hole_expr,
        &candidate,
    );
    if (!found) return error.RecoverHoleNotFound;

    if (view_bindings[recover.target_view_idx]) |existing| {
        if (existing != candidate.?) return error.RecoverConflict;
        return .no_progress;
    }
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
    if (source_expr == pattern_expr) return false;

    const source_node = theorem.interner.node(source_expr);
    const pattern_node = theorem.interner.node(pattern_expr);
    return switch (pattern_node.*) {
        .variable => return error.RecoverStructureMismatch,
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
    const candidate = try abstractContextExpr(
        theorem,
        left_expr,
        right_expr,
        hole_expr,
        left_plug,
        right_plug,
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
