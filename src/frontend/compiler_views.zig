const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const Expr = @import("../trusted/expressions.zig").Expr;
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;

const ViewSignature = struct {
    arg_names: []const ?[]const u8,
    arg_infos: []const ArgInfo,
    arg_exprs: []const *const Expr,
    hyps: []const *const Expr,
    concl: *const Expr,
};

pub const RecoverDecl = struct {
    target_view_idx: usize,
    source_view_idx: usize,
    pattern_view_idx: usize,
    hole_view_idx: usize,
};

pub const ViewDecl = struct {
    hyps: []const TemplateExpr,
    concl: TemplateExpr,
    num_binders: usize,
    arg_infos: []const ArgInfo,
    /// Maps view binder index -> rule arg index, null for phantom binders.
    binder_map: []const ?usize,
    recovers: []const RecoverDecl,
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

    var maybe_view: ?ViewDecl = null;
    var view_sig: ?ViewSignature = null;
    var recovers = std.ArrayListUnmanaged(RecoverDecl){};
    defer recovers.deinit(allocator);

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
                .arg_infos = sig.arg_infos,
                .binder_map = binder_map,
                .recovers = &.{},
            };
            view_sig = sig;
            continue;
        }

        if (std.mem.startsWith(u8, ann, recover_prefix)) {
            const sig = view_sig orelse return error.RecoverWithoutView;
            const view = maybe_view orelse return error.RecoverWithoutView;
            try recovers.append(
                allocator,
                try parseRecoverAnnotation(
                    ann[recover_prefix.len..],
                    sig,
                    view.binder_map,
                ),
            );
        }
    }

    if (maybe_view) |*view| {
        view.recovers = try recovers.toOwnedSlice(allocator);
        try views.put(rule_id, view.*);
    }
}

pub fn applyViewBindings(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    view: *const ViewDecl,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    partial_bindings: []?ExprId,
) !void {
    const view_bindings = try allocator.alloc(?ExprId, view.num_binders);
    @memset(view_bindings, null);

    for (view.binder_map, 0..) |mapping, vi| {
        const rule_idx = mapping orelse continue;
        view_bindings[vi] = partial_bindings[rule_idx];
    }

    if (!theorem.matchTemplate(view.concl, line_expr, view_bindings)) {
        return error.ViewConclusionMismatch;
    }
    for (view.hyps, ref_exprs) |hyp_template, ref_expr| {
        if (!theorem.matchTemplate(hyp_template, ref_expr, view_bindings)) {
            return error.ViewHypothesisMismatch;
        }
    }

    for (view.recovers) |recover| {
        try applyRecoverBinding(theorem, view_bindings, recover);
    }

    for (view.binder_map, 0..) |mapping, vi| {
        const rule_idx = mapping orelse continue;
        const binding = view_bindings[vi] orelse continue;
        if (partial_bindings[rule_idx]) |existing| {
            if (existing != binding) return error.ViewBindingConflict;
        } else {
            partial_bindings[rule_idx] = binding;
        }
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
    dst.sort_names = src.sort_names;
    dst.term_names = src.term_names;
    dst.sort_infos = src.sort_infos;
    dst.terms = src.terms;
    dst.prefix_notations = src.prefix_notations;
    dst.infix_notations = src.infix_notations;
    dst.formula_markers = src.formula_markers;
    dst.token_precs = src.token_precs;
    dst.infix_assoc = src.infix_assoc;
    dst.leading_tokens = src.leading_tokens;
    dst.infixy_tokens = src.infixy_tokens;
    dst.coercion_table = src.coercion_table;
    dst.left_delims = src.left_delims;
    dst.right_delims = src.right_delims;
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

fn applyRecoverBinding(
    theorem: *const TheoremContext,
    view_bindings: []?ExprId,
    recover: RecoverDecl,
) !void {
    if (view_bindings[recover.target_view_idx] != null) return;

    const source_expr = view_bindings[recover.source_view_idx] orelse {
        return error.RecoverSourceUnsolved;
    };
    const pattern_expr = view_bindings[recover.pattern_view_idx] orelse {
        return error.RecoverPatternUnsolved;
    };
    const hole_expr = view_bindings[recover.hole_view_idx] orelse {
        return error.RecoverHoleUnsolved;
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
    view_bindings[recover.target_view_idx] = candidate;
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
