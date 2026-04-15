const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const AlphaRule = @import("../rewrite_registry.zig").AlphaRule;
const ResolvedRelation =
    @import("../rewrite_registry.zig").ResolvedRelation;
const Normalizer = @import("../normalizer.zig").Normalizer;
const ProofEmit = @import("../normalizer/proof_emit.zig");
const RewriteProof = @import("../normalizer/proof_emit.zig");
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const Expr = @import("../../trusted/expressions.zig").Expr;
const CompilerFresh = @import("./fresh.zig");
const FreshenDecl = CompilerFresh.FreshenDecl;
const SortVarRegistry = @import("./vars.zig").SortVarRegistry;
const Inference = @import("./inference.zig");
const DepViolationDetail = Inference.DepViolationDetail;
const CompilerDiag = @import("./diag.zig");
const CheckedIr = @import("./checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendRuleLine = CheckedIr.appendRuleLine;

const NameExprMap = std.StringHashMap(*const Expr);

pub const FreshenResult = struct {
    bindings: []const ExprId,
    target_arg_idx: usize,
    blocker_arg_idx: usize,
    old_target_expr: ExprId,
    new_target_expr: ExprId,
    target_conv_line_idx: usize,
};

const NormalizeResult = @import("../normalizer/types.zig").NormalizeResult;

pub fn tryFreshenBindings(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    rule: *const RuleDecl,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    bindings: []const ExprId,
    freshen_decls: []const FreshenDecl,
    dep_detail: DepViolationDetail,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
) !?FreshenResult {
    const decl = matchingFreshenDecl(
        freshen_decls,
        dep_detail,
    ) orelse return null;

    const blocker_expr = bindings[decl.blocker_arg_idx];
    const optional_bindings = try allocator.alloc(?ExprId, bindings.len);
    defer allocator.free(optional_bindings);
    for (bindings, 0..) |binding, idx| {
        optional_bindings[idx] = binding;
    }
    const used_deps = try CompilerFresh.collectUsedDeps(
        env,
        theorem,
        line_expr,
        ref_exprs,
        optional_bindings,
        0,
    );
    const selection = try CompilerFresh.chooseFreshBinding(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        rule.args[decl.blocker_arg_idx].sort_name,
        used_deps,
        0,
    );

    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    const freshened = try freshenExpr(
        &normalizer,
        bindings[decl.target_arg_idx],
        blocker_expr,
        selection.expr_id,
    ) orelse return error.NoAlphaRewriteAvailable;

    if (freshened.result_expr == bindings[decl.target_arg_idx]) {
        return error.AlphaRewriteSearchFailed;
    }
    const new_info = try Inference.exprInfo(
        env,
        theorem,
        theorem.arg_infos,
        freshened.result_expr,
    );
    const blocker_info = try Inference.exprInfo(
        env,
        theorem,
        theorem.arg_infos,
        blocker_expr,
    );
    if (new_info.deps & blocker_info.deps != 0) {
        return error.AlphaRewriteSearchFailed;
    }
    const conv_idx = freshened.conv_line_idx orelse {
        return error.AlphaRewriteSearchFailed;
    };

    const new_bindings = try allocator.dupe(ExprId, bindings);
    new_bindings[decl.target_arg_idx] = freshened.result_expr;
    return .{
        .bindings = new_bindings,
        .target_arg_idx = decl.target_arg_idx,
        .blocker_arg_idx = decl.blocker_arg_idx,
        .old_target_expr = bindings[decl.target_arg_idx],
        .new_target_expr = freshened.result_expr,
        .target_conv_line_idx = conv_idx,
    };
}

pub fn buildRelationProofFromTargetChange(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    old_expr: ExprId,
    new_expr: ExprId,
    old_target: ExprId,
    new_target: ExprId,
    target_conv_line_idx: usize,
) !?usize {
    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    return try buildRelationProofRec(
        &normalizer,
        old_expr,
        new_expr,
        old_target,
        new_target,
        target_conv_line_idx,
    );
}

pub fn transportRefAlongProof(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    target_expr: ExprId,
    source_expr: ExprId,
    conv_line_idx: usize,
    source_ref: CheckedRef,
) !CheckedRef {
    const relation = relationForExpr(
        registry,
        env,
        theorem,
        source_expr,
    ) orelse return error.FreshenMissingRelation;
    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    return .{ .line = try normalizer.emitTransport(
        relation,
        target_expr,
        source_expr,
        conv_line_idx,
        source_ref,
    ) };
}

pub fn transportRefBackwardAlongProof(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    target_expr: ExprId,
    source_expr: ExprId,
    old_to_new_conv_line_idx: usize,
    source_ref: CheckedRef,
) !CheckedRef {
    const relation = relationForExpr(
        registry,
        env,
        theorem,
        target_expr,
    ) orelse return error.FreshenMissingRelation;
    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    const symm_idx = try normalizer.emitSymm(
        relation,
        target_expr,
        source_expr,
        old_to_new_conv_line_idx,
    );
    return .{ .line = try normalizer.emitTransport(
        relation,
        target_expr,
        source_expr,
        symm_idx,
        source_ref,
    ) };
}

fn freshenExpr(
    normalizer: *Normalizer,
    expr_id: ExprId,
    blocker_expr: ExprId,
    fresh_expr: ExprId,
) !?NormalizeResult {
    const blocker_deps = (try Inference.exprInfo(
        normalizer.env,
        normalizer.theorem,
        normalizer.theorem.arg_infos,
        blocker_expr,
    )).deps;
    const current_deps = (try Inference.exprInfo(
        normalizer.env,
        normalizer.theorem,
        normalizer.theorem.arg_infos,
        expr_id,
    )).deps;
    if (current_deps & blocker_deps == 0) {
        return .{
            .result_expr = expr_id,
            .conv_line_idx = null,
        };
    }

    if (try tryApplyAlphaAtRoot(
        normalizer,
        expr_id,
        blocker_expr,
        fresh_expr,
    )) |root_result| {
        const relation = relationForExpr(
            normalizer.registry,
            normalizer.env,
            normalizer.theorem,
            expr_id,
        ) orelse return error.FreshenMissingRelation;
        const normalized = try normalizer.normalize(root_result.result_expr);
        const combined_conv = try normalizer.composeTransitivity(
            relation,
            expr_id,
            root_result.result_expr,
            normalized.result_expr,
            root_result.conv_line_idx,
            normalized.conv_line_idx,
        );
        const root_info = try Inference.exprInfo(
            normalizer.env,
            normalizer.theorem,
            normalizer.theorem.arg_infos,
            normalized.result_expr,
        );
        if (root_info.deps & blocker_deps == 0) {
            return .{
                .result_expr = normalized.result_expr,
                .conv_line_idx = combined_conv,
            };
        }
        if (try freshenExpr(
            normalizer,
            normalized.result_expr,
            blocker_expr,
            fresh_expr,
        )) |next| {
            return .{
                .result_expr = next.result_expr,
                .conv_line_idx = try normalizer.composeTransitivity(
                    relation,
                    expr_id,
                    normalized.result_expr,
                    next.result_expr,
                    combined_conv,
                    next.conv_line_idx,
                ),
            };
        }
        return .{
            .result_expr = normalized.result_expr,
            .conv_line_idx = combined_conv,
        };
    }

    const node = normalizer.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return error.AlphaRewriteSearchFailed,
    };

    const new_args = try normalizer.allocator.dupe(ExprId, app.args);
    defer normalizer.allocator.free(new_args);
    const child_proofs = try normalizer.allocator.alloc(?usize, app.args.len);
    defer normalizer.allocator.free(child_proofs);
    @memset(child_proofs, null);

    var any_changed = false;
    for (app.args, 0..) |arg, idx| {
        const child_result = try freshenExpr(
            normalizer,
            arg,
            blocker_expr,
            fresh_expr,
        ) orelse continue;
        new_args[idx] = child_result.result_expr;
        child_proofs[idx] = child_result.conv_line_idx;
        any_changed = any_changed or child_result.result_expr != arg;
    }
    if (!any_changed) return error.AlphaRewriteSearchFailed;

    const new_expr = try normalizer.theorem.interner.internApp(
        app.term_id,
        new_args,
    );
    const proof = try ProofEmit.emitCongruenceLine(
        normalizer,
        app.term_id,
        app.args,
        new_args,
        child_proofs,
    ) orelse return error.AlphaRewriteSearchFailed;
    return .{
        .result_expr = new_expr,
        .conv_line_idx = proof,
    };
}

fn tryApplyAlphaAtRoot(
    normalizer: *Normalizer,
    expr_id: ExprId,
    blocker_expr: ExprId,
    fresh_expr: ExprId,
) !?NormalizeResult {
    const node = normalizer.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
    };

    const rules = normalizer.registry.getAlphaRules(app.term_id);
    if (rules.len == 0) return null;
    const relation = relationForExpr(
        normalizer.registry,
        normalizer.env,
        normalizer.theorem,
        expr_id,
    ) orelse return error.FreshenMissingRelation;

    for (rules) |rule| {
        const result = try tryApplyAlphaRule(
            normalizer,
            relation,
            expr_id,
            blocker_expr,
            fresh_expr,
            rule,
        );
        if (result != null) return result;
    }
    return null;
}

fn tryApplyAlphaRule(
    normalizer: *Normalizer,
    relation: ResolvedRelation,
    expr_id: ExprId,
    blocker_expr: ExprId,
    fresh_expr: ExprId,
    rule: AlphaRule,
) !?NormalizeResult {
    const bindings = try normalizer.allocator.alloc(?ExprId, rule.num_binders);
    defer normalizer.allocator.free(bindings);
    @memset(bindings, null);
    bindings[rule.old_idx] = blocker_expr;
    bindings[rule.new_idx] = fresh_expr;

    if (!normalizer.theorem.matchTemplate(rule.lhs, expr_id, bindings)) {
        return null;
    }

    const concrete = try normalizer.allocator.alloc(ExprId, rule.num_binders);
    errdefer normalizer.allocator.free(concrete);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding orelse {
            normalizer.allocator.free(concrete);
            return null;
        };
    }

    const rule_decl = &normalizer.env.rules.items[rule.rule_id];
    RewriteProof.validateRewriteBindings(
        normalizer.env,
        normalizer.theorem,
        rule_decl.args,
        concrete,
    ) catch {
        normalizer.allocator.free(concrete);
        return null;
    };

    const rhs_expr = try normalizer.theorem.instantiateTemplate(
        rule.rhs,
        concrete,
    );
    if (rhs_expr == expr_id) {
        normalizer.allocator.free(concrete);
        return null;
    }
    const step_expr = try ProofEmit.buildRelExpr(
        normalizer,
        relation,
        expr_id,
        rhs_expr,
    );
    const line_idx = try appendRuleLine(
        normalizer.lines,
        normalizer.allocator,
        step_expr,
        rule.rule_id,
        concrete,
        &.{},
    );
    return .{
        .result_expr = rhs_expr,
        .conv_line_idx = line_idx,
    };
}

fn buildRelationProofRec(
    normalizer: *Normalizer,
    old_expr: ExprId,
    new_expr: ExprId,
    old_target: ExprId,
    new_target: ExprId,
    target_conv_line_idx: usize,
) !?usize {
    if (old_expr == new_expr) return null;
    if (old_expr == old_target and new_expr == new_target) {
        return target_conv_line_idx;
    }

    const old_node = normalizer.theorem.interner.node(old_expr);
    const new_node = normalizer.theorem.interner.node(new_expr);
    const old_app = switch (old_node.*) {
        .app => |value| value,
        .variable => return error.FreshenTransportFailed,
    };
    const new_app = switch (new_node.*) {
        .app => |value| value,
        .variable => return error.FreshenTransportFailed,
    };
    if (old_app.term_id != new_app.term_id or
        old_app.args.len != new_app.args.len)
    {
        return error.FreshenTransportFailed;
    }

    const child_proofs = try normalizer.allocator.alloc(?usize, old_app.args.len);
    defer normalizer.allocator.free(child_proofs);
    var any_changed = false;
    for (old_app.args, new_app.args, 0..) |old_arg, new_arg, idx| {
        child_proofs[idx] = try buildRelationProofRec(
            normalizer,
            old_arg,
            new_arg,
            old_target,
            new_target,
            target_conv_line_idx,
        );
        any_changed = any_changed or old_arg != new_arg;
    }
    if (!any_changed) return null;
    return try ProofEmit.emitCongruenceLine(
        normalizer,
        old_app.term_id,
        old_app.args,
        new_app.args,
        child_proofs,
    );
}

fn relationForExpr(
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    expr_id: ExprId,
) ?ResolvedRelation {
    var dummy_lines = std.ArrayListUnmanaged(CheckedLine){};
    defer dummy_lines.deinit(theorem.allocator);
    var normalizer = Normalizer.init(
        theorem.allocator,
        theorem,
        registry,
        env,
        &dummy_lines,
    );
    return normalizer.resolveRelationForExpr(expr_id);
}

fn matchingFreshenDecl(
    freshen_decls: []const FreshenDecl,
    dep_detail: DepViolationDetail,
) ?FreshenDecl {
    for (freshen_decls) |decl| {
        const a = dep_detail.first_arg_idx;
        const b = dep_detail.second_arg_idx;
        if ((decl.target_arg_idx == a and decl.blocker_arg_idx == b) or
            (decl.target_arg_idx == b and decl.blocker_arg_idx == a))
        {
            return decl;
        }
    }
    return null;
}

