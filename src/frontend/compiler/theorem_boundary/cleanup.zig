const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const ExprNode = @import("../../expr.zig").ExprNode;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation =
    @import("../../rewrite_registry.zig").ResolvedRelation;
const AlphaRule = @import("../../rewrite_registry.zig").AlphaRule;
const Normalizer = @import("../../normalizer.zig").Normalizer;
const ProofEmit = @import("../../normalizer/proof_emit.zig");
const Inference = @import("../inference.zig");
const CompilerDiag = @import("../diag.zig");
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const appendRuleLine = CheckedIr.appendRuleLine;
const rollbackToMark = CheckedIr.rollbackToMark;

pub const CleanupConversion = struct {
    relation: ResolvedRelation,
    declared_to_cleaned_line_idx: usize,
};

pub fn tryBuildFinalCleanupConversion(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    declared: ExprId,
    cleaned: ExprId,
) anyerror!?CleanupConversion {
    var builder = Builder{
        .allocator = allocator,
        .theorem = theorem,
        .registry = registry,
        .env = env,
        .checked = checked,
        .scratch = scratch,
    };
    const relation = builder.resolveRelationForExpr(declared) orelse return null;
    const line_idx = try builder.buildDeclaredToCleaned(
        declared,
        cleaned,
    ) orelse return null;
    return .{
        .relation = relation,
        .declared_to_cleaned_line_idx = line_idx,
    };
}

const Builder = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,

    fn buildDeclaredToCleaned(
        self: *Builder,
        declared: ExprId,
        cleaned: ExprId,
    ) anyerror!?usize {
        if (declared == cleaned) return null;

        if (try self.tryTransparentProof(declared, cleaned)) |proof_idx| {
            return proof_idx;
        }

        if (try self.tryAlphaAtRoot(declared, cleaned)) |proof_idx| {
            return proof_idx;
        }

        if (try self.tryStructuralProof(declared, cleaned)) |proof_idx| {
            return proof_idx;
        }

        return null;
    }

    fn tryTransparentProof(
        self: *Builder,
        declared: ExprId,
        cleaned: ExprId,
    ) anyerror!?usize {
        if (!try Inference.canConvertTransparent(
            self.allocator,
            self.theorem,
            self.env,
            cleaned,
            declared,
        )) {
            return null;
        }
        var norm = self.makeNormalizer();
        const relation = norm.resolveRelationForExpr(declared) orelse {
            return null;
        };
        return try ProofEmit.emitTransparentRelationProof(
            &norm,
            relation,
            declared,
            cleaned,
        );
    }

    fn tryAlphaAtRoot(
        self: *Builder,
        declared: ExprId,
        cleaned: ExprId,
    ) anyerror!?usize {
        const declared_node = self.theorem.interner.node(declared);
        const declared_app = switch (declared_node.*) {
            .app => |app| app,
            .variable => return null,
        };
        const cleaned_node = self.theorem.interner.node(cleaned);
        const cleaned_app = switch (cleaned_node.*) {
            .app => |app| app,
            .variable => return null,
        };
        if (declared_app.term_id != cleaned_app.term_id or
            declared_app.args.len != cleaned_app.args.len)
        {
            return null;
        }

        const alpha_rules = self.registry.getAlphaRules(declared_app.term_id);
        for (alpha_rules) |rule| {
            const checked_mark = self.checked.items.len;
            const scratch_mark = self.scratch.mark();
            const attempt = self.applyAlphaRuleAtRoot(
                declared,
                cleaned_app,
                rule,
            ) catch |err| {
                rollbackToMark(self.allocator, self.checked, checked_mark);
                return err;
            } orelse {
                self.scratch.discard(scratch_mark);
                continue;
            };
            if (attempt.result_expr == cleaned) {
                self.scratch.discard(scratch_mark);
                return attempt.proof_idx;
            }
            if (try self.buildDeclaredToCleaned(
                attempt.result_expr,
                cleaned,
            )) |rest_idx| {
                const relation = self.resolveRelationForExpr(declared) orelse {
                    rollbackToMark(self.allocator, self.checked, checked_mark);
                    self.scratch.discard(scratch_mark);
                    continue;
                };
                var norm = self.makeNormalizer();
                const composed = try norm.composeTransitivity(
                    relation,
                    declared,
                    attempt.result_expr,
                    cleaned,
                    attempt.proof_idx,
                    rest_idx,
                ) orelse {
                    rollbackToMark(self.allocator, self.checked, checked_mark);
                    self.scratch.discard(scratch_mark);
                    continue;
                };
                self.scratch.discard(scratch_mark);
                return composed;
            }
            rollbackToMark(self.allocator, self.checked, checked_mark);
            self.scratch.discard(scratch_mark);
        }
        return null;
    }

    fn tryStructuralProof(
        self: *Builder,
        declared: ExprId,
        cleaned: ExprId,
    ) anyerror!?usize {
        const declared_node = self.theorem.interner.node(declared);
        const cleaned_node = self.theorem.interner.node(cleaned);
        const declared_app = switch (declared_node.*) {
            .app => |app| app,
            .variable => return null,
        };
        const cleaned_app = switch (cleaned_node.*) {
            .app => |app| app,
            .variable => return null,
        };
        if (declared_app.term_id != cleaned_app.term_id or
            declared_app.args.len != cleaned_app.args.len)
        {
            return null;
        }
        if (declared_app.term_id >= self.env.terms.items.len) return null;
        const term = &self.env.terms.items[declared_app.term_id];
        if (term.args.len != declared_app.args.len) return null;

        const checked_mark = self.checked.items.len;
        const scratch_mark = self.scratch.mark();
        errdefer rollbackToMark(self.allocator, self.checked, checked_mark);

        const child_proofs = try self.allocator.alloc(?usize, term.args.len);
        defer self.allocator.free(child_proofs);
        @memset(child_proofs, null);

        var any_changed = false;
        for (term.args, declared_app.args, cleaned_app.args, 0..) |
            arg_info,
            declared_arg,
            cleaned_arg,
            idx,
        | {
            if (arg_info.bound) {
                if (declared_arg != cleaned_arg) {
                    rollbackToMark(self.allocator, self.checked, checked_mark);
                    self.scratch.discard(scratch_mark);
                    return null;
                }
                continue;
            }
            if (declared_arg == cleaned_arg) continue;
            child_proofs[idx] = try self.buildDeclaredToCleaned(
                declared_arg,
                cleaned_arg,
            ) orelse {
                rollbackToMark(self.allocator, self.checked, checked_mark);
                self.scratch.discard(scratch_mark);
                return null;
            };
            any_changed = true;
        }
        if (!any_changed) {
            rollbackToMark(self.allocator, self.checked, checked_mark);
            self.scratch.discard(scratch_mark);
            return null;
        }

        var norm = self.makeNormalizer();
        const proof_idx = (try ProofEmit.emitCongruenceLine(
            &norm,
            declared_app.term_id,
            declared_app.args,
            cleaned_app.args,
            child_proofs,
        )) orelse {
            rollbackToMark(self.allocator, self.checked, checked_mark);
            self.scratch.discard(scratch_mark);
            return null;
        };
        self.scratch.discard(scratch_mark);
        return proof_idx;
    }

    fn applyAlphaRuleAtRoot(
        self: *Builder,
        declared: ExprId,
        cleaned_app: ExprNode.App,
        rule: AlphaRule,
    ) anyerror!?AlphaAttempt {
        const lhs_app = switch (rule.lhs) {
            .app => |app| app,
            .binder => return null,
        };
        const rhs_app = switch (rule.rhs) {
            .app => |app| app,
            .binder => return null,
        };
        const old_arg_idx = rootBinderArgIndex(lhs_app.args, rule.old_idx) orelse {
            return null;
        };
        const new_arg_idx = rootBinderArgIndex(rhs_app.args, rule.new_idx) orelse {
            return null;
        };

        const bindings = try self.allocator.alloc(?ExprId, rule.num_binders);
        defer self.allocator.free(bindings);
        @memset(bindings, null);

        const declared_app = self.theorem.interner.node(declared).app;
        if (old_arg_idx >= declared_app.args.len or
            new_arg_idx >= cleaned_app.args.len)
        {
            return null;
        }
        bindings[rule.old_idx] = declared_app.args[old_arg_idx];
        bindings[rule.new_idx] = cleaned_app.args[new_arg_idx];
        if (!self.theorem.matchTemplate(rule.lhs, declared, bindings)) {
            return null;
        }

        const concrete = try self.allocator.alloc(ExprId, rule.num_binders);
        errdefer self.allocator.free(concrete);
        for (bindings, 0..) |binding, idx| {
            concrete[idx] = binding orelse {
                self.allocator.free(concrete);
                return null;
            };
        }

        if (rule.rule_id >= self.env.rules.items.len) {
            self.allocator.free(concrete);
            return null;
        }
        const rule_decl = &self.env.rules.items[rule.rule_id];
        ProofEmit.validateRewriteBindings(
            self.env,
            self.theorem,
            rule_decl.args,
            concrete,
        ) catch {
            self.allocator.free(concrete);
            return null;
        };

        var norm = self.makeNormalizer();
        const relation = norm.resolveRelationForExpr(declared) orelse {
            self.allocator.free(concrete);
            return null;
        };
        const rhs = try self.theorem.instantiateTemplate(rule.rhs, concrete);
        if (rhs == declared) {
            self.allocator.free(concrete);
            return null;
        }
        const rel_expr = try ProofEmit.buildRelExpr(
            &norm,
            relation,
            declared,
            rhs,
        );
        const alpha_idx = try appendRuleLine(
            self.checked,
            self.allocator,
            rel_expr,
            rule.rule_id,
            concrete,
            &.{},
        );

        const normalized = try norm.normalize(rhs);
        const proof_idx = (try norm.composeTransitivity(
            relation,
            declared,
            rhs,
            normalized.result_expr,
            alpha_idx,
            normalized.conv_line_idx,
        )) orelse alpha_idx;
        return .{
            .result_expr = normalized.result_expr,
            .proof_idx = proof_idx,
        };
    }

    fn resolveRelationForExpr(
        self: *Builder,
        expr_id: ExprId,
    ) ?ResolvedRelation {
        var norm = self.makeNormalizer();
        return norm.resolveRelationForExpr(expr_id);
    }

    fn makeNormalizer(self: *Builder) Normalizer {
        return Normalizer.initWithScratch(
            self.allocator,
            self.theorem,
            self.registry,
            self.env,
            self.checked,
            self.scratch,
        );
    }
};

const AlphaAttempt = struct {
    result_expr: ExprId,
    proof_idx: usize,
};

fn rootBinderArgIndex(
    args: []const @import("../../rules.zig").TemplateExpr,
    binder_idx: usize,
) ?usize {
    for (args, 0..) |arg, idx| {
        switch (arg) {
            .binder => |value| if (value == binder_idx) return idx,
            else => {},
        }
    }
    return null;
}

