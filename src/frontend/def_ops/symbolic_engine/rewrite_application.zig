const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch = @import("./transparent_match.zig");
const WitnessState = @import("./witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BoundValue = Types.BoundValue;
const MatchSession = MatchState.MatchSession;

pub fn applyRewriteRuleToExpr(
    self: anytype,
    rule: RewriteRule,
    expr_id: ExprId,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const node = self.shared.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
        .placeholder => return null,
    };
    if (app.term_id != rule.head_term_id) return null;

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    const rewrite_bindings = try self.shared.allocator.alloc(
        ?BoundValue,
        rule.num_binders,
    );
    defer self.shared.allocator.free(rewrite_bindings);
    @memset(rewrite_bindings, null);

    if (!try matchRewriteTemplateToExpr(
        self,
        rule.lhs,
        expr_id,
        rewrite_bindings,
        state,
    )) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        return null;
    }
    if (!try validateRewriteRuleBindings(
        self,
        rule,
        rewrite_bindings,
        state,
    )) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        return null;
    }
    return try instantiateRewriteRuleRhs(
        self,
        rule,
        rewrite_bindings,
    ) orelse blk: {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        break :blk null;
    };
}

pub fn applyRewriteRuleToSymbolic(
    self: anytype,
    rule: RewriteRule,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    return switch (symbolic.*) {
        .fixed => |expr_id| try applyRewriteRuleToExpr(
            self,
            rule,
            expr_id,
            state,
        ),
        .app => |app| blk: {
            if (app.term_id != rule.head_term_id) break :blk null;

            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            const rewrite_bindings = try self.shared.allocator.alloc(
                ?BoundValue,
                rule.num_binders,
            );
            defer self.shared.allocator.free(rewrite_bindings);
            @memset(rewrite_bindings, null);

            if (!try matchRewriteTemplateToSymbolic(
                self,
                rule.lhs,
                symbolic,
                rewrite_bindings,
                state,
            )) {
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                break :blk null;
            }
            if (!try validateRewriteRuleBindings(
                self,
                rule,
                rewrite_bindings,
                state,
            )) {
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                break :blk null;
            }
            break :blk try instantiateRewriteRuleRhs(
                self,
                rule,
                rewrite_bindings,
            ) orelse inner: {
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                break :inner null;
            };
        },
        .binder, .dummy => null,
    };
}

fn matchRewriteTemplateToExpr(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    rewrite_bindings: []?BoundValue,
    state: *MatchSession,
) anyerror!bool {
    return switch (template) {
        .binder => |idx| try assignRewriteBinderFromExpr(
            self,
            rewrite_bindings,
            idx,
            actual,
            state,
        ),
        .app => |tmpl_app| blk: {
            const actual_node = self.shared.theorem.interner.node(actual);
            const actual_app = switch (actual_node.*) {
                .app => |value| value,
                .variable => break :blk false,
                .placeholder => break :blk false,
            };
            if (actual_app.term_id != tmpl_app.term_id or
                actual_app.args.len != tmpl_app.args.len)
            {
                break :blk false;
            }

            const saved = try self.shared.allocator.dupe(
                ?BoundValue,
                rewrite_bindings,
            );
            defer self.shared.allocator.free(saved);
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            for (tmpl_app.args, actual_app.args) |tmpl_arg, actual_arg| {
                if (!try matchRewriteTemplateToExpr(
                    self,
                    tmpl_arg,
                    actual_arg,
                    rewrite_bindings,
                    state,
                )) {
                    @memcpy(rewrite_bindings, saved);
                    try WitnessState.restoreMatchSnapshot(
                        self,
                        &snapshot,
                        state,
                    );
                    break :blk false;
                }
            }
            break :blk true;
        },
    };
}

fn matchRewriteTemplateToSymbolic(
    self: anytype,
    template: TemplateExpr,
    actual: *const SymbolicExpr,
    rewrite_bindings: []?BoundValue,
    state: *MatchSession,
) anyerror!bool {
    return switch (template) {
        .binder => |idx| try assignRewriteBinderFromSymbolic(
            self,
            rewrite_bindings,
            idx,
            actual,
            state,
        ),
        .app => |tmpl_app| switch (actual.*) {
            .fixed => |expr_id| try matchRewriteTemplateToExpr(
                self,
                template,
                expr_id,
                rewrite_bindings,
                state,
            ),
            .app => |actual_app| blk: {
                if (actual_app.term_id != tmpl_app.term_id or
                    actual_app.args.len != tmpl_app.args.len)
                {
                    break :blk false;
                }

                const saved = try self.shared.allocator.dupe(
                    ?BoundValue,
                    rewrite_bindings,
                );
                defer self.shared.allocator.free(saved);
                var snapshot = try WitnessState.saveMatchSnapshot(self, state);
                defer WitnessState.deinitMatchSnapshot(self, &snapshot);

                for (tmpl_app.args, actual_app.args) |tmpl_arg, actual_arg| {
                    if (!try matchRewriteTemplateToSymbolic(
                        self,
                        tmpl_arg,
                        actual_arg,
                        rewrite_bindings,
                        state,
                    )) {
                        @memcpy(rewrite_bindings, saved);
                        try WitnessState.restoreMatchSnapshot(
                            self,
                            &snapshot,
                            state,
                        );
                        break :blk false;
                    }
                }
                break :blk true;
            },
            .binder, .dummy => false,
        },
    };
}

fn assignRewriteBinderFromExpr(
    self: anytype,
    rewrite_bindings: []?BoundValue,
    idx: usize,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (idx >= rewrite_bindings.len) return false;
    const value = try WitnessState.rebuildBoundValueFromState(
        self,
        actual,
        state,
        .transparent,
    );
    if (rewrite_bindings[idx]) |existing| {
        return try rewriteBoundValuesEql(self, existing, value);
    }
    rewrite_bindings[idx] = value;
    return true;
}

fn assignRewriteBinderFromSymbolic(
    self: anytype,
    rewrite_bindings: []?BoundValue,
    idx: usize,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    if (idx >= rewrite_bindings.len) return false;
    const value = try rewriteBoundValueFromSymbolic(self, symbolic, state);
    if (rewrite_bindings[idx]) |existing| {
        return try rewriteBoundValuesEql(self, existing, value);
    }
    rewrite_bindings[idx] = value;
    return true;
}

fn rewriteBoundValueFromSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!BoundValue {
    return switch (symbolic.*) {
        .fixed => |expr_id| try WitnessState.rebuildBoundValueFromState(
            self,
            expr_id,
            state,
            .transparent,
        ),
        else => WitnessState.makeSymbolicBoundValue(
            self,
            symbolic,
            .transparent,
        ),
    };
}

fn rewriteBoundValuesEql(
    self: anytype,
    lhs: BoundValue,
    rhs: BoundValue,
) anyerror!bool {
    const lhs_repr = try WitnessState.boundValueRepresentative(self, lhs);
    const rhs_repr = try WitnessState.boundValueRepresentative(self, rhs);
    return WitnessState.symbolicExprEql(self, lhs_repr, rhs_repr);
}

fn validateRewriteRuleBindings(
    self: anytype,
    rule: RewriteRule,
    rewrite_bindings: []const ?BoundValue,
    state: *MatchSession,
) anyerror!bool {
    if (rule.rule_id >= self.shared.env.rules.items.len) return false;
    const rule_decl = &self.shared.env.rules.items[rule.rule_id];
    if (rule_decl.args.len != rewrite_bindings.len) return false;

    for (rule_decl.args, rewrite_bindings) |arg, binding_opt| {
        const binding = binding_opt orelse return false;
        const sort_name = try rewriteBoundValueSortName(
            self,
            binding,
            state,
        ) orelse return false;
        if (!std.mem.eql(u8, sort_name, arg.sort_name)) return false;
        const actual_bound = try rewriteBoundValueIsBound(
            self,
            binding,
            state,
        );
        if (arg.bound and !actual_bound) {
            return false;
        }
    }
    return true;
}

fn rewriteBoundValueSortName(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!?[]const u8 {
    const symbolic = try WitnessState.boundValueRepresentative(self, bound);
    return WitnessState.symbolicSortName(self, symbolic, state);
}

fn rewriteBoundValueIsBound(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!bool {
    _ = state;
    const symbolic = try WitnessState.boundValueRepresentative(self, bound);
    return try symbolicIsBound(self, symbolic);
}

fn symbolicIsBound(
    self: anytype,
    symbolic: *const SymbolicExpr,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => false,
        .dummy => true,
        .app => false,
        .fixed => |expr_id| blk: {
            const info =
                (try WitnessState.getConcreteLeafInfo(self, expr_id)) orelse
                break :blk false;
            break :blk info.bound;
        },
    };
}

fn instantiateRewriteRuleRhs(
    self: anytype,
    rule: RewriteRule,
    rewrite_bindings: []const ?BoundValue,
) anyerror!?*const SymbolicExpr {
    const subst = try self.shared.allocator.alloc(
        *const SymbolicExpr,
        rewrite_bindings.len,
    );
    for (rewrite_bindings, 0..) |binding_opt, idx| {
        const binding = binding_opt orelse return null;
        subst[idx] = try WitnessState.boundValueRepresentative(self, binding);
    }
    return try TransparentMatch.symbolicFromTemplateSubst(self, rule.rhs, subst);
}
