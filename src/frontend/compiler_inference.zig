const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const DefOps = @import("./def_ops.zig");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const UnifyReplay = @import("../trusted/unify_replay.zig");
const ProofLine = @import("./proof_script.zig").ProofLine;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const Normalizer = @import("./normalizer.zig").Normalizer;
const InferenceSolver = @import("./inference_solver.zig").Solver;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const CompilerViews = @import("./compiler_views.zig");
const ViewDecl = CompilerViews.ViewDecl;
const CompilerDiag = @import("./compiler_diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedLine = @import("./compiler.zig").CheckedLine;
const CheckedRef = @import("./compiler.zig").CheckedRef;
const Emit = @import("./compiler_emit.zig");

const ExprInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

pub const InferenceContext = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    // Heap prefix `0..rule.args.len` stores inferred theorem arguments.
    // These slots start as either an explicit binding or `null` if omitted.
    // Any entries appended later by `UTermSave` are concrete by construction.
    uheap: std.ArrayListUnmanaged(?ExprId) = .{},
    ustack: std.ArrayListUnmanaged(ExprId) = .{},
    hyps: []const ExprId,
    next_hyp: usize,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        partial_bindings: []const ?ExprId,
        hyps: []const ExprId,
        line_expr: ExprId,
    ) !InferenceContext {
        var ctx = InferenceContext{
            .allocator = allocator,
            .theorem = theorem,
            .hyps = hyps,
            .next_hyp = hyps.len,
        };
        try ctx.uheap.appendSlice(allocator, partial_bindings);
        try ctx.ustack.append(allocator, line_expr);
        return ctx;
    }

    pub fn deinit(self: *InferenceContext) void {
        self.uheap.deinit(self.allocator);
        self.ustack.deinit(self.allocator);
    }

    pub fn uopRef(self: *InferenceContext, heap_id: u32) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        if (heap_id >= self.uheap.items.len) return error.UHeapOutOfBounds;
        if (self.uheap.items[heap_id]) |expected| {
            if (expr_id != expected) return error.UnifyMismatch;
        } else {
            // This is the one semantic difference from verifier-style unify:
            // the first encounter with an omitted binder solves it.
            self.uheap.items[heap_id] = expr_id;
        }
    }

    // Stage 2: unify replay is exact replay. Def-aware inference lives in
    // higher-level solver paths rather than in the opcode interpreter.
    pub fn uopTerm(
        self: *InferenceContext,
        term_id: u32,
        save: bool,
    ) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return error.ExpectedTermApp,
        };
        if (app.term_id != term_id) return error.TermMismatch;
        if (save) try self.uheap.append(self.allocator, expr_id);
        var i = app.args.len;
        while (i > 0) {
            i -= 1;
            try self.ustack.append(self.allocator, app.args[i]);
        }
    }

    pub fn uopDummy(self: *InferenceContext, _: u32) !void {
        _ = self;
        return error.UDummyNotAllowed;
    }

    pub fn uopHyp(self: *InferenceContext) !void {
        if (self.next_hyp == 0) return error.HypCountMismatch;
        // See `buildRuleUnifyStream`: hypotheses are replayed from the end so
        // that they are matched in source order overall.
        self.next_hyp -= 1;
        try self.ustack.append(self.allocator, self.hyps[self.next_hyp]);
    }
};

pub fn canConvertByDefOpening(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    target_expr: ExprId,
    source_expr: ExprId,
) !bool {
    var def_ops = DefOps.Context.init(
        allocator,
        theorem,
        env,
    );
    defer def_ops.deinit();
    return (try def_ops.planConversionByDefOpening(
        target_expr,
        source_expr,
    )) != null;
}

const MirroredTheoremContext = struct {
    theorem: TheoremContext,
    source_dummy_map: []const ExprId,
    mirror_dummy_map: []const ExprId,

    fn init(
        allocator: std.mem.Allocator,
        source: *const TheoremContext,
    ) !MirroredTheoremContext {
        var theorem = TheoremContext.init(allocator);
        theorem.arg_infos = source.arg_infos;
        try theorem.seedBinderCount(source.theorem_vars.items.len);
        theorem.next_dummy_dep = countBoundArgs(source.arg_infos);

        const source_dummy_map = try allocator.alloc(
            ExprId,
            source.theorem_dummies.items.len,
        );
        const mirror_dummy_map = try allocator.alloc(
            ExprId,
            source.theorem_dummies.items.len,
        );
        for (source.theorem_dummies.items, 0..) |dummy, idx| {
            const mirror_dummy = try theorem.addDummyVarResolved(
                dummy.sort_name,
                dummy.sort_id,
            );
            source_dummy_map[idx] = mirror_dummy;
            mirror_dummy_map[idx] = try originalDummyExprId(source, idx);
        }

        return .{
            .theorem = theorem,
            .source_dummy_map = source_dummy_map,
            .mirror_dummy_map = mirror_dummy_map,
        };
    }

    fn deinit(
        self: *MirroredTheoremContext,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.source_dummy_map);
        allocator.free(self.mirror_dummy_map);
        self.theorem.deinit();
    }
};

pub fn countBoundArgs(args: []const ArgInfo) u32 {
    var count: u32 = 0;
    for (args) |arg| {
        if (arg.bound) count += 1;
    }
    return count;
}

pub fn originalDummyExprId(
    theorem: *const TheoremContext,
    idx: usize,
) !ExprId {
    return try @constCast(&theorem.interner).internVar(.{
        .dummy_var = @intCast(idx),
    });
}

pub fn copyExprBetweenTheorems(
    allocator: std.mem.Allocator,
    source: *const TheoremContext,
    target: *TheoremContext,
    source_expr: ExprId,
    source_dummy_map: []const ExprId,
    cache: *std.AutoHashMapUnmanaged(ExprId, ExprId),
) !ExprId {
    if (cache.get(source_expr)) |existing| return existing;

    const copied = switch (source.interner.node(source_expr).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= target.theorem_vars.items.len) {
                    return error.UnknownTheoremVariable;
                }
                break :blk target.theorem_vars.items[idx];
            },
            .dummy_var => |idx| blk: {
                if (idx >= source_dummy_map.len) {
                    return error.UnknownDummyVar;
                }
                break :blk source_dummy_map[idx];
            },
        },
        .app => |app| blk: {
            const args = try allocator.alloc(ExprId, app.args.len);
            errdefer allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = try copyExprBetweenTheorems(
                    allocator,
                    source,
                    target,
                    arg,
                    source_dummy_map,
                    cache,
                );
            }
            break :blk try target.interner.internAppOwned(app.term_id, args);
        },
    };

    try cache.put(allocator, source_expr, copied);
    return copied;
}

fn matchNormalizedPattern(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    mirror: *const MirroredTheoremContext,
    pattern_expr: ExprId,
    actual_expr: ExprId,
    placeholders: *const std.AutoHashMapUnmanaged(ExprId, usize),
    bindings: []?ExprId,
    reverse_cache: *std.AutoHashMapUnmanaged(ExprId, ExprId),
) !bool {
    if (placeholders.get(pattern_expr)) |idx| {
        const actual = try copyExprBetweenTheorems(
            allocator,
            &mirror.theorem,
            theorem,
            actual_expr,
            mirror.mirror_dummy_map,
            reverse_cache,
        );
        if (bindings[idx]) |existing| {
            return existing == actual;
        }
        bindings[idx] = actual;
        return true;
    }

    const pattern_node = mirror.theorem.interner.node(pattern_expr);
    const actual_node = mirror.theorem.interner.node(actual_expr);
    return switch (pattern_node.*) {
        .variable => switch (actual_node.*) {
            .variable => pattern_expr == actual_expr,
            .app => false,
        },
        .app => |pattern_app| switch (actual_node.*) {
            .variable => false,
            .app => |actual_app| blk: {
                if (pattern_app.term_id != actual_app.term_id) break :blk false;
                if (pattern_app.args.len != actual_app.args.len) {
                    break :blk false;
                }
                for (pattern_app.args, actual_app.args) |pattern_arg, actual_arg| {
                    if (!try matchNormalizedPattern(
                        allocator,
                        theorem,
                        mirror,
                        pattern_arg,
                        actual_arg,
                        placeholders,
                        bindings,
                        reverse_cache,
                    )) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
        },
    };
}

pub fn inferBindingsByNormalizedConclusion(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    const bindings = try allocator.dupe(?ExprId, partial_bindings);
    var def_ops = DefOps.Context.init(
        allocator,
        theorem,
        env,
    );
    defer def_ops.deinit();
    for (rule.hyps, ref_exprs) |hyp, ref_expr| {
        if (!try def_ops.matchTemplateWithDefOpening(
            hyp,
            ref_expr,
            bindings,
        )) {
            return error.UnifyMismatch;
        }
    }
    if (!hasOmittedBindings(bindings)) {
        return try requireConcreteBindings(allocator, bindings);
    }

    var mirror = try MirroredTheoremContext.init(allocator, theorem);
    defer mirror.deinit(allocator);

    var to_mirror = std.AutoHashMapUnmanaged(ExprId, ExprId){};
    defer to_mirror.deinit(allocator);

    const mirror_line = try copyExprBetweenTheorems(
        allocator,
        theorem,
        &mirror.theorem,
        line_expr,
        mirror.source_dummy_map,
        &to_mirror,
    );

    const mirror_binders = try allocator.alloc(ExprId, rule.args.len);
    defer allocator.free(mirror_binders);
    var placeholders = std.AutoHashMapUnmanaged(ExprId, usize){};
    defer placeholders.deinit(allocator);

    for (bindings, 0..) |binding, idx| {
        if (binding) |expr_id| {
            mirror_binders[idx] = try copyExprBetweenTheorems(
                allocator,
                theorem,
                &mirror.theorem,
                expr_id,
                mirror.source_dummy_map,
                &to_mirror,
            );
            continue;
        }
        const sort_id = env.sort_names.get(rule.args[idx].sort_name) orelse {
            return error.UnknownSort;
        };
        const placeholder = try mirror.theorem.addDummyVarResolved(
            rule.args[idx].sort_name,
            sort_id,
        );
        mirror_binders[idx] = placeholder;
        try placeholders.put(allocator, placeholder, idx);
    }

    const mirror_concl = try mirror.theorem.instantiateTemplate(
        rule.concl,
        mirror_binders,
    );

    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer checked.deinit(allocator);

    var expected_normalizer = Normalizer.init(
        allocator,
        &mirror.theorem,
        registry,
        env,
        &checked,
    );
    const normalized_expected = try expected_normalizer.normalize(mirror_concl);

    var actual_normalizer = Normalizer.init(
        allocator,
        &mirror.theorem,
        registry,
        env,
        &checked,
    );
    const normalized_actual = try actual_normalizer.normalize(mirror_line);

    var reverse_cache = std.AutoHashMapUnmanaged(ExprId, ExprId){};
    defer reverse_cache.deinit(allocator);
    if (!try matchNormalizedPattern(
        allocator,
        theorem,
        &mirror,
        normalized_expected.result_expr,
        normalized_actual.result_expr,
        &placeholders,
        bindings,
        &reverse_cache,
    )) {
        return error.UnifyMismatch;
    }

    return try requireConcreteBindings(allocator, bindings);
}

pub fn shouldUseAdvancedInference(
    rule_id: u32,
    maybe_view: ?ViewDecl,
    registry: *RewriteRegistry,
) bool {
    if (maybe_view != null) return true;
    return registry.getNormalizeSpec(rule_id) != null;
}

pub fn inferBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    theorem: *TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ProofLine,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
    maybe_view: ?ViewDecl,
    use_advanced_inference: bool,
) ![]const ExprId {
    if (use_advanced_inference) {
        var solver = InferenceSolver.init(
            allocator,
            env,
            theorem,
            registry,
            rule,
            if (maybe_view) |*view| view else null,
        );
        const bindings = solver.solve(
            partial_bindings,
            ref_exprs,
            line_expr,
        ) catch |err| {
            if (maybe_view == null) {
                const fallback = inferBindingsByNormalizedConclusion(
                    allocator,
                    env,
                    registry,
                    theorem,
                    rule,
                    partial_bindings,
                    ref_exprs,
                    line_expr,
                ) catch null;
                if (fallback) |bindings| {
                    try validateResolvedBindings(
                        self,
                        env,
                        theorem,
                        assertion,
                        line,
                        rule,
                        bindings,
                    );
                    return bindings;
                }
            }
            self.setDiagnostic(.{
                .kind = .inference_failed,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .span = line.span,
            });
            return err;
        };
        try validateResolvedBindings(
            self,
            env,
            theorem,
            assertion,
            line,
            rule,
            bindings,
        );
        return bindings;
    }

    return strictInferBindings(
        self,
        allocator,
        env,
        theorem,
        assertion,
        rule,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
    ) catch |err| {
        self.setDiagnostic(.{
            .kind = .inference_failed,
            .err = err,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.rule_name,
            .span = line.span,
        });
        return err;
    };
}

pub fn strictInferBindings(
    self: anytype,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ProofLine,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    line_expr: ExprId,
) ![]const ExprId {
    _ = self;
    _ = line;

    const unify = try Emit.buildRuleUnifyStream(allocator, rule);

    var inference = try InferenceContext.init(
        allocator,
        theorem,
        partial_bindings,
        ref_exprs,
        line_expr,
    );
    defer inference.deinit();

    try UnifyReplay.run(unify, 0, &inference);
    if (inference.ustack.items.len != 0) {
        return error.UnifyStackNotEmpty;
    }
    if (inference.next_hyp != 0) {
        return error.HypCountMismatch;
    }

    const bindings = try allocator.alloc(ExprId, rule.args.len);
    for (0..rule.args.len) |idx| {
        const binding = inference.uheap.items[idx] orelse {
            return error.MissingBinderAssignment;
        };
        try validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        );
        bindings[idx] = binding;
    }
    return bindings;
}

pub fn validateResolvedBindings(
    self: anytype,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: ProofLine,
    rule: *const RuleDecl,
    bindings: []const ExprId,
) !void {
    for (bindings, 0..) |binding, idx| {
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            self.setDiagnostic(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.rule_name,
                .name = rule.arg_names[idx],
                .span = line.span,
            });
            return err;
        };
    }
}

// Inference only solves equalities. We still need the same sort, boundness,
// and dependency checks that explicit parser-side argument parsing performs.
pub fn validateBindingExpr(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expected: ArgInfo,
    expr_id: ExprId,
) !void {
    const info = try exprInfo(env, theorem, theorem_args, expr_id);
    if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
        return error.SortMismatch;
    }
    // Match verifier semantics: bound params require bound exprs,
    // but regular params accept any expression (including bound vars).
    if (expected.bound and !info.bound) return error.BoundnessMismatch;
    // Note: dep checking is deferred to the verifier which checks deps
    // relative to the theorem's own bound variables.
}

pub fn exprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expr_id: ExprId,
) !ExprInfo {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= theorem_args.len) return error.UnknownTheoremVariable;
                const arg = theorem_args[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                    .deps = arg.deps,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                    .deps = dummy.deps,
                };
            },
        },
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            var deps: u55 = 0;
            for (app.args) |arg_id| {
                deps |= (try exprInfo(env, theorem, theorem_args, arg_id)).deps;
            }
            break :blk .{
                .sort_name = env.terms.items[app.term_id].ret_sort_name,
                .bound = false,
                .deps = deps,
            };
        },
    };
}

pub fn hasOmittedBindings(bindings: []const ?ExprId) bool {
    for (bindings) |binding| {
        if (binding == null) return true;
    }
    return false;
}

pub fn requireConcreteBindings(
    allocator: std.mem.Allocator,
    partial_bindings: []const ?ExprId,
) ![]const ExprId {
    const bindings = try allocator.alloc(ExprId, partial_bindings.len);
    for (partial_bindings, 0..) |binding, idx| {
        bindings[idx] = binding orelse return error.MissingBinderAssignment;
    }
    return bindings;
}
