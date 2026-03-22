const std = @import("std");
const ExprId = @import("./compiler_expr.zig").ExprId;
const ExprNode = @import("./compiler_expr.zig").ExprNode;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const TermDecl = @import("./compiler_env.zig").TermDecl;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner = @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const SExpr = @import("./transparent_expr.zig");
const SExprId = SExpr.SExprId;
const SExprNode = SExpr.SExprNode;
const SExprInterner = SExpr.SExprInterner;
const FreshId = SExpr.FreshId;

/// Context for symbolic transparent operations. Scoped to one solver
/// invocation; owns the symbolic interner and occurrence counter.
pub const Context = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    interner: SExprInterner,
    next_occurrence: u32 = 0,
    step_limit: usize = 100,

    /// Cache from ExprId to its lifted SExprId (for `liftConcrete`).
    lift_cache: std.AutoHashMap(ExprId, SExprId),

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        env: *const GlobalEnv,
    ) Context {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .interner = SExprInterner.init(allocator),
            .lift_cache = std.AutoHashMap(ExprId, SExprId).init(allocator),
        };
    }

    pub fn deinit(self: *Context) void {
        self.interner.deinit();
        self.lift_cache.deinit();
    }

    // ---------------------------------------------------------------
    // Lifting: ExprId → SExprId (wraps concrete exprs as symbolic)
    // ---------------------------------------------------------------

    /// Lift a concrete ExprId into the symbolic domain as `Concrete(expr_id)`.
    /// This is the cheapest operation — it does not expose any structure.
    pub fn liftConcrete(self: *Context, expr_id: ExprId) !SExprId {
        if (self.lift_cache.get(expr_id)) |cached| return cached;
        const sid = try self.interner.internConcrete(expr_id);
        try self.lift_cache.put(expr_id, sid);
        return sid;
    }

    // ---------------------------------------------------------------
    // One-step symbolic def opening
    // ---------------------------------------------------------------

    /// Symbolically unfold a concrete expression one step. If the expression
    /// is an application of a transparent `def`, returns an `SExprId`
    /// representing the definition body with:
    ///   - visible arguments as `Concrete(arg_expr_id)`
    ///   - hidden dummy binders as `Fresh(occurrence, slot, sort)`
    ///
    /// Returns `null` if the expression is not an openable def application.
    /// Each call allocates a new `occurrence` id for freshness scoping.
    pub fn openDefSymbolic(
        self: *Context,
        expr_id: ExprId,
    ) !?SExprId {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return null,
        };

        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const occurrence = self.next_occurrence;
        self.next_occurrence += 1;

        // Build substitution: visible args → Concrete, hidden dummies → Fresh
        const subst = try self.allocator.alloc(
            SExprId,
            term.args.len + term.dummy_args.len,
        );
        defer self.allocator.free(subst);

        for (app.args, 0..) |arg, idx| {
            subst[idx] = try self.liftConcrete(arg);
        }
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            subst[term.args.len + idx] = try self.interner.internFresh(.{
                .occurrence = occurrence,
                .slot = @intCast(idx),
                .sort_name = dummy_arg.sort_name,
            });
        }

        return try self.instantiateTemplateSymbolic(body, subst);
    }

    /// Instantiate a TemplateExpr into a symbolic SExprId using the given
    /// substitution (binder index → SExprId).
    fn instantiateTemplateSymbolic(
        self: *Context,
        template: TemplateExpr,
        subst: []const SExprId,
    ) !SExprId {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= subst.len) return error.TemplateBinderOutOfRange;
                break :blk subst[idx];
            },
            .app => |app| blk: {
                const args = try self.allocator.alloc(SExprId, app.args.len);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.instantiateTemplateSymbolic(arg, subst);
                }
                break :blk try self.interner.internAppOwned(app.term_id, args);
            },
        };
    }

    // ---------------------------------------------------------------
    // Weak-head transparent exposure (WHNF)
    // ---------------------------------------------------------------

    /// The result of weak-head exposure: either we exposed symbolic structure,
    /// or the expression was already in WHNF (head is not a transparent def).
    pub const ExposedExpr = union(enum) {
        /// The expression was not a transparent def, or we hit the step limit.
        /// The original concrete ExprId is returned unchanged.
        opaque_concrete: ExprId,
        /// We exposed one or more layers. The result is symbolic.
        exposed: SExprId,
    };

    /// Repeatedly unfold at the head until the head is not a transparent
    /// definition or the step budget is exceeded. This is weak-head only —
    /// it does not recurse into arguments.
    pub fn whnfTransparent(
        self: *Context,
        expr_id: ExprId,
    ) !ExposedExpr {
        var current_concrete = expr_id;
        var steps: usize = 0;

        while (steps < self.step_limit) : (steps += 1) {
            const opened = try self.openDefSymbolic(current_concrete) orelse {
                if (steps == 0) return .{ .opaque_concrete = expr_id };
                return .{ .exposed = try self.liftConcrete(current_concrete) };
            };

            // Check if the result is itself a concrete expression we can
            // continue unfolding.
            const opened_node = self.interner.node(opened);
            switch (opened_node.*) {
                .concrete => |inner_id| {
                    current_concrete = inner_id;
                    // Continue trying to unfold.
                },
                .app, .fresh => {
                    // We've exposed symbolic structure; the head is now
                    // either a non-def term application or a fresh variable.
                    return .{ .exposed = opened };
                },
            }
        }

        // Step limit exceeded — return what we have.
        return .{ .opaque_concrete = current_concrete };
    }

    /// Get the head term_id of a concrete expression, or null if it's a variable.
    pub fn concreteHeadTermId(self: *const Context, expr_id: ExprId) ?u32 {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| app.term_id,
            .variable => null,
        };
    }

    /// Get the head term_id of a symbolic expression, or null.
    pub fn symbolicHeadTermId(self: *const Context, sexpr_id: SExprId) ?u32 {
        const node = self.interner.node(sexpr_id);
        return switch (node.*) {
            .app => |app| app.term_id,
            .concrete => |expr_id| self.concreteHeadTermId(expr_id),
            .fresh => null,
        };
    }

    // ---------------------------------------------------------------
    // ACUI-specific transparent exposure
    // ---------------------------------------------------------------

    /// Transparently expose an expression through an ACUI combiner.
    ///
    /// Given an expression and the ACUI combiner's head_term_id and
    /// unit_term_id:
    ///   1. Weak-head expose the expression.
    ///   2. If the exposed head is the ACUI combiner, recurse into children.
    ///   3. If the exposed head is the ACUI unit, return no items.
    ///   4. Otherwise return the expression as one atomic item.
    ///
    /// Returns a list of atomic SExprId items (the ACUI "leaves").
    pub fn exposeAcui(
        self: *Context,
        expr_id: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) ![]SExprId {
        var items = std.ArrayListUnmanaged(SExprId){};
        try self.collectAcuiItems(
            expr_id,
            head_term_id,
            unit_term_id,
            &items,
            0,
        );
        return try items.toOwnedSlice(self.allocator);
    }

    const AcuiError = std.mem.Allocator.Error || error{TemplateBinderOutOfRange, TooManySymbolicExprs};

    fn collectAcuiItems(
        self: *Context,
        expr_id: ExprId,
        head_term_id: u32,
        unit_term_id: u32,
        items: *std.ArrayListUnmanaged(SExprId),
        depth: usize,
    ) AcuiError!void {
        if (depth > self.step_limit) {
            try items.append(self.allocator, try self.liftConcrete(expr_id));
            return;
        }

        // First, try the concrete expression directly.
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .app => |app| {
                if (app.term_id == head_term_id) {
                    // It's the ACUI combiner — recurse into children.
                    // Binary combiner: args[0] and args[1].
                    for (app.args) |arg| {
                        try self.collectAcuiItems(
                            arg,
                            head_term_id,
                            unit_term_id,
                            items,
                            depth + 1,
                        );
                    }
                    return;
                }
                if (app.term_id == unit_term_id and app.args.len == 0) {
                    // It's the ACUI unit — contributes nothing.
                    return;
                }
            },
            .variable => {},
        }

        // Try transparent unfolding.
        const opened = try self.openDefSymbolic(expr_id) orelse {
            // Opaque — treat as one atomic item.
            try items.append(self.allocator, try self.liftConcrete(expr_id));
            return;
        };

        // Check if the unfolded form exposes the combiner or unit.
        try self.collectAcuiItemsSymbolic(
            opened,
            head_term_id,
            unit_term_id,
            items,
            depth + 1,
        );
    }

    fn collectAcuiItemsSymbolic(
        self: *Context,
        sexpr_id: SExprId,
        head_term_id: u32,
        unit_term_id: u32,
        items: *std.ArrayListUnmanaged(SExprId),
        depth: usize,
    ) AcuiError!void {
        if (depth > self.step_limit) {
            try items.append(self.allocator, sexpr_id);
            return;
        }

        const snode = self.interner.node(sexpr_id);
        switch (snode.*) {
            .app => |app| {
                if (app.term_id == head_term_id) {
                    for (app.args) |arg| {
                        try self.collectAcuiItemsSymbolic(
                            arg,
                            head_term_id,
                            unit_term_id,
                            items,
                            depth + 1,
                        );
                    }
                    return;
                }
                if (app.term_id == unit_term_id and app.args.len == 0) {
                    return;
                }
            },
            .concrete => |expr_id| {
                // Recurse back into concrete domain — might be further
                // unfoldable.
                return try self.collectAcuiItems(
                    expr_id,
                    head_term_id,
                    unit_term_id,
                    items,
                    depth + 1,
                );
            },
            .fresh => {},
        }

        // Atomic item.
        try items.append(self.allocator, sexpr_id);
    }

    // ---------------------------------------------------------------
    // Helpers
    // ---------------------------------------------------------------

    fn getOpenableTerm(self: *const Context, term_id: u32) ?*const TermDecl {
        if (term_id >= self.env.terms.items.len) return null;
        const term = &self.env.terms.items[term_id];
        if (!term.is_def or term.body == null) return null;
        return term;
    }
};
