const std = @import("std");
const TermDecl = @import("./compiler_env.zig").TermDecl;
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const ExprId = @import("./compiler_expr.zig").ExprId;
const TheoremContext = @import("./compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;

pub const OpenPolicy = enum {
    all_defs,
    abbrev_only,
};

pub const ConversionPlan = union(enum) {
    refl,
    unfold_lhs: struct {
        witness: ExprId,
        next: *const ConversionPlan,
    },
    unfold_rhs: struct {
        witness: ExprId,
        next: *const ConversionPlan,
    },
    cong: struct {
        children: []const *const ConversionPlan,
    },
};

const BoundPair = struct {
    lhs: ExprId,
    rhs: ExprId,
};

const DummyBinding = struct {
    slot: usize,
    actual: ExprId,
};

const PatternDummyInfo = struct {
    sort_name: []const u8,
};

const PatternExpr = union(enum) {
    binder: usize,
    dummy: usize,
    app: App,

    const App = struct {
        term_id: u32,
        args: []const *const PatternExpr,
    };
};

const ConcreteVarInfo = struct {
    sort_name: []const u8,
    bound: bool,
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    policy: OpenPolicy,
    open_cache: std.AutoHashMap(ExprId, ExprId),
    pattern_dummy_infos: std.ArrayListUnmanaged(PatternDummyInfo) = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        policy: OpenPolicy,
    ) Context {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .policy = policy,
            .open_cache = std.AutoHashMap(ExprId, ExprId).init(allocator),
        };
    }

    pub fn deinit(self: *Context) void {
        self.open_cache.deinit();
        self.pattern_dummy_infos.deinit(self.allocator);
    }

    pub fn openConcreteDef(self: *Context, expr_id: ExprId) !?ExprId {
        if (self.open_cache.get(expr_id)) |cached| {
            return cached;
        }

        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return null,
        };
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const binders = try self.allocator.alloc(
            ExprId,
            term.args.len + term.dummy_args.len,
        );
        @memcpy(binders[0..term.args.len], app.args);
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const sort_id = self.env.sort_names.get(dummy_arg.sort_name) orelse {
                return error.UnknownSort;
            };
            binders[term.args.len + idx] = try self.theorem.addDummyVarResolved(
                dummy_arg.sort_name,
                sort_id,
            );
        }

        const opened = try self.theorem.instantiateTemplate(body, binders);
        if (term.dummy_args.len == 0) {
            try self.open_cache.put(expr_id, opened);
        }
        return opened;
    }

    pub fn exprMatchesByDefOpening(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) !bool {
        var pairs = std.ArrayListUnmanaged(BoundPair){};
        defer pairs.deinit(self.allocator);
        return try self.exprMatchesRec(lhs, rhs, &pairs);
    }

    pub fn exprMatchesAlphaOnly(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) !bool {
        var pairs = std.ArrayListUnmanaged(BoundPair){};
        defer pairs.deinit(self.allocator);
        return try self.exprMatchesAlphaRec(lhs, rhs, &pairs);
    }

    pub fn matchTemplateWithDefOpening(
        self: *Context,
        template: TemplateExpr,
        actual: ExprId,
        bindings: []?ExprId,
    ) !bool {
        const pattern = try self.patternFromTemplate(template);
        var dummy_bindings = std.ArrayListUnmanaged(DummyBinding){};
        defer dummy_bindings.deinit(self.allocator);
        return try self.matchPattern(
            pattern,
            actual,
            bindings,
            &dummy_bindings,
        );
    }

    pub fn planConversionByDefOpening(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) !?*const ConversionPlan {
        return try self.planConversionRec(lhs, rhs);
    }

    fn planConversionRec(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) !?*const ConversionPlan {
        if (lhs == rhs) {
            return try self.allocPlan(.refl);
        }

        if (try self.openConcreteDef(lhs)) |opened_lhs| {
            if (try self.exprMatchesAlphaOnly(opened_lhs, rhs)) {
                return try self.allocPlan(.{ .unfold_lhs = .{
                    .witness = rhs,
                    .next = try self.allocPlan(.refl),
                } });
            }
            if (try self.planConversionRec(opened_lhs, rhs)) |next| {
                return try self.allocPlan(.{ .unfold_lhs = .{
                    .witness = opened_lhs,
                    .next = next,
                } });
            }
        }

        if (try self.openConcreteDef(rhs)) |opened_rhs| {
            if (try self.exprMatchesAlphaOnly(lhs, opened_rhs)) {
                return try self.allocPlan(.{ .unfold_rhs = .{
                    .witness = lhs,
                    .next = try self.allocPlan(.refl),
                } });
            }
            if (try self.planConversionRec(lhs, opened_rhs)) |next| {
                return try self.allocPlan(.{ .unfold_rhs = .{
                    .witness = opened_rhs,
                    .next = next,
                } });
            }
        }

        const lhs_node = self.theorem.interner.node(lhs);
        const rhs_node = self.theorem.interner.node(rhs);
        const lhs_app = switch (lhs_node.*) {
            .app => |value| value,
            .variable => return null,
        };
        const rhs_app = switch (rhs_node.*) {
            .app => |value| value,
            .variable => return null,
        };
        if (lhs_app.term_id != rhs_app.term_id or
            lhs_app.args.len != rhs_app.args.len)
        {
            return null;
        }

        const children = try self.allocator.alloc(
            *const ConversionPlan,
            lhs_app.args.len,
        );
        for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
            children[idx] = try self.planConversionRec(lhs_arg, rhs_arg) orelse {
                return null;
            };
        }
        return try self.allocPlan(.{ .cong = .{ .children = children } });
    }

    fn exprMatchesRec(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
        pairs: *std.ArrayListUnmanaged(BoundPair),
    ) !bool {
        const checkpoint = pairs.items.len;
        if (try self.exprMatchesAlphaRec(lhs, rhs, pairs)) {
            return true;
        }
        pairs.shrinkRetainingCapacity(checkpoint);

        const lhs_node = self.theorem.interner.node(lhs);
        const rhs_node = self.theorem.interner.node(rhs);
        if (lhs_node.* == .app and rhs_node.* == .app) {
            const lhs_app = lhs_node.app;
            const rhs_app = rhs_node.app;
            if (lhs_app.term_id == rhs_app.term_id and
                lhs_app.args.len == rhs_app.args.len)
            {
                const child_checkpoint = pairs.items.len;
                for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                    if (!try self.exprMatchesRec(lhs_arg, rhs_arg, pairs)) {
                        pairs.shrinkRetainingCapacity(child_checkpoint);
                        break;
                    }
                } else {
                    return true;
                }
                pairs.shrinkRetainingCapacity(checkpoint);
            }
        }

        if (try self.openConcreteDef(lhs)) |opened_lhs| {
            if (try self.exprMatchesRec(opened_lhs, rhs, pairs)) {
                return true;
            }
            pairs.shrinkRetainingCapacity(checkpoint);
        }

        if (try self.openConcreteDef(rhs)) |opened_rhs| {
            if (try self.exprMatchesRec(lhs, opened_rhs, pairs)) {
                return true;
            }
            pairs.shrinkRetainingCapacity(checkpoint);
        }
        return false;
    }

    fn exprMatchesAlphaRec(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
        pairs: *std.ArrayListUnmanaged(BoundPair),
    ) !bool {
        if (lhs == rhs) return true;

        const lhs_node = self.theorem.interner.node(lhs);
        const rhs_node = self.theorem.interner.node(rhs);
        switch (lhs_node.*) {
            .variable => switch (rhs_node.*) {
                .variable => return try self.matchConcreteBoundVar(lhs, rhs, pairs),
                .app => return false,
            },
            .app => |lhs_app| switch (rhs_node.*) {
                .variable => return false,
                .app => |rhs_app| {
                    if (lhs_app.term_id != rhs_app.term_id or
                        lhs_app.args.len != rhs_app.args.len)
                    {
                        return false;
                    }
                    const checkpoint = pairs.items.len;
                    for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                        if (!try self.exprMatchesAlphaRec(lhs_arg, rhs_arg, pairs)) {
                            pairs.shrinkRetainingCapacity(checkpoint);
                            return false;
                        }
                    }
                    return true;
                },
            },
        }
    }

    fn matchConcreteBoundVar(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
        pairs: *std.ArrayListUnmanaged(BoundPair),
    ) !bool {
        const lhs_info = try self.getConcreteVarInfo(lhs);
        const rhs_info = try self.getConcreteVarInfo(rhs);
        if (!lhs_info.bound or !rhs_info.bound) return false;
        if (!std.mem.eql(u8, lhs_info.sort_name, rhs_info.sort_name)) {
            return false;
        }

        for (pairs.items) |pair| {
            if (pair.lhs == lhs) return pair.rhs == rhs;
            if (pair.rhs == rhs) return pair.lhs == lhs;
        }
        try pairs.append(self.allocator, .{ .lhs = lhs, .rhs = rhs });
        return true;
    }

    fn getConcreteVarInfo(self: *Context, expr_id: ExprId) !ConcreteVarInfo {
        const node = self.theorem.interner.node(expr_id);
        const var_id = switch (node.*) {
            .variable => |value| value,
            .app => return error.ExpectedVariable,
        };
        return switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= self.theorem.arg_infos.len) {
                    return error.UnknownTheoremVariable;
                }
                const arg = self.theorem.arg_infos[idx];
                break :blk .{
                    .sort_name = arg.sort_name,
                    .bound = arg.bound,
                };
            },
            .dummy_var => |idx| blk: {
                if (idx >= self.theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = self.theorem.theorem_dummies.items[idx];
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                };
            },
        };
    }

    fn matchPattern(
        self: *Context,
        pattern: *const PatternExpr,
        actual: ExprId,
        bindings: []?ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) !bool {
        switch (pattern.*) {
            .binder => |idx| {
                if (idx >= bindings.len) return false;
                if (bindings[idx]) |existing| {
                    return try self.exprMatchesByDefOpening(existing, actual);
                }
                bindings[idx] = actual;
                return true;
            },
            .dummy => |slot| {
                const info = self.pattern_dummy_infos.items[slot];
                return try self.matchPatternDummy(
                    slot,
                    info,
                    actual,
                    dummy_bindings,
                );
            },
            .app => |app| {
                const actual_node = self.theorem.interner.node(actual);
                if (actual_node.* == .app) {
                    const actual_app = actual_node.app;
                    if (actual_app.term_id == app.term_id and
                        actual_app.args.len == app.args.len)
                    {
                        const saved_bindings = try self.allocator.dupe(
                            ?ExprId,
                            bindings,
                        );
                        defer self.allocator.free(saved_bindings);
                        const dummy_checkpoint = dummy_bindings.items.len;
                        for (app.args, actual_app.args) |pat_arg, actual_arg| {
                            if (!try self.matchPattern(
                                pat_arg,
                                actual_arg,
                                bindings,
                                dummy_bindings,
                            )) {
                                @memcpy(bindings, saved_bindings);
                                dummy_bindings.shrinkRetainingCapacity(
                                    dummy_checkpoint,
                                );
                                return false;
                            }
                        }
                        return true;
                    }
                }

                const saved_bindings = try self.allocator.dupe(
                    ?ExprId,
                    bindings,
                );
                defer self.allocator.free(saved_bindings);
                const dummy_checkpoint = dummy_bindings.items.len;
                if (try self.openConcreteDef(actual)) |opened_actual| {
                    if (try self.matchPattern(
                        pattern,
                        opened_actual,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }

                if (try self.openPatternApp(app)) |opened_pattern| {
                    if (try self.matchPattern(
                        opened_pattern,
                        actual,
                        bindings,
                        dummy_bindings,
                    )) {
                        return true;
                    }
                    @memcpy(bindings, saved_bindings);
                    dummy_bindings.shrinkRetainingCapacity(dummy_checkpoint);
                }
                return false;
            },
        }
    }

    fn matchPatternDummy(
        self: *Context,
        slot: usize,
        info: PatternDummyInfo,
        actual: ExprId,
        dummy_bindings: *std.ArrayListUnmanaged(DummyBinding),
    ) !bool {
        const actual_info = try self.getConcreteVarInfo(actual);
        if (!actual_info.bound) return false;
        if (!std.mem.eql(u8, info.sort_name, actual_info.sort_name)) {
            return false;
        }

        for (dummy_bindings.items) |binding| {
            if (binding.slot == slot) return binding.actual == actual;
        }
        try dummy_bindings.append(self.allocator, .{
            .slot = slot,
            .actual = actual,
        });
        return true;
    }

    fn patternFromTemplate(
        self: *Context,
        template: TemplateExpr,
    ) !*const PatternExpr {
        return try self.patternFromTemplateSubst(template, null);
    }

    fn patternFromTemplateSubst(
        self: *Context,
        template: TemplateExpr,
        subst: ?[]const *const PatternExpr,
    ) !*const PatternExpr {
        switch (template) {
            .binder => |idx| {
                if (subst) |args| {
                    if (idx >= args.len) return error.TemplateBinderOutOfRange;
                    return args[idx];
                }
                return try self.allocPattern(.{ .binder = idx });
            },
            .app => |app| {
                const args = try self.allocator.alloc(
                    *const PatternExpr,
                    app.args.len,
                );
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.patternFromTemplateSubst(arg, subst);
                }
                return try self.allocPattern(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        }
    }

    fn openPatternApp(
        self: *Context,
        app: PatternExpr.App,
    ) !?*const PatternExpr {
        const term = self.getOpenableTerm(app.term_id) orelse return null;
        const body = term.body orelse return null;

        const subst = try self.allocator.alloc(
            *const PatternExpr,
            term.args.len + term.dummy_args.len,
        );
        @memcpy(subst[0..term.args.len], app.args);
        for (term.dummy_args, 0..) |dummy_arg, idx| {
            const slot = self.pattern_dummy_infos.items.len;
            try self.pattern_dummy_infos.append(self.allocator, .{
                .sort_name = dummy_arg.sort_name,
            });
            subst[term.args.len + idx] = try self.allocPattern(
                .{ .dummy = slot },
            );
        }
        return try self.patternFromTemplateSubst(body, subst);
    }

    fn getOpenableTerm(self: *const Context, term_id: u32) ?*const TermDecl {
        if (term_id >= self.env.terms.items.len) return null;
        const term = &self.env.terms.items[term_id];
        if (!term.is_def or term.body == null) return null;
        return switch (self.policy) {
            .all_defs => term,
            .abbrev_only => if (term.is_abbrev) term else null,
        };
    }

    fn allocPattern(self: *Context, pattern: PatternExpr) !*const PatternExpr {
        const node = try self.allocator.create(PatternExpr);
        node.* = pattern;
        return node;
    }

    fn allocPlan(
        self: *Context,
        plan: ConversionPlan,
    ) !*const ConversionPlan {
        const node = try self.allocator.create(ConversionPlan);
        node.* = plan;
        return node;
    }
};
