const std = @import("std");
const GlobalEnv = @import("./compiler_env.zig").GlobalEnv;
const RuleDecl = @import("./compiler_env.zig").RuleDecl;
const TemplateExpr = @import("./compiler_rules.zig").TemplateExpr;

/// Which positions of a rule should be normalized after instantiation.
pub const NormalizeSpec = struct {
    concl: bool = false,
    hyp_indices: []const usize = &.{},
};

/// A relation bundle defines an equivalence relation on a sort, with the
/// theorem names needed to compose conversion proofs.
pub const RelationBundle = struct {
    sort_name: []const u8,
    rel_term_name: []const u8,
    refl_name: []const u8,
    trans_name: []const u8,
    symm_name: []const u8,
    transport_name: []const u8,
    /// Resolved lazily from names.
    rel_term_id: ?u32 = null,
    refl_id: ?u32 = null,
    trans_id: ?u32 = null,
    symm_id: ?u32 = null,
    transport_id: ?u32 = null,
};

/// Resolved relation with all IDs known.
pub const ResolvedRelation = struct {
    rel_term_id: u32,
    refl_id: u32,
    trans_id: u32,
    symm_id: u32,
    transport_id: ?u32,
};

/// A rewrite rule: lhs ~ rhs, indexed by the head term_id of lhs.
pub const RewriteRule = struct {
    rule_id: u32,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    num_binders: usize,
    head_term_id: u32,
};

/// A congruence rule for a specific head term.
pub const CongruenceRule = struct {
    rule_id: u32,
    head_term_id: u32,
    num_binders: usize,
};

const LeftUnitRule = struct {
    rule_id: u32,
    reversed: bool,
};

pub const StructuralCombiner = struct {
    unit_term_name: []const u8,
    assoc_name: []const u8,
    comm_name: ?[]const u8,
    idem_name: ?[]const u8,
    unit_term_id: ?u32 = null,
    assoc_id: ?u32 = null,
    comm_id: ?u32 = null,
    idem_id: ?u32 = null,
    left_unit_rule: ?LeftUnitRule = null,
};

pub const ResolvedStructuralCombiner = struct {
    head_term_id: u32,
    unit_term_id: u32,
    assoc_id: u32,
    comm_id: ?u32,
    idem_id: ?u32,
    left_unit_rule_id: u32,
    left_unit_rule_reversed: bool,
};

pub const RewriteRegistry = struct {
    allocator: std.mem.Allocator,
    /// Relation bundles keyed by sort name.
    relations: std.StringHashMap(RelationBundle),
    /// Rewrite rules indexed by LHS head term_id.
    rewrites_by_head: std.AutoHashMap(
        u32,
        std.ArrayListUnmanaged(RewriteRule),
    ),
    /// Congruence rules by head term_id.
    congr_by_head: std.AutoHashMap(u32, CongruenceRule),
    /// Normalize specs by rule_id.
    normalize_specs: std.AutoHashMap(u32, NormalizeSpec),
    /// ACUI structural metadata by combiner head term_id.
    acui_by_head: std.AutoHashMap(u32, StructuralCombiner),

    pub fn init(allocator: std.mem.Allocator) RewriteRegistry {
        return .{
            .allocator = allocator,
            .relations = std.StringHashMap(RelationBundle).init(allocator),
            .rewrites_by_head = std.AutoHashMap(
                u32,
                std.ArrayListUnmanaged(RewriteRule),
            ).init(allocator),
            .congr_by_head = std.AutoHashMap(u32, CongruenceRule).init(
                allocator,
            ),
            .normalize_specs = std.AutoHashMap(u32, NormalizeSpec).init(
                allocator,
            ),
            .acui_by_head = std.AutoHashMap(u32, StructuralCombiner).init(
                allocator,
            ),
        };
    }

    pub fn processAnnotations(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        annotations: []const []const u8,
    ) !void {
        for (annotations) |ann| {
            try self.processOneAnnotation(env, stmt_name, ann);
        }
    }

    fn processOneAnnotation(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        annotation: []const u8,
    ) !void {
        var iter = std.mem.tokenizeScalar(u8, annotation, ' ');
        const directive = iter.next() orelse return;

        if (std.mem.eql(u8, directive, "@relation")) {
            try self.processRelation(&iter);
        } else if (std.mem.eql(u8, directive, "@rewrite")) {
            try self.processRewrite(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@congr")) {
            try self.processCongr(env, stmt_name);
        } else if (std.mem.eql(u8, directive, "@normalize")) {
            try self.processNormalize(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@acui")) {
            try self.processAcui(env, stmt_name, &iter);
        }
    }

    fn processRelation(
        self: *RewriteRegistry,
        iter: *std.mem.TokenIterator(u8, .scalar),
    ) !void {
        const sort_name = iter.next() orelse return;
        const rel_term = iter.next() orelse return;
        const refl = iter.next() orelse return;
        const trans = iter.next() orelse return;
        const symm = iter.next() orelse return;
        const transport = iter.next() orelse return;

        try self.relations.put(sort_name, .{
            .sort_name = sort_name,
            .rel_term_name = rel_term,
            .refl_name = refl,
            .trans_name = trans,
            .symm_name = symm,
            .transport_name = transport,
        });
    }

    fn processRewrite(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .scalar),
    ) !void {
        _ = iter;
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];

        // The conclusion should be of the form `rel(lhs, rhs)` where rel
        // is a registered relation term.
        switch (rule.concl) {
            .app => |app| {
                if (app.args.len != 2) return;
                const lhs = app.args[0];
                const rhs = app.args[1];
                const head_id = getHeadTermId(lhs) orelse return;

                const gop = try self.rewrites_by_head.getOrPut(head_id);
                if (!gop.found_existing) {
                    gop.value_ptr.* = .{};
                }
                try gop.value_ptr.append(self.allocator, .{
                    .rule_id = rule_id,
                    .lhs = lhs,
                    .rhs = rhs,
                    .num_binders = rule.args.len,
                    .head_term_id = head_id,
                });
            },
            else => {},
        }
    }

    fn processCongr(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
    ) !void {
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];

        switch (rule.concl) {
            .app => |app| {
                if (app.args.len != 2) return;
                const head_id = getHeadTermId(app.args[0]) orelse return;
                try self.congr_by_head.put(head_id, .{
                    .rule_id = rule_id,
                    .head_term_id = head_id,
                    .num_binders = rule.args.len,
                });
            },
            else => {},
        }
    }

    fn processNormalize(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .scalar),
    ) !void {
        const rule_id = env.getRuleId(stmt_name) orelse return;

        var concl = false;
        var hyp_indices = std.ArrayListUnmanaged(usize){};

        while (iter.next()) |tok| {
            if (std.mem.eql(u8, tok, "conc")) {
                concl = true;
            } else if (std.mem.startsWith(u8, tok, "hyp")) {
                const idx = std.fmt.parseInt(usize, tok[3..], 10) catch continue;
                try hyp_indices.append(self.allocator, idx);
            }
        }

        try self.normalize_specs.put(rule_id, .{
            .concl = concl,
            .hyp_indices = try hyp_indices.toOwnedSlice(self.allocator),
        });
    }

    fn processAcui(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .scalar),
    ) !void {
        const head_term_id = env.term_names.get(stmt_name) orelse return;

        const assoc_name = iter.next() orelse return;
        const comm_tok = iter.next() orelse return;
        const unit_term_name = iter.next() orelse return;
        const idem_tok = iter.next();

        const comm_name = if (!std.mem.eql(u8, comm_tok, "_"))
            comm_tok
        else
            null;
        const idem_name = if (idem_tok) |tok|
            if (!std.mem.eql(u8, tok, "_")) tok else null
        else
            null;

        try self.acui_by_head.put(head_term_id, .{
            .unit_term_name = unit_term_name,
            .assoc_name = assoc_name,
            .comm_name = comm_name,
            .idem_name = idem_name,
        });
    }

    pub fn getNormalizeSpec(
        self: *const RewriteRegistry,
        rule_id: u32,
    ) ?NormalizeSpec {
        return self.normalize_specs.get(rule_id);
    }

    pub fn getRelationForSort(
        self: *const RewriteRegistry,
        sort_name: []const u8,
    ) ?*const RelationBundle {
        return if (self.relations.getPtr(sort_name)) |ptr| ptr else null;
    }

    pub fn resolveRelation(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        sort_name: []const u8,
    ) ?ResolvedRelation {
        const bundle = self.relations.getPtr(sort_name) orelse return null;

        if (bundle.rel_term_id == null) {
            bundle.rel_term_id = env.term_names.get(bundle.rel_term_name);
        }
        if (bundle.refl_id == null) {
            bundle.refl_id = env.getRuleId(bundle.refl_name);
        }
        if (bundle.trans_id == null) {
            bundle.trans_id = env.getRuleId(bundle.trans_name);
        }
        if (bundle.symm_id == null) {
            bundle.symm_id = env.getRuleId(bundle.symm_name);
        }
        const has_transport = !std.mem.eql(u8, bundle.transport_name, "_");
        if (has_transport and bundle.transport_id == null) {
            bundle.transport_id = env.getRuleId(bundle.transport_name);
        }

        return .{
            .rel_term_id = bundle.rel_term_id orelse return null,
            .refl_id = bundle.refl_id orelse return null,
            .trans_id = bundle.trans_id orelse return null,
            .symm_id = bundle.symm_id orelse return null,
            .transport_id = if (has_transport)
                (bundle.transport_id orelse return null)
            else
                null,
        };
    }

    pub fn getRewriteRules(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) []const RewriteRule {
        if (self.rewrites_by_head.get(head_term_id)) |list| {
            return list.items;
        }
        return &.{};
    }

    pub fn getCongruenceRule(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) ?CongruenceRule {
        return self.congr_by_head.get(head_term_id);
    }

    pub fn hasStructuralCombiner(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) bool {
        return self.acui_by_head.contains(head_term_id);
    }

    pub fn resolveStructuralCombiner(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        head_term_id: u32,
    ) ?ResolvedStructuralCombiner {
        const combiner = self.acui_by_head.getPtr(head_term_id) orelse return null;
        const term_decl = if (head_term_id < env.terms.items.len)
            &env.terms.items[head_term_id]
        else
            return null;
        const relation = self.resolveRelation(env, term_decl.ret_sort_name) orelse {
            return null;
        };

        if (combiner.unit_term_id == null) {
            combiner.unit_term_id = env.term_names.get(combiner.unit_term_name);
        }
        if (combiner.assoc_id == null) {
            combiner.assoc_id = env.getRuleId(combiner.assoc_name);
        }
        if (combiner.comm_id == null and combiner.comm_name != null) {
            combiner.comm_id = env.getRuleId(combiner.comm_name.?);
        }
        if (combiner.idem_id == null and combiner.idem_name != null) {
            combiner.idem_id = env.getRuleId(combiner.idem_name.?);
        }
        if (combiner.left_unit_rule == null) {
            combiner.left_unit_rule = findLeftUnitRule(
                env,
                relation.rel_term_id,
                head_term_id,
                combiner.unit_term_id orelse return null,
            );
        }

        const left_unit = combiner.left_unit_rule orelse return null;
        return .{
            .head_term_id = head_term_id,
            .unit_term_id = combiner.unit_term_id orelse return null,
            .assoc_id = combiner.assoc_id orelse return null,
            .comm_id = combiner.comm_id,
            .idem_id = combiner.idem_id,
            .left_unit_rule_id = left_unit.rule_id,
            .left_unit_rule_reversed = left_unit.reversed,
        };
    }
};

fn findLeftUnitRule(
    env: *const GlobalEnv,
    rel_term_id: u32,
    head_term_id: u32,
    unit_term_id: u32,
) ?LeftUnitRule {
    for (env.rules.items, 0..) |rule, rule_idx| {
        const app = switch (rule.concl) {
            .app => |value| value,
            else => continue,
        };
        if (app.term_id != rel_term_id or app.args.len != 2) continue;

        if (isLeftUnitPattern(app.args[0], app.args[1], head_term_id, unit_term_id)) {
            return .{
                .rule_id = @intCast(rule_idx),
                .reversed = false,
            };
        }
        if (isLeftUnitPattern(app.args[1], app.args[0], head_term_id, unit_term_id)) {
            return .{
                .rule_id = @intCast(rule_idx),
                .reversed = true,
            };
        }
    }
    return null;
}

fn isLeftUnitPattern(
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    head_term_id: u32,
    unit_term_id: u32,
) bool {
    const lhs_app = switch (lhs) {
        .app => |value| value,
        else => return false,
    };
    const unit_app = switch (lhs_app.args[0]) {
        .app => |value| value,
        else => return false,
    };
    const rhs_binder = switch (rhs) {
        .binder => |value| value,
        else => return false,
    };
    const lhs_rhs_binder = switch (lhs_app.args[1]) {
        .binder => |value| value,
        else => return false,
    };
    return lhs_app.term_id == head_term_id and
        lhs_app.args.len == 2 and
        unit_app.term_id == unit_term_id and
        unit_app.args.len == 0 and
        lhs_rhs_binder == rhs_binder;
}

fn getHeadTermId(template: TemplateExpr) ?u32 {
    return switch (template) {
        .app => |app| app.term_id,
        .binder => null,
    };
}
