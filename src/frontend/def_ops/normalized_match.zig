const std = @import("std");
const ExprId = @import("../compiler_expr.zig").ExprId;
const TheoremContext = @import("../compiler_expr.zig").TheoremContext;
const TemplateExpr = @import("../compiler_rules.zig").TemplateExpr;
const ArgInfo = @import("../../trusted/parse.zig").ArgInfo;
const MirrorSupport = @import("./mirror_support.zig");
const Types = @import("./types.zig");
const MatchState = @import("./match_state.zig");
const SharedContext = @import("./shared_context.zig").SharedContext;
const SymbolicEngine = @import("./symbolic_engine.zig").SymbolicEngine;

const MirroredTheoremContext = MirrorSupport.MirroredTheoremContext;
const copyExprBetweenTheorems = MirrorSupport.copyExprBetweenTheorems;
const BoundValue = Types.BoundValue;
const BindingSeed = Types.BindingSeed;
const SymbolicDummyInfo = Types.SymbolicDummyInfo;
const SymbolicExpr = Types.SymbolicExpr;
const MatchSeedState = Types.MatchSeedState;
const WitnessMap = Types.WitnessMap;
const WitnessSlotMap = Types.WitnessSlotMap;
const ProvisionalWitnessInfoMap = Types.ProvisionalWitnessInfoMap;
const MaterializedWitnessInfoMap = Types.MaterializedWitnessInfoMap;
const MatchSession = MatchState.MatchSession;

const NormalizedPlaceholderTarget = union(enum) {
    binder: usize,
    dummy: usize,
};

const NormalizedView = struct {
    mirror: MirroredTheoremContext,
    to_mirror: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,
    placeholder_targets: std.AutoHashMapUnmanaged(
        ExprId,
        NormalizedPlaceholderTarget,
    ) = .empty,
    mirror_binders: []ExprId,
    binder_status: []u8,
    dummy_values: []?ExprId,

    fn init(session: *RuleMatchSession) !NormalizedView {
        var mirror = try MirroredTheoremContext.init(
            session.shared.allocator,
            session.shared.theorem,
        );
        errdefer mirror.deinit(session.shared.allocator);

        const mirror_binders = try session.shared.allocator.alloc(
            ExprId,
            session.state.bindings.len,
        );
        errdefer session.shared.allocator.free(mirror_binders);
        const binder_status = try session.shared.allocator.alloc(
            u8,
            session.state.bindings.len,
        );
        errdefer session.shared.allocator.free(binder_status);
        const dummy_values = try session.shared.allocator.alloc(
            ?ExprId,
            session.state.symbolic_dummy_infos.items.len,
        );
        errdefer session.shared.allocator.free(dummy_values);

        @memset(binder_status, 0);
        @memset(dummy_values, null);

        var view = NormalizedView{
            .mirror = mirror,
            .mirror_binders = mirror_binders,
            .binder_status = binder_status,
            .dummy_values = dummy_values,
        };
        errdefer view.deinit(session.shared.allocator);

        for (0..session.state.bindings.len) |idx| {
            _ = try view.ensureMirrorBinder(session, idx);
        }
        return view;
    }

    fn deinit(
        self: *NormalizedView,
        allocator: std.mem.Allocator,
    ) void {
        self.to_mirror.deinit(allocator);
        self.placeholder_targets.deinit(allocator);
        allocator.free(self.mirror_binders);
        allocator.free(self.binder_status);
        allocator.free(self.dummy_values);
        self.mirror.deinit(allocator);
    }

    fn ensureMirrorBinder(
        self: *NormalizedView,
        session: *RuleMatchSession,
        idx: usize,
    ) anyerror!ExprId {
        if (idx >= self.mirror_binders.len or idx >= session.rule_args.len) {
            return error.TemplateBinderOutOfRange;
        }
        switch (self.binder_status[idx]) {
            2 => return self.mirror_binders[idx],
            1 => return error.CyclicSymbolicBinding,
            else => {},
        }

        self.binder_status[idx] = 1;
        errdefer self.binder_status[idx] = 0;

        const value = if (session.state.bindings[idx]) |bound| blk: {
            break :blk try session.boundValueToMirror(bound, self);
        } else blk: {
            const sort_id = session.shared.env.sort_names.get(
                session.rule_args[idx].sort_name,
            ) orelse return error.UnknownSort;
            // Mirror-only allocation: placeholder in temporary mirror context,
            // not the real theorem. Does not consume real dependency slots.
            const placeholder = try self.mirror.theorem
                .addPlaceholderDummyVarResolved(
                    session.rule_args[idx].sort_name,
                    sort_id,
                );
            try self.placeholder_targets.put(
                session.shared.allocator,
                placeholder,
                .{ .binder = idx },
            );
            break :blk placeholder;
        };
        self.mirror_binders[idx] = value;
        self.binder_status[idx] = 2;
        return value;
    }

    fn ensureMirrorDummy(
        self: *NormalizedView,
        session: *RuleMatchSession,
        slot: usize,
    ) anyerror!ExprId {
        if (slot >= self.dummy_values.len) return error.UnknownDummyVar;
        if (self.dummy_values[slot]) |existing| return existing;

        var symbolic_engine = session.engine();
        if (symbolic_engine.currentWitnessExpr(slot, &session.state)) |witness| {
            if (!symbolic_engine.isProvisionalWitnessExpr(
                witness,
                &session.state,
            )) {
                const copied = try copyExprBetweenTheorems(
                    session.shared.allocator,
                    session.shared.theorem,
                    &self.mirror.theorem,
                    witness,
                    self.mirror.source_dummy_map,
                    &self.to_mirror,
                );
                self.dummy_values[slot] = copied;
                return copied;
            }
        }

        const info = session.state.symbolic_dummy_infos.items[slot];
        const sort_id = session.shared.env.sort_names.get(info.sort_name) orelse return error.UnknownSort;
        // Mirror-only allocation: placeholder for symbolic dummy in temporary
        // mirror context, not the real theorem. Does not consume real dependency slots.
        const placeholder = try self.mirror.theorem
            .addPlaceholderDummyVarResolved(
                info.sort_name,
                sort_id,
            );
        try self.placeholder_targets.put(
            session.shared.allocator,
            placeholder,
            .{ .dummy = slot },
        );
        self.dummy_values[slot] = placeholder;
        return placeholder;
    }
};

fn cloneWitnessMap(
    allocator: std.mem.Allocator,
    map: WitnessMap,
) !WitnessMap {
    var clone: WitnessMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

fn cloneWitnessSlotMap(
    allocator: std.mem.Allocator,
    map: WitnessSlotMap,
) !WitnessSlotMap {
    var clone: WitnessSlotMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

fn cloneProvisionalWitnessInfoMap(
    allocator: std.mem.Allocator,
    map: ProvisionalWitnessInfoMap,
) !ProvisionalWitnessInfoMap {
    var clone: ProvisionalWitnessInfoMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

fn cloneMaterializedWitnessInfoMap(
    allocator: std.mem.Allocator,
    map: MaterializedWitnessInfoMap,
) !MaterializedWitnessInfoMap {
    var clone: MaterializedWitnessInfoMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub const RuleMatchSession = struct {
    shared: *SharedContext,
    rule_args: []const ArgInfo,
    state: MatchSession,

    pub fn init(
        shared: *SharedContext,
        rule_args: []const ArgInfo,
        seeds: []const BindingSeed,
    ) anyerror!RuleMatchSession {
        return try initWithMetadata(shared, rule_args, seeds, null);
    }

    pub fn initFromSeedState(
        shared: *SharedContext,
        rule_args: []const ArgInfo,
        seed_state: *const MatchSeedState,
    ) anyerror!RuleMatchSession {
        return try initWithMetadata(
            shared,
            rule_args,
            seed_state.bindings,
            seed_state,
        );
    }

    fn initWithMetadata(
        shared: *SharedContext,
        rule_args: []const ArgInfo,
        seeds: []const BindingSeed,
        seed_state: ?*const MatchSeedState,
    ) anyerror!RuleMatchSession {
        var symbolic_engine = SymbolicEngine{ .shared = shared };
        var state = try MatchSession.init(
            shared.allocator,
            seeds.len,
        );
        errdefer state.deinit(shared.allocator);

        if (seed_state) |saved| {
            try state.symbolic_dummy_infos.appendSlice(
                shared.allocator,
                saved.symbolic_dummy_infos,
            );
            state.witnesses = try cloneWitnessMap(
                shared.allocator,
                saved.witnesses,
            );
            state.materialized_witnesses = try cloneWitnessMap(
                shared.allocator,
                saved.materialized_witnesses,
            );
            state.materialized_witness_slots = try cloneWitnessSlotMap(
                shared.allocator,
                saved.materialized_witness_slots,
            );
            state.provisional_witness_infos =
                try cloneProvisionalWitnessInfoMap(
                    shared.allocator,
                    saved.provisional_witness_infos,
                );
            state.materialized_witness_infos =
                try cloneMaterializedWitnessInfoMap(
                    shared.allocator,
                    saved.materialized_witness_infos,
                );
        }

        var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
        defer witness_slots.deinit(shared.allocator);
        var wit_iter = state.witnesses.iterator();
        while (wit_iter.next()) |entry| {
            try witness_slots.put(
                shared.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }
        var mat_iter = state.materialized_witnesses.iterator();
        while (mat_iter.next()) |entry| {
            try witness_slots.put(
                shared.allocator,
                entry.value_ptr.*,
                entry.key_ptr.*,
            );
        }

        for (seeds, 0..) |seed, idx| {
            state.bindings[idx] = try symbolic_engine.boundValueFromSeed(
                seed,
                &state,
                &witness_slots,
            );
        }

        return .{
            .shared = shared,
            .rule_args = rule_args,
            .state = state,
        };
    }

    fn engine(self: *RuleMatchSession) SymbolicEngine {
        return .{ .shared = self.shared };
    }

    pub fn deinit(self: *RuleMatchSession) void {
        self.state.deinit(self.shared.allocator);
    }

    pub fn matchTransparent(
        self: *RuleMatchSession,
        template: TemplateExpr,
        actual: ExprId,
    ) anyerror!bool {
        var symbolic_engine = self.engine();
        return try symbolic_engine.matchTemplateRecState(
            template,
            actual,
            &self.state,
        );
    }

    pub fn matchSemantic(
        self: *RuleMatchSession,
        template: TemplateExpr,
        actual: ExprId,
        budget: usize,
    ) anyerror!bool {
        var symbolic_engine = self.engine();
        return try symbolic_engine.matchTemplateSemanticState(
            template,
            actual,
            &self.state,
            budget,
        );
    }

    pub fn beginNormalizedComparison(
        self: *RuleMatchSession,
        template: TemplateExpr,
        actual: ExprId,
    ) anyerror!NormalizedComparison {
        var view = try NormalizedView.init(self);
        errdefer view.deinit(self.shared.allocator);

        const expected_expr = try view.mirror.theorem.instantiateTemplate(
            template,
            view.mirror_binders,
        );
        const actual_expr = try copyExprBetweenTheorems(
            self.shared.allocator,
            self.shared.theorem,
            &view.mirror.theorem,
            actual,
            view.mirror.source_dummy_map,
            &view.to_mirror,
        );
        return .{
            .session = self,
            .view = view,
            .expected_expr = expected_expr,
            .actual_expr = actual_expr,
        };
    }

    pub fn resolveOptionalBindings(self: *RuleMatchSession) ![]?ExprId {
        var symbolic_engine = self.engine();
        const bindings = try self.shared.allocator.alloc(
            ?ExprId,
            self.state.bindings.len,
        );
        for (self.state.bindings, 0..) |binding, idx| {
            bindings[idx] = if (binding) |bound|
                try symbolic_engine.resolveBoundValue(
                    bound,
                    &self.state,
                )
            else
                null;
        }
        return bindings;
    }

    /// Like resolveOptionalBindings, but returns BindingSeeds that preserve
    /// symbolic BoundValues instead of collapsing them to concrete ExprIds.
    /// Concrete bindings become .exact seeds; symbolic bindings become
    /// .bound seeds carrying the full BoundValue.
    pub fn resolveBindingSeeds(self: *RuleMatchSession) ![]BindingSeed {
        var symbolic_engine = self.engine();
        const seeds = try self.shared.allocator.alloc(
            BindingSeed,
            self.state.bindings.len,
        );
        for (self.state.bindings, 0..) |binding, idx| {
            seeds[idx] = if (binding) |bound| switch (bound) {
                .concrete => |concrete| blk: {
                    const expr_id = (try symbolic_engine.concreteBindingMatchExpr(
                        concrete,
                        &self.state,
                    )) orelse break :blk BindingSeed{ .bound = bound };
                    break :blk BindingSeed{ .exact = expr_id };
                },
                .symbolic => BindingSeed{ .bound = bound },
            } else .none;
        }
        return seeds;
    }

    pub fn exportMatchSeedState(
        self: *RuleMatchSession,
        bindings: []BindingSeed,
    ) !MatchSeedState {
        return .{
            .bindings = bindings,
            .symbolic_dummy_infos = try self.shared.allocator.dupe(
                SymbolicDummyInfo,
                self.state.symbolic_dummy_infos.items,
            ),
            .witnesses = try cloneWitnessMap(
                self.shared.allocator,
                self.state.witnesses,
            ),
            .materialized_witnesses = try cloneWitnessMap(
                self.shared.allocator,
                self.state.materialized_witnesses,
            ),
            .materialized_witness_slots = try cloneWitnessSlotMap(
                self.shared.allocator,
                self.state.materialized_witness_slots,
            ),
            .provisional_witness_infos = try cloneProvisionalWitnessInfoMap(
                self.shared.allocator,
                self.state.provisional_witness_infos,
            ),
            .materialized_witness_infos = try cloneMaterializedWitnessInfoMap(
                self.shared.allocator,
                self.state.materialized_witness_infos,
            ),
        };
    }

    pub fn guideBindingTowardExpr(
        self: *RuleMatchSession,
        idx: usize,
        actual: ExprId,
        budget: usize,
    ) !bool {
        if (idx >= self.state.bindings.len) {
            return error.TemplateBinderOutOfRange;
        }
        const bound = self.state.bindings[idx] orelse return false;

        var symbolic_engine = self.engine();
        return switch (bound) {
            .concrete => |concrete| blk: {
                const expr_id = (try symbolic_engine.concreteBindingMatchExpr(
                    concrete,
                    &self.state,
                )) orelse break :blk false;
                const symbolic = try symbolic_engine.allocSymbolic(.{
                    .fixed = expr_id,
                });
                break :blk try symbolic_engine.matchSymbolicToExprSemantic(
                    symbolic,
                    actual,
                    &self.state,
                    budget,
                );
            },
            .symbolic => |symbolic| try symbolic_engine.matchSymbolicToExprSemantic(
                symbolic.expr,
                actual,
                &self.state,
                budget,
            ),
        };
    }

    /// Finalize all bindings to concrete ExprIds. Returns
    /// error.UnresolvedDummyWitness if any hidden-dummy slot lacks a
    /// witness — the user must provide explicit bindings that cover the
    /// hidden def structure.
    pub fn finalizeConcreteBindings(self: *RuleMatchSession) ![]ExprId {
        var symbolic_engine = self.engine();
        const bindings = try self.shared.allocator.alloc(
            ExprId,
            self.state.bindings.len,
        );
        errdefer self.shared.allocator.free(bindings);
        for (self.state.bindings, 0..) |binding, idx| {
            const bound = binding orelse return error.MissingBinderAssignment;
            bindings[idx] = try symbolic_engine.finalizeBoundValue(
                bound,
                &self.state,
            );
        }
        return bindings;
    }

    fn boundValueToMirror(
        self: *RuleMatchSession,
        bound: BoundValue,
        view: *NormalizedView,
    ) anyerror!ExprId {
        var symbolic_engine = self.engine();
        return switch (bound) {
            .concrete => |concrete| try copyExprBetweenTheorems(
                self.shared.allocator,
                self.shared.theorem,
                &view.mirror.theorem,
                (try symbolic_engine.concreteBindingMatchExpr(
                    concrete,
                    &self.state,
                )) orelse return error.MissingRepresentative,
                view.mirror.source_dummy_map,
                &view.to_mirror,
            ),
            .symbolic => |symbolic| try self.symbolicToMirror(
                symbolic.expr,
                view,
            ),
        };
    }

    fn symbolicToMirror(
        self: *RuleMatchSession,
        symbolic: *const SymbolicExpr,
        view: *NormalizedView,
    ) anyerror!ExprId {
        return switch (symbolic.*) {
            .binder => |idx| try view.ensureMirrorBinder(self, idx),
            .fixed => |expr_id| try copyExprBetweenTheorems(
                self.shared.allocator,
                self.shared.theorem,
                &view.mirror.theorem,
                expr_id,
                view.mirror.source_dummy_map,
                &view.to_mirror,
            ),
            .dummy => |slot| try view.ensureMirrorDummy(self, slot),
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(
                    ExprId,
                    app.args.len,
                );
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.symbolicToMirror(arg, view);
                }
                break :blk try view.mirror.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn matchNormalizedPattern(
        self: *RuleMatchSession,
        view: *NormalizedView,
        pattern_expr: ExprId,
        actual_expr: ExprId,
    ) anyerror!bool {
        if (view.placeholder_targets.get(pattern_expr)) |target| {
            return try self.assignNormalizedTarget(target, actual_expr, view);
        }

        var symbolic_engine = self.engine();
        if (!view.placeholder_targets.contains(actual_expr)) {
            const pattern_concrete =
                try self.mirrorExprToConcrete(pattern_expr, view);
            const actual_concrete =
                try self.mirrorExprToConcrete(actual_expr, view);
            if (pattern_concrete != null and actual_concrete != null) {
                const pattern_repr = try symbolic_engine.chooseRepresentativeSymbolic(
                    pattern_concrete.?,
                    &self.state,
                    .normalized,
                );
                const actual_repr = try symbolic_engine.chooseRepresentativeSymbolic(
                    actual_concrete.?,
                    &self.state,
                    .normalized,
                );
                if (symbolic_engine.symbolicExprEql(pattern_repr, actual_repr)) {
                    return true;
                }
            }
        }

        const pattern_node = view.mirror.theorem.interner.node(pattern_expr);
        const actual_node = view.mirror.theorem.interner.node(actual_expr);
        return switch (pattern_node.*) {
            .variable => switch (actual_node.*) {
                .variable => pattern_expr == actual_expr,
                .app => false,
            },
            .app => |pattern_app| switch (actual_node.*) {
                .variable => false,
                .app => |actual_app| blk: {
                    if (pattern_app.term_id != actual_app.term_id) {
                        break :blk false;
                    }
                    if (pattern_app.args.len != actual_app.args.len) {
                        break :blk false;
                    }
                    for (pattern_app.args, actual_app.args) |pattern_arg, actual_arg| {
                        if (!try self.matchNormalizedPattern(
                            view,
                            pattern_arg,
                            actual_arg,
                        )) {
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
            },
        };
    }

    fn assignNormalizedTarget(
        self: *RuleMatchSession,
        target: NormalizedPlaceholderTarget,
        actual_expr: ExprId,
        view: *NormalizedView,
    ) anyerror!bool {
        if (view.placeholder_targets.get(actual_expr)) |actual_target| {
            if (samePlaceholderTarget(target, actual_target)) return true;
        }

        var symbolic_engine = self.engine();
        const translated = try self.mirrorExprToBoundValue(actual_expr, view);
        return switch (target) {
            .binder => |idx| blk: {
                if (translated == .symbolic and
                    self.symbolicContainsBinder(translated.symbolic.expr, idx))
                {
                    break :blk false;
                }
                break :blk try symbolic_engine.assignBinderValue(
                    idx,
                    translated,
                    &self.state,
                );
            },
            .dummy => |slot| blk: {
                if (translated == .symbolic and
                    self.symbolicContainsDummy(translated.symbolic.expr, slot))
                {
                    break :blk false;
                }
                const info = self.state.symbolic_dummy_infos.items[slot];
                break :blk switch (translated) {
                    .concrete => |concrete| blk_inner: {
                        const actual = (try symbolic_engine.concreteBindingMatchExpr(
                            concrete,
                            &self.state,
                        )) orelse break :blk_inner false;
                        break :blk_inner try symbolic_engine.matchSymbolicDummyState(
                            slot,
                            info,
                            actual,
                            &self.state,
                        );
                    },
                    .symbolic => |symbolic| try symbolic_engine.matchDummyToSymbolic(
                        slot,
                        symbolic.expr,
                        &self.state,
                    ),
                };
            },
        };
    }

    fn mirrorExprToBoundValue(
        self: *RuleMatchSession,
        expr_id: ExprId,
        view: *const NormalizedView,
    ) anyerror!BoundValue {
        var symbolic_engine = self.engine();
        if (try self.mirrorExprToConcrete(expr_id, view)) |concrete| {
            return try symbolic_engine.makeConcreteBoundValue(
                concrete,
                &self.state,
                .normalized,
            );
        }
        return symbolic_engine.makeSymbolicBoundValue(
            try self.mirrorExprToSymbolic(expr_id, view),
            .normalized,
        );
    }

    fn mirrorExprToConcrete(
        self: *RuleMatchSession,
        expr_id: ExprId,
        view: *const NormalizedView,
    ) anyerror!?ExprId {
        if (view.placeholder_targets.contains(expr_id)) return null;

        return switch (view.mirror.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| blk: {
                    if (idx >= self.shared.theorem.theorem_vars.items.len) {
                        return error.UnknownTheoremVariable;
                    }
                    break :blk self.shared.theorem.theorem_vars.items[idx];
                },
                .dummy_var => |idx| blk: {
                    if (idx >= view.mirror.mirror_dummy_map.len) {
                        return error.UnknownDummyVar;
                    }
                    break :blk view.mirror.mirror_dummy_map[idx];
                },
            },
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(
                    ExprId,
                    app.args.len,
                );
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.mirrorExprToConcrete(arg, view)) orelse {
                        self.shared.allocator.free(args);
                        break :blk null;
                    };
                }
                break :blk try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }

    fn mirrorExprToSymbolic(
        self: *RuleMatchSession,
        expr_id: ExprId,
        view: *const NormalizedView,
    ) anyerror!*const SymbolicExpr {
        var symbolic_engine = self.engine();
        if (view.placeholder_targets.get(expr_id)) |target| {
            return switch (target) {
                .binder => |idx| try symbolic_engine.allocSymbolic(.{ .binder = idx }),
                .dummy => |slot| try symbolic_engine.allocSymbolic(.{ .dummy = slot }),
            };
        }

        return switch (view.mirror.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| blk: {
                    if (idx >= self.shared.theorem.theorem_vars.items.len) {
                        return error.UnknownTheoremVariable;
                    }
                    break :blk try symbolic_engine.allocSymbolic(.{
                        .fixed = self.shared.theorem.theorem_vars.items[idx],
                    });
                },
                .dummy_var => |idx| blk: {
                    if (idx >= view.mirror.mirror_dummy_map.len) {
                        return error.UnknownDummyVar;
                    }
                    break :blk try symbolic_engine.allocSymbolic(.{
                        .fixed = view.mirror.mirror_dummy_map[idx],
                    });
                },
            },
            .app => |app| blk: {
                const args = try self.shared.allocator.alloc(
                    *const SymbolicExpr,
                    app.args.len,
                );
                errdefer self.shared.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.mirrorExprToSymbolic(arg, view);
                }
                break :blk try symbolic_engine.allocSymbolic(.{ .app = .{
                    .term_id = app.term_id,
                    .args = args,
                } });
            },
        };
    }

    fn symbolicContainsBinder(
        self: *RuleMatchSession,
        symbolic: *const SymbolicExpr,
        target: usize,
    ) bool {
        return switch (symbolic.*) {
            .binder => |idx| idx == target,
            .fixed => false,
            .dummy => false,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.symbolicContainsBinder(arg, target)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
        };
    }

    fn symbolicContainsDummy(
        self: *RuleMatchSession,
        symbolic: *const SymbolicExpr,
        target: usize,
    ) bool {
        return switch (symbolic.*) {
            .binder => false,
            .fixed => false,
            .dummy => |slot| slot == target,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.symbolicContainsDummy(arg, target)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
        };
    }
};

pub const NormalizedComparison = struct {
    session: *RuleMatchSession,
    view: NormalizedView,
    expected_expr: ExprId,
    actual_expr: ExprId,

    pub fn deinit(self: *NormalizedComparison) void {
        self.view.deinit(self.session.shared.allocator);
    }

    pub fn mirrorTheorem(self: *NormalizedComparison) *TheoremContext {
        return &self.view.mirror.theorem;
    }

    pub fn finish(
        self: *NormalizedComparison,
        normalized_expected: ExprId,
        normalized_actual: ExprId,
    ) anyerror!bool {
        return try self.session.matchNormalizedPattern(
            &self.view,
            normalized_expected,
            normalized_actual,
        );
    }
};

fn samePlaceholderTarget(
    lhs: NormalizedPlaceholderTarget,
    rhs: NormalizedPlaceholderTarget,
) bool {
    return switch (lhs) {
        .binder => |idx| switch (rhs) {
            .binder => |rhs_idx| idx == rhs_idx,
            .dummy => false,
        },
        .dummy => |idx| switch (rhs) {
            .binder => false,
            .dummy => |rhs_idx| idx == rhs_idx,
        },
    };
}
