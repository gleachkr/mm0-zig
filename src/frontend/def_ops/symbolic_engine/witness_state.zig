const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Canonicalizer = @import("../../canonicalizer.zig").Canonicalizer;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch =
    @import("./transparent_match.zig");

const SymbolicDummyInfo = Types.SymbolicDummyInfo;
const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const BindingSeed = Types.BindingSeed;
const ConcreteBinding = Types.ConcreteBinding;
const BoundValue = Types.BoundValue;
const UnresolvedDummyRoot = Types.UnresolvedDummyRoot;
const WitnessMap = Types.WitnessMap;
const WitnessSlotMap = Types.WitnessSlotMap;
const DummyAliasMap = Types.DummyAliasMap;
const ProvisionalWitnessInfoMap = Types.ProvisionalWitnessInfoMap;
const MaterializedWitnessInfoMap = Types.MaterializedWitnessInfoMap;
const RepresentativeCache = Types.RepresentativeCache;
const MatchSession = MatchState.MatchSession;
const MatchSnapshot = MatchState.MatchSnapshot;
const ConcreteVarInfo = Types.ConcreteVarInfo;

pub fn rebuildBoundValue(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
    mode: BindingMode,
) anyerror!BoundValue {
    if (try resymbolizeBinding(self, expr_id, state, witness_slots)) |symbolic| {
        return makeSymbolicBoundValue(self, symbolic, mode);
    }
    return try makeConcreteBoundValue(self, expr_id, state, mode);
}

pub fn rebuildBoundValueFromState(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!BoundValue {
    var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
    defer witness_slots.deinit(self.shared.allocator);

    var it = state.witnesses.iterator();
    while (it.next()) |entry| {
        try witness_slots.put(
            self.shared.allocator,
            entry.value_ptr.*,
            entry.key_ptr.*,
        );
    }
    var materialized_it = state.materialized_witnesses.iterator();
    while (materialized_it.next()) |entry| {
        try witness_slots.put(
            self.shared.allocator,
            entry.value_ptr.*,
            entry.key_ptr.*,
        );
    }
    return try rebuildBoundValue(
        self,
        expr_id,
        state,
        &witness_slots,
        mode,
    );
}

pub fn makeConcreteBoundValue(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!BoundValue {
    return .{ .concrete = .{
        .raw = expr_id,
        .repr = try chooseRepresentativeSymbolic(
            self,
            expr_id,
            state,
            mode,
        ),
        .mode = mode,
    } };
}

pub fn makeSymbolicBoundValue(
    self: anytype,
    symbolic: *const SymbolicExpr,
    mode: BindingMode,
) BoundValue {
    _ = self;
    return .{ .symbolic = .{
        .expr = symbolic,
        .mode = mode,
    } };
}

pub fn assignBinderFromExpr(
    self: anytype,
    idx: usize,
    actual: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!bool {
    if (idx >= state.bindings.len) return false;
    if (state.bindings[idx]) |existing| {
        if (!try boundValueMatchesExpr(self, existing, actual, state)) {
            return false;
        }
        switch (existing) {
            .concrete => {},
            .symbolic => {
                // If a binder was first solved from a symbolic expansion
                // with hidden dummy slots, and we later see a concrete
                // proof expression that matches it, prefer the concrete
                // witness-preserving form over keeping the symbolic
                // placeholder. This avoids needlessly finalizing hidden
                // binders back into fresh theorem dummies.
                state.bindings[idx] = try rebuildBoundValueFromState(
                    self,
                    actual,
                    state,
                    mode,
                );
            },
        }
        return true;
    }
    state.bindings[idx] = try rebuildBoundValueFromState(
        self,
        actual,
        state,
        mode,
    );
    return true;
}

pub fn assignBinderFromSymbolic(
    self: anytype,
    idx: usize,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!bool {
    if (idx >= state.bindings.len) return false;
    if (state.bindings[idx]) |existing| {
        return try boundValueMatchesSymbolic(
            self,
            existing,
            symbolic,
            state,
        );
    }
    state.bindings[idx] = makeSymbolicBoundValue(self, symbolic, mode);
    return true;
}

pub fn assignBinderValue(
    self: anytype,
    idx: usize,
    value: BoundValue,
    state: *MatchSession,
) anyerror!bool {
    if (idx >= state.bindings.len) return false;
    if (state.bindings[idx]) |existing| {
        return switch (value) {
            .concrete => |concrete| blk: {
                const actual = (try concreteBindingMatchExpr(
                    self,
                    concrete,
                    state,
                )) orelse break :blk false;
                break :blk try boundValueMatchesExpr(
                    self,
                    existing,
                    actual,
                    state,
                );
            },
            .symbolic => |symbolic| try boundValueMatchesSymbolic(
                self,
                existing,
                symbolic.expr,
                state,
            ),
        };
    }
    state.bindings[idx] = value;
    return true;
}

pub fn boundValueFromSeed(
    self: anytype,
    seed: BindingSeed,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!?BoundValue {
    return switch (seed) {
        .none => null,
        .exact => |expr_id| try rebuildBoundValue(
            self,
            expr_id,
            state,
            witness_slots,
            .exact,
        ),
        .semantic => |semantic| try rebuildBoundValue(
            self,
            semantic.expr_id,
            state,
            witness_slots,
            semantic.mode,
        ),
        .bound => |bv| bv,
    };
}

pub fn chooseRepresentative(
    self: anytype,
    expr_id: ExprId,
    mode: BindingMode,
) anyerror!ExprId {
    if (mode == .exact) return expr_id;

    var state = try MatchSession.init(self.shared.allocator, 0);
    defer state.deinit(self.shared.allocator);

    const symbolic = try chooseRepresentativeSymbolic(
        self,
        expr_id,
        &state,
        mode,
    );
    return (try materializeRepresentativeSymbolic(
        self,
        symbolic,
        &state,
    )) orelse error.MissingRepresentative;
}

pub fn representativeCacheForMode(
    self: anytype,
    state: *MatchSession,
    mode: BindingMode,
) *RepresentativeCache {
    _ = self;
    return switch (mode) {
        .exact => unreachable,
        .transparent => &state.transparent_representatives,
        .normalized => &state.normalized_representatives,
    };
}

pub fn chooseRepresentativeSymbolic(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!*const SymbolicExpr {
    if (mode == .exact) {
        return try self.allocSymbolic(.{ .fixed = expr_id });
    }

    const cache = representativeCacheForMode(self, state, mode);
    if (cache.get(expr_id)) |cached| return cached;

    var current = try rebuildExprRepresentativeSymbolic(
        self,
        expr_id,
        state,
        mode,
    );
    if (self.shared.registry) |registry| {
        if (try symbolicToConcreteIfPlain(self, current, state)) |plain| {
            var canonicalizer = Canonicalizer.init(
                self.shared.allocator,
                self.shared.theorem,
                registry,
                self.shared.env,
            );
            const canonical = try canonicalizer.canonicalize(plain);
            current = try self.allocSymbolic(.{ .fixed = canonical });
        }
    }
    while (try compressRepresentativeToDef(self, current, state)) |compressed| {
        if (symbolicExprEql(self, current, compressed)) break;
        current = compressed;
    }
    try cache.put(self.shared.allocator, expr_id, current);
    return current;
}

pub fn rebuildExprRepresentativeSymbolic(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!*const SymbolicExpr {
    var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
    defer witness_slots.deinit(self.shared.allocator);

    var witness_it = state.witnesses.iterator();
    while (witness_it.next()) |entry| {
        try witness_slots.put(
            self.shared.allocator,
            entry.value_ptr.*,
            entry.key_ptr.*,
        );
    }
    var materialized_it = state.materialized_witnesses.iterator();
    while (materialized_it.next()) |entry| {
        try witness_slots.put(
            self.shared.allocator,
            entry.value_ptr.*,
            entry.key_ptr.*,
        );
    }

    if (try getResymbolizableWitnessInfo(self, expr_id)) |info| {
        const slot = try slotForWitness(
            self,
            expr_id,
            info,
            state,
            &witness_slots,
        );
        return try self.allocSymbolic(.{ .dummy = slot });
    }

    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable => try self.allocSymbolic(.{ .fixed = expr_id }),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(
                *const SymbolicExpr,
                app.args.len,
            );
            errdefer self.shared.allocator.free(args);
            const plain_args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(plain_args);

            var all_plain = true;
            var changed = false;
            for (app.args, 0..) |arg, idx| {
                args[idx] = try chooseRepresentativeSymbolic(
                    self,
                    arg,
                    state,
                    mode,
                );
                if (try symbolicToConcreteIfPlain(self, args[idx], state)) |plain| {
                    plain_args[idx] = plain;
                    changed = changed or plain != arg;
                } else {
                    all_plain = false;
                    changed = true;
                }
            }
            if (all_plain) {
                self.shared.allocator.free(args);
                if (!changed) {
                    self.shared.allocator.free(plain_args);
                    break :blk try self.allocSymbolic(
                        .{ .fixed = expr_id },
                    );
                }
                const rebuilt = try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    plain_args,
                );
                break :blk try self.allocSymbolic(
                    .{ .fixed = rebuilt },
                );
            }
            self.shared.allocator.free(plain_args);
            break :blk try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = args,
            } });
        },
    };
}

const CompressionMatchKind = enum {
    concrete,
    symbolic,
};

pub fn compressRepresentativeToDef(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *const MatchSession,
) anyerror!?*const SymbolicExpr {
    const sort_name = symbolicSortName(self, symbolic, state) orelse {
        return null;
    };

    term_loop: for (self.shared.env.terms.items, 0..) |term, term_id| {
        if (!term.is_def or term.body == null) continue;
        if (!std.mem.eql(u8, term.ret_sort_name, sort_name)) continue;

        var temp = try cloneRepresentativeState(
            self,
            state,
            term.args.len + term.dummy_args.len,
        );
        defer temp.deinit(self.shared.allocator);

        const symbolic_template = try TransparentMatch.symbolicFromTemplate(
            self,
            term.body.?,
        );
        const plain_symbolic = try symbolicToConcreteIfPlain(
            self,
            symbolic,
            state,
        );
        const match_kind: CompressionMatchKind = if (plain_symbolic != null)
            .concrete
        else
            .symbolic;
        const matched = if (plain_symbolic) |plain|
            try TransparentMatch.matchExprToSymbolic(
                self,
                plain,
                symbolic_template,
                &temp,
                .transparent,
            )
        else
            try TransparentMatch.matchSymbolicToSymbolicState(
                self,
                symbolic_template,
                symbolic,
                &temp,
            );
        if (!matched) {
            continue;
        }

        const args = try self.shared.allocator.alloc(
            *const SymbolicExpr,
            term.args.len,
        );
        errdefer self.shared.allocator.free(args);
        const plain_args = try self.shared.allocator.alloc(
            ExprId,
            term.args.len,
        );
        errdefer self.shared.allocator.free(plain_args);
        var all_plain = true;
        for (0..term.args.len) |idx| {
            const binding = temp.bindings[idx] orelse {
                self.shared.allocator.free(args);
                self.shared.allocator.free(plain_args);
                continue :term_loop;
            };
            args[idx] = try exportCompressedArgFromTempState(
                self,
                binding,
                &temp,
                match_kind,
            );
            if (try symbolicToConcreteIfPlain(self, args[idx], &temp)) |plain| {
                plain_args[idx] = plain;
            } else {
                all_plain = false;
            }
        }

        if (all_plain) {
            self.shared.allocator.free(args);
            const rebuilt = try self.shared.theorem.interner.internAppOwned(
                @intCast(term_id),
                plain_args,
            );
            return try self.allocSymbolic(.{ .fixed = rebuilt });
        }
        self.shared.allocator.free(plain_args);
        return try self.allocSymbolic(.{ .app = .{
            .term_id = @intCast(term_id),
            .args = args,
        } });
    }
    return null;
}

fn exportCompressedArgFromTempState(
    self: anytype,
    bound: BoundValue,
    state: *const MatchSession,
    match_kind: CompressionMatchKind,
) anyerror!*const SymbolicExpr {
    return switch (match_kind) {
        // A concrete match builds bindings entirely inside the temporary
        // session. Any binder that survives here is temp-local and must
        // be inlined before we return a representative to the caller.
        .concrete => try exportConcreteMatchedBoundValue(
            self,
            bound,
            state,
        ),
        // A symbolic-to-symbolic match may legitimately bind a def arg to
        // a caller-owned binder. We therefore preserve the representative
        // structure as-is on this path.
        .symbolic => try boundValueRepresentative(self, bound),
    };
}

fn exportConcreteMatchedBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *const MatchSession,
) anyerror!*const SymbolicExpr {
    return switch (bound) {
        .concrete => |concrete| if (concrete.mode == .exact)
            try self.allocSymbolic(.{ .fixed = concrete.raw })
        else
            try exportConcreteMatchedSymbolic(
                self,
                concrete.repr,
                state,
            ),
        .symbolic => |symbolic| try exportConcreteMatchedSymbolic(
            self,
            symbolic.expr,
            state,
        ),
    };
}

fn exportConcreteMatchedSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *const MatchSession,
) anyerror!*const SymbolicExpr {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx >= state.bindings.len) {
                return error.TemplateBinderOutOfRange;
            }
            const binding = state.bindings[idx] orelse {
                return error.MissingBinderAssignment;
            };
            break :blk try exportConcreteMatchedBoundValue(
                self,
                binding,
                state,
            );
        },
        .fixed => |expr_id| try self.allocSymbolic(.{ .fixed = expr_id }),
        .dummy => |slot| try self.allocSymbolic(.{ .dummy = slot }),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(
                *const SymbolicExpr,
                app.args.len,
            );
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = try exportConcreteMatchedSymbolic(
                    self,
                    arg,
                    state,
                );
            }
            break :blk try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = args,
            } });
        },
    };
}

pub fn symbolicSortName(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *const MatchSession,
) ?[]const u8 {
    return switch (symbolic.*) {
        .binder => null,
        .fixed => |expr_id| exprSortName(self, expr_id),
        .dummy => |slot| if (slot < state.symbolic_dummy_infos.items.len)
            state.symbolic_dummy_infos.items[slot].sort_name
        else
            null,
        .app => |app| if (app.term_id < self.shared.env.terms.items.len)
            self.shared.env.terms.items[app.term_id].ret_sort_name
        else
            null,
    };
}

pub fn symbolicToConcreteIfPlain(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *const MatchSession,
) anyerror!?ExprId {
    return switch (symbolic.*) {
        .binder => null,
        .dummy => null,
        .fixed => |expr_id| expr_id,
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try symbolicToConcreteIfPlain(
                    self,
                    arg,
                    state,
                )) orelse {
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

pub fn symbolicExprEql(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
) bool {
    return switch (lhs.*) {
        .binder => |idx| switch (rhs.*) {
            .binder => |rhs_idx| idx == rhs_idx,
            else => false,
        },
        .fixed => |expr_id| switch (rhs.*) {
            .fixed => |rhs_expr| expr_id == rhs_expr,
            else => false,
        },
        .dummy => |slot| switch (rhs.*) {
            .dummy => |rhs_slot| slot == rhs_slot,
            else => false,
        },
        .app => |app| switch (rhs.*) {
            .app => |rhs_app| blk: {
                if (app.term_id != rhs_app.term_id) break :blk false;
                if (app.args.len != rhs_app.args.len) break :blk false;
                for (app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                    if (!symbolicExprEql(self, lhs_arg, rhs_arg)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            else => false,
        },
    };
}

pub fn boundValueRepresentative(
    self: anytype,
    bound: BoundValue,
) anyerror!*const SymbolicExpr {
    return switch (bound) {
        .concrete => |concrete| if (concrete.mode == .exact)
            try self.allocSymbolic(.{ .fixed = concrete.raw })
        else
            concrete.repr,
        .symbolic => |symbolic| symbolic.expr,
    };
}

pub fn exprSortName(
    self: anytype,
    expr_id: ExprId,
) ?[]const u8 {
    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .app => |app| if (app.term_id < self.shared.env.terms.items.len)
            self.shared.env.terms.items[app.term_id].ret_sort_name
        else
            null,
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| if (idx < self.shared.theorem.arg_infos.len)
                self.shared.theorem.arg_infos[idx].sort_name
            else
                null,
            .dummy_var => |idx| if (idx < self.shared.theorem.theorem_dummies.items.len)
                self.shared.theorem.theorem_dummies.items[idx].sort_name
            else
                null,
        },
    };
}

pub fn resymbolizeBinding(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!?*const SymbolicExpr {
    if (try symbolicForExistingConcreteBinding(self, expr_id, state)) |binding| {
        return binding;
    }

    if (try getResymbolizableWitnessInfo(self, expr_id)) |info| {
        const slot = try slotForWitness(
            self,
            expr_id,
            info,
            state,
            witness_slots,
        );
        return try self.allocSymbolic(.{ .dummy = slot });
    }

    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable => null,
        .app => |app| blk: {
            var has_symbolic = false;
            const args = try self.shared.allocator.alloc(
                *const SymbolicExpr,
                app.args.len,
            );
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg_expr, idx| {
                if (try resymbolizeBinding(
                    self,
                    arg_expr,
                    state,
                    witness_slots,
                )) |symbolic_arg| {
                    args[idx] = symbolic_arg;
                    has_symbolic = true;
                } else {
                    args[idx] = try self.allocSymbolic(.{ .fixed = arg_expr });
                }
            }
            if (!has_symbolic) {
                self.shared.allocator.free(args);
                break :blk null;
            }
            break :blk try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = args,
            } });
        },
    };
}

pub fn symbolicForExistingConcreteBinding(
    self: anytype,
    expr_id: ExprId,
    state: *const MatchSession,
) anyerror!?*const SymbolicExpr {
    for (state.bindings, 0..) |binding_opt, idx| {
        const binding = binding_opt orelse continue;
        switch (binding) {
            .concrete => |concrete| {
                if (concrete.raw != expr_id) continue;
                return try self.allocSymbolic(.{ .binder = idx });
            },
            .symbolic => {},
        }
    }
    return null;
}

pub fn slotForWitness(
    self: anytype,
    witness: ExprId,
    info: SymbolicDummyInfo,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!usize {
    if (witness_slots.get(witness)) |slot| return slot;
    if (state.materialized_witness_slots.get(witness)) |slot| {
        try witness_slots.put(self.shared.allocator, witness, slot);
        return slot;
    }

    const slot = state.symbolic_dummy_infos.items.len;
    try state.symbolic_dummy_infos.append(self.shared.allocator, info);
    try witness_slots.put(self.shared.allocator, witness, slot);
    try state.witnesses.put(self.shared.allocator, slot, witness);
    try state.provisional_witness_infos.put(
        self.shared.allocator,
        witness,
        info,
    );
    return slot;
}

pub fn resolveDummySlot(
    self: anytype,
    slot: usize,
    state: *const MatchSession,
) anyerror!usize {
    if (slot >= state.symbolic_dummy_infos.items.len) {
        return error.UnknownDummyVar;
    }
    var current = slot;
    var steps: usize = 0;
    while (state.dummy_aliases.get(current)) |next| {
        if (next >= state.symbolic_dummy_infos.items.len) {
            return error.UnknownDummyVar;
        }
        current = next;
        steps += 1;
        if (steps > state.symbolic_dummy_infos.items.len) {
            return error.CyclicSymbolicDummyAlias;
        }
    }
    _ = self;
    return current;
}

pub fn putWitnessForDummySlot(
    self: anytype,
    slot: usize,
    actual: ExprId,
    state: *MatchSession,
) anyerror!void {
    const root = try resolveDummySlot(self, slot, state);
    try state.witnesses.put(self.shared.allocator, root, actual);
}

pub fn alignDummySlots(
    self: anytype,
    lhs_slot: usize,
    rhs_slot: usize,
    state: *MatchSession,
) anyerror!bool {
    const lhs_root = try resolveDummySlot(self, lhs_slot, state);
    const rhs_root = try resolveDummySlot(self, rhs_slot, state);
    if (lhs_root == rhs_root) return true;

    const lhs_info = state.symbolic_dummy_infos.items[lhs_root];
    const rhs_info = state.symbolic_dummy_infos.items[rhs_root];
    if (!std.mem.eql(u8, lhs_info.sort_name, rhs_info.sort_name)) {
        return false;
    }
    if (lhs_info.bound != rhs_info.bound) {
        return false;
    }

    const lhs_witness = currentWitnessExpr(self, lhs_root, state);
    const rhs_witness = currentWitnessExpr(self, rhs_root, state);
    if (lhs_witness != null and rhs_witness != null and
        lhs_witness.? != rhs_witness.?)
    {
        return false;
    }

    const winner = if (lhs_witness != null)
        lhs_root
    else if (rhs_witness != null)
        rhs_root
    else if (lhs_root <= rhs_root)
        lhs_root
    else
        rhs_root;
    const loser = if (winner == lhs_root) rhs_root else lhs_root;

    if (state.witnesses.get(loser)) |existing| {
        if (state.witnesses.get(winner)) |winner_existing| {
            if (winner_existing != existing) return false;
        } else {
            try state.witnesses.put(self.shared.allocator, winner, existing);
        }
        _ = state.witnesses.remove(loser);
    }
    if (state.materialized_witnesses.get(loser)) |existing| {
        if (state.materialized_witnesses.get(winner)) |winner_existing| {
            if (winner_existing != existing) return false;
        } else {
            try state.materialized_witnesses.put(
                self.shared.allocator,
                winner,
                existing,
            );
            try state.materialized_witness_slots.put(
                self.shared.allocator,
                existing,
                winner,
            );
        }
        _ = state.materialized_witnesses.remove(loser);
    }

    try state.dummy_aliases.put(self.shared.allocator, loser, winner);
    return true;
}

pub fn saveMatchSnapshot(
    self: anytype,
    state: *const MatchSession,
) anyerror!MatchSnapshot {
    return .{
        .bindings = try self.shared.allocator.dupe(?BoundValue, state.bindings),
        .witnesses = try cloneWitnessMap(self, state.witnesses),
        .materialized_witnesses = try cloneWitnessMap(self, state.materialized_witnesses),
        .materialized_witness_slots = try cloneWitnessSlotMap(self, state.materialized_witness_slots),
        .dummy_aliases = try cloneDummyAliasMap(self, state.dummy_aliases),
        .provisional_witness_infos = try cloneProvisionalWitnessInfoMap(
            self,
            state.provisional_witness_infos,
        ),
        .materialized_witness_infos = try cloneMaterializedWitnessInfoMap(
            self,
            state.materialized_witness_infos,
        ),
        .transparent_representatives = try cloneRepresentativeCache(
            self,
            state.transparent_representatives,
        ),
        .normalized_representatives = try cloneRepresentativeCache(
            self,
            state.normalized_representatives,
        ),
        .dummy_info_len = state.symbolic_dummy_infos.items.len,
    };
}

pub fn restoreMatchSnapshot(
    self: anytype,
    snapshot: *const MatchSnapshot,
    state: *MatchSession,
) anyerror!void {
    @memcpy(state.bindings, snapshot.bindings);
    state.witnesses.deinit(self.shared.allocator);
    state.witnesses = try cloneWitnessMap(self, snapshot.witnesses);
    state.materialized_witnesses.deinit(self.shared.allocator);
    state.materialized_witnesses =
        try cloneWitnessMap(self, snapshot.materialized_witnesses);
    state.materialized_witness_slots.deinit(self.shared.allocator);
    state.materialized_witness_slots = try cloneWitnessSlotMap(
        self,
        snapshot.materialized_witness_slots,
    );
    state.dummy_aliases.deinit(self.shared.allocator);
    state.dummy_aliases = try cloneDummyAliasMap(
        self,
        snapshot.dummy_aliases,
    );
    state.provisional_witness_infos.deinit(self.shared.allocator);
    state.provisional_witness_infos =
        try cloneProvisionalWitnessInfoMap(
            self,
            snapshot.provisional_witness_infos,
        );
    state.materialized_witness_infos.deinit(self.shared.allocator);
    state.materialized_witness_infos =
        try cloneMaterializedWitnessInfoMap(
            self,
            snapshot.materialized_witness_infos,
        );
    state.transparent_representatives.deinit(self.shared.allocator);
    state.transparent_representatives =
        try cloneRepresentativeCache(
            self,
            snapshot.transparent_representatives,
        );
    state.normalized_representatives.deinit(self.shared.allocator);
    state.normalized_representatives =
        try cloneRepresentativeCache(
            self,
            snapshot.normalized_representatives,
        );
    state.symbolic_dummy_infos.shrinkRetainingCapacity(
        snapshot.dummy_info_len,
    );
}

pub fn deinitMatchSnapshot(
    self: anytype,
    snapshot: *MatchSnapshot,
) void {
    self.shared.allocator.free(snapshot.bindings);
    snapshot.witnesses.deinit(self.shared.allocator);
    snapshot.materialized_witnesses.deinit(self.shared.allocator);
    snapshot.materialized_witness_slots.deinit(self.shared.allocator);
    snapshot.dummy_aliases.deinit(self.shared.allocator);
    snapshot.provisional_witness_infos.deinit(self.shared.allocator);
    snapshot.materialized_witness_infos.deinit(self.shared.allocator);
    snapshot.transparent_representatives.deinit(self.shared.allocator);
    snapshot.normalized_representatives.deinit(self.shared.allocator);
}

pub fn cloneWitnessMap(self: anytype, map: WitnessMap) anyerror!WitnessMap {
    var clone: WitnessMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            self.shared.allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub fn cloneWitnessSlotMap(
    self: anytype,
    map: WitnessSlotMap,
) anyerror!WitnessSlotMap {
    var clone: WitnessSlotMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            self.shared.allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub fn cloneDummyAliasMap(
    self: anytype,
    map: DummyAliasMap,
) anyerror!DummyAliasMap {
    var clone: DummyAliasMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            self.shared.allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub fn cloneProvisionalWitnessInfoMap(
    self: anytype,
    map: ProvisionalWitnessInfoMap,
) anyerror!ProvisionalWitnessInfoMap {
    var clone: ProvisionalWitnessInfoMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            self.shared.allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub fn cloneMaterializedWitnessInfoMap(
    self: anytype,
    map: MaterializedWitnessInfoMap,
) anyerror!MaterializedWitnessInfoMap {
    var clone: MaterializedWitnessInfoMap = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            self.shared.allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub fn cloneRepresentativeCache(
    self: anytype,
    map: RepresentativeCache,
) anyerror!RepresentativeCache {
    var clone: RepresentativeCache = .{};
    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(
            self.shared.allocator,
            entry.key_ptr.*,
            entry.value_ptr.*,
        );
    }
    return clone;
}

pub fn cloneRepresentativeState(
    self: anytype,
    source: *const MatchSession,
    binding_len: usize,
) anyerror!MatchSession {
    var clone = try MatchSession.init(self.shared.allocator, binding_len);
    errdefer clone.deinit(self.shared.allocator);

    clone.witnesses = try cloneWitnessMap(self, source.witnesses);
    clone.materialized_witnesses =
        try cloneWitnessMap(self, source.materialized_witnesses);
    clone.materialized_witness_slots =
        try cloneWitnessSlotMap(self, source.materialized_witness_slots);
    clone.dummy_aliases = try cloneDummyAliasMap(self, source.dummy_aliases);
    clone.provisional_witness_infos =
        try cloneProvisionalWitnessInfoMap(
            self,
            source.provisional_witness_infos,
        );
    clone.materialized_witness_infos =
        try cloneMaterializedWitnessInfoMap(
            self,
            source.materialized_witness_infos,
        );
    try clone.symbolic_dummy_infos.appendSlice(
        self.shared.allocator,
        source.symbolic_dummy_infos.items,
    );
    return clone;
}

pub fn boundValueMatchesExpr(
    self: anytype,
    bound: BoundValue,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    return switch (bound) {
        .concrete => |concrete| {
            return try concreteBindingMatchesExpr(
                self,
                concrete,
                actual,
                state,
            );
        },
        .symbolic => |symbolic| {
            return try TransparentMatch.matchSymbolicToExprState(
                self,
                symbolic.expr,
                actual,
                state,
            );
        },
    };
}

pub fn concreteBindingMatchesExpr(
    self: anytype,
    concrete: ConcreteBinding,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (concrete.mode == .exact) {
        return concrete.raw == actual;
    }
    const actual_repr = try chooseRepresentativeSymbolic(
        self,
        actual,
        state,
        concrete.mode,
    );
    return symbolicExprEql(self, concrete.repr, actual_repr);
}

pub fn boundValueMatchesSymbolic(
    self: anytype,
    bound: BoundValue,
    actual: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    return switch (bound) {
        .concrete => |concrete| {
            const match_expr = (try concreteBindingMatchExpr(
                self,
                concrete,
                state,
            )) orelse return false;
            return try TransparentMatch.matchExprToSymbolic(
                self,
                match_expr,
                actual,
                state,
                concrete.mode,
            );
        },
        .symbolic => |symbolic| {
            return try TransparentMatch.matchSymbolicToSymbolicState(
                self,
                symbolic.expr,
                actual,
                state,
            );
        },
    };
}

pub fn concreteBindingMatchExpr(
    self: anytype,
    concrete: ConcreteBinding,
    state: *MatchSession,
) anyerror!?ExprId {
    if (concrete.mode == .exact) return concrete.raw;
    return try materializeRepresentativeSymbolic(
        self,
        concrete.repr,
        state,
    );
}

pub fn matchSymbolicDummyState(
    self: anytype,
    slot: usize,
    info: SymbolicDummyInfo,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const root = try resolveDummySlot(self, slot, state);
    const root_info = state.symbolic_dummy_infos.items[root];

    // Matching a symbolic dummy against a non-variable is a plain mismatch,
    // not a fatal error.
    const actual_info = getConcreteVarInfo(self, actual) catch |err| switch (err) {
        error.ExpectedVariable => return false,
        else => return err,
    };
    if (root_info.bound and !actual_info.bound) return false;
    if (!std.mem.eql(u8, root_info.sort_name, actual_info.sort_name)) {
        return false;
    }
    _ = info;

    if (currentWitnessExpr(self, root, state)) |existing| {
        if (existing == actual) return true;
        if (isProvisionalWitnessExpr(self, existing, state)) {
            try putWitnessForDummySlot(self, root, actual, state);
            return true;
        }
        return false;
    }
    try putWitnessForDummySlot(self, root, actual, state);
    return true;
}

pub fn matchDummyToSymbolic(
    self: anytype,
    slot: usize,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    return switch (rhs.*) {
        .binder => |idx| blk: {
            const symbolic = try self.allocSymbolic(.{ .dummy = slot });
            break :blk try assignBinderFromSymbolic(
                self,
                idx,
                symbolic,
                state,
                .transparent,
            );
        },
        .fixed => |expr_id| {
            const info = state.symbolic_dummy_infos.items[slot];
            return try matchSymbolicDummyState(
                self,
                slot,
                info,
                expr_id,
                state,
            );
        },
        .dummy => |rhs_slot| {
            return try alignDummySlots(self, slot, rhs_slot, state);
        },
        .app => {
            const rhs_expr = try materializeAssignedSymbolic(
                self,
                rhs,
                state,
                .transparent,
            ) orelse return false;
            const info = state.symbolic_dummy_infos.items[slot];
            return try matchSymbolicDummyState(
                self,
                slot,
                info,
                rhs_expr,
                state,
            );
        },
    };
}

/// Materialize the current binding state, then project each binding
/// through its representative-selection mode.
pub fn representResolvedBindings(
    self: anytype,
    state: *MatchSession,
    bindings: []?ExprId,
) anyerror!void {
    for (state.bindings, 0..) |binding, idx| {
        bindings[idx] = if (binding) |bound| blk: {
            const materialized = try materializeResolvedBoundValue(
                self,
                bound,
                state,
            );
            break :blk try projectMaterializedExpr(
                self,
                materialized,
                switch (bound) {
                    .concrete => |concrete| concrete.mode,
                    .symbolic => |symbolic| symbolic.mode,
                },
            );
        } else null;
    }
}

fn exprDeps(self: anytype, expr_id: ExprId) anyerror!u55 {
    return switch (self.shared.theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| blk: {
                if (idx >= self.shared.theorem.arg_infos.len) {
                    return error.UnknownTheoremVariable;
                }
                break :blk self.shared.theorem.arg_infos[idx].deps;
            },
            .dummy_var => |idx| blk: {
                if (idx >= self.shared.theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                break :blk self.shared.theorem.theorem_dummies.items[idx].deps;
            },
        },
        .app => |app| blk: {
            var deps: u55 = 0;
            for (app.args) |arg| {
                deps |= try exprDeps(self, arg);
            }
            break :blk deps;
        },
    };
}

fn collectUnresolvedRootsInSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    out: *std.ArrayListUnmanaged(UnresolvedDummyRoot),
    seen_roots: *std.AutoHashMapUnmanaged(usize, void),
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (symbolic.*) {
        .binder => |idx| {
            const seen = try seen_binders.getOrPut(
                self.shared.allocator,
                idx,
            );
            if (seen.found_existing) return;
            const bound = state.bindings[idx] orelse {
                return error.MissingBinderAssignment;
            };
            try collectUnresolvedRootsInBoundValue(
                self,
                bound,
                state,
                out,
                seen_roots,
                seen_binders,
            );
        },
        .fixed => {},
        .dummy => |slot| {
            const root = try resolveDummySlot(self, slot, state);
            if (state.witnesses.get(root) != null or
                state.materialized_witnesses.get(root) != null) return;
            const seen = try seen_roots.getOrPut(
                self.shared.allocator,
                root,
            );
            if (seen.found_existing) return;
            const info = state.symbolic_dummy_infos.items[root];
            try out.append(self.shared.allocator, .{
                .root_slot = root,
                .sort_name = info.sort_name,
                .bound = info.bound,
            });
        },
        .app => |app| {
            for (app.args) |arg| {
                try collectUnresolvedRootsInSymbolic(
                    self,
                    arg,
                    state,
                    out,
                    seen_roots,
                    seen_binders,
                );
            }
        },
    }
}

pub fn collectUnresolvedRootsInBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
    out: *std.ArrayListUnmanaged(UnresolvedDummyRoot),
    seen_roots: *std.AutoHashMapUnmanaged(usize, void),
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (bound) {
        .concrete => |concrete| try collectUnresolvedRootsInSymbolic(
            self,
            concrete.repr,
            state,
            out,
            seen_roots,
            seen_binders,
        ),
        .symbolic => |symbolic| try collectUnresolvedRootsInSymbolic(
            self,
            symbolic.expr,
            state,
            out,
            seen_roots,
            seen_binders,
        ),
    }
}

fn collectConcreteDepsInSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    deps: *u55,
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (symbolic.*) {
        .binder => |idx| {
            const seen = try seen_binders.getOrPut(
                self.shared.allocator,
                idx,
            );
            if (seen.found_existing) return;
            const bound = state.bindings[idx] orelse {
                return error.MissingBinderAssignment;
            };
            try collectConcreteDepsInBoundValue(
                self,
                bound,
                state,
                deps,
                seen_binders,
            );
        },
        .fixed => |expr_id| deps.* |= try exprDeps(self, expr_id),
        .dummy => |slot| {
            const root = try resolveDummySlot(self, slot, state);
            if (state.witnesses.get(root)) |expr_id| {
                deps.* |= try exprDeps(self, expr_id);
            }
            if (state.materialized_witnesses.get(root)) |expr_id| {
                deps.* |= try exprDeps(self, expr_id);
            }
        },
        .app => |app| {
            for (app.args) |arg| {
                try collectConcreteDepsInSymbolic(
                    self,
                    arg,
                    state,
                    deps,
                    seen_binders,
                );
            }
        },
    }
}

pub fn collectConcreteDepsInBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
    deps: *u55,
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!void {
    switch (bound) {
        .concrete => |concrete| {
            deps.* |= try exprDeps(self, concrete.raw);
            try collectConcreteDepsInSymbolic(
                self,
                concrete.repr,
                state,
                deps,
                seen_binders,
            );
        },
        .symbolic => |symbolic| try collectConcreteDepsInSymbolic(
            self,
            symbolic.expr,
            state,
            deps,
            seen_binders,
        ),
    }
}

/// Materialize the concrete expression justified by the current match
/// state without applying representative selection.
pub fn materializeResolvedBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (bound) {
        .concrete => |concrete| concrete.raw,
        .symbolic => |symbolic| try materializeResolvedSymbolic(
            self,
            symbolic.expr,
            state,
        ),
    };
}

/// Project a materialized expression through the binding mode's
/// representative-selection semantics.
pub fn projectMaterializedExpr(
    self: anytype,
    expr_id: ?ExprId,
    mode: BindingMode,
) anyerror!?ExprId {
    const materialized = expr_id orelse return null;
    return try chooseRepresentative(self, materialized, mode);
}

// This is the only escape path that turns symbolic match state back into
// main-theorem expressions. Internal matching and representative work
// should stay symbolic until a caller explicitly finalizes bindings.
/// Finalize a BoundValue to a concrete ExprId. Returns
/// error.UnresolvedDummyWitness if any hidden-dummy slot in the
/// symbolic structure lacks a witness.
pub fn finalizeBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!ExprId {
    return switch (bound) {
        .concrete => |concrete| {
            return (try concreteBindingMatchExpr(
                self,
                concrete,
                state,
            )) orelse error.MissingRepresentative;
        },
        .symbolic => |symbolic| {
            const expr_id = try materializeFinalSymbolic(
                self,
                symbolic.expr,
                state,
            );
            return try chooseRepresentative(self, expr_id, symbolic.mode);
        },
    };
}

pub fn materializeAssignedBoundValue(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (bound) {
        .concrete => |concrete| try concreteBindingMatchExpr(
            self,
            concrete,
            state,
        ),
        .symbolic => |symbolic| {
            return try materializeAssignedSymbolic(
                self,
                symbolic.expr,
                state,
                symbolic.mode,
            );
        },
    };
}

pub fn materializeRepresentativeSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx >= state.bindings.len) break :blk null;
            const bound = state.bindings[idx] orelse break :blk null;
            break :blk try materializeAssignedBoundValue(self, bound, state);
        },
        .fixed => |expr| expr,
        .dummy => |slot| currentWitnessExpr(self, slot, state),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try materializeRepresentativeSymbolic(
                    self,
                    arg,
                    state,
                )) orelse break :blk null;
            }
            break :blk try self.shared.theorem.interner.internAppOwned(
                app.term_id,
                args,
            );
        },
    };
}

pub fn materializeAssignedSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!?ExprId {
    const expr_id = try materializeRepresentativeSymbolic(
        self,
        symbolic,
        state,
    ) orelse return null;
    return try chooseRepresentative(self, expr_id, mode);
}

pub fn materializeResolvedSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?ExprId {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx >= state.bindings.len) {
                return error.TemplateBinderOutOfRange;
            }
            const bound = state.bindings[idx] orelse break :blk null;
            break :blk try materializeResolvedBoundValue(
                self,
                bound,
                state,
            );
        },
        .fixed => |expr_id| expr_id,
        .dummy => |slot| currentWitnessExpr(self, slot, state),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try materializeResolvedSymbolic(
                    self,
                    arg,
                    state,
                )) orelse break :blk null;
            }
            break :blk try self.shared.theorem.interner.internAppOwned(
                app.term_id,
                args,
            );
        },
    };
}

/// Materialize a symbolic expression to a concrete ExprId. Returns
/// error.UnresolvedDummyWitness if any hidden-dummy slot lacks a witness.
pub fn materializeFinalSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!ExprId {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx >= state.bindings.len) {
                return error.TemplateBinderOutOfRange;
            }
            const bound = state.bindings[idx] orelse {
                return error.MissingBinderAssignment;
            };
            break :blk try finalizeBoundValue(self, bound, state);
        },
        .fixed => |expr_id| expr_id,
        .dummy => |slot| try resolveWitnessForDummySlot(self, slot, state),
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(ExprId, app.args.len);
            errdefer self.shared.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = try materializeFinalSymbolic(
                    self,
                    arg,
                    state,
                );
            }
            break :blk try self.shared.theorem.interner.internAppOwned(
                app.term_id,
                args,
            );
        },
    };
}

pub fn currentWitnessExpr(
    self: anytype,
    slot: usize,
    state: *const MatchSession,
) ?ExprId {
    const root = resolveDummySlot(self, slot, state) catch return null;
    return state.witnesses.get(root) orelse
        state.materialized_witnesses.get(root);
}

pub fn isProvisionalWitnessExpr(
    self: anytype,
    expr_id: ExprId,
    state: *const MatchSession,
) bool {
    _ = self;
    return state.provisional_witness_infos.contains(expr_id) or
        state.materialized_witness_infos.contains(expr_id);
}

/// Resolve a hidden-dummy slot to a concrete ExprId. Only succeeds
/// if the slot was previously filled by a witness during matching.
/// Returns error.UnresolvedDummyWitness if the slot has no witness —
/// the user must provide explicit bindings that cover the hidden
/// def structure.
pub fn resolveWitnessForDummySlot(
    self: anytype,
    slot: usize,
    state: *MatchSession,
) anyerror!ExprId {
    const root = try resolveDummySlot(self, slot, state);
    if (state.witnesses.get(root)) |existing| return existing;
    if (state.materialized_witnesses.get(root)) |existing| return existing;
    return error.UnresolvedDummyWitness;
}

pub fn getResymbolizableWitnessInfo(
    self: anytype,
    expr_id: ExprId,
) !?SymbolicDummyInfo {
    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .app => null,
        .variable => |var_id| switch (var_id) {
            .theorem_var => null,
            .dummy_var => |idx| blk: {
                if (idx >= self.shared.theorem.theorem_dummies.items.len) {
                    return error.UnknownDummyVar;
                }
                const dummy = self.shared.theorem.theorem_dummies.items[idx];
                if (dummy.kind != .placeholder) break :blk null;
                break :blk .{
                    .sort_name = dummy.sort_name,
                    .bound = true,
                };
            },
        },
    };
}

pub fn getConcreteVarInfo(self: anytype, expr_id: ExprId) !ConcreteVarInfo {
    const node = self.shared.theorem.interner.node(expr_id);
    const var_id = switch (node.*) {
        .variable => |value| value,
        .app => return error.ExpectedVariable,
    };
    return switch (var_id) {
        .theorem_var => |idx| blk: {
            if (idx >= self.shared.theorem.arg_infos.len) {
                return error.UnknownTheoremVariable;
            }
            const arg = self.shared.theorem.arg_infos[idx];
            break :blk .{
                .sort_name = arg.sort_name,
                .bound = arg.bound,
            };
        },
        .dummy_var => |idx| blk: {
            if (idx >= self.shared.theorem.theorem_dummies.items.len) {
                return error.UnknownDummyVar;
            }
            const dummy = self.shared.theorem.theorem_dummies.items[idx];
            break :blk .{
                .sort_name = dummy.sort_name,
                .bound = true,
            };
        },
    };
}
