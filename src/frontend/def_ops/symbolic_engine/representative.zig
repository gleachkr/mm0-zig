const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Canonicalizer = @import("../../canonicalizer.zig").Canonicalizer;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch = @import("./transparent_match.zig");
const Root = @import("witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const BoundValue = Types.BoundValue;
const RepresentativeCache = Types.RepresentativeCache;
const MatchSession = MatchState.MatchSession;

const symbolicSortName = Root.symbolicSortName;
const symbolicToConcreteIfPlain = Root.symbolicToConcreteIfPlain;
const symbolicExprEql = Root.symbolicExprEql;
const boundValueRepresentative = Root.boundValueRepresentative;
const slotForWitness = Root.slotForWitness;
const cloneRepresentativeState = Root.cloneRepresentativeState;
const materializeRepresentativeSymbolic = Root.materializeRepresentativeSymbolic;

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
    state: *MatchSession,
    mode: BindingMode,
) *RepresentativeCache {
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

    const cache = representativeCacheForMode(state, mode);
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

    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable => try self.allocSymbolic(.{ .fixed = expr_id }),
        .placeholder => |idx| try resymbolizePlaceholderExpr(
            self,
            expr_id,
            idx,
            state,
            &witness_slots,
        ),
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

pub fn resymbolizePlaceholderExpr(
    self: anytype,
    expr_id: ExprId,
    idx: usize,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!*const SymbolicExpr {
    const placeholder = try self.shared.theorem.requirePlaceholderInfo(idx);
    const slot = try slotForWitness(
        self,
        expr_id,
        .{
            .sort_name = placeholder.sort_name,
            .bound = true,
        },
        state,
        witness_slots,
    );
    return try self.allocSymbolic(.{ .dummy = slot });
}
