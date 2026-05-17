const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Root = @import("witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BoundValue = Types.BoundValue;
const MatchSession = MatchState.MatchSession;

const resymbolizePlaceholderExpr = Root.resymbolizePlaceholderExpr;

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
    if (self.shared.theorem.currentLeafSortName(expr_id)) |sort_name| {
        return sort_name;
    }

    const app = switch (self.shared.theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => return null,
    };
    return if (app.term_id < self.shared.env.terms.items.len)
        self.shared.env.terms.items[app.term_id].ret_sort_name
    else
        null;
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

    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable => null,
        .placeholder => |idx| try resymbolizePlaceholderExpr(
            self,
            expr_id,
            idx,
            state,
            witness_slots,
        ),
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
