const std = @import("std");

const ExprModule = @import("../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const MM0Parser = @import("../trusted/parse.zig").MM0Parser;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;

pub fn containsHole(expr: *const Expr) bool {
    return switch (expr.*) {
        .hole => true,
        .variable => false,
        .term => |term| blk: {
            for (term.args) |arg| {
                if (containsHole(arg)) break :blk true;
            }
            break :blk false;
        },
    };
}

pub fn firstHoleSourceSpan(expr: *const Expr) ?SourceSpan {
    return switch (expr.*) {
        .hole => |hole| hole.token_span,
        .variable => null,
        .term => |term| blk: {
            for (term.args) |arg| {
                if (firstHoleSourceSpan(arg)) |span| break :blk span;
            }
            break :blk null;
        },
    };
}

pub fn sortNameById(env: *const GlobalEnv, sort_id: u7) ?[]const u8 {
    var it = env.sort_names.iterator();
    while (it.next()) |entry| {
        if (entry.value_ptr.* == sort_id) return entry.key_ptr.*;
    }
    return null;
}

pub fn parserSortName(parser: *const MM0Parser, sort: u7) []const u8 {
    var iter = parser.sort_names.iterator();
    while (iter.next()) |entry| {
        if (entry.value_ptr.* == sort) return entry.key_ptr.*;
    }
    return "?";
}

pub fn exprIdSortName(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) ![]const u8 {
    return switch (theorem.interner.node(expr_id).*) {
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            break :blk env.terms.items[app.term_id].ret_sort_name;
        },
        .variable, .placeholder => theorem.currentLeafSortName(expr_id) orelse {
            return error.UnknownSort;
        },
    };
}

pub fn exprIdSort(
    parser: *MM0Parser,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) !u7 {
    const name = try exprIdSortName(theorem, env, expr_id);
    return @intCast(parser.sort_names.get(name) orelse {
        return error.UnknownSort;
    });
}

pub fn containsStructuralHole(
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    expr: *const Expr,
) !bool {
    return switch (expr.*) {
        .hole => |hole| blk: {
            const sort_name = sortNameById(env, hole.sort) orelse {
                break :blk false;
            };
            break :blk (try registry.resolveStructuralCombinerForSort(
                env,
                sort_name,
            )) != null;
        },
        .variable => false,
        .term => |term| blk: {
            for (term.args) |arg| {
                if (try containsStructuralHole(env, registry, arg)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

pub fn lowerStructuralHolesToUnits(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    expr: *const Expr,
) !?ExprId {
    return switch (expr.*) {
        .hole => |hole| blk: {
            const sort_name = sortNameById(env, hole.sort) orelse return null;
            const acui = try registry.resolveStructuralCombinerForSort(
                env,
                sort_name,
            ) orelse return null;
            break :blk try theorem.interner.internApp(
                acui.unit_term_id,
                &.{},
            );
        },
        .variable => try theorem.internParsedExpr(expr),
        .term => |term| blk: {
            const args = try theorem.allocator.alloc(ExprId, term.args.len);
            errdefer theorem.allocator.free(args);
            for (term.args, 0..) |arg, idx| {
                args[idx] = (try lowerStructuralHolesToUnits(
                    theorem,
                    env,
                    registry,
                    arg,
                )) orelse {
                    theorem.allocator.free(args);
                    return null;
                };
            }
            break :blk try theorem.interner.internAppOwned(term.id, args);
        },
    };
}
