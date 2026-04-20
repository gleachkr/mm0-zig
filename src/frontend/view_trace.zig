const builtin = @import("builtin");
const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const BindingMode = @import("./def_ops.zig").BindingMode;
const BindingSeed = @import("./def_ops.zig").BindingSeed;
const BoundValue = @import("./def_ops/types.zig").BoundValue;
const SymbolicExpr = @import("./def_ops/types.zig").SymbolicExpr;

pub fn printViewBindings(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    label: []const u8,
    bindings: []const ?ExprId,
    seeds: ?[]const BindingSeed,
) anyerror!void {
    debugPrint("[debug:views] {s}\n", .{label});
    for (bindings, 0..) |binding, idx| {
        const name = binderLabel(view_arg_names, idx);
        if (binding) |expr_id| {
            const text = try formatExpr(allocator, theorem, env, expr_id);
            defer allocator.free(text);
            debugPrint(
                "[debug:views]   {s}#{d} = {s}\n",
                .{ name, idx, text },
            );
        } else {
            debugPrint(
                "[debug:views]   {s}#{d} = <null>\n",
                .{ name, idx },
            );
        }
        if (seeds) |all_seeds| {
            if (idx < all_seeds.len) {
                const seed_text = try formatBindingSeed(
                    allocator,
                    theorem,
                    env,
                    view_arg_names,
                    all_seeds,
                    all_seeds[idx],
                );
                defer allocator.free(seed_text);
                debugPrint(
                    "[debug:views]     seed: {s}\n",
                    .{seed_text},
                );
            }
        }
    }
}

pub fn printRecoverState(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    target_idx: usize,
    source_idx: usize,
    pattern_idx: usize,
    hole_idx: usize,
    bindings: []const ?ExprId,
    seeds: ?[]const BindingSeed,
) anyerror!void {
    debugPrint(
        "[debug:views] recover {s}#{d} from {s}#{d} via {s}#{d} hole {s}#{d}\n",
        .{
            binderLabel(view_arg_names, target_idx),
            target_idx,
            binderLabel(view_arg_names, source_idx),
            source_idx,
            binderLabel(view_arg_names, pattern_idx),
            pattern_idx,
            binderLabel(view_arg_names, hole_idx),
            hole_idx,
        },
    );
    try printSingleBinding(
        allocator,
        theorem,
        env,
        view_arg_names,
        "target",
        target_idx,
        bindings,
        seeds,
    );
    try printSingleBinding(
        allocator,
        theorem,
        env,
        view_arg_names,
        "source",
        source_idx,
        bindings,
        seeds,
    );
    try printSingleBinding(
        allocator,
        theorem,
        env,
        view_arg_names,
        "pattern",
        pattern_idx,
        bindings,
        seeds,
    );
    try printSingleBinding(
        allocator,
        theorem,
        env,
        view_arg_names,
        "hole",
        hole_idx,
        bindings,
        seeds,
    );
}

pub fn printMessage(comptime fmt: []const u8, args: anytype) void {
    debugPrint("[debug:views] " ++ fmt ++ "\n", args);
}

pub fn formatExpr(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) ![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);
    try appendExpr(&out, allocator, theorem, env, expr_id);
    return try out.toOwnedSlice(allocator);
}

pub fn formatBindingSeed(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    all_seeds: []const BindingSeed,
    seed: BindingSeed,
) ![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);
    var seen = std.ArrayListUnmanaged(usize){};
    defer seen.deinit(allocator);
    try appendSeed(
        &out,
        allocator,
        theorem,
        env,
        view_arg_names,
        all_seeds,
        seed,
        &seen,
    );
    return try out.toOwnedSlice(allocator);
}

fn printSingleBinding(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    role: []const u8,
    idx: usize,
    bindings: []const ?ExprId,
    seeds: ?[]const BindingSeed,
) anyerror!void {
    const name = binderLabel(view_arg_names, idx);
    if (idx < bindings.len) {
        if (bindings[idx]) |expr_id| {
            const text = try formatExpr(allocator, theorem, env, expr_id);
            defer allocator.free(text);
            debugPrint(
                "[debug:views]   {s} {s}#{d} = {s}\n",
                .{ role, name, idx, text },
            );
        } else {
            debugPrint(
                "[debug:views]   {s} {s}#{d} = <null>\n",
                .{ role, name, idx },
            );
        }
    } else {
        debugPrint(
            "[debug:views]   {s} {s}#{d} = <null>\n",
            .{ role, name, idx },
        );
    }
    if (seeds) |all_seeds| {
        if (idx < all_seeds.len) {
            const seed_text = try formatBindingSeed(
                allocator,
                theorem,
                env,
                view_arg_names,
                all_seeds,
                all_seeds[idx],
            );
            defer allocator.free(seed_text);
            debugPrint(
                "[debug:views]     {s} seed: {s}\n",
                .{ role, seed_text },
            );
        }
    }
}

fn debugPrint(comptime fmt: []const u8, args: anytype) void {
    if (comptime builtin.target.os.tag == .freestanding) return;
    std.debug.print(fmt, args);
}

fn appendExpr(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) anyerror!void {
    switch (theorem.interner.node(expr_id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try out.writer(allocator).print("v{d}", .{idx});
            },
            .dummy_var => |idx| {
                try out.writer(allocator).print(".d{d}", .{idx});
            },
        },
        .placeholder => |idx| {
            try out.writer(allocator).print(".p{d}", .{idx});
        },
        .app => |app| {
            const term_name = if (app.term_id < env.terms.items.len)
                env.terms.items[app.term_id].name
            else
                "<term>";
            try out.writer(allocator).print("{s}", .{term_name});
            if (app.args.len == 0) return;
            try out.append(allocator, '(');
            for (app.args, 0..) |arg, idx| {
                if (idx != 0) try out.appendSlice(allocator, ", ");
                try appendExpr(out, allocator, theorem, env, arg);
            }
            try out.append(allocator, ')');
        },
    }
}

fn appendSeed(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    all_seeds: []const BindingSeed,
    seed: BindingSeed,
    seen: *std.ArrayListUnmanaged(usize),
) anyerror!void {
    switch (seed) {
        .none => try out.appendSlice(allocator, "none"),
        .exact => |expr_id| {
            try out.appendSlice(allocator, "exact(");
            try appendExpr(out, allocator, theorem, env, expr_id);
            try out.append(allocator, ')');
        },
        .semantic => |semantic| {
            try out.writer(allocator).print(
                "semantic({s}, ",
                .{bindingModeName(semantic.mode)},
            );
            try appendExpr(out, allocator, theorem, env, semantic.expr_id);
            try out.append(allocator, ')');
        },
        .bound => |bound| try appendBoundValue(
            out,
            allocator,
            theorem,
            env,
            view_arg_names,
            all_seeds,
            bound,
            seen,
        ),
    }
}

fn appendBoundValue(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    all_seeds: []const BindingSeed,
    bound: BoundValue,
    seen: *std.ArrayListUnmanaged(usize),
) anyerror!void {
    switch (bound) {
        .concrete => |concrete| {
            try out.writer(allocator).print(
                "bound.concrete({s}, raw=",
                .{bindingModeName(concrete.mode)},
            );
            try appendExpr(
                out,
                allocator,
                theorem,
                env,
                concrete.raw,
            );
            try out.append(allocator, ')');
        },
        .symbolic => |symbolic| {
            try out.writer(allocator).print(
                "bound.symbolic({s}, ",
                .{bindingModeName(symbolic.mode)},
            );
            try appendSymbolic(
                out,
                allocator,
                theorem,
                env,
                view_arg_names,
                all_seeds,
                symbolic.expr,
                seen,
            );
            try out.append(allocator, ')');
        },
    }
}

fn appendSymbolic(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    view_arg_names: []const ?[]const u8,
    all_seeds: []const BindingSeed,
    symbolic: *const SymbolicExpr,
    seen: *std.ArrayListUnmanaged(usize),
) anyerror!void {
    switch (symbolic.*) {
        .binder => |idx| {
            const name = binderLabel(view_arg_names, idx);
            try out.writer(allocator).print(
                "binder({s}#{d}",
                .{ name, idx },
            );
            if (!containsIndex(seen.items, idx) and idx < all_seeds.len) {
                try seen.append(allocator, idx);
                defer _ = seen.pop();
                try out.appendSlice(allocator, " => ");
                try appendSeed(
                    out,
                    allocator,
                    theorem,
                    env,
                    view_arg_names,
                    all_seeds,
                    all_seeds[idx],
                    seen,
                );
            }
            try out.append(allocator, ')');
        },
        .fixed => |expr_id| {
            try out.appendSlice(allocator, "fixed(");
            try appendExpr(out, allocator, theorem, env, expr_id);
            try out.append(allocator, ')');
        },
        .dummy => |slot| {
            try out.writer(allocator).print("dummy({d})", .{slot});
        },
        .app => |app| {
            const term_name = if (app.term_id < env.terms.items.len)
                env.terms.items[app.term_id].name
            else
                "<term>";
            try out.writer(allocator).print("{s}(", .{term_name});
            for (app.args, 0..) |arg, idx| {
                if (idx != 0) try out.appendSlice(allocator, ", ");
                try appendSymbolic(
                    out,
                    allocator,
                    theorem,
                    env,
                    view_arg_names,
                    all_seeds,
                    arg,
                    seen,
                );
            }
            try out.append(allocator, ')');
        },
    }
}

pub fn binderLabel(view_arg_names: []const ?[]const u8, idx: usize) []const u8 {
    if (idx < view_arg_names.len) {
        if (view_arg_names[idx]) |name| return name;
    }
    return "_";
}

fn bindingModeName(mode: BindingMode) []const u8 {
    return switch (mode) {
        .exact => "exact",
        .transparent => "transparent",
        .normalized => "normalized",
    };
}

fn containsIndex(items: []const usize, needle: usize) bool {
    for (items) |item| {
        if (item == needle) return true;
    }
    return false;
}
