const builtin = @import("builtin");
const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const ViewTrace = @import("../view_trace.zig");
const DebugTrace = @import("../debug.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralItems = @import("./items.zig");
const types = @import("./types.zig");
const BranchState = types.BranchState;

pub const SolutionPreference = enum {
    first,
    minimal_structural,
};

pub const AmbiguityReport = struct {
    distinct_solution_count: usize = 0,
    chosen_bindings: ?[]const u8 = null,
    alternative_bindings: ?[]const u8 = null,
};

pub fn pickUniqueSolution(
    self: anytype,
    states: []const BranchState,
    preference: SolutionPreference,
) anyerror![]const ExprId {
    if (states.len == 0) return error.UnifyMismatch;

    var distinct_idxs = std.ArrayListUnmanaged(usize){};
    defer distinct_idxs.deinit(self.allocator);

    for (states, 0..) |state, idx| {
        for (state.rule_bindings) |binding| {
            if (binding == null) return error.MissingBinderAssignment;
        }

        var already_seen = false;
        for (distinct_idxs.items) |seen_idx| {
            if (try SemanticCompare.sameRuleBindingsCompatible(
                self,
                states[seen_idx].rule_bindings,
                state.rule_bindings,
            )) {
                already_seen = true;
                break;
            }
        }
        if (!already_seen) {
            try distinct_idxs.append(self.allocator, idx);
        }
    }

    const chosen_distinct_idx = try chooseDistinctSolution(
        self,
        states,
        distinct_idxs.items,
        preference,
    );
    if (distinct_idxs.items.len > 1) {
        self.ambiguity_warning = true;
        try captureAmbiguityReport(
            self,
            states,
            distinct_idxs.items,
            chosen_distinct_idx,
        );
        if (self.debug.inference) {
            try debugPrintAmbiguousSolutions(
                self,
                states,
                distinct_idxs.items,
                chosen_distinct_idx,
                preference,
            );
        }
    }

    const chosen = states[distinct_idxs.items[chosen_distinct_idx]]
        .rule_bindings;
    const result = try self.allocator.alloc(ExprId, chosen.len);
    for (chosen, 0..) |binding, idx| {
        result[idx] = binding.?;
    }
    return result;
}

fn chooseDistinctSolution(
    self: anytype,
    states: []const BranchState,
    distinct_idxs: []const usize,
    preference: SolutionPreference,
) !usize {
    if (distinct_idxs.len == 0) return error.UnifyMismatch;
    switch (preference) {
        .first => return 0,
        .minimal_structural => {},
    }

    var best: usize = 0;
    var best_rank = try structuralBindingRank(
        self,
        states[distinct_idxs[0]].rule_bindings,
    );
    for (distinct_idxs[1..], 1..) |state_idx, distinct_idx| {
        const rank = try structuralBindingRank(
            self,
            states[state_idx].rule_bindings,
        );
        if (rank < best_rank) {
            best = distinct_idx;
            best_rank = rank;
        }
    }
    return best;
}

fn structuralBindingRank(
    self: anytype,
    bindings: []const ?ExprId,
) !usize {
    var rank: usize = 0;
    for (bindings, 0..) |maybe_binding, idx| {
        const binding = maybe_binding orelse continue;
        const sort_name = StructuralItems.getBinderSort(
            self,
            .rule,
            idx,
        ) orelse continue;
        const combiner = try self.registry.resolveStructuralCombinerForSort(
            self.env,
            sort_name,
        ) orelse continue;
        const profile = types.StructuralProfile.init(combiner);
        var items = std.ArrayListUnmanaged(ExprId){};
        defer items.deinit(self.allocator);
        try StructuralItems.collectCanonicalStructuralItems(
            self,
            binding,
            profile,
            &items,
        );
        rank += items.items.len;
    }
    return rank;
}

fn captureAmbiguityReport(
    self: anytype,
    states: []const BranchState,
    distinct_idxs: []const usize,
    chosen_distinct_idx: usize,
) !void {
    self.ambiguity_report.distinct_solution_count = distinct_idxs.len;
    if (distinct_idxs.len == 0) return;

    self.ambiguity_report.chosen_bindings = try formatBindingSummary(
        self,
        states[distinct_idxs[chosen_distinct_idx]].rule_bindings,
    );
    if (distinct_idxs.len > 1) {
        const alt_idx: usize = if (chosen_distinct_idx == 0) 1 else 0;
        self.ambiguity_report.alternative_bindings = try formatBindingSummary(
            self,
            states[distinct_idxs[alt_idx]].rule_bindings,
        );
    }
}

fn formatBindingSummary(
    self: anytype,
    bindings: []const ?ExprId,
) ![]const u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(self.allocator);

    var emitted: usize = 0;
    for (bindings, 0..) |binding, idx| {
        if (emitted == 3) break;
        if (emitted != 0) {
            try out.appendSlice(self.allocator, "; ");
        }

        const name = self.rule.arg_names[idx] orelse "_";
        try out.writer(self.allocator).print("{s} = ", .{name});
        if (binding) |expr_id| {
            const text = try ViewTrace.formatExpr(
                self.allocator,
                self.theorem,
                self.env,
                expr_id,
            );
            defer self.allocator.free(text);
            try appendTruncatedText(&out, self.allocator, text, 48);
        } else {
            try out.appendSlice(self.allocator, "<unsolved>");
        }
        emitted += 1;
    }

    if (bindings.len > emitted) {
        try out.writer(self.allocator).print(
            "; +{d} more",
            .{bindings.len - emitted},
        );
    }
    return try out.toOwnedSlice(self.allocator);
}

fn debugPrintAmbiguousSolutions(
    self: anytype,
    states: []const BranchState,
    distinct_idxs: []const usize,
    chosen_distinct_idx: usize,
    preference: SolutionPreference,
) !void {
    if (comptime builtin.target.os.tag == .freestanding) return;

    DebugTrace.traceInference(
        self.debug,
        "omitted binders left {d} distinct final solutions; " ++
            "choosing by {s}",
        .{ distinct_idxs.len, solutionPreferenceName(preference) },
    );
    for (distinct_idxs, 0..) |state_idx, choice_idx| {
        DebugTrace.traceInference(
            self.debug,
            "  solution {d}{s}",
            .{
                choice_idx + 1,
                if (choice_idx == chosen_distinct_idx) " (chosen)" else "",
            },
        );
        try debugPrintRuleBindings(self, states[state_idx].rule_bindings);
    }
}

fn debugPrintRuleBindings(
    self: anytype,
    bindings: []const ?ExprId,
) !void {
    for (bindings, 0..) |binding, idx| {
        const name = self.rule.arg_names[idx] orelse "_";
        const text = if (binding) |expr_id| blk: {
            break :blk try ViewTrace.formatExpr(
                self.allocator,
                self.theorem,
                self.env,
                expr_id,
            );
        } else null;
        defer if (text) |value| self.allocator.free(value);

        DebugTrace.traceInference(
            self.debug,
            "    {s}#{d} = {s}",
            .{ name, idx, text orelse "<null>" },
        );
    }
}

fn solutionPreferenceName(preference: SolutionPreference) []const u8 {
    return switch (preference) {
        .first => "first solution",
        .minimal_structural => "minimal structural residual",
    };
}

fn appendTruncatedText(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    text: []const u8,
    limit: usize,
) !void {
    if (text.len <= limit) {
        try out.appendSlice(allocator, text);
        return;
    }
    if (limit <= 1) {
        try out.appendSlice(allocator, text[0..limit]);
        return;
    }
    try out.appendSlice(allocator, text[0 .. limit - 1]);
    try out.appendSlice(allocator, "...");
}
