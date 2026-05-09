const std = @import("std");
const compareExprIds = @import("../acui_support.zig").compareExprIds;
const ExprId = @import("../expr.zig").ExprId;
const types = @import("./types.zig");
const StructuralProfile = types.StructuralProfile;

pub fn expressionsEqual(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
    profile: StructuralProfile,
) anyerror!bool {
    var lhs_items = std.ArrayListUnmanaged(ExprId){};
    defer lhs_items.deinit(self.allocator);
    var rhs_items = std.ArrayListUnmanaged(ExprId){};
    defer rhs_items.deinit(self.allocator);

    try collectItems(self, lhs, profile, &lhs_items);
    try collectItems(self, rhs, profile, &rhs_items);
    normalizeItems(self, profile, lhs_items.items);
    normalizeItems(self, profile, rhs_items.items);
    dedupItems(profile, &lhs_items);
    dedupItems(profile, &rhs_items);
    return itemListsEqual(lhs_items.items, rhs_items.items);
}

pub fn collectItems(
    self: anytype,
    expr_id: ExprId,
    profile: StructuralProfile,
    out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    const node = self.theorem.interner.node(expr_id);
    switch (node.*) {
        .variable => try out.append(self.allocator, expr_id),
        .placeholder => try out.append(self.allocator, expr_id),
        .app => |app| {
            if (app.term_id == profile.headTermId() and app.args.len == 2) {
                try collectItems(self, app.args[0], profile, out);
                try collectItems(self, app.args[1], profile, out);
                return;
            }
            if (app.term_id == profile.unitTermId() and app.args.len == 0 and
                profile.combiner.supportsLeftUnit() and
                profile.combiner.supportsRightUnit())
            {
                return;
            }
            try out.append(self.allocator, expr_id);
        },
    }
}

pub fn normalizeItems(
    self: anytype,
    profile: StructuralProfile,
    items: []ExprId,
) void {
    switch (profile.fragment) {
        .au, .aui => {},
        .acu, .acui => sortItems(self, items),
    }
}

pub fn dedupItems(
    profile: StructuralProfile,
    items: *std.ArrayListUnmanaged(ExprId),
) void {
    switch (profile.fragment) {
        .au, .acu => {},
        .aui, .acui => dedupAdjacentItems(items),
    }
}

pub fn sortItems(self: anytype, items: []ExprId) void {
    var idx: usize = 1;
    while (idx < items.len) : (idx += 1) {
        const item = items[idx];
        var pos = idx;
        while (pos > 0 and compareExprIds(
            self.theorem,
            items[pos - 1],
            item,
        ) == .gt) : (pos -= 1) {
            items[pos] = items[pos - 1];
        }
        items[pos] = item;
    }
}

pub fn dedupAdjacentItems(items: *std.ArrayListUnmanaged(ExprId)) void {
    if (items.items.len <= 1) return;
    var write: usize = 1;
    var read: usize = 1;
    while (read < items.items.len) : (read += 1) {
        if (items.items[read] == items.items[write - 1]) continue;
        items.items[write] = items.items[read];
        write += 1;
    }
    items.shrinkRetainingCapacity(write);
}

pub fn itemListsEqual(lhs: []const ExprId, rhs: []const ExprId) bool {
    if (lhs.len != rhs.len) return false;
    for (lhs, rhs) |lhs_item, rhs_item| {
        if (lhs_item != rhs_item) return false;
    }
    return true;
}
