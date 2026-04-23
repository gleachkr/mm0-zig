const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralItems = @import("./structural_items.zig");
const StructuralStateUpdates =
    @import("./structural_state_updates.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;
const StructuralProfile = types.StructuralProfile;
const StructuralRemainder = types.StructuralRemainder;
const StructuralTemplateItem = types.StructuralTemplateItem;

pub fn matchStructural(
    comptime Matcher: type,
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror!?[]BranchState {
    const app = switch (template) {
        .app => |value| value,
        .binder => return null,
    };
    const profile =
        try StructuralItems.resolveStructuralProfile(self, app.term_id) orelse
        return null;

    const bindings = BranchStateOps.getBindings(self, @constCast(&state), space);

    var template_items = std.ArrayListUnmanaged(StructuralTemplateItem){};
    defer template_items.deinit(self.allocator);
    var pre_required = std.ArrayListUnmanaged(ExprId){};
    defer pre_required.deinit(self.allocator);
    var remainders = std.ArrayListUnmanaged(StructuralRemainder){};
    defer remainders.deinit(self.allocator);
    try StructuralItems.collectTemplateStructuralItems(
        self,
        template,
        space,
        profile,
        &template_items,
        &remainders,
        bindings,
        &pre_required,
    );

    var actual_items = std.ArrayListUnmanaged(ExprId){};
    defer actual_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        actual,
        profile,
        &actual_items,
    );

    if (!profile.isCommutative()) {
        if (pre_required.items.len != 0) return &.{};
        return try matchOrderedStructural(
            Matcher,
            self,
            template_items.items,
            actual_items.items,
            remainders.items,
            space,
            state,
            profile,
        );
    }

    const used = try self.allocator.alloc(bool, actual_items.items.len);
    defer self.allocator.free(used);
    @memset(used, false);

    for (pre_required.items) |required| {
        var found = false;
        for (actual_items.items, 0..) |actual_item, idx| {
            if (profile.fragment != .acui and used[idx]) continue;
            if (!try SemanticCompare.bindingCompatible(
                self,
                required,
                actual_item,
            )) continue;
            used[idx] = true;
            found = true;
            break;
        }
        if (!found) return &.{};
    }

    var matches = std.ArrayListUnmanaged(BranchState){};
    try matchCommutativeStructuralObligations(
        Matcher,
        self,
        template_items.items,
        actual_items.items,
        remainders.items,
        space,
        0,
        used,
        state,
        &matches,
        profile,
    );
    if (matches.items.len == 0) return &.{};
    return try matches.toOwnedSlice(self.allocator);
}

fn matchOrderedStructural(
    comptime Matcher: type,
    self: anytype,
    template_items: []const StructuralTemplateItem,
    actual_items: []const ExprId,
    remainders: []const StructuralRemainder,
    space: BinderSpace,
    state: BranchState,
    profile: StructuralProfile,
) anyerror![]BranchState {
    if (actual_items.len < template_items.len) return &.{};

    const matched_positions =
        try self.allocator.alloc(usize, template_items.len);
    defer self.allocator.free(matched_positions);

    var out = std.ArrayListUnmanaged(BranchState){};
    try matchOrderedStructuralAnchors(
        Matcher,
        self,
        template_items,
        actual_items,
        remainders,
        space,
        state,
        profile,
        0,
        0,
        matched_positions,
        &out,
    );
    if (out.items.len == 0) return &.{};
    return try out.toOwnedSlice(self.allocator);
}

fn matchOrderedStructuralAnchors(
    comptime Matcher: type,
    self: anytype,
    template_items: []const StructuralTemplateItem,
    actual_items: []const ExprId,
    remainders: []const StructuralRemainder,
    space: BinderSpace,
    state: BranchState,
    profile: StructuralProfile,
    next_item: usize,
    actual_start: usize,
    matched_positions: []usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (next_item >= template_items.len) {
        try appendOrderedStructuralMatchState(
            self,
            actual_items,
            remainders,
            matched_positions[0..template_items.len],
            space,
            state,
            out,
            profile,
        );
        return;
    }

    var actual_idx = actual_start;
    while (actual_idx + (template_items.len - next_item) <= actual_items.len) : (actual_idx += 1) {
        const matches = try matchStructuralItem(
            Matcher,
            self,
            template_items[next_item],
            actual_items[actual_idx],
            space,
            state,
        );
        for (matches) |next_state| {
            matched_positions[next_item] = actual_idx;
            try matchOrderedStructuralAnchors(
                Matcher,
                self,
                template_items,
                actual_items,
                remainders,
                space,
                next_state,
                profile,
                next_item + 1,
                actual_idx + 1,
                matched_positions,
                out,
            );
        }
    }
}

fn appendOrderedStructuralMatchState(
    self: anytype,
    actual_items: []const ExprId,
    remainders: []const StructuralRemainder,
    matched_positions: []const usize,
    space: BinderSpace,
    state: BranchState,
    out: *std.ArrayListUnmanaged(BranchState),
    profile: StructuralProfile,
) anyerror!void {
    var states = std.ArrayListUnmanaged(BranchState){};
    try states.append(
        self.allocator,
        try BranchStateOps.cloneState(self, state),
    );

    var segment_start: usize = 0;
    var remainder_start: usize = 0;
    var segment_idx: usize = 0;
    while (segment_idx <= matched_positions.len) : (segment_idx += 1) {
        const segment_end = if (segment_idx < matched_positions.len)
            matched_positions[segment_idx]
        else
            actual_items.len;
        const segment_items = actual_items[segment_start..segment_end];

        const group_start = remainder_start;
        while (remainder_start < remainders.len and
            remainders[remainder_start].item_pos == segment_idx) : (remainder_start += 1)
        {}
        const group = remainders[group_start..remainder_start];

        var next = std.ArrayListUnmanaged(BranchState){};
        if (group.len == 0) {
            if (segment_items.len != 0) return;
            try next.appendSlice(self.allocator, states.items);
        } else if (group.len == 1) {
            for (states.items) |current| {
                try StructuralStateUpdates.appendExactStructuralIntervalState(
                    self,
                    group[0].binder_idx,
                    segment_items,
                    space,
                    current,
                    &next,
                    profile,
                );
            }
        } else {
            const interval =
                try StructuralStateUpdates.buildExactStructuralInterval(
                    self,
                    segment_items,
                    profile,
                );
            for (states.items) |current| {
                try StructuralStateUpdates
                    .appendCombinedStructuralObligationState(
                    self,
                    group,
                    interval,
                    space,
                    current,
                    &next,
                );
            }
        }
        if (next.items.len == 0) return;
        states = next;

        if (segment_idx < matched_positions.len) {
            segment_start = matched_positions[segment_idx] + 1;
        }
    }

    try out.appendSlice(self.allocator, states.items);
}

fn matchCommutativeStructuralObligations(
    comptime Matcher: type,
    self: anytype,
    template_items: []const StructuralTemplateItem,
    actual_items: []const ExprId,
    remainders: []const StructuralRemainder,
    space: BinderSpace,
    next_item: usize,
    used: []bool,
    state: BranchState,
    out: *std.ArrayListUnmanaged(BranchState),
    profile: StructuralProfile,
) anyerror!void {
    if (next_item >= template_items.len) {
        try StructuralStateUpdates.appendStructuralRemainderState(
            self,
            actual_items,
            used,
            remainders,
            space,
            state,
            out,
            profile,
        );
        return;
    }

    for (actual_items, 0..) |actual_item, actual_idx| {
        if (profile.fragment != .acui and used[actual_idx]) continue;
        const matches = try matchStructuralItem(
            Matcher,
            self,
            template_items[next_item],
            actual_item,
            space,
            state,
        );
        for (matches) |next_state| {
            const was_used = used[actual_idx];
            used[actual_idx] = true;
            try matchCommutativeStructuralObligations(
                Matcher,
                self,
                template_items,
                actual_items,
                remainders,
                space,
                next_item + 1,
                used,
                next_state,
                out,
                profile,
            );
            used[actual_idx] = was_used;
        }
    }
}

fn matchStructuralItem(
    comptime Matcher: type,
    self: anytype,
    item: StructuralTemplateItem,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    return switch (item) {
        .template => |tmpl| try Matcher.matchExpr(
            self,
            tmpl,
            actual,
            space,
            state,
        ),
        .exact => |expected| blk: {
            if (!try SemanticCompare.bindingCompatible(
                self,
                expected,
                actual,
            )) {
                break :blk &.{};
            }
            const out = try self.allocator.alloc(BranchState, 1);
            out[0] = try BranchStateOps.cloneState(self, state);
            break :blk out;
        },
    };
}
