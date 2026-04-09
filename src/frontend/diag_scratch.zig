const std = @import("std");

pub const MissingCongruenceReason = enum {
    missing_rule,
    changed_bound_arg,
    missing_child_relation,
    missing_child_proof,
    missing_parent_relation,
    malformed_rule,
    unknown_term,
};

pub const CapturedDetail = union(enum) {
    missing_congruence_rule: struct {
        reason: MissingCongruenceReason,
        term_id: ?u32 = null,
        sort_name: ?[]const u8 = null,
        arg_index: ?usize = null,
    },
};

pub const CapturedEntry = struct {
    err: anyerror,
    detail: CapturedDetail,
};

pub const Scratch = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayListUnmanaged(CapturedEntry) = .{},

    pub const Mark = struct {
        start: usize,
    };

    pub fn init(allocator: std.mem.Allocator) Scratch {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Scratch) void {
        self.entries.deinit(self.allocator);
    }

    pub fn mark(self: *Scratch) Mark {
        return .{ .start = self.entries.items.len };
    }

    pub fn discard(self: *Scratch, scratch_mark: Mark) void {
        self.entries.shrinkRetainingCapacity(scratch_mark.start);
    }

    pub fn record(
        self: *Scratch,
        err: anyerror,
        detail: CapturedDetail,
    ) void {
        self.entries.append(self.allocator, .{
            .err = err,
            .detail = detail,
        }) catch {};
    }

    pub fn takeSince(
        self: *Scratch,
        scratch_mark: Mark,
        err: anyerror,
    ) ?CapturedDetail {
        var i = self.entries.items.len;
        while (i > scratch_mark.start) {
            i -= 1;
            const entry = self.entries.items[i];
            if (entry.err == err) {
                const detail = entry.detail;
                self.entries.shrinkRetainingCapacity(scratch_mark.start);
                return detail;
            }
        }
        self.entries.shrinkRetainingCapacity(scratch_mark.start);
        return null;
    }
};
