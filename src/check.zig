const std = @import("std");
const Arg = @import("./args.zig").Arg;
const Sort = @import("./sorts.zig").Sort;
const Term = @import("./terms.zig").Term;
const Theorem = @import("./theorems.zig").Theorem;
const MM0Parser = @import("./parse.zig").MM0Parser;

pub const CrossChecker = struct {
    parser: MM0Parser,
    sort_names: std.StringHashMap(u8),  // name -> index
    arena: std.heap.ArenaAllocator,

    pub fn init(mm0_src: []const u8, backing: std.mem.Allocator) !*CrossChecker {
        const self = try backing.create(CrossChecker);
        self.arena = std.heap.ArenaAllocator.init(backing);
        self.parser = MM0Parser.init(mm0_src, self.arena.allocator());
        self.sort_names = std.StringHashMap(u8).init(self.arena.allocator());
        return self;
    }

    pub fn deinit(self: *CrossChecker, backing: std.mem.Allocator) void {
        self.arena.deinit();
        backing.destroy(self);
    }

    pub fn checkSort(self: *CrossChecker, sort_idx: u8, mmb_sort: Sort) !void {
        const stmt = try self.parser.next() orelse return error.MM0Exhausted;
        const mm0_sort = switch (stmt) {
            .sort => |s| s,
            else => return error.MM0Mismatch,
        };
        // Check modifiers match
        if (mm0_sort.modifiers.pure != mmb_sort.pure) return error.SortModifierMismatch;
        if (mm0_sort.modifiers.strict != mmb_sort.strict) return error.SortModifierMismatch;
        if (mm0_sort.modifiers.provable != mmb_sort.provable) return error.SortModifierMismatch;
        if (mm0_sort.modifiers.free != mmb_sort.free) return error.SortModifierMismatch;
        // Register sort name for later resolution
        try self.sort_names.put(mm0_sort.name, sort_idx);
    }

    pub fn checkTerm(self: *CrossChecker, mmb_term: Term, file_bytes: []const u8) !void {
        const stmt = try self.parser.next() orelse return error.MM0Exhausted;
        const mm0_term = switch (stmt) {
            .term => |t| t,
            else => return error.MM0Mismatch,
        };
        // Check is_def matches
        if (mm0_term.is_def != mmb_term.ret_sort.is_def) return error.TermKindMismatch;
        // Check arg count
        const mmb_args = mmb_term.getArgs(file_bytes);
        if (mm0_term.args.len != mmb_args.len) return error.ArgCountMismatch;
        // Check each arg's bound flag, deps, and sort
        for (mm0_term.args, mmb_args) |mm0_arg, mmb_arg| {
            if (mm0_arg.bound != mmb_arg.bound) return error.ArgBoundMismatch;
            if (mm0_arg.deps != mmb_arg.deps) return error.ArgDepsMismatch;
            const expected_sort = self.sort_names.get(mm0_arg.sort_name) 
                orelse return error.UnknownSort;
            if (expected_sort != mmb_arg.sort) return error.ArgSortMismatch;
        }
        // Check return sort
        const expected_ret = self.sort_names.get(mm0_term.ret_sort_name)
            orelse return error.UnknownSort;
        if (expected_ret != mmb_term.ret_sort.sort) return error.RetSortMismatch;
    }

    pub fn checkAssertion(self: *CrossChecker, mmb_thm: Theorem, file_bytes: []const u8) !void {
        const stmt = try self.parser.next() orelse return error.MM0Exhausted;
        const mm0_thm = switch (stmt) {
            .assertion => |a| a,
            else => return error.MM0Mismatch,
        };
        // Check arg count
        const mmb_args = mmb_thm.getArgs(file_bytes);
        if (mm0_thm.args.len != mmb_args.len) return error.ArgCountMismatch;
        // Check each arg's bound flag and sort
        for (mm0_thm.args, mmb_args) |mm0_arg, mmb_arg| {
            if (mm0_arg.bound != mmb_arg.bound) return error.ArgBoundMismatch;
            if (mm0_arg.deps != mmb_arg.deps) {
                std.debug.print("ArgDepsMismatch: thm={s} arg={} mm0_deps={b} mmb_deps={b} bound={}\n", .{
                    mm0_thm.name, mm0_arg, mm0_arg.deps, mmb_arg.deps, mm0_arg.bound,
                });
                return error.ArgDepsMismatch;
            }
            const expected_sort = self.sort_names.get(mm0_arg.sort_name)
                orelse return error.UnknownSort;
            if (expected_sort != mmb_arg.sort) return error.ArgSortMismatch;
        }
    }
};
