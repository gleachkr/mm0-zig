const std = @import("std");
const Expr = @import("./expressions.zig").Expr;
const Proof = @import("./proof.zig");
const Sort = @import("./sorts.zig").Sort;
const Term = @import("./terms.zig").Term;
const Theorem = @import("./theorems.zig").Theorem;
const parse = @import("./parse.zig");
const MM0Parser = parse.MM0Parser;
const UHEAP_SIZE = @import("./constants.zig").UHEAP_SIZE;
const USTACK_SIZE = @import("./constants.zig").USTACK_SIZE;

const UnifyMode = enum {
    definition,
    theorem,
};

const EqPair = struct {
    lhs: *const Expr,
    rhs: *const Expr,
};

pub const CrossChecker = struct {
    parser: MM0Parser,
    sort_names: std.StringHashMap(u8),
    // Parsed expressions use parser-local term ids. Record the matching MMB
    // term id for each declared term so expression checks compare against the
    // real ids used by unify streams.
    term_ids: std.AutoHashMap(u32, u32),
    arena: std.heap.ArenaAllocator,
    // Working storage for unify-stream replay: the saved-expression heap, the
    // expression traversal stack, and the non-recursive equality stack.
    uheap: [UHEAP_SIZE]*const Expr = undefined,
    uheap_len: usize = 0,
    ustack: [USTACK_SIZE]*const Expr = undefined,
    ustack_top: usize = 0,
    eq_stack: [USTACK_SIZE]EqPair = undefined,
    eq_stack_top: usize = 0,

    pub fn init(mm0_src: []const u8, backing: std.mem.Allocator) !*CrossChecker {
        const self = try backing.create(CrossChecker);
        self.arena = std.heap.ArenaAllocator.init(backing);
        self.parser = MM0Parser.init(mm0_src, self.arena.allocator());
        self.sort_names = std.StringHashMap(u8).init(self.arena.allocator());
        self.term_ids = std.AutoHashMap(u32, u32).init(self.arena.allocator());
        self.uheap_len = 0;
        self.ustack_top = 0;
        self.eq_stack_top = 0;
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

        if (mm0_sort.modifiers.pure != mmb_sort.pure) {
            return error.SortModifierMismatch;
        }
        if (mm0_sort.modifiers.strict != mmb_sort.strict) {
            return error.SortModifierMismatch;
        }
        if (mm0_sort.modifiers.provable != mmb_sort.provable) {
            return error.SortModifierMismatch;
        }
        if (mm0_sort.modifiers.free != mmb_sort.free) {
            return error.SortModifierMismatch;
        }
        try self.sort_names.put(mm0_sort.name, sort_idx);
    }

    pub fn checkTerm(
        self: *CrossChecker,
        term_idx: u32,
        mmb_term: Term,
        file_bytes: []const u8,
    ) !void {
        const stmt = try self.parser.next() orelse return error.MM0Exhausted;
        const mm0_term = switch (stmt) {
            .term => |t| t,
            else => return error.MM0Mismatch,
        };

        const parser_term_id = self.parser.term_names.get(mm0_term.name) orelse {
            return error.UnknownTerm;
        };
        try self.term_ids.put(parser_term_id, term_idx);

        if (mm0_term.is_def != mmb_term.ret_sort.is_def) {
            return error.TermKindMismatch;
        }

        const mmb_args = try mmb_term.getArgsChecked(file_bytes);
        try self.checkArgMetadata(mm0_term.args, mmb_args);

        const expected_ret = self.sort_names.get(mm0_term.ret_sort_name) orelse {
            return error.UnknownSort;
        };
        if (expected_ret != mmb_term.ret_sort.sort) return error.RetSortMismatch;

        if (mm0_term.body) |body| {
            const unify_ptr = mmb_term.getUnifyPtr(file_bytes) orelse {
                return error.ExpectedDef;
            };
            try self.matchUnifyStream(
                file_bytes,
                unify_ptr,
                .definition,
                mm0_term.arg_exprs,
                &.{},
                body,
            );
        }
    }

    pub fn checkAssertion(
        self: *CrossChecker,
        mmb_thm: Theorem,
        file_bytes: []const u8,
    ) !void {
        const stmt = try self.parser.next() orelse return error.MM0Exhausted;
        const mm0_thm = switch (stmt) {
            .assertion => |a| a,
            else => return error.MM0Mismatch,
        };

        const mmb_args = try mmb_thm.getArgsChecked(file_bytes);
        try self.checkArgMetadata(mm0_thm.args, mmb_args);
        try self.matchUnifyStream(
            file_bytes,
            mmb_thm.getUnifyPtr(file_bytes),
            .theorem,
            mm0_thm.arg_exprs,
            mm0_thm.hyps,
            mm0_thm.concl,
        );
    }

    fn checkArgMetadata(
        self: *CrossChecker,
        mm0_args: []const parse.ArgInfo,
        mmb_args: anytype,
    ) !void {
        if (mm0_args.len != mmb_args.len) return error.ArgCountMismatch;
        for (mm0_args, mmb_args) |mm0_arg, mmb_arg| {
            if (mm0_arg.bound != mmb_arg.bound) return error.ArgBoundMismatch;
            if (mm0_arg.deps != mmb_arg.deps) return error.ArgDepsMismatch;
            const expected_sort = self.sort_names.get(mm0_arg.sort_name) orelse {
                return error.UnknownSort;
            };
            if (expected_sort != mmb_arg.sort) return error.ArgSortMismatch;
        }
    }

    fn matchUnifyStream(
        self: *CrossChecker,
        file_bytes: []const u8,
        start_pos: u32,
        mode: UnifyMode,
        args: []const *const Expr,
        hyps: []const *const Expr,
        target: *const Expr,
    ) !void {
        // Replay the MMB unify stream against the parsed MM0 expression tree.
        // The initial heap prefix is the declared arguments, and the stack is
        // seeded with the target expression to be matched.
        if (args.len > UHEAP_SIZE) return error.UHeapOverflow;
        self.uheap_len = args.len;
        for (args, 0..) |expr, idx| {
            self.uheap[idx] = expr;
        }

        self.ustack_top = 1;
        self.ustack[0] = target;

        var hyp_idx: usize = hyps.len;
        var pos: usize = start_pos;
        while (true) {
            const cmd = try Proof.Cmd.read(file_bytes, pos, file_bytes.len);
            pos += cmd.size;
            switch (@as(Proof.UnifyCmd, @enumFromInt(cmd.op))) {
                .End => break,
                .URef => try self.matchURef(cmd.data),
                .UTerm => try self.matchUTerm(cmd.data, false),
                .UTermSave => try self.matchUTerm(cmd.data, true),
                .UDummy => switch (mode) {
                    .definition => try self.matchUDummy(cmd.data, args),
                    .theorem => return error.UDummyNotAllowed,
                },
                .UHyp => switch (mode) {
                    .theorem => {
                        if (hyp_idx == 0) return error.HypCountMismatch;
                        hyp_idx -= 1;
                        try self.pushUStack(hyps[hyp_idx]);
                    },
                    .definition => return error.UHypNotAllowed,
                },
                _ => return error.UnknownUnifyCmd,
            }
        }

        if (self.ustack_top != 0) return error.UnifyStackNotEmpty;
        if (mode == .theorem and hyp_idx != 0) return error.HypCountMismatch;
    }

    fn matchURef(self: *CrossChecker, heap_id: u32) !void {
        const expr = try self.popUStack();
        if (heap_id >= self.uheap_len) return error.UHeapOutOfBounds;
        if (!self.deepEq(expr, self.uheap[heap_id])) return error.UnifyMismatch;
    }

    fn matchUTerm(self: *CrossChecker, term_id: u32, save: bool) !void {
        const expr = try self.popUStack();
        const term = switch (expr.*) {
            .term => |t| t,
            else => return error.ExpectedTermApp,
        };
        // Parsed expression nodes store parser-local ids. Compare against the
        // unify stream using the recorded MMB term id when available.
        const actual_term_id = self.term_ids.get(term.id) orelse term.id;
        if (actual_term_id != term_id) return error.TermMismatch;
        if (save) {
            if (self.uheap_len >= UHEAP_SIZE) return error.UHeapOverflow;
            self.uheap[self.uheap_len] = expr;
            self.uheap_len += 1;
        }
        var i: usize = term.args.len;
        while (i > 0) {
            i -= 1;
            try self.pushUStack(term.args[i]);
        }
    }

    fn matchUDummy(
        self: *CrossChecker,
        sort_id: u32,
        args: []const *const Expr,
    ) !void {
        const expr = try self.popUStack();
        const variable = switch (expr.*) {
            .variable => |v| v,
            else => return error.ExpectedVariable,
        };
        if (variable.sort != @as(u7, @intCast(sort_id))) return error.SortMismatch;
        for (args) |arg_expr| {
            if (arg_expr == expr) return error.ExpectedDummy;
        }
        if (self.uheap_len >= UHEAP_SIZE) return error.UHeapOverflow;
        self.uheap[self.uheap_len] = expr;
        self.uheap_len += 1;
    }

    fn deepEq(self: *CrossChecker, lhs: *const Expr, rhs: *const Expr) bool {
        self.eq_stack_top = 0;
        if (!self.pushEqPair(lhs, rhs)) return false;

        while (self.eq_stack_top > 0) {
            self.eq_stack_top -= 1;
            const pair = self.eq_stack[self.eq_stack_top];
            if (pair.lhs == pair.rhs) continue;

            switch (pair.lhs.*) {
                .variable => {
                    // Variable equality is by identity. Distinct variable
                    // nodes are not interchangeable, even if their payloads
                    // happen to match structurally.
                    return false;
                },
                .term => |lhs_term| switch (pair.rhs.*) {
                    .term => |rhs_term| {
                        if (lhs_term.id != rhs_term.id) return false;
                        if (lhs_term.args.len != rhs_term.args.len) return false;
                        for (lhs_term.args, rhs_term.args) |l_arg, r_arg| {
                            if (!self.pushEqPair(l_arg, r_arg)) return false;
                        }
                    },
                    else => return false,
                },
            }
        }
        return true;
    }

    fn pushEqPair(
        self: *CrossChecker,
        lhs: *const Expr,
        rhs: *const Expr,
    ) bool {
        if (self.eq_stack_top >= USTACK_SIZE) return false;
        self.eq_stack[self.eq_stack_top] = .{ .lhs = lhs, .rhs = rhs };
        self.eq_stack_top += 1;
        return true;
    }

    fn popUStack(self: *CrossChecker) !*const Expr {
        if (self.ustack_top == 0) return error.UStackUnderflow;
        self.ustack_top -= 1;
        return self.ustack[self.ustack_top];
    }

    fn pushUStack(self: *CrossChecker, expr: *const Expr) !void {
        if (self.ustack_top >= USTACK_SIZE) return error.UStackOverflow;
        self.ustack[self.ustack_top] = expr;
        self.ustack_top += 1;
    }
};
