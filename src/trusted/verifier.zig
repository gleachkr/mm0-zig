const std = @import("std");
const Stack = @import("./stack.zig").Stack;
const Heap = @import("./heap.zig").Heap;
const UHeap = @import("./uheap.zig").UHeap;
const UStack = @import("./ustack.zig").UStack;
const HypList = @import("./hypothesis.zig").HypList;
const Sort = @import("./sorts.zig").Sort;
const Term = @import("./terms.zig").Term;
const Theorem = @import("./theorems.zig").Theorem;
const Index = @import("./mmb.zig").Index;

const ProofCmd = @import("./proof.zig").ProofCmd;
const StmtCmd = @import("./proof.zig").StmtCmd;
const Cmd = @import("./proof.zig").Cmd;
const UnifyReplay = @import("./unify_replay.zig");

const Expr = @import("./expressions.zig").Expr;
const Arg = @import("./args.zig").Arg;
const HEAP_SIZE = @import("./constants.zig").HEAP_SIZE;
const ARENA_SIZE = @import("./constants.zig").ARENA_SIZE;

const ProofContext = enum {
    defn,
    axiom,
    theorem,
};

const UnifyContext = enum {
    defn,
    theorem,
};

const StatementRef = union(enum) {
    none,
    sort: usize,
    term: usize,
    theorem: usize,
};

pub const Verifier = struct {
    // Per-theorem working state - reset between theorems
    stack: Stack,
    heap: Heap,
    uheap: UHeap,
    ustack: UStack,
    hyps: HypList,
    next_bv: u32,
    sorry_used: bool,
    available_sorts: usize,
    available_terms: usize,
    available_thms: usize,
    proof_context: ?ProofContext,
    unify_context: ?UnifyContext,
    current_statement: StatementRef,
    index: ?Index,

    // Arena for expression nodes - reset between theorems
    arena: std.heap.FixedBufferAllocator,
    arena_buf: [ARENA_SIZE]u8,

    // Immutable file data - shared across all verifiers, set once at init
    file_bytes: []const u8,
    sort_table: []const Sort,
    term_table: []const Term,
    thm_table: []const Theorem,

    pub fn init(
        allocator: std.mem.Allocator,
        file_bytes: []const u8,
        sort_table: []const Sort,
        term_table: []const Term,
        thm_table: []const Theorem,
        index: ?Index,
    ) !*Verifier {
        const v = try allocator.create(Verifier);
        v.file_bytes = file_bytes;
        v.sort_table = sort_table;
        v.term_table = term_table;
        v.thm_table = thm_table;
        v.index = index;
        v.current_statement = .none;
        v.reset(); // XXX is this actually needed?
        return v;
    }

    pub fn deinit(self: *Verifier, allocator: std.mem.Allocator) void {
        allocator.destroy(self);
    }

    pub fn reset(self: *Verifier) void {
        self.stack.top = 0;
        self.ustack.top = 0;
        self.heap.len = 0;
        self.uheap.len = 0;
        self.hyps.len = 0;
        self.next_bv = 0;
        self.sorry_used = false;
        self.available_sorts = 0;
        self.available_terms = 0;
        self.available_thms = 0;
        self.proof_context = null;
        self.unify_context = null;
        self.arena = std.heap.FixedBufferAllocator.init(&self.arena_buf);
    }

    fn verifyThm(
        self: *Verifier,
        thm: Theorem,
        proof_pos: u32,
        proof_end: u32,
        available_sorts: usize,
        available_terms: usize,
        available_thms: usize,
    ) !void {
        defer self.reset();
        self.proof_context = .theorem;
        self.available_sorts = available_sorts;
        self.available_terms = available_terms;
        self.available_thms = available_thms;
        try self.initHeapFromThmArgs(thm);
        try self.runProofStream(proof_pos, proof_end);
        const top = try self.stack.pop();
        const proof_expr = switch (top) {
            .proof => |e| e,
            else => return error.ExpectedProof,
        };
        if (!self.sort_table[proof_expr.sort()].provable) return error.NotProvable;
        if (self.stack.top != 0) return error.StackNotEmpty;
        if (self.sorry_used) return error.SorryUsed;
    }

    fn verifyDef(
        self: *Verifier,
        term: Term,
        proof_pos: u32,
        proof_end: u32,
        available_sorts: usize,
        available_terms: usize,
        available_thms: usize,
    ) !void {
        defer self.reset();
        self.proof_context = .defn;
        self.available_sorts = available_sorts;
        self.available_terms = available_terms;
        self.available_thms = available_thms;
        try self.initHeapFromTermArgs(term);
        try self.runProofStream(proof_pos, proof_end);
        const top = try self.stack.pop();
        const def_expr = switch (top) {
            .expr => |e| e,
            else => return error.ExpectedExpr,
        };
        const ret = try term.getRetArgChecked(self.file_bytes);
        try self.checkExprAgainstArg(def_expr, ret);
        if (self.stack.top != 0) return error.StackNotEmpty;
        try self.initUHeapFromHeapArgs(term.num_args);
        try self.runUnifyStream(
            try term.getUnifyPtrChecked(self.file_bytes) orelse
                return error.ExpectedDef,
            def_expr,
            .defn,
        );
        if (self.sorry_used) return error.SorryUsed;
    }

    fn verifyAxiom(
        self: *Verifier,
        thm: Theorem,
        proof_pos: u32,
        proof_end: u32,
        available_sorts: usize,
        available_terms: usize,
        available_thms: usize,
    ) !void {
        defer self.reset();
        self.proof_context = .axiom;
        self.available_sorts = available_sorts;
        self.available_terms = available_terms;
        self.available_thms = available_thms;
        try self.initHeapFromThmArgs(thm);
        try self.runProofStream(proof_pos, proof_end);
        const top = try self.stack.pop();
        const concl_expr = switch (top) {
            .expr => |e| e,
            else => return error.ExpectedExpr,
        };
        if (!self.sort_table[concl_expr.sort()].provable) return error.NotProvable;
        if (self.stack.top != 0) return error.StackNotEmpty;
        if (self.sorry_used) return error.SorryUsed;
    }

    fn runProofStream(self: *Verifier, start_pos: u32, end_pos: u32) !void {
        var pos: usize = start_pos;
        const limit: usize = end_pos;
        while (true) {
            const cmd = try Cmd.read(self.file_bytes, pos, limit);
            pos += cmd.size;
            switch (@as(ProofCmd, @enumFromInt(cmd.op))) {
                .End => {
                    if (pos != limit) return error.BadStatementLength;
                    break;
                },
                .Term => try self.opTerm(cmd.data, false),
                .TermSave => try self.opTerm(cmd.data, true),
                .Ref => try self.opRef(cmd.data),
                .Dummy => try self.opDummy(cmd.data),
                .Thm => try self.opThm(cmd.data, false),
                .ThmSave => try self.opThm(cmd.data, true),
                .Hyp => try self.opHyp(),
                .Conv => try self.opConv(),
                .Refl => try self.opRefl(),
                .Symm => try self.opSymm(),
                .Cong => try self.opCong(),
                .Unfold => try self.opUnfold(),
                .ConvCut => try self.opConvCut(),
                .ConvSave => try self.opConvSave(),
                .Save => try self.opSave(),
                .Sorry => try self.opSorry(),
                _ => return error.UnknownProofCmd,
            }
        }
    }

    fn initHeapFromThmArgs(self: *Verifier, thm: Theorem) !void {
        try self.initHeapFromArgs(try thm.getArgsChecked(self.file_bytes));
    }

    fn initHeapFromTermArgs(self: *Verifier, term: Term) !void {
        try self.initHeapFromArgs(try term.getArgsChecked(self.file_bytes));
    }

    fn initHeapFromArgs(self: *Verifier, args: []const Arg) !void {
        var bv_idx: u6 = 0;
        for (args) |arg| {
            const expr = try self.arena.allocator().create(Expr);
            if (arg.bound) {
                if (self.sort_table[arg.sort].strict) return error.StrictSort;
                expr.* = .{ .variable = .{
                    .sort = arg.sort,
                    .bound = true,
                    .deps = @as(u55, 1) << bv_idx,
                } };
                bv_idx += 1;
                self.next_bv += 1;
            } else {
                expr.* = .{ .variable = .{
                    .sort = arg.sort,
                    .bound = false,
                    .deps = arg.deps,
                } };
            }
            try self.heap.push(.{ .expr = expr });
        }
    }

    fn initUHeapFromHeapArgs(self: *Verifier, arg_count: u16) !void {
        self.uheap.len = 0;
        for (0..arg_count) |i| {
            const expr = switch (self.heap.entries[i]) {
                .expr => |e| e,
                else => return error.ExpectedExpr,
            };
            try self.uheap.push(expr);
        }
    }

    fn checkExprAgainstArg(
        self: *Verifier,
        expr: *const Expr,
        arg: Arg,
    ) !void {
        _ = self;
        if (expr.sort() != arg.sort) return error.SortMismatch;
        if (arg.bound and !expr.bound()) return error.ExpectedBoundVar;
        if (expr.deps() & ~arg.deps != 0) return error.DepViolation;
    }

    pub fn verifyProofStream(
        self: *Verifier,
        proof_start: u32,
        checker: anytype,
    ) !void {
        var pos: usize = proof_start;
        var sort_count: usize = 0;
        var term_count: usize = 0;
        var thm_count: usize = 0;

        while (true) {
            const stmt_start = pos;
            const cmd = try Cmd.read(self.file_bytes, pos, self.file_bytes.len);
            pos += cmd.size;

            switch (@as(StmtCmd, @enumFromInt(cmd.op))) {
                .End => break,
                .Sort => {
                    const stmt_end = try self.statementEnd(stmt_start, pos, cmd.data);
                    if (sort_count >= self.sort_table.len) {
                        return error.SortCountMismatch;
                    }
                    self.current_statement = .{ .sort = sort_count };
                    if (self.index) |index| {
                        try index.validateSortProof(sort_count, stmt_start);
                    }
                    try checker.checkSort(
                        @intCast(sort_count),
                        self.sort_table[sort_count],
                    );
                    if (stmt_end != pos) return error.NonEmptySortStatement;
                    sort_count += 1;
                    pos = stmt_end;
                },
                .TermDef => {
                    const stmt_end = try self.statementEnd(stmt_start, pos, cmd.data);
                    if (term_count >= self.term_table.len) {
                        return error.TermCountMismatch;
                    }
                    self.current_statement = .{ .term = term_count };
                    if (self.index) |index| {
                        try index.validateTermProof(term_count, stmt_start);
                    }
                    const term = self.term_table[term_count];
                    if (self.sort_table[term.ret_sort.sort].pure)
                        return error.PureSort;
                    try checker.checkTerm(
                        @intCast(term_count),
                        term,
                        self.file_bytes,
                    );
                    if (term.ret_sort.is_def) {
                        try self.verifyDef(
                            term,
                            @intCast(pos),
                            @intCast(stmt_end),
                            sort_count,
                            term_count + 1,
                            thm_count,
                        );
                    } else if (stmt_end != pos) {
                        return error.NonDefTermHasProof;
                    }
                    term_count += 1;
                    pos = stmt_end;
                },
                .Axiom => {
                    const stmt_end = try self.statementEnd(stmt_start, pos, cmd.data);
                    if (thm_count >= self.thm_table.len) {
                        return error.TheoremCountMismatch;
                    }
                    self.current_statement = .{ .theorem = thm_count };
                    if (self.index) |index| {
                        try index.validateTheoremProof(thm_count, stmt_start);
                    }
                    const theorem = self.thm_table[thm_count];
                    try checker.checkAssertion(theorem, self.file_bytes);
                    try self.verifyAxiom(
                        theorem,
                        @intCast(pos),
                        @intCast(stmt_end),
                        sort_count,
                        term_count,
                        thm_count + 1,
                    );
                    thm_count += 1;
                    pos = stmt_end;
                },
                .Thm => {
                    const stmt_end = try self.statementEnd(stmt_start, pos, cmd.data);
                    if (thm_count >= self.thm_table.len) {
                        return error.TheoremCountMismatch;
                    }
                    self.current_statement = .{ .theorem = thm_count };
                    if (self.index) |index| {
                        try index.validateTheoremProof(thm_count, stmt_start);
                    }
                    const theorem = self.thm_table[thm_count];
                    try checker.checkAssertion(theorem, self.file_bytes);
                    try self.verifyThm(
                        theorem,
                        @intCast(pos),
                        @intCast(stmt_end),
                        sort_count,
                        term_count,
                        thm_count + 1,
                    );
                    thm_count += 1;
                    pos = stmt_end;
                },
                .LocalDef => {
                    const stmt_end = try self.statementEnd(stmt_start, pos, cmd.data);
                    if (term_count >= self.term_table.len) {
                        return error.TermCountMismatch;
                    }
                    self.current_statement = .{ .term = term_count };
                    if (self.index) |index| {
                        try index.validateTermProof(term_count, stmt_start);
                    }
                    if (self.sort_table[self.term_table[term_count].ret_sort.sort].pure)
                        return error.PureSort;
                    try self.verifyDef(
                        self.term_table[term_count],
                        @intCast(pos),
                        @intCast(stmt_end),
                        sort_count,
                        term_count + 1,
                        thm_count,
                    );
                    term_count += 1;
                    pos = stmt_end;
                },
                .LocalThm => {
                    const stmt_end = try self.statementEnd(stmt_start, pos, cmd.data);
                    if (thm_count >= self.thm_table.len) {
                        return error.TheoremCountMismatch;
                    }
                    self.current_statement = .{ .theorem = thm_count };
                    if (self.index) |index| {
                        try index.validateTheoremProof(thm_count, stmt_start);
                    }
                    try self.verifyThm(
                        self.thm_table[thm_count],
                        @intCast(pos),
                        @intCast(stmt_end),
                        sort_count,
                        term_count,
                        thm_count + 1,
                    );
                    thm_count += 1;
                    pos = stmt_end;
                },
                else => return error.UnknownStatement,
            }
        }

        if (sort_count != self.sort_table.len) return error.SortCountMismatch;
        if (term_count != self.term_table.len) return error.TermCountMismatch;
        if (thm_count != self.thm_table.len) return error.TheoremCountMismatch;
    }

    pub fn reportError(self: *const Verifier, err: anyerror) void {
        var name_buf: [32]u8 = undefined;
        switch (self.current_statement) {
            .none => std.debug.print("Verification failed: {s}\n", .{
                @errorName(err),
            }),
            .sort => |id| std.debug.print(
                "Verification failed in sort {s}: {s}\n",
                .{ self.sortName(id, &name_buf), @errorName(err) },
            ),
            .term => |id| std.debug.print(
                "Verification failed in term {s}: {s}\n",
                .{ self.termName(id, &name_buf), @errorName(err) },
            ),
            .theorem => |id| std.debug.print(
                "Verification failed in theorem {s}: {s}\n",
                .{ self.theoremName(id, &name_buf), @errorName(err) },
            ),
        }
    }

    fn sortName(self: *const Verifier, id: usize, buf: *[32]u8) []const u8 {
        if (self.index) |index| {
            if (index.sortName(self.file_bytes, id) catch null) |name| return name;
        }
        return std.fmt.bufPrint(buf, "s{}", .{id}) catch "<sort>";
    }

    fn termName(self: *const Verifier, id: usize, buf: *[32]u8) []const u8 {
        if (self.index) |index| {
            if (index.termName(self.file_bytes, id) catch null) |name| return name;
        }
        return std.fmt.bufPrint(buf, "t{}", .{id}) catch "<term>";
    }

    fn theoremName(self: *const Verifier, id: usize, buf: *[32]u8) []const u8 {
        if (self.index) |index| {
            if (index.theoremName(self.file_bytes, id) catch null) |name| {
                return name;
            }
        }
        return std.fmt.bufPrint(buf, "T{}", .{id}) catch "<theorem>";
    }

    fn statementEnd(
        self: *Verifier,
        stmt_start: usize,
        body_start: usize,
        encoded_len: u32,
    ) !usize {
        const stmt_len = std.math.cast(usize, encoded_len) orelse return error.IntegerOverflow;
        const stmt_end = try std.math.add(usize, stmt_start, stmt_len);
        if (stmt_end < body_start) return error.BadStatementLength;
        if (stmt_end > self.file_bytes.len) return error.BadStatementLength;
        return stmt_end;
    }

    fn opTerm(self: *Verifier, term_id: u32, save: bool) !void {
        if (term_id >= self.available_terms) return error.ForwardTermRef;

        const term = self.term_table[term_id];
        const args = try term.getArgsChecked(self.file_bytes);
        const n = term.num_args;

        // Pop n args in reverse order.
        const popped = try self.arena.allocator().alloc(*const Expr, n);
        var i: usize = n;
        while (i > 0) {
            i -= 1;
            const entry = try self.stack.pop();
            const expr = switch (entry) {
                .expr => |e| e,
                else => return error.ExpectedExpr,
            };
            if (expr.sort() != args[i].sort) return error.SortMismatch;
            if (args[i].bound and !expr.bound()) return error.ExpectedBoundVar;
            popped[i] = expr;
        }

        // Cache theorem-mode V(e) or def-mode FV(e), matching mm0-c.
        const context = self.proof_context orelse return error.InvalidProofContext;
        var deps: u55 = 0;
        switch (context) {
            .axiom, .theorem => {
                for (popped) |expr| deps |= expr.deps();
            },
            .defn => {
                var bound_deps: [56]u55 = undefined;
                var bound_len: usize = 0;
                for (args, popped) |arg, expr| {
                    var arg_deps = expr.deps();
                    if (arg.bound) {
                        bound_deps[bound_len] = arg_deps;
                        bound_len += 1;
                        continue;
                    }
                    for (0..bound_len) |j| {
                        if (arg.dependsOn(@intCast(j))) {
                            arg_deps &= ~bound_deps[j];
                        }
                    }
                    deps |= arg_deps;
                }
                const ret = try term.getRetArgChecked(self.file_bytes);
                for (0..bound_len) |j| {
                    if (ret.dependsOn(@intCast(j))) deps |= bound_deps[j];
                }
            },
        }

        const node = try self.arena.allocator().create(Expr);
        node.* = .{ .term = .{
            .sort = term.ret_sort.sort,
            .deps = deps,
            .id = term_id,
            .args = popped,
        } };

        try self.stack.push(.{ .expr = node });
        if (save) try self.heap.push(.{ .expr = node });
    }

    fn opThm(self: *Verifier, thm_id: u32, save: bool) !void {
        switch (self.proof_context orelse return error.InvalidProofContext) {
            .axiom, .theorem => {},
            .defn => return error.ThmNotAllowed,
        }
        if (thm_id >= self.available_thms) return error.ForwardTheoremRef;

        self.uheap.len = 0;
        const thm = self.thm_table[thm_id];
        const args = try thm.getArgsChecked(self.file_bytes);
        const n = thm.num_args;

        // Pop the conclusion expression
        const concl_entry = try self.stack.pop();
        const concl = switch (concl_entry) {
            .expr => |e| e,
            else => return error.ExpectedExpr,
        };

        // Pop n args in reverse order, filling uheap in forward order
        self.uheap.len = n;
        var i: usize = n;
        while (i > 0) {
            i -= 1;
            const entry = try self.stack.pop();
            const expr = switch (entry) {
                .expr => |e| e,
                else => return error.ExpectedExpr,
            };
            if (expr.sort() != args[i].sort) return error.SortMismatch;
            if (args[i].bound and !expr.bound()) return error.ExpectedBoundVar;
            self.uheap.entries[i] = .{ .expr = expr, .saved = false };
        }

        // Dep checks in forward order
        var deps_buf: [56]u55 = undefined;
        var deps_len: usize = 0;
        for (0..n) |j| {
            const expr = self.uheap.entries[j].expr;
            if (args[j].bound) {
                // Bound var must not overlap with any previously seen bound var
                for (0..j) |k| {
                    const prev = self.uheap.entries[k].expr;
                    if (prev.deps() & expr.deps() != 0) {
                        return error.DepViolation;
                    }
                }
                deps_buf[deps_len] = expr.deps();
                deps_len += 1;
            } else {
                // Regular arg must not contain bound vars it's not allowed to
                // depend on
                for (0..deps_len) |k| {
                    if ((@as(u64, args[j].deps) >> @intCast(k)) & 1 != 0)
                        continue;
                    if (deps_buf[k] & expr.deps() != 0) {
                        return error.DepViolation;
                    }
                }
            }
        }

        // Run unification against the conclusion
        try self.runUnifyStream(
            try thm.getUnifyPtrChecked(self.file_bytes),
            concl,
            .theorem,
        );

        // Push |- concl
        try self.stack.push(.{ .proof = concl });
        if (save) try self.heap.push(.{ .proof = concl });
    }

    pub fn uopRef(self: *Verifier, heap_id: u32) !void {
        const expr = try self.ustack.pop();
        if (heap_id >= self.uheap.len) return error.UHeapOutOfBounds;
        const expected = self.uheap.entries[heap_id].expr;
        // Pointer equality per spec
        if (expr != expected) return error.UnifyMismatch;
    }

    pub fn uopTerm(self: *Verifier, term_id: u32, save: bool) !void {
        if (term_id >= self.available_terms) return error.ForwardTermRef;

        const expr = try self.ustack.pop();
        // Must be a term application with matching constructor
        const t = switch (expr.*) {
            .term => |t| t,
            else => return error.ExpectedTermApp,
        };
        if (t.id != term_id) return error.TermMismatch;
        // Save before pushing children per spec
        if (save) try self.uheap.pushSaved(expr);
        // Push children in reverse order so they're popped in forward order
        var i: usize = t.args.len;
        while (i > 0) {
            i -= 1;
            try self.ustack.push(t.args[i]);
        }
    }

    pub fn uopDummy(self: *Verifier, sort_id: u32) !void {
        switch (self.unify_context orelse return error.InvalidUnifyContext) {
            .defn => {},
            .theorem => return error.UDummyNotAllowed,
        }
        if (sort_id >= self.available_sorts) return error.InvalidSort;

        const expr = try self.ustack.pop();
        const v = switch (expr.*) {
            .variable => |v| v,
            else => return error.ExpectedVariable,
        };
        // mm0-c's verifier and the mm1 parser both treat `(.x)` and `{.x}`
        // as dummy-bound variables, even though the written MMB `UDummy`
        // rule does not spell out the boundness check. Keep that
        // compatibility here. See third_party/mm0/mm0-c/verifier.c and
        // third_party/mm0/mm0-rs/components/mm1_parser/src/ast.rs.
        if (!v.bound) return error.ExpectedBoundVar;
        if (v.sort != @as(u7, @intCast(sort_id))) return error.SortMismatch;
        for (self.uheap.entries[0..self.uheap.len]) |prev| {
            if (prev.saved) continue;
            if (prev.expr.deps() & expr.deps() != 0) {
                return error.DepViolation;
            }
        }
        try self.uheap.push(expr);
    }

    pub fn uopHyp(self: *Verifier) !void {
        switch (self.unify_context orelse return error.InvalidUnifyContext) {
            .theorem => {},
            .defn => return error.UHypNotAllowed,
        }

        // Pop |- e from main stack, push e onto unify stack
        const entry = try self.stack.pop();
        const expr = switch (entry) {
            .proof => |e| e,
            else => return error.ExpectedProof,
        };
        try self.ustack.push(expr);
    }

    fn opRef(self: *Verifier, heap_id: u32) !void {
        if (heap_id >= self.heap.len) return error.HeapOutOfBounds;
        const entry = self.heap.entries[heap_id];

        // Fast path: most refs just push the heap entry.
        if (entry == .conv and self.stack.top > 0) {
            const top = self.stack.entries[self.stack.top - 1];
            if (top == .conv_obligation) {
                self.stack.top -= 1;
                const obl = self.stack.entries[self.stack.top].conv_obligation;
                const conv = entry.conv;
                if (obl.left != conv.left or obl.right != conv.right)
                    return error.ConvMismatch;
                return;
            }
        }

        try self.stack.push(entry);
    }

    fn opDummy(self: *Verifier, sort_id: u32) !void {
        // Check sort exists and is not strict or free
        if (sort_id >= self.available_sorts) return error.InvalidSort;
        if (self.sort_table[sort_id].strict) return error.StrictSort;
        if (self.sort_table[sort_id].free) return error.FreeSort;
        // Allocate fresh bound variable
        const expr = try self.arena.allocator().create(Expr);
        expr.* = .{ .variable = .{
            .sort = @intCast(sort_id),
            .bound = true,
            .deps = @as(u55, 1) << @intCast(self.next_bv),
        } };
        self.next_bv += 1;
        try self.stack.push(.{ .expr = expr });
        try self.heap.push(.{ .expr = expr });
    }

    fn opHyp(self: *Verifier) !void {
        switch (self.proof_context orelse return error.InvalidProofContext) {
            .axiom, .theorem => {},
            .defn => return error.HypNotAllowed,
        }

        const entry = try self.stack.pop();
        const expr = switch (entry) {
            .expr => |e| e,
            else => return error.ExpectedExpr,
        };
        if (!self.sort_table[expr.sort()].provable) return error.NotProvable;
        try self.hyps.append(expr);
        try self.heap.push(.{ .proof = expr });
    }

    fn opSave(self: *Verifier) !void {
        const entry = try self.stack.peek();
        switch (entry) {
            .conv_obligation => return error.CannotSaveObligation,
            else => try self.heap.push(entry),
        }
    }

    fn opRefl(self: *Verifier) !void {
        const entry = try self.stack.pop();
        const obl = switch (entry) {
            .conv_obligation => |o| o,
            else => return error.ExpectedConvObligation,
        };
        if (obl.left != obl.right) return error.ReflMismatch;
    }

    fn opSymm(self: *Verifier) !void {
        const entry = try self.stack.pop();
        const obl = switch (entry) {
            .conv_obligation => |o| o,
            else => return error.ExpectedConvObligation,
        };
        try self.stack.push(.{ .conv_obligation = .{
            .left = obl.right,
            .right = obl.left,
        } });
    }

    fn opConv(self: *Verifier) !void {
        const proof_entry = try self.stack.pop();
        const e2 = switch (proof_entry) {
            .proof => |e| e,
            else => return error.ExpectedProof,
        };
        const expr_entry = try self.stack.pop();
        const e1 = switch (expr_entry) {
            .expr => |e| e,
            else => return error.ExpectedExpr,
        };
        try self.stack.push(.{ .proof = e1 });
        try self.stack.push(.{ .conv_obligation = .{
            .left = e1,
            .right = e2,
        } });
    }

    fn opConvCut(self: *Verifier) !void {
        const entry = try self.stack.pop();
        const obl = switch (entry) {
            .conv_obligation => |o| o,
            else => return error.ExpectedConvObligation,
        };
        // Push conv proof, then re-push obligation
        try self.stack.push(.{ .conv = .{
            .left = obl.left,
            .right = obl.right,
        } });
        try self.stack.push(.{ .conv_obligation = obl });
    }

    fn opConvSave(self: *Verifier) !void {
        const entry = try self.stack.pop();
        const conv = switch (entry) {
            .conv => |c| c,
            else => return error.ExpectedConv,
        };
        try self.heap.push(.{ .conv = conv });
    }

    fn opSorry(self: *Verifier) !void {
        // Sorry is not a valid proof command but we handle it gracefully
        // Check what's on top and either push a proof or discharge an obligation
        if (self.stack.top > 0) {
            const top = try self.stack.peek();
            if (top == .conv_obligation) {
                _ = try self.stack.pop();
                return;
            }
        }
        const entry = try self.stack.pop();
        const expr = switch (entry) {
            .expr => |e| e,
            else => return error.ExpectedExpr,
        };
        try self.stack.push(.{ .proof = expr });
        self.sorry_used = true;
    }

    fn opCong(self: *Verifier) !void {
        const entry = try self.stack.pop();
        const obl = switch (entry) {
            .conv_obligation => |o| o,
            else => return error.ExpectedConvObligation,
        };
        // Both sides must be term applications with the same constructor
        const left = switch (obl.left.*) {
            .term => |t| t,
            else => return error.ExpectedTermApp,
        };
        const right = switch (obl.right.*) {
            .term => |t| t,
            else => return error.ExpectedTermApp,
        };
        if (left.id != right.id) return error.TermMismatch;
        if (left.args.len != right.args.len) return error.ArgCountMismatch;
        // Push subobligations in reverse order so they're discharged left to right
        var i: usize = left.args.len;
        while (i > 0) {
            i -= 1;
            try self.stack.push(.{ .conv_obligation = .{
                .left = left.args[i],
                .right = right.args[i],
            } });
        }
    }

    fn opUnfold(self: *Verifier) !void {
        // Stack: (t e1...en) =?= e', e
        // Pop e
        const e_entry = try self.stack.pop();
        const e = switch (e_entry) {
            .expr => |ex| ex,
            else => return error.ExpectedExpr,
        };
        // Pop conversion obligation
        const obl_entry = try self.stack.pop();
        const obl = switch (obl_entry) {
            .conv_obligation => |o| o,
            else => return error.ExpectedConvObligation,
        };
        // Left side must be a def application
        const t = switch (obl.left.*) {
            .term => |t| t,
            else => return error.ExpectedTermApp,
        };
        if (t.id >= self.available_terms) return error.ForwardTermRef;
        if (!self.term_table[t.id].ret_sort.is_def) return error.ExpectedDef;
        // Run unification of def's unify stream against e,
        // with def's args as initial uheap
        self.uheap.len = t.args.len;
        for (t.args, 0..) |arg, i| {
            self.uheap.entries[i] = .{ .expr = arg, .saved = false };
        }
        // Run the def's unify stream with e on the unify stack
        const unify_ptr =
            (try self.term_table[t.id].getUnifyPtrChecked(self.file_bytes)).?;
        self.ustack.reset();
        try self.ustack.push(e);
        try self.runUnifyStreamRaw(unify_ptr, .defn);
        // Push e =?= e'
        try self.stack.push(.{ .conv_obligation = .{
            .left = e,
            .right = obl.right,
        } });
    }

    fn runUnifyStreamRaw(
        self: *Verifier,
        start_pos: u32,
        context: UnifyContext,
    ) !void {
        const prev_context = self.unify_context;
        self.unify_context = context;
        defer self.unify_context = prev_context;

        try UnifyReplay.run(self.file_bytes, start_pos, self);
        if (self.ustack.top != 0) return error.UnifyStackNotEmpty;
    }

    fn runUnifyStream(
        self: *Verifier,
        start_pos: u32,
        concl: *const Expr,
        context: UnifyContext,
    ) !void {
        self.ustack.reset();
        try self.ustack.push(concl);
        try self.runUnifyStreamRaw(start_pos, context);
    }
};
