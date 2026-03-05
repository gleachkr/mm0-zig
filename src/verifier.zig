const std = @import("std");
const Stack = @import("./stack.zig").Stack;
const Heap = @import("./heap.zig").Heap;
const UHeap = @import("./uheap.zig").UHeap;
const UStack = @import("./ustack.zig").UStack;
const HypList = @import("./hypothesis.zig").HypList;
const Sort = @import("./sorts.zig").Sort;
const Term = @import("./terms.zig").Term;
const Theorem = @import("./theorems.zig").Theorem;
const CrossChecker = @import("./check.zig").CrossChecker;

const ProofCmd = @import("./proof.zig").ProofCmd;
const StmtCmd = @import("./proof.zig").StmtCmd;
const UnifyCmd = @import("./proof.zig").UnifyCmd;
const Cmd = @import("./proof.zig").Cmd;

const Expr = @import("./expressions.zig").Expr;
const Arg = @import("./args.zig").Arg;
const HEAP_SIZE = @import("./constants.zig").HEAP_SIZE;
const ARENA_SIZE = @import("./constants.zig").ARENA_SIZE;

pub const Verifier = struct {
    // Per-theorem working state - reset between theorems
    stack: Stack,
    heap: Heap,
    uheap: UHeap,
    ustack: UStack,
    hyps: HypList,
    next_bv: u32,
    sorry_used: bool,

    // Arena for expression nodes - reset between theorems
    arena: std.heap.FixedBufferAllocator,
    arena_buf: [ARENA_SIZE]u8,

    // Immutable file data - shared across all verifiers, set once at init
    file_bytes: []const u8,
    sort_table: []const Sort,
    term_table: []const Term,
    thm_table: []const Theorem,

    pub fn init(allocator: std.mem.Allocator, file_bytes: []const u8, sort_table: []const Sort, term_table: []const Term, thm_table: []const Theorem) !*Verifier {
        const v = try allocator.create(Verifier);
        v.file_bytes = file_bytes;
        v.sort_table = sort_table;
        v.term_table = term_table;
        v.thm_table = thm_table;
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
        self.arena = std.heap.FixedBufferAllocator.init(&self.arena_buf);
    }

    fn verifyThm(self: *Verifier, thm: Theorem, proof_pos: u32) !void {
        defer self.reset();
        try self.initHeapFromThmArgs(thm);
        try self.runProofStream(proof_pos);
        const top = try self.stack.pop();
        if (top != .proof) return error.ExpectedProof;
        if (self.stack.top != 0) return error.StackNotEmpty;
    }

    fn verifyDef(self: *Verifier, term: Term, proof_pos: u32) !void {
        defer self.reset();
        try self.initHeapFromTermArgs(term);
        try self.runProofStream(proof_pos);
        const top = try self.stack.pop();
        if (top != .expr) return error.ExpectedExpr;
        if (self.stack.top != 0) return error.StackNotEmpty;
    }

    fn verifyAxiom(self: *Verifier, thm: Theorem, proof_pos: u32) !void {
        defer self.reset();
        try self.initHeapFromThmArgs(thm);
        try self.runProofStream(proof_pos);
        const top = try self.stack.pop();
        if (top != .expr) return error.ExpectedExpr;
        if (self.stack.top != 0) return error.StackNotEmpty;
    }

    fn runProofStream(self: *Verifier, start_pos: u32) !void {
        var pos = start_pos;
        while (true) {
            const cmd = Cmd.read(self.file_bytes, pos);
            pos += @intCast(cmd.size);
            switch (@as(ProofCmd, @enumFromInt(cmd.op))) {
                .End => break,
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
        try self.initHeapFromArgs(thm.getArgs(self.file_bytes));
    }

    fn initHeapFromTermArgs(self: *Verifier, term: Term) !void {
        try self.initHeapFromArgs(term.getArgs(self.file_bytes));
    }

    fn initHeapFromArgs(self: *Verifier, args: []const Arg) !void {
        var bv_idx: u6 = 0;
        for (args) |arg| {
            const expr = try self.arena.allocator().create(Expr);
            if (arg.bound) {
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

    pub fn verifyProofStream(self: *Verifier, proof_start: u32, checker: *CrossChecker) !void {
        var pos: u32 = proof_start;
        var sort_count: u32 = 0;
        var term_count: u32 = 0;
        var thm_count: u32 = 0;

        while (true) {
            const stmt_start = pos;
            const cmd = Cmd.read(self.file_bytes, pos);
            pos += @intCast(cmd.size); // now pos points to first proof command

            switch (@as(StmtCmd, @enumFromInt(cmd.op))) {
                .End => break,
                .Sort => {
                    try checker.checkSort(@intCast(sort_count), self.sort_table[sort_count]);
                    sort_count += 1;
                },
                .TermDef => {
                    const term = self.term_table[term_count];
                    try checker.checkTerm(term, self.file_bytes);
                    if (term.ret_sort.is_def) {
                        try self.verifyDef(term, pos);
                    }
                    term_count += 1;
                },
                .Axiom => {
                    try checker.checkAssertion(self.thm_table[thm_count], self.file_bytes);
                    try self.verifyAxiom(self.thm_table[thm_count], pos);
                    thm_count += 1;
                },
                .Thm => {
                    try checker.checkAssertion(self.thm_table[thm_count], self.file_bytes);
                    try self.verifyThm(self.thm_table[thm_count], pos);
                    thm_count += 1;
                },
                .LocalDef => {
                    try self.verifyDef(self.term_table[term_count], pos);
                    term_count += 1;
                },
                .LocalThm => {
                    try self.verifyThm(self.thm_table[thm_count], pos);
                    thm_count += 1;
                },
                else => return error.UnknownStatement,
            }

            // Use data field to jump to next statement
            pos = stmt_start + cmd.data;
        }
    }

    fn opTerm(self: *Verifier, term_id: u32, save: bool) !void {
        const term = self.term_table[term_id];
        const args = term.getArgs(self.file_bytes);
        const n = term.num_args;

        // Pop n args in reverse order
        const popped = try self.arena.allocator().alloc(*const Expr, n);
        var i: usize = n;
        while (i > 0) {
            i -= 1;
            const entry = try self.stack.pop();
            const expr = switch (entry) {
                .expr => |e| e,
                else => return error.ExpectedExpr,
            };
            // Check sort matches
            if (expr.sort() != args[i].sort) return error.SortMismatch;
            // If arg is bound, expr must be a bound variable
            if (args[i].bound and !expr.bound()) return error.ExpectedBoundVar;
            popped[i] = expr;
        }

        // Compute deps as union of children's deps
        var deps: u55 = 0;
        for (popped) |arg| {
            deps |= arg.deps();
        }

        // Allocate new node
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
        self.uheap.len = 0;
        const thm = self.thm_table[thm_id];
        const args = thm.getArgs(self.file_bytes);
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
        var deps_buf: [56]u55 = std.mem.zeroes([56]u55);
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
        try self.runUnifyStream(thm.getUnifyPtr(self.file_bytes), concl);

        // Push |- concl
        try self.stack.push(.{ .proof = concl });
        if (save) try self.heap.push(.{ .proof = concl });
    }

    fn uopRef(self: *Verifier, heap_id: u32) !void {
        const expr = try self.ustack.pop();
        const expected = try self.uheap.get(heap_id);
        // Pointer equality per spec
        if (expr != expected) return error.UnifyMismatch;
    }

    fn uopTerm(self: *Verifier, term_id: u32, save: bool) !void {
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

    fn uopDummy(self: *Verifier, sort_id: u32) !void {
        const expr = try self.ustack.pop();
        // Must be a bound variable of the right sort
        const v = switch (expr.*) {
            .variable => |v| v,
            else => return error.ExpectedVariable,
        };
        if (!v.bound) return error.ExpectedBoundVar;
        if (v.sort != @as(u7, @intCast(sort_id))) return error.SortMismatch;
        // Must not overlap with any non-saved expr already in uheap
        for (self.uheap.entries[0..self.uheap.len]) |prev| {
            if (prev.saved) continue;
            if (prev.expr.deps() & expr.deps() != 0) {
                return error.DepViolation;
            }
        }
        try self.uheap.push(expr);
    }

    fn uopHyp(self: *Verifier) !void {
        // Pop |- e from main stack, push e onto unify stack
        const entry = try self.stack.pop();
        const expr = switch (entry) {
            .proof => |e| e,
            else => return error.ExpectedProof,
        };
        try self.ustack.push(expr);
    }

    fn opRef(self: *Verifier, heap_id: u32) !void {
        const entry = try self.heap.get(heap_id);
        // Special case: if top of stack is conv_obligation,
        // and heap[i] is a conv proof, discharge it
        if (self.stack.top > 0) {
            const top = try self.stack.peek();
            if (top == .conv_obligation) {
                if (entry == .conv) {
                    const obl = (try self.stack.pop()).conv_obligation;
                    const conv = entry.conv;
                    if (obl.left != conv.left or obl.right != conv.right)
                        return error.ConvMismatch;
                    return;
                }
            }
        }
        try self.stack.push(entry);
    }

    fn opDummy(self: *Verifier, sort_id: u32) !void {
        // Check sort exists and is not strict
        if (sort_id >= self.sort_table.len) return error.InvalidSort;
        if (self.sort_table[sort_id].strict) return error.StrictSort;
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
        if (!self.term_table[t.id].ret_sort.is_def) return error.ExpectedDef;
        // Run unification of def's unify stream against e,
        // with def's args as initial uheap
        self.uheap.len = t.args.len;
        for (t.args, 0..) |arg, i| {
            self.uheap.entries[i] = .{ .expr = arg, .saved = false };
        }
        // Run the def's unify stream with e on the unify stack
        const unify_ptr = self.term_table[t.id].getUnifyPtr(self.file_bytes).?;
        self.ustack.reset();
        try self.ustack.push(e);
        try self.runUnifyStreamRaw(unify_ptr);
        // Push e =?= e'
        try self.stack.push(.{ .conv_obligation = .{
            .left = e,
            .right = obl.right,
        } });
    }

    fn runUnifyStreamRaw(self: *Verifier, start_pos: u32) !void {
        var pos = start_pos;
        while (true) {
            const cmd = Cmd.read(self.file_bytes, pos);
            pos += @intCast(cmd.size);
            switch (@as(UnifyCmd, @enumFromInt(cmd.op))) {
                .End => break,
                .UTerm => try self.uopTerm(cmd.data, false),
                .UTermSave => try self.uopTerm(cmd.data, true),
                .URef => try self.uopRef(cmd.data),
                .UDummy => try self.uopDummy(cmd.data),
                .UHyp => try self.uopHyp(),
                _ => return error.UnknownUnifyCmd,
            }
        }
        if (self.ustack.top != 0) return error.UnifyStackNotEmpty;
    }

    fn runUnifyStream(self: *Verifier, start_pos: u32, concl: *const Expr) !void {
        self.ustack.reset();
        try self.ustack.push(concl);
        try self.runUnifyStreamRaw(start_pos);
    }
};
