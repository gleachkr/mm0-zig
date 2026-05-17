const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const Expr = @import("../../../trusted/expressions.zig").Expr;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("../diag.zig");
const CompilerVars = @import("../vars.zig");
const Emit = @import("../emit.zig");

const SortVarRegistry = CompilerVars.SortVarRegistry;
const NameExprMap = std.StringHashMap(*const Expr);

/// Per-proof cache for verifier-style rule unify streams used by strict
/// inference replay.  Rule templates are immutable once they enter the env,
/// so the stream only depends on the rule id.
pub const RuleUnifyCache = struct {
    allocator: std.mem.Allocator,
    entries: std.AutoHashMapUnmanaged(u32, []const u8) = .empty,

    pub fn init(allocator: std.mem.Allocator) RuleUnifyCache {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *RuleUnifyCache) void {
        var it = self.entries.valueIterator();
        while (it.next()) |stream| {
            self.allocator.free(stream.*);
        }
        self.entries.deinit(self.allocator);
    }

    pub fn get(
        self: *RuleUnifyCache,
        rule_id: u32,
        rule: *const RuleDecl,
    ) ![]const u8 {
        const gop = try self.entries.getOrPut(self.allocator, rule_id);
        if (!gop.found_existing) {
            gop.value_ptr.* = try Emit.buildRuleUnifyStream(
                self.allocator,
                rule,
            );
        }
        return gop.value_ptr.*;
    }
};

pub const HiddenWitnessFreshContext = struct {
    parser: *MM0Parser,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
};

/// Shared state for one rule application inference attempt.
///
/// The compiler-specific diagnostic receiver and source line stay outside this
/// context because they are `anytype` values.  Everything else here is the
/// stable rule/application state that used to be threaded through most
/// inference helpers as a long positional prefix.
pub const RuleInferenceContext = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    theorem: *TheoremContext,
    assertion: AssertionStmt,
    rule_id: u32,
    rule: *const RuleDecl,
    rule_unify_cache: ?*RuleUnifyCache = null,

    pub fn cachedUnify(self: *const RuleInferenceContext) !?[]const u8 {
        const cache = self.rule_unify_cache orelse return null;
        return try cache.get(self.rule_id, self.rule);
    }
};

pub const InferenceContext = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    // Heap prefix `0..rule.args.len` stores inferred theorem arguments.
    // These slots start as either an explicit binding or `null` if omitted.
    // Any entries appended later by `UTermSave` are concrete by construction.
    uheap: std.ArrayListUnmanaged(?ExprId) = .{},
    ustack: std.ArrayListUnmanaged(ExprId) = .{},
    hyps: []const ExprId,
    next_hyp: usize,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        partial_bindings: []const ?ExprId,
        hyps: []const ExprId,
        line_expr: ExprId,
    ) !InferenceContext {
        var ctx = InferenceContext{
            .allocator = allocator,
            .theorem = theorem,
            .hyps = hyps,
            .next_hyp = hyps.len,
        };
        try ctx.uheap.appendSlice(allocator, partial_bindings);
        try ctx.ustack.append(allocator, line_expr);
        return ctx;
    }

    pub fn deinit(self: *InferenceContext) void {
        self.uheap.deinit(self.allocator);
        self.ustack.deinit(self.allocator);
    }

    pub fn uopRef(self: *InferenceContext, heap_id: u32) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        if (heap_id >= self.uheap.items.len) return error.UHeapOutOfBounds;
        if (self.uheap.items[heap_id]) |expected| {
            if (expr_id != expected) return error.UnifyMismatch;
        } else {
            // This is the one semantic difference from verifier-style unify:
            // the first encounter with an omitted binder solves it.
            self.uheap.items[heap_id] = expr_id;
        }
    }

    // Unify replay is exact replay. Def-aware inference lives in
    // higher-level solver paths rather than in the opcode interpreter.
    pub fn uopTerm(
        self: *InferenceContext,
        term_id: u32,
        save: bool,
    ) !void {
        if (self.ustack.items.len == 0) return error.UStackUnderflow;
        const expr_id = self.ustack.pop().?;
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return error.ExpectedTermApp,
            .placeholder => return error.ExpectedTermApp,
        };
        if (app.term_id != term_id) return error.TermMismatch;
        if (save) try self.uheap.append(self.allocator, expr_id);
        var i = app.args.len;
        while (i > 0) {
            i -= 1;
            try self.ustack.append(self.allocator, app.args[i]);
        }
    }

    pub fn uopDummy(self: *InferenceContext, _: u32) !void {
        _ = self;
        return error.UDummyNotAllowed;
    }

    pub fn uopHyp(self: *InferenceContext) !void {
        if (self.next_hyp == 0) return error.HypCountMismatch;
        // See `buildRuleUnifyStream`: hypotheses are replayed from the end so
        // that they are matched in source order overall.
        self.next_hyp -= 1;
        try self.ustack.append(self.allocator, self.hyps[self.next_hyp]);
    }
};
