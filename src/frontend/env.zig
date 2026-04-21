const std = @import("std");
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;
const AssertionKind = @import("../trusted/parse.zig").AssertionKind;
const AssertionStmt = @import("../trusted/parse.zig").AssertionStmt;
const Expr = @import("../trusted/expressions.zig").Expr;
const MM0Stmt = @import("../trusted/parse.zig").MM0Stmt;
const SortStmt = @import("../trusted/parse.zig").SortStmt;
const TermStmt = @import("../trusted/parse.zig").TermStmt;
const TemplateExpr = @import("./rules.zig").TemplateExpr;

pub const TermDecl = struct {
    name: []const u8,
    args: []const ArgInfo,
    arg_names: []const ?[]const u8,
    dummy_args: []const ArgInfo,
    ret_sort_name: []const u8,
    is_def: bool,
    body: ?TemplateExpr,
    // In recovery mode we sometimes keep a placeholder here for a parsed
    // term that failed semantic validation. The parser bakes term ids into
    // later expressions, so the `terms` array must stay aligned with parser
    // order even when the frontend decides that a term is unusable.
    available: bool = true,
};

pub const RuleDecl = struct {
    name: []const u8,
    args: []const ArgInfo,
    arg_names: []const ?[]const u8,
    hyps: []const TemplateExpr,
    concl: TemplateExpr,
    kind: AssertionKind,
    is_local: bool,
};

pub const GlobalEnv = struct {
    allocator: std.mem.Allocator,
    sort_names: std.StringHashMap(u8),
    term_names: std.StringHashMap(u32),
    rule_names: std.StringHashMap(u32),
    terms: std.ArrayListUnmanaged(TermDecl) = .{},
    rules: std.ArrayListUnmanaged(RuleDecl) = .{},

    pub fn init(allocator: std.mem.Allocator) GlobalEnv {
        return .{
            .allocator = allocator,
            .sort_names = std.StringHashMap(u8).init(allocator),
            .term_names = std.StringHashMap(u32).init(allocator),
            .rule_names = std.StringHashMap(u32).init(allocator),
        };
    }

    pub fn addStmt(self: *GlobalEnv, stmt: MM0Stmt) !void {
        switch (stmt) {
            .sort => |sort| try self.addSort(sort),
            .term => |term| try self.addTerm(term),
            .assertion => |rule| try self.addRule(rule),
        }
    }

    pub fn addSort(self: *GlobalEnv, stmt: SortStmt) !void {
        const sort_id = std.math.cast(u8, self.sort_names.count()) orelse {
            return error.TooManySorts;
        };
        try self.sort_names.put(stmt.name, sort_id);
    }

    pub fn addTerm(self: *GlobalEnv, stmt: TermStmt) !void {
        const term_id = std.math.cast(u32, self.terms.items.len) orelse {
            return error.TooManyCompilerTerms;
        };
        try self.terms.append(self.allocator, try self.buildTermDecl(stmt));
        try self.term_names.put(stmt.name, term_id);
    }

    pub fn appendInvalidTerm(self: *GlobalEnv, name: []const u8) !void {
        // Reserve the parser-assigned term id, but do not expose the name in
        // `term_names`. Later parsed expressions may still mention this id,
        // and recovery code will reject those references via `available`.
        try self.terms.append(self.allocator, invalidTermDecl(name));
    }

    pub fn invalidateLastTerm(self: *GlobalEnv, name: []const u8) void {
        std.debug.assert(self.terms.items.len != 0);
        _ = self.term_names.remove(name);
        // Keep the slot so parser term ids remain stable, but replace the
        // declaration with an unavailable placeholder so semantic lookups do
        // not treat the broken term as part of the surviving environment.
        self.terms.items[self.terms.items.len - 1] = invalidTermDecl(name);
    }

    pub fn hasAvailableTerm(self: *const GlobalEnv, term_id: u32) bool {
        return term_id < self.terms.items.len and
            self.terms.items[term_id].available;
    }

    pub fn addRule(self: *GlobalEnv, stmt: AssertionStmt) !void {
        if (self.rule_names.contains(stmt.name)) {
            return error.DuplicateRuleName;
        }
        const rule_id = std.math.cast(u32, self.rules.items.len) orelse {
            return error.TooManyCompilerRules;
        };
        const hyps = try self.allocator.alloc(TemplateExpr, stmt.hyps.len);
        for (stmt.hyps, 0..) |hyp, idx| {
            hyps[idx] = try TemplateExpr.fromExpr(
                self.allocator,
                hyp,
                stmt.arg_exprs,
            );
        }
        const concl = try TemplateExpr.fromExpr(
            self.allocator,
            stmt.concl,
            stmt.arg_exprs,
        );
        try self.rules.append(self.allocator, .{
            .name = stmt.name,
            .args = stmt.args,
            .arg_names = stmt.arg_names,
            .hyps = hyps,
            .concl = concl,
            .kind = stmt.kind,
            .is_local = stmt.is_local,
        });
        try self.rule_names.put(stmt.name, rule_id);
    }

    pub fn rollbackRulesToLen(
        self: *GlobalEnv,
        previous_len: usize,
        name: []const u8,
    ) void {
        if (self.rules.items.len > previous_len) {
            self.rules.items.len = previous_len;
        }
        if (self.rule_names.get(name)) |rule_id| {
            if (rule_id >= previous_len) {
                _ = self.rule_names.remove(name);
            }
        }
    }

    pub fn removeLastRule(self: *GlobalEnv, name: []const u8) void {
        const rule_id = self.rule_names.get(name) orelse return;
        std.debug.assert(self.rules.items.len != 0);
        const last_idx = self.rules.items.len - 1;
        std.debug.assert(rule_id == last_idx);
        _ = self.rule_names.remove(name);
        self.rules.items.len = last_idx;
    }

    pub fn getRuleId(self: *const GlobalEnv, name: []const u8) ?u32 {
        return self.rule_names.get(name);
    }

    pub fn getRule(self: *const GlobalEnv, name: []const u8) ?*const RuleDecl {
        const rule_id = self.getRuleId(name) orelse return null;
        return &self.rules.items[rule_id];
    }

    fn buildTermDecl(self: *GlobalEnv, stmt: TermStmt) !TermDecl {
        const body = if (stmt.body) |expr| blk: {
            if (stmt.dummy_exprs.len > 0) {
                const all_exprs = try self.allocator.alloc(
                    *const Expr,
                    stmt.arg_exprs.len + stmt.dummy_exprs.len,
                );
                @memcpy(all_exprs[0..stmt.arg_exprs.len], stmt.arg_exprs);
                @memcpy(all_exprs[stmt.arg_exprs.len..], stmt.dummy_exprs);
                break :blk try TemplateExpr.fromExpr(
                    self.allocator,
                    expr,
                    all_exprs,
                );
            } else {
                break :blk try TemplateExpr.fromExpr(
                    self.allocator,
                    expr,
                    stmt.arg_exprs,
                );
            }
        } else null;
        return .{
            .name = stmt.name,
            .args = stmt.args,
            .arg_names = stmt.arg_names,
            .dummy_args = stmt.dummy_args,
            .ret_sort_name = stmt.ret_sort_name,
            .is_def = stmt.is_def,
            .body = body,
        };
    }
};

fn invalidTermDecl(name: []const u8) TermDecl {
    // This sentinel is intentionally minimal. It exists only to occupy the
    // parser's term-id slot after recovery has discarded the declaration.
    return .{
        .name = name,
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .ret_sort_name = "",
        .is_def = false,
        .body = null,
        .available = false,
    };
}
