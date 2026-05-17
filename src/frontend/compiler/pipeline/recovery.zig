const std = @import("std");
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RewriteModule = @import("../../rewrite_registry.zig");
const RewriteRegistry = RewriteModule.RewriteRegistry;
const Metadata = @import("../metadata.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CompilerVars = @import("../vars.zig");

const FreshDecl = Metadata.FreshDecl;
const FreshenDecl = Metadata.FreshenDecl;
const ViewDecl = Metadata.ViewDecl;
const FreshBindingMap = std.AutoHashMap(u32, []const FreshDecl);
const FreshenBindingMap = std.AutoHashMap(u32, []const FreshenDecl);
const ViewMap = std.AutoHashMap(u32, ViewDecl);
const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const WarningSnapshot = struct {
    warning_count: usize,
    dropped_warning_count: usize,

    pub fn capture(self: *CompilerContext) WarningSnapshot {
        return .{
            .warning_count = self.diagnostics.warning_count,
            .dropped_warning_count = self.diagnostics.dropped_warning_count,
        };
    }

    pub fn restore(
        self: WarningSnapshot,
        context: *CompilerContext,
    ) void {
        context.diagnostics.warning_count = self.warning_count;
        context.diagnostics.dropped_warning_count =
            self.dropped_warning_count;
    }
};

pub const TermRecoverySnapshot = struct {
    registry: RewriteRegistry,
    term_count: usize,

    pub fn capture(
        allocator: std.mem.Allocator,
        state: anytype,
    ) !TermRecoverySnapshot {
        return .{
            .registry = try cloneRewriteRegistry(allocator, &state.registry),
            .term_count = state.env.terms.items.len,
        };
    }

    pub fn restore(
        self: TermRecoverySnapshot,
        state: anytype,
    ) void {
        state.registry = self.registry;
    }

    pub fn discardTerm(
        self: TermRecoverySnapshot,
        env: *GlobalEnv,
        name: []const u8,
    ) !void {
        if (env.terms.items.len > self.term_count) {
            env.invalidateLastTerm(name);
        } else {
            try env.appendInvalidTerm(name);
        }
    }
};

pub const AssertionRecoverySnapshot = struct {
    registry: RewriteRegistry,
    fresh_bindings: FreshBindingMap,
    freshen_bindings: FreshenBindingMap,
    views: ViewMap,
    rule_count: usize,

    pub fn capture(
        allocator: std.mem.Allocator,
        state: anytype,
    ) !AssertionRecoverySnapshot {
        return .{
            .registry = try cloneRewriteRegistry(allocator, &state.registry),
            .fresh_bindings = try cloneAutoHashMap(
                []const FreshDecl,
                allocator,
                &state.fresh_bindings,
            ),
            .freshen_bindings = try cloneAutoHashMap(
                []const FreshenDecl,
                allocator,
                &state.freshen_bindings,
            ),
            .views = try cloneAutoHashMap(
                ViewDecl,
                allocator,
                &state.views,
            ),
            .rule_count = state.env.rules.items.len,
        };
    }

    pub fn restore(
        self: AssertionRecoverySnapshot,
        state: anytype,
    ) void {
        state.registry = self.registry;
        state.fresh_bindings = self.fresh_bindings;
        state.freshen_bindings = self.freshen_bindings;
        state.views = self.views;
    }

    pub fn rollbackRule(
        self: AssertionRecoverySnapshot,
        env: *GlobalEnv,
        name: []const u8,
    ) void {
        env.rollbackRulesToLen(self.rule_count, name);
    }
};

fn cloneStringHashMap(
    comptime V: type,
    allocator: std.mem.Allocator,
    src: *const std.StringHashMap(V),
) !std.StringHashMap(V) {
    var dst = std.StringHashMap(V).init(allocator);
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

fn cloneAutoHashMap(
    comptime V: type,
    allocator: std.mem.Allocator,
    src: *const std.AutoHashMap(u32, V),
) !std.AutoHashMap(u32, V) {
    var dst = std.AutoHashMap(u32, V).init(allocator);
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

fn cloneAutoHashMapKV(
    comptime K: type,
    comptime V: type,
    allocator: std.mem.Allocator,
    src: *const std.AutoHashMap(K, V),
) !std.AutoHashMap(K, V) {
    var dst = std.AutoHashMap(K, V).init(allocator);
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

pub fn cloneSortVarRegistry(
    allocator: std.mem.Allocator,
    src: *const SortVarRegistry,
) !SortVarRegistry {
    return .{
        .allocator = allocator,
        .tokens = try cloneStringHashMap(
            CompilerVars.SortVarDecl,
            allocator,
            &src.tokens,
        ),
        .pools = try cloneStringHashMap(
            CompilerVars.SortVarPool,
            allocator,
            &src.pools,
        ),
    };
}

fn cloneRewriteRegistry(
    allocator: std.mem.Allocator,
    src: *const RewriteRegistry,
) !RewriteRegistry {
    return .{
        .allocator = allocator,
        .relations = try cloneStringHashMap(
            RewriteModule.RelationBundle,
            allocator,
            &src.relations,
        ),
        .rewrites_by_head = try cloneAutoHashMapKV(
            u32,
            std.ArrayListUnmanaged(
                RewriteModule.RewriteRule,
            ),
            allocator,
            &src.rewrites_by_head,
        ),
        .alpha_by_head = try cloneAutoHashMapKV(
            u32,
            std.ArrayListUnmanaged(
                RewriteModule.AlphaRule,
            ),
            allocator,
            &src.alpha_by_head,
        ),
        .congr_by_head = try cloneAutoHashMapKV(
            u32,
            RewriteModule.CongruenceRule,
            allocator,
            &src.congr_by_head,
        ),
        .fallbacks = try cloneAutoHashMapKV(
            u32,
            u32,
            allocator,
            &src.fallbacks,
        ),
        .acui_by_head = try cloneAutoHashMapKV(
            u32,
            RewriteModule.StructuralCombiner,
            allocator,
            &src.acui_by_head,
        ),
    };
}
