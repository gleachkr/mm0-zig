const std = @import("std");
const GlobalEnv = @import("../compiler_env.zig").GlobalEnv;
const TheoremContext = @import("../compiler_expr.zig").TheoremContext;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;

pub const SharedContext = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: ?*RewriteRegistry,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) SharedContext {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = null,
        };
    }

    pub fn initWithRegistry(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
    ) SharedContext {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = registry,
        };
    }

    pub fn deinit(self: *SharedContext) void {
        _ = self;
    }
};
