const std = @import("std");

/// Extensible debug configuration. Each field corresponds to a subsystem
/// that can emit targeted debug output when enabled.
///
/// Enable from the CLI with `--debug inference,unfolding` etc.
/// In code, check `if (debug.inference) std.debug.print(...)`.
pub const DebugConfig = struct {
    inference: bool = false,
    unfolding: bool = false,
    normalization: bool = false,
    emission: bool = false,
    check: bool = false,

    pub const none = DebugConfig{};

    pub fn parse(arg: []const u8) error{InvalidDebugFlag}!DebugConfig {
        var config = DebugConfig{};
        var iter = std.mem.splitScalar(u8, arg, ',');
        while (iter.next()) |token| {
            const flag = std.mem.trim(u8, token, " ");
            if (flag.len == 0) continue;
            if (std.mem.eql(u8, flag, "inference")) {
                config.inference = true;
            } else if (std.mem.eql(u8, flag, "unfolding")) {
                config.unfolding = true;
            } else if (std.mem.eql(u8, flag, "normalization")) {
                config.normalization = true;
            } else if (std.mem.eql(u8, flag, "emission")) {
                config.emission = true;
            } else if (std.mem.eql(u8, flag, "check")) {
                config.check = true;
            } else if (std.mem.eql(u8, flag, "all")) {
                return .{
                    .inference = true,
                    .unfolding = true,
                    .normalization = true,
                    .emission = true,
                    .check = true,
                };
            } else {
                return error.InvalidDebugFlag;
            }
        }
        return config;
    }

    pub fn any(self: DebugConfig) bool {
        return self.inference or self.unfolding or self.normalization or
            self.emission or self.check;
    }
};

/// Print a debug message tagged with the subsystem name.
/// Usage: debug.print("inference", "solving rule {s}", .{rule_name});
pub fn print(comptime subsystem: []const u8, comptime fmt: []const u8, args: anytype) void {
    std.debug.print("[debug:" ++ subsystem ++ "] " ++ fmt ++ "\n", args);
}
