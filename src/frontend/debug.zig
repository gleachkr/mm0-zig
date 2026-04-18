const builtin = @import("builtin");
const std = @import("std");

pub const DebugChannel = enum {
    inference,
    views,
    dependency,
    freshen,
    normalization,
    boundary,
};

pub const advertised_channel_list =
    "inference,views,dependency,freshen,normalization,boundary,all";

fn parseChannelFlag(flag: []const u8) ?DebugChannel {
    if (std.mem.eql(u8, flag, "inference") or
        std.mem.eql(u8, flag, "unfolding"))
    {
        return .inference;
    }
    if (std.mem.eql(u8, flag, "views")) {
        return .views;
    }
    if (std.mem.eql(u8, flag, "dependency")) {
        return .dependency;
    }
    if (std.mem.eql(u8, flag, "freshen")) {
        return .freshen;
    }
    if (std.mem.eql(u8, flag, "normalization") or
        std.mem.eql(u8, flag, "emission"))
    {
        return .normalization;
    }
    if (std.mem.eql(u8, flag, "boundary") or
        std.mem.eql(u8, flag, "reconciliation") or
        std.mem.eql(u8, flag, "check"))
    {
        return .boundary;
    }
    return null;
}

/// Extensible debug configuration. Each field corresponds to a maintained
/// trace category with stable CLI spellings.
pub const DebugConfig = struct {
    inference: bool = false,
    views: bool = false,
    dependency: bool = false,
    freshen: bool = false,
    normalization: bool = false,
    boundary: bool = false,

    pub const none = DebugConfig{};

    pub fn parse(arg: []const u8) error{InvalidDebugFlag}!DebugConfig {
        var config = DebugConfig{};
        var iter = std.mem.splitScalar(u8, arg, ',');
        while (iter.next()) |token| {
            const flag = std.mem.trim(u8, token, " ");
            if (flag.len == 0) continue;

            if (std.mem.eql(u8, flag, "all")) {
                return all();
            }

            const channel = parseChannelFlag(flag) orelse {
                return error.InvalidDebugFlag;
            };
            config.enable(channel);
        }
        return config;
    }

    pub fn all() DebugConfig {
        return .{
            .inference = true,
            .views = true,
            .dependency = true,
            .freshen = true,
            .normalization = true,
            .boundary = true,
        };
    }

    pub fn any(self: DebugConfig) bool {
        return self.inference or self.views or self.dependency or
            self.freshen or self.normalization or self.boundary;
    }

    pub fn enabled(
        self: DebugConfig,
        comptime channel: DebugChannel,
    ) bool {
        return switch (channel) {
            .inference => self.inference,
            .views => self.views,
            .dependency => self.dependency,
            .freshen => self.freshen,
            .normalization => self.normalization,
            .boundary => self.boundary,
        };
    }

    pub fn enable(self: *DebugConfig, channel: DebugChannel) void {
        switch (channel) {
            .inference => self.inference = true,
            .views => self.views = true,
            .dependency => self.dependency = true,
            .freshen => self.freshen = true,
            .normalization => self.normalization = true,
            .boundary => self.boundary = true,
        }
    }
};

pub fn channelName(comptime channel: DebugChannel) []const u8 {
    return switch (channel) {
        .inference => "inference",
        .views => "views",
        .dependency => "dependency",
        .freshen => "freshen",
        .normalization => "normalization",
        .boundary => "boundary",
    };
}

pub fn trace(
    comptime channel: DebugChannel,
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    if (comptime builtin.target.os.tag == .freestanding) return;
    if (!config.enabled(channel)) return;
    std.debug.print(
        "[debug:" ++ channelName(channel) ++ "] " ++ fmt ++ "\n",
        args,
    );
}

pub fn traceInference(
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    trace(.inference, config, fmt, args);
}

pub fn traceViews(
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    trace(.views, config, fmt, args);
}

pub fn traceDependency(
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    trace(.dependency, config, fmt, args);
}

pub fn traceFreshen(
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    trace(.freshen, config, fmt, args);
}

pub fn traceNormalization(
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    trace(.normalization, config, fmt, args);
}

pub fn traceBoundary(
    config: DebugConfig,
    comptime fmt: []const u8,
    args: anytype,
) void {
    trace(.boundary, config, fmt, args);
}

test "debug config parses maintained channels" {
    const config = try DebugConfig.parse(
        "inference,views,dependency,freshen,normalization,boundary",
    );
    try std.testing.expect(config.inference);
    try std.testing.expect(config.views);
    try std.testing.expect(config.dependency);
    try std.testing.expect(config.freshen);
    try std.testing.expect(config.normalization);
    try std.testing.expect(config.boundary);
}

test "debug config accepts compatibility aliases" {
    const config = try DebugConfig.parse(
        "unfolding,emission,check,reconciliation",
    );
    try std.testing.expect(config.inference);
    try std.testing.expect(config.normalization);
    try std.testing.expect(config.boundary);
}

test "debug config trims whitespace and ignores empty entries" {
    const config = try DebugConfig.parse(
        " views , , dependency , freshen ",
    );
    try std.testing.expect(config.views);
    try std.testing.expect(config.dependency);
    try std.testing.expect(config.freshen);
    try std.testing.expect(!config.inference);
}

test "debug config rejects unknown channels" {
    try std.testing.expectError(
        error.InvalidDebugFlag,
        DebugConfig.parse("views,wat"),
    );
}

test "debug config all enables every maintained channel" {
    const config = try DebugConfig.parse("all");
    try std.testing.expectEqual(DebugConfig.all(), config);
}
