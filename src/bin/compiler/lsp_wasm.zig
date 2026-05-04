const std = @import("std");
const lsp = @import("lsp");
const compiler_lsp = @import("./lsp.zig");

const allocator = std.heap.wasm_allocator;

var result_lsp: []u8 = &.{};
var lsp_handler: compiler_lsp.Handler = undefined;
var lsp_handler_initialized = false;
var browser_transport: BrowserTransport = .{};

pub export fn alloc(len: u32) u32 {
    if (len == 0) return 0;
    const buf = allocator.alloc(u8, len) catch return 0;
    return @intCast(@intFromPtr(buf.ptr));
}

pub export fn free(ptr: u32, len: u32) void {
    if (ptr == 0 or len == 0) return;
    allocator.free(ptrToSlice(ptr, len));
}

pub export fn process_lsp_message(message_ptr: u32, message_len: u32) u32 {
    clearLspResult();
    if (!lsp_handler_initialized) {
        lsp_handler = compiler_lsp.Handler.init(
            allocator,
            &browser_transport.transport,
        );
        lsp_handler_initialized = true;
    }

    browser_transport.reset(ptrToConstSlice(message_ptr, message_len));
    lsp.basic_server.run(
        allocator,
        &browser_transport.transport,
        &lsp_handler,
        null,
    ) catch |err| switch (err) {
        error.EndOfStream => {},
        else => {
            writeLspError(err) catch clearLspResult();
            return 0;
        },
    };

    result_lsp = allocator.dupe(u8, browser_transport.output.items) catch {
        clearLspResult();
        return 0;
    };
    return 1;
}

pub export fn reset_lsp_server() void {
    clearLspResult();
    browser_transport.deinit();
    if (lsp_handler_initialized) {
        lsp_handler.deinit();
        lsp_handler_initialized = false;
    }
}

pub export fn result_lsp_ptr() u32 {
    return slicePtr(result_lsp);
}

pub export fn result_lsp_len() u32 {
    return @intCast(result_lsp.len);
}

fn clearLspResult() void {
    if (result_lsp.len != 0) allocator.free(result_lsp);
    result_lsp = &.{};
}

fn ptrToSlice(ptr: u32, len: u32) []u8 {
    return @as([*]u8, @ptrFromInt(ptr))[0..len];
}

fn ptrToConstSlice(ptr: u32, len: u32) []const u8 {
    if (ptr == 0 or len == 0) return &.{};
    return @as([*]const u8, @ptrFromInt(ptr))[0..len];
}

fn slicePtr(bytes: []const u8) u32 {
    if (bytes.len == 0) return 0;
    return @intCast(@intFromPtr(bytes.ptr));
}

const BrowserTransport = struct {
    transport: lsp.Transport = .{ .vtable = &vtable },
    input: []const u8 = &.{},
    consumed: bool = true,
    output: std.ArrayListUnmanaged(u8) = .empty,

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    fn reset(self: *BrowserTransport, input: []const u8) void {
        self.input = input;
        self.consumed = false;
        self.output.clearRetainingCapacity();
    }

    fn deinit(self: *BrowserTransport) void {
        self.output.deinit(allocator);
        self.* = .{};
    }

    fn readJsonMessage(
        transport: *lsp.Transport,
        arena: std.mem.Allocator,
    ) lsp.Transport.ReadError![]u8 {
        const self: *BrowserTransport = @fieldParentPtr(
            "transport",
            transport,
        );
        if (self.consumed) return error.EndOfStream;
        self.consumed = true;
        return try arena.dupe(u8, self.input);
    }

    fn writeJsonMessage(
        transport: *lsp.Transport,
        json_message: []const u8,
    ) lsp.Transport.WriteError!void {
        const self: *BrowserTransport = @fieldParentPtr(
            "transport",
            transport,
        );
        self.output.appendSlice(allocator, json_message) catch unreachable;
        self.output.append(allocator, '\n') catch unreachable;
    }
};

fn writeLspError(err: anyerror) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    try out.writer.print(
        "{{\"jsonrpc\":\"2.0\",\"error\":{{" ++
            "\"code\":-32603,\"message\":\"{s}\"}}}}\n",
        .{@errorName(err)},
    );
    result_lsp = try out.toOwnedSlice();
}
