const std = @import("std");
const mm0 = @import("mm0");

const allocator = std.heap.wasm_allocator;

var result_json: []u8 = &.{};

pub export fn alloc(len: u32) u32 {
    if (len == 0) return 0;
    const buf = allocator.alloc(u8, len) catch return 0;
    return @intCast(@intFromPtr(buf.ptr));
}

pub export fn free(ptr: u32, len: u32) void {
    if (ptr == 0 or len == 0) return;
    allocator.free(ptrToSlice(ptr, len));
}

pub export fn verify_pair(
    mm0_ptr: u32,
    mm0_len: u32,
    mmb_ptr: u32,
    mmb_len: u32,
) u32 {
    clearState();

    const mm0_src = ptrToConstSlice(mm0_ptr, mm0_len);
    const mmb_bytes = ptrToConstSlice(mmb_ptr, mmb_len);
    mm0.verifyPair(allocator, mm0_src, mmb_bytes) catch |err| {
        writeVerifyFailure(err) catch clearState();
        return 0;
    };
    writeVerifySuccess() catch {
        clearState();
        return 0;
    };
    return 1;
}

pub export fn result_json_ptr() u32 {
    return slicePtr(result_json);
}

pub export fn result_json_len() u32 {
    return @intCast(result_json.len);
}

fn clearState() void {
    if (result_json.len != 0) allocator.free(result_json);
    result_json = &.{};
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

fn writeVerifySuccess() !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.writeAll("{");
    try out.writer.writeAll("\"ok\":true,");
    try out.writer.writeAll("\"phase\":\"verify\",");
    try out.writer.writeAll("\"message\":\"ok\",");
    try out.writer.writeAll("\"error\":null}");

    result_json = try out.toOwnedSlice();
}

fn writeVerifyFailure(err: anyerror) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.writeAll("{");
    try out.writer.writeAll("\"ok\":false,");
    try out.writer.writeAll("\"phase\":\"verify\",");
    try writeJsonStringField(&out.writer, "error", @errorName(err));
    try out.writer.writeByte(',');
    try writeJsonStringField(&out.writer, "message", @errorName(err));
    try out.writer.writeAll("}");

    result_json = try out.toOwnedSlice();
}

fn writeJsonStringField(
    writer: anytype,
    name: []const u8,
    value: []const u8,
) !void {
    try writer.print("\"{s}\":\"{s}\"", .{ name, value });
}
