const std = @import("std");
const mm0 = @import("mm0");

const allocator = std.heap.wasm_allocator;

var result_json: []u8 = &.{};
var result_mmb: []u8 = &.{};

pub export fn alloc(len: u32) u32 {
    if (len == 0) return 0;
    const buf = allocator.alloc(u8, len) catch return 0;
    return @intCast(@intFromPtr(buf.ptr));
}

pub export fn free(ptr: u32, len: u32) void {
    if (ptr == 0 or len == 0) return;
    allocator.free(ptrToSlice(ptr, len));
}

pub export fn compile_sources(
    mm0_ptr: u32,
    mm0_len: u32,
    proof_ptr: u32,
    proof_len: u32,
) u32 {
    clearState();

    const mm0_src = ptrToConstSlice(mm0_ptr, mm0_len);
    const proof_src = ptrToConstSlice(proof_ptr, proof_len);
    var compiler = mm0.Compiler.initWithProof(allocator, mm0_src, proof_src);

    result_mmb = compiler.compileMmb(allocator) catch |err| {
        var analysis_compiler = mm0.Compiler.initWithProof(
            allocator,
            mm0_src,
            proof_src,
        );
        analysis_compiler.analyze() catch {};
        writeCompileFailure(&compiler, &analysis_compiler, err) catch clearState();
        return 0;
    };
    writeCompileSuccess(result_mmb.len) catch {
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

pub export fn result_mmb_ptr() u32 {
    return slicePtr(result_mmb);
}

pub export fn result_mmb_len() u32 {
    return @intCast(result_mmb.len);
}

fn clearState() void {
    if (result_json.len != 0) allocator.free(result_json);
    if (result_mmb.len != 0) allocator.free(result_mmb);
    result_json = &.{};
    result_mmb = &.{};
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

fn writeCompileSuccess(mmb_len: usize) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.writeAll("{");
    try out.writer.writeAll("\"ok\":true,");
    try out.writer.writeAll("\"phase\":\"compile\",");
    try out.writer.writeAll("\"message\":\"ok\",");
    try out.writer.writeAll("\"error\":null,");
    try out.writer.writeAll("\"mmbLen\":");
    try out.writer.print("{d}", .{mmb_len});
    try out.writer.writeAll(",\"diagnostic\":null,");
    try writeDiagnosticsField(&out.writer, null);
    try out.writer.writeByte('}');

    result_json = try out.toOwnedSlice();
}

fn writeCompileFailure(
    compiler: *const mm0.Compiler,
    analysis_compiler: *const mm0.Compiler,
    err: anyerror,
) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.writeAll("{");
    try out.writer.writeAll("\"ok\":false,");
    try out.writer.writeAll("\"phase\":\"compile\",");
    try writeJsonStringField(&out.writer, "error", @errorName(err));
    try out.writer.writeByte(',');

    if (compiler.last_diagnostic) |diag| {
        try writeJsonStringField(
            &out.writer,
            "message",
            mm0.compilerDiagnosticSummary(diag),
        );
        try out.writer.writeAll(",\"mmbLen\":0,\"diagnostic\":");
        try writeDiagnosticObject(&out.writer, diag);
    } else {
        try writeJsonStringField(&out.writer, "message", @errorName(err));
        try out.writer.writeAll(",\"mmbLen\":0,\"diagnostic\":null");
    }
    try out.writer.writeByte(',');
    try writeDiagnosticsField(&out.writer, analysis_compiler);
    try out.writer.writeByte('}');

    result_json = try out.toOwnedSlice();
}

fn writeDiagnosticsField(
    writer: anytype,
    compiler: ?*const mm0.Compiler,
) !void {
    try writer.writeAll("\"diagnostics\":[");

    if (compiler) |actual| {
        var need_comma = false;
        for (actual.primaryDiagnostics()) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, diag);
            need_comma = true;
        }
        if (actual.omittedPrimaryDiagnostic(.mm0)) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, diag);
            need_comma = true;
        }
        if (actual.omittedPrimaryDiagnostic(.proof)) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, diag);
            need_comma = true;
        }
        for (actual.warningDiagnostics()) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, diag);
            need_comma = true;
        }
    }

    try writer.writeByte(']');
}

fn writeDiagnosticObject(
    writer: anytype,
    diag: mm0.CompilerDiagnostic,
) !void {
    try writer.writeByte('{');
    try writeJsonStringField(
        writer,
        "message",
        mm0.compilerDiagnosticSummary(diag),
    );
    try writer.writeByte(',');
    try writeJsonStringField(writer, "severity", @tagName(diag.severity));
    try writer.writeByte(',');
    try writeJsonStringField(writer, "source", @tagName(diag.source));
    try writer.writeByte(',');
    try writeJsonStringField(writer, "error", @errorName(diag.err));
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "theorem", diag.theorem_name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "block", diag.block_name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "lineLabel", diag.line_label);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "rule", diag.rule_name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "name", diag.name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "expected", diag.expected_name);
    try writer.writeByte(',');
    try writeOptionalStringField(
        writer,
        "phase",
        if (diag.phase) |phase|
            diagnosticPhaseName(phase)
        else
            null,
    );
    try writer.writeByte(',');
    try writeOptionalUsizeField(
        writer,
        "spanStart",
        if (diag.span) |span| span.start else null,
    );
    try writer.writeByte(',');
    try writeOptionalUsizeField(
        writer,
        "spanEnd",
        if (diag.span) |span| span.end else null,
    );
    try writer.writeByte(',');
    try writeDiagnosticDetailField(writer, diag);
    try writer.writeByte(',');
    try writeDiagnosticNotesField(writer, diag);
    try writer.writeByte(',');
    try writeDiagnosticRelatedField(writer, diag);
    try writer.writeByte('}');
}

fn writeJsonStringField(
    writer: anytype,
    name: []const u8,
    value: []const u8,
) !void {
    try writer.print("\"{s}\":\"{s}\"", .{ name, value });
}

fn writeOptionalStringField(
    writer: anytype,
    name: []const u8,
    value: ?[]const u8,
) !void {
    try writer.print("\"{s}\":", .{name});
    if (value) |actual| {
        try writer.print("\"{s}\"", .{actual});
    } else {
        try writer.writeAll("null");
    }
}

fn writeOptionalUsizeField(
    writer: anytype,
    name: []const u8,
    value: anytype,
) !void {
    try writer.print("\"{s}\":", .{name});
    switch (@typeInfo(@TypeOf(value))) {
        .optional => {
            if (value) |actual| {
                try writer.print("{d}", .{actual});
            } else {
                try writer.writeAll("null");
            }
        },
        else => {
            try writer.print("{d}", .{value});
        },
    }
}

fn diagnosticPhaseName(phase: mm0.CompilerDiagnosticPhase) []const u8 {
    return switch (phase) {
        .parse => "parse",
        .inference => "inference",
        .theorem_application => "theorem_application",
        .freshen => "freshen",
        .normalization => "normalization",
        .final_reconciliation => "final_reconciliation",
    };
}

fn writeDiagnosticDetailField(
    writer: anytype,
    diag: mm0.CompilerDiagnostic,
) !void {
    try writer.writeAll("\"detail\":");
    switch (diag.detail) {
        .none => try writer.writeAll("null"),
        .omitted_diagnostics => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(
                writer,
                "kind",
                "omitted_diagnostics",
            );
            try writer.writeByte(',');
            try writer.writeAll("\"summary\":\"");
            try mm0.writeCompilerOmittedDiagnosticsSummary(
                writer,
                info.count,
            );
            try writer.writeByte('"');
            try writer.writeByte(',');
            try writer.print("\"count\":{d}", .{info.count});
            try writer.writeAll("}");
        },
        .unknown_math_token => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "unknown_math_token");
            try writer.writeByte(',');
            try writeJsonStringField(writer, "token", info.token);
            try writer.writeAll("}");
        },
        .missing_binder_assignment => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(
                writer,
                "kind",
                "missing_binder_assignment",
            );
            try writer.writeByte(',');
            try writeJsonStringField(writer, "binder", info.binder_name);
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "path",
                @tagName(info.path),
            );
            try writer.writeAll("}");
        },
        .inference_failure => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "inference_failure");
            try writer.writeByte(',');
            try writeJsonStringField(writer, "path", @tagName(info.path));
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "firstUnsolvedBinder",
                info.first_unsolved_binder_name,
            );
            try writer.writeAll("}");
        },
        .dep_violation => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "dep_violation");
            try writer.writeByte(',');
            try writer.writeAll("\"summary\":\"");
            try mm0.writeCompilerDepViolationSummary(writer, info);
            try writer.writeByte('"');
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "firstArgName",
                info.first_arg_name,
            );
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "secondArgName",
                info.second_arg_name,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "firstArgIndex",
                info.first_arg_idx,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "secondArgIndex",
                info.second_arg_idx,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "firstDeps",
                info.first_deps,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "secondDeps",
                info.second_deps,
            );
            try writer.writeByte(',');
            try writer.print("\"firstBound\":{}", .{info.first_bound});
            try writer.writeByte(',');
            try writer.print("\"secondBound\":{}", .{info.second_bound});
            try writer.writeAll("}");
        },
        .definition_body => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "definition_body");
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "summary",
                mm0.compilerDiagnosticSummary(diag),
            );
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "declaredSort",
                info.declared_sort_name,
            );
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "actualSort",
                info.actual_sort_name,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(writer, "bodyDeps", info.body_deps);
            try writer.writeByte(',');
            try writer.print(
                "\"hiddenBinderCount\":{d}",
                .{info.hidden_binder_count},
            );
            try writer.writeAll("}");
        },
        .missing_congruence_rule => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(
                writer,
                "kind",
                "missing_congruence_rule",
            );
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "reason",
                @tagName(info.reason),
            );
            try writer.writeByte(',');
            try writer.writeAll("\"summary\":\"");
            try mm0.writeCompilerMissingCongruenceRuleSummary(writer, info);
            try writer.writeByte('"');
            try writer.writeByte(',');
            try writeOptionalStringField(writer, "term", info.term_name);
            try writer.writeByte(',');
            try writeOptionalStringField(writer, "sort", info.sort_name);
            try writer.writeByte(',');
            try writeOptionalUsizeField(writer, "argIndex", info.arg_index);
            try writer.writeAll("}");
        },
        .hypothesis_ref => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "hypothesis_ref");
            try writer.writeByte(',');
            try writer.writeAll("\"index\":");
            try writer.print("{d}", .{info.index});
            try writer.writeAll("}");
        },
        .unused_parameter => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "unused_parameter");
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "parameter",
                info.parameter_name,
            );
            try writer.writeAll("}");
        },
    }
}

fn writeDiagnosticNotesField(
    writer: anytype,
    diag: mm0.CompilerDiagnostic,
) !void {
    try writer.writeAll("\"notes\":[");
    for (diag.noteSlice(), 0..) |note, idx| {
        if (idx != 0) try writer.writeByte(',');
        try writer.writeAll("{");
        try writeJsonStringField(writer, "message", note.message);
        try writer.writeByte(',');
        try writeJsonStringField(writer, "source", @tagName(note.source));
        try writer.writeByte(',');
        try writeOptionalUsizeField(
            writer,
            "spanStart",
            if (note.span) |span| span.start else null,
        );
        try writer.writeByte(',');
        try writeOptionalUsizeField(
            writer,
            "spanEnd",
            if (note.span) |span| span.end else null,
        );
        try writer.writeAll("}");
    }
    try writer.writeByte(']');
}

fn writeDiagnosticRelatedField(
    writer: anytype,
    diag: mm0.CompilerDiagnostic,
) !void {
    try writer.writeAll("\"related\":[");
    for (diag.relatedSlice(), 0..) |related, idx| {
        if (idx != 0) try writer.writeByte(',');
        try writer.writeAll("{");
        try writeJsonStringField(writer, "label", related.label);
        try writer.writeByte(',');
        try writeJsonStringField(
            writer,
            "source",
            @tagName(related.source),
        );
        try writer.writeByte(',');
        try writeOptionalUsizeField(writer, "spanStart", related.span.start);
        try writer.writeByte(',');
        try writeOptionalUsizeField(writer, "spanEnd", related.span.end);
        try writer.writeAll("}");
    }
    try writer.writeByte(']');
}
