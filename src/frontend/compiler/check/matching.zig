const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const Inference = @import("../inference.zig");
const Normalize = @import("../normalize.zig");
const DebugConfig = @import("../../debug.zig").DebugConfig;
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendRuleLine = CheckedIr.appendRuleLine;
const appendTransportLine = CheckedIr.appendTransportLine;
const CompilerDiag = @import("../diag.zig");
const AcuiSupport = @import("../../acui_support.zig");

const max_fold_depth: usize = 12;
const max_acui_fold_items: usize = 24;

pub fn tryMatchHypothesis(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    debug: DebugConfig,
    hyp_idx: usize,
    actual_ref: CheckedRef,
    actual: ExprId,
    expected: ExprId,
) !?CheckedRef {
    if (actual == expected) return actual_ref;

    if (try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        expected,
        actual,
    )) {
        return .{ .line = try appendTransportLine(
            checked,
            allocator,
            expected,
            actual,
            actual_ref,
        ) };
    }

    // A referenced line may be in a raw producer form.  Final validation can
    // insert a transport to the expected hypothesis when the normalizer proves
    // equivalence.
    _ = hyp_idx;

    const normalized_mark = checked.items.len;
    if (try Normalize.buildNormalizedConversionWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        actual,
        expected,
        debug,
    )) |conversion| {
        var conversion_mut = conversion;
        if (conversion_mut.conv_line_idx) |conv_line_idx| {
            return .{ .line = try conversion_mut.normalizer.emitTransport(
                conversion_mut.relation,
                expected,
                actual,
                conv_line_idx,
                actual_ref,
            ) };
        }
        return actual_ref;
    }
    CheckedIr.rollbackToMark(allocator, checked, normalized_mark);

    const transparent_normalized_mark = checked.items.len;
    const converted = try Normalize.buildTransparentNormalizedHypRefWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        actual_ref,
        actual,
        expected,
        debug,
    );
    if (converted == null) {
        CheckedIr.rollbackToMark(
            allocator,
            checked,
            transparent_normalized_mark,
        );
    }
    return converted;
}

fn tryBuildFoldedIntermediateConclusionLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    debug: DebugConfig,
    line_expr: ExprId,
    expected_line: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !?usize {
    const intermediate = try buildFoldedIntermediate(
        allocator,
        theorem,
        registry,
        env,
        expected_line,
        line_expr,
        max_fold_depth,
    ) orelse return null;

    if (intermediate == expected_line) return null;
    if (!try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        intermediate,
        expected_line,
    )) return null;

    var conversion = if (intermediate == line_expr)
        null
    else
        try Normalize.buildNormalizedConversionWithDebug(
            allocator,
            theorem,
            registry,
            env,
            checked,
            scratch,
            intermediate,
            line_expr,
            debug,
        ) orelse return null;

    const raw_idx = try appendRuleLine(
        checked,
        allocator,
        expected_line,
        rule_id,
        bindings,
        refs,
    );
    const folded_idx = try appendTransportLine(
        checked,
        allocator,
        intermediate,
        expected_line,
        .{ .line = raw_idx },
    );

    if (conversion) |*conversion_mut| {
        if (conversion_mut.conv_line_idx) |conv_idx| {
            return try conversion_mut.normalizer.emitTransport(
                conversion_mut.relation,
                line_expr,
                intermediate,
                conv_idx,
                .{ .line = folded_idx },
            );
        }
    }
    return folded_idx;
}

fn buildFoldedIntermediate(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    raw: ExprId,
    user: ExprId,
    depth: usize,
) !?ExprId {
    if (raw == user or depth == 0) return null;
    if (isDefinitionApp(env, theorem, user)) {
        if (try Inference.canConvertTransparent(
            allocator,
            theorem,
            env,
            user,
            raw,
        )) return user;
    }

    if (try buildAcuiLeafFold(
        allocator,
        theorem,
        registry,
        env,
        raw,
        user,
    )) |folded| return folded;

    const raw_node = theorem.interner.node(raw);
    const user_node = theorem.interner.node(user);
    if (raw_node.* != .app or user_node.* != .app) return null;
    const raw_app = raw_node.app;
    const user_app = user_node.app;
    if (raw_app.term_id != user_app.term_id) return null;
    if (raw_app.args.len != user_app.args.len) return null;

    var changed = false;
    const new_args = try allocator.dupe(ExprId, raw_app.args);
    defer allocator.free(new_args);
    for (raw_app.args, user_app.args, 0..) |raw_arg, user_arg, idx| {
        if (try buildFoldedIntermediate(
            allocator,
            theorem,
            registry,
            env,
            raw_arg,
            user_arg,
            depth - 1,
        )) |folded_arg| {
            new_args[idx] = folded_arg;
            changed = true;
        }
    }
    if (!changed) return null;
    return try theorem.interner.internApp(raw_app.term_id, new_args);
}

fn buildAcuiLeafFold(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    raw: ExprId,
    user: ExprId,
) !?ExprId {
    var support = AcuiSupport.Context.init(allocator, theorem, env, registry);
    const acui = try support.sharedStructuralCombiner(raw, user) orelse {
        return null;
    };

    var user_items = std.ArrayListUnmanaged(ExprId){};
    defer user_items.deinit(allocator);
    try support.collectConcreteSetItems(user, acui, &user_items);
    if (user_items.items.len > max_acui_fold_items) return null;

    var raw_items = std.ArrayListUnmanaged(AcuiSupport.LeafInfo){};
    defer raw_items.deinit(allocator);
    try support.collectLeafInfos(raw, acui.head_term_id, &raw_items);
    if (raw_items.items.len > max_acui_fold_items) return null;

    for (raw_items.items) |raw_leaf| {
        for (user_items.items) |user_item| {
            if (raw_leaf.expr_id == user_item) continue;
            if (!isDefinitionApp(env, theorem, user_item)) continue;
            if (!try Inference.canConvertTransparent(
                allocator,
                theorem,
                env,
                user_item,
                raw_leaf.expr_id,
            )) continue;
            var replaced = false;
            return try replaceFirstAcuiLeaf(
                allocator,
                theorem,
                raw,
                acui.head_term_id,
                raw_leaf.expr_id,
                user_item,
                &replaced,
            );
        }
    }
    return null;
}

fn replaceFirstAcuiLeaf(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    expr: ExprId,
    head_term_id: u32,
    old_leaf: ExprId,
    new_leaf: ExprId,
    replaced: *bool,
) !ExprId {
    if (!replaced.* and expr == old_leaf) {
        replaced.* = true;
        return new_leaf;
    }
    const node = theorem.interner.node(expr);
    if (node.* != .app) return expr;
    const app = node.app;
    if (app.term_id != head_term_id or app.args.len != 2) return expr;

    var new_args = try allocator.dupe(ExprId, app.args);
    defer allocator.free(new_args);
    new_args[0] = try replaceFirstAcuiLeaf(
        allocator,
        theorem,
        app.args[0],
        head_term_id,
        old_leaf,
        new_leaf,
        replaced,
    );
    new_args[1] = try replaceFirstAcuiLeaf(
        allocator,
        theorem,
        app.args[1],
        head_term_id,
        old_leaf,
        new_leaf,
        replaced,
    );
    if (!replaced.*) return expr;
    return try theorem.interner.internApp(app.term_id, new_args);
}

fn isDefinitionApp(
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    expr: ExprId,
) bool {
    const node = theorem.interner.node(expr);
    const app = switch (node.*) {
        .app => |value| value,
        .variable, .placeholder => return false,
    };
    if (app.term_id >= env.terms.items.len) return false;
    return env.terms.items[app.term_id].is_def;
}

pub fn tryBuildConclusionLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    debug: DebugConfig,
    line_expr: ExprId,
    expected_line: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !?usize {
    if (line_expr == expected_line) {
        return try appendRuleLine(
            checked,
            allocator,
            line_expr,
            rule_id,
            bindings,
            refs,
        );
    }

    if (try Inference.canConvertTransparent(
        allocator,
        theorem,
        env,
        line_expr,
        expected_line,
    )) {
        const raw_idx = try appendRuleLine(
            checked,
            allocator,
            expected_line,
            rule_id,
            bindings,
            refs,
        );
        return try appendTransportLine(
            checked,
            allocator,
            line_expr,
            expected_line,
            .{ .line = raw_idx },
        );
    }

    const folded_mark = checked.items.len;
    const folded = try tryBuildFoldedIntermediateConclusionLine(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        debug,
        line_expr,
        expected_line,
        rule_id,
        bindings,
        refs,
    );
    if (folded) |line_idx| return line_idx;
    CheckedIr.rollbackToMark(allocator, checked, folded_mark);

    // Conclusion normalization is a validation fallback.  If the normalizer
    // proves the user's assertion equivalent to the raw conclusion, emit the
    // required proof-producing transport.
    const normalized_mark = checked.items.len;
    if (try Normalize.buildNormalizedConversionWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        expected_line,
        line_expr,
        debug,
    )) |conversion| {
        var conversion_mut = conversion;
        const raw_idx = try appendRuleLine(
            checked,
            allocator,
            expected_line,
            rule_id,
            bindings,
            refs,
        );

        return if (conversion_mut.conv_line_idx) |conv_idx|
            try conversion_mut.normalizer.emitTransport(
                conversion_mut.relation,
                line_expr,
                expected_line,
                conv_idx,
                .{ .line = raw_idx },
            )
        else
            raw_idx;
    }
    CheckedIr.rollbackToMark(allocator, checked, normalized_mark);

    const transparent_normalized_mark = checked.items.len;
    const converted = try Normalize.buildTransparentNormalizedConclusionLineWithDebug(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        line_expr,
        expected_line,
        rule_id,
        bindings,
        refs,
        debug,
    );
    if (converted == null) {
        CheckedIr.rollbackToMark(
            allocator,
            checked,
            transparent_normalized_mark,
        );
    }
    return converted;
}
