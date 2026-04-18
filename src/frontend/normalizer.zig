const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation =
    @import("./rewrite_registry.zig").ResolvedRelation;
const DiagScratch = @import("./diag_scratch.zig");
const DebugConfig = @import("./debug.zig").DebugConfig;
const CheckedLine = @import("./compiler/checked_ir.zig").CheckedLine;
const CheckedRef = @import("./compiler/checked_ir.zig").CheckedRef;
const Types = @import("./normalizer/types.zig");
const Support = @import("./normalizer/support.zig");
const Core = @import("./normalizer/core.zig");
const CommonTarget = @import("./normalizer/common_target.zig");
const ProofEmit = @import("./normalizer/proof_emit.zig");

pub const NormalizeResult = Types.NormalizeResult;
pub const CommonTargetResult = Types.CommonTargetResult;

pub const Normalizer = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    lines: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: ?*DiagScratch.Scratch,
    debug: DebugConfig = .none,
    cache: std.AutoHashMap(ExprId, NormalizeResult),
    step_count: usize = 0,
    step_limit: usize = 1000,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        env: *const GlobalEnv,
        lines: *std.ArrayListUnmanaged(CheckedLine),
    ) Normalizer {
        return initWithDebugAndScratch(
            allocator,
            theorem,
            registry,
            env,
            lines,
            null,
            .none,
        );
    }

    pub fn initWithDebug(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        env: *const GlobalEnv,
        lines: *std.ArrayListUnmanaged(CheckedLine),
        debug: DebugConfig,
    ) Normalizer {
        return initWithDebugAndScratch(
            allocator,
            theorem,
            registry,
            env,
            lines,
            null,
            debug,
        );
    }

    pub fn initWithScratch(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        env: *const GlobalEnv,
        lines: *std.ArrayListUnmanaged(CheckedLine),
        diag_scratch: ?*DiagScratch.Scratch,
    ) Normalizer {
        return initWithDebugAndScratch(
            allocator,
            theorem,
            registry,
            env,
            lines,
            diag_scratch,
            .none,
        );
    }

    pub fn initWithDebugAndScratch(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        env: *const GlobalEnv,
        lines: *std.ArrayListUnmanaged(CheckedLine),
        diag_scratch: ?*DiagScratch.Scratch,
        debug: DebugConfig,
    ) Normalizer {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = registry,
            .lines = lines,
            .diag_scratch = diag_scratch,
            .debug = debug,
            .cache = std.AutoHashMap(ExprId, NormalizeResult).init(
                allocator,
            ),
        };
    }

    pub fn normalize(
        self: *Normalizer,
        expr_id: ExprId,
    ) anyerror!NormalizeResult {
        return try Core.normalize(self, expr_id);
    }

    pub fn resolveRelationForExpr(
        self: *Normalizer,
        expr_id: ExprId,
    ) ?ResolvedRelation {
        return Support.resolveRelationForExpr(self, expr_id);
    }

    pub fn buildCommonTarget(
        self: *Normalizer,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?CommonTargetResult {
        return try CommonTarget.buildCommonTarget(self, lhs, rhs);
    }

    pub fn composeTransitivity(
        self: *Normalizer,
        relation: ResolvedRelation,
        original: ExprId,
        mid: ExprId,
        final: ExprId,
        first_proof: ?usize,
        second_proof: ?usize,
    ) anyerror!?usize {
        return try ProofEmit.composeTransitivity(
            self,
            relation,
            original,
            mid,
            final,
            first_proof,
            second_proof,
        );
    }

    pub fn emitTransport(
        self: *Normalizer,
        relation: ResolvedRelation,
        target_expr: ExprId,
        source_expr: ExprId,
        conv_line_idx: usize,
        source_line: CheckedRef,
    ) anyerror!usize {
        return try ProofEmit.emitTransport(
            self,
            relation,
            target_expr,
            source_expr,
            conv_line_idx,
            source_line,
        );
    }

    pub fn emitSymm(
        self: *Normalizer,
        relation: ResolvedRelation,
        a: ExprId,
        b: ExprId,
        proof_line_idx: usize,
    ) anyerror!usize {
        return try ProofEmit.emitSymm(
            self,
            relation,
            a,
            b,
            proof_line_idx,
        );
    }
};
