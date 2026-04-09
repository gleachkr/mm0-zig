const std = @import("std");

pub const Arg = @import("./trusted/args.zig").Arg;
pub const Compiler = @import("./frontend/compiler.zig").Compiler;
pub const CheckedLine = @import("./frontend/compiler.zig").CheckedLine;
pub const DebugConfig = @import("./frontend/debug.zig").DebugConfig;
pub const DefOpsTests = if (@import("builtin").is_test)
    @import("./frontend/def_ops/tests/root.zig")
else
    struct {};
pub const CompilerDiagnostic = @import("./frontend/compiler.zig").Diagnostic;
pub const compilerDiagnosticSummary =
    @import("./frontend/compiler.zig").diagnosticSummary;
pub const Frontend = struct {
    pub const Env = @import("./frontend/env.zig");
    pub const Expr = @import("./frontend/expr.zig");
    pub const Rules = @import("./frontend/rules.zig");
};

pub const CompilerSupport = struct {
    pub const Inference = @import("./frontend/compiler/inference.zig");
    pub const Vars = @import("./frontend/compiler/vars.zig");
    pub const Views = @import("./frontend/compiler/views.zig");
    pub const Normalize = @import("./frontend/compiler/normalize.zig");
};
pub const DefOps = @import("./frontend/def_ops.zig");
pub const TermAnnotations = @import("./frontend/term_annotations.zig");
pub const Normalizer = @import("./frontend/normalizer.zig");
pub const RewriteRegistry = @import("./frontend/rewrite_registry.zig");
pub const MmbWriter = @import("./frontend/mmb_writer.zig");
pub const CrossChecker = @import("./trusted/check.zig").CrossChecker;
pub const Expr = @import("./trusted/expressions.zig").Expr;
pub const Header = @import("./trusted/headers.zig").Header;
pub const MAGIC = @import("./trusted/headers.zig").MAGIC;
pub const Heap = @import("./trusted/heap.zig").Heap;
pub const MM0Parser = @import("./trusted/parse.zig").MM0Parser;
pub const Mmb = @import("./trusted/mmb.zig").Mmb;
pub const Index = @import("./trusted/mmb.zig").Index;
pub const StringList = @import("./trusted/mmb.zig").StringList;
pub const Proof = @import("./trusted/proof.zig");
pub const ProofScript = @import("./frontend/proof_script.zig");
pub const Sort = @import("./trusted/sorts.zig").Sort;
pub const Stack = @import("./trusted/stack.zig").Stack;
pub const Term = @import("./trusted/terms.zig").Term;
pub const Theorem = @import("./trusted/theorems.zig").Theorem;
pub const Verifier = @import("./trusted/verifier.zig").Verifier;

pub const VerificationSession = struct {
    allocator: std.mem.Allocator,
    parsed: Mmb,
    verifier: *Verifier,
    checker: *CrossChecker,

    pub fn init(
        allocator: std.mem.Allocator,
        mm0_src: []const u8,
        mmb_bytes: []const u8,
    ) !VerificationSession {
        const parsed = try Mmb.parse(allocator, mmb_bytes);
        return try initParsed(allocator, mm0_src, parsed);
    }

    pub fn initParsed(
        allocator: std.mem.Allocator,
        mm0_src: []const u8,
        parsed: Mmb,
    ) !VerificationSession {
        var session = VerificationSession{
            .allocator = allocator,
            .parsed = parsed,
            .verifier = undefined,
            .checker = undefined,
        };

        session.verifier = try Verifier.init(
            allocator,
            session.parsed.file_bytes,
            session.parsed.sort_table,
            session.parsed.term_table,
            session.parsed.theorem_table,
            session.parsed.index,
        );
        errdefer session.verifier.deinit(allocator);

        session.checker = try CrossChecker.init(mm0_src, allocator);
        errdefer session.checker.deinit(allocator);

        return session;
    }

    pub fn deinit(self: *VerificationSession) void {
        self.checker.deinit(self.allocator);
        self.verifier.deinit(self.allocator);
    }

    pub fn verify(self: *VerificationSession) !void {
        try self.verifier.verifyProofStream(
            self.parsed.header.p_proof,
            self.checker,
        );
    }
};

pub fn verifyPair(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    mmb_bytes: []const u8,
) !void {
    var session = try VerificationSession.init(
        allocator,
        mm0_src,
        mmb_bytes,
    );
    defer session.deinit();

    try session.verify();
}
