const std = @import("std");

pub const Arg = @import("./args.zig").Arg;
pub const Compiler = @import("./compiler.zig").Compiler;
pub const CompilerEnv = @import("./compiler_env.zig");
pub const CompilerExpr = @import("./compiler_expr.zig");
pub const CompilerRules = @import("./compiler_rules.zig");
pub const MmbWriter = @import("./mmb_writer.zig");
pub const CrossChecker = @import("./check.zig").CrossChecker;
pub const Expr = @import("./expressions.zig").Expr;
pub const Header = @import("./headers.zig").Header;
pub const MAGIC = @import("./headers.zig").MAGIC;
pub const Heap = @import("./heap.zig").Heap;
pub const MM0Parser = @import("./parse.zig").MM0Parser;
pub const Mmb = @import("./mmb.zig").Mmb;
pub const Index = @import("./mmb.zig").Index;
pub const StringList = @import("./mmb.zig").StringList;
pub const Proof = @import("./proof.zig");
pub const ProofScript = @import("./proof_script.zig");
pub const Sort = @import("./sorts.zig").Sort;
pub const Stack = @import("./stack.zig").Stack;
pub const Term = @import("./terms.zig").Term;
pub const Theorem = @import("./theorems.zig").Theorem;
pub const Verifier = @import("./verifier.zig").Verifier;

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
            &session.parsed.index,
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
