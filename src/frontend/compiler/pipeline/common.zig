const std = @import("std");
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const MmbWriter = @import("../../mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const Metadata = @import("../metadata.zig");
const Sort = @import("../../../trusted/sorts.zig").Sort;
const Expr = @import("../../../trusted/expressions.zig").Expr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const SortStmt = @import("../../parse_recovery.zig").SortStmt;
const TermStmt = @import("../../parse_recovery.zig").TermStmt;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("../../parse_recovery.zig").MM0Stmt;
const MathSpan = @import("../../parse_recovery.zig").MathSpan;
const PublicStmtHeader = @import("../../parse_recovery.zig").PublicStmtHeader;
const ProofScript = @import("../../proof_script.zig");
const ProofScriptParser = ProofScript.Parser;
const TheoremBlock = ProofScript.TheoremBlock;
const DefItem = ProofScript.DefItem;
const TopLevelItem = ProofScript.TopLevelItem;
const Span = ProofScript.Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const BindingValidation = @import("../../binding_validation.zig");
const CompilerEmit = @import("../emit.zig");
const Check = @import("../check.zig");
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerVars = @import("../vars.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CompilerLints = @import("../lints.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticSource = CompilerDiag.DiagnosticSource;

const ViewDecl = Metadata.ViewDecl;
const FreshDecl = Metadata.FreshDecl;
const FreshenDecl = Metadata.FreshenDecl;
const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const Output = struct {
    sort_names: std.ArrayListUnmanaged([]const u8) = .{},
    sorts: std.ArrayListUnmanaged(Sort) = .{},
    terms: std.ArrayListUnmanaged(TermRecord) = .{},
    theorems: std.ArrayListUnmanaged(TheoremRecord) = .{},
    statements: std.ArrayListUnmanaged(Statement) = .{},
};

pub const ProofItemStream = struct {
    allocator: std.mem.Allocator,
    parser: ProofScriptParser,
    pending: std.ArrayListUnmanaged(TopLevelItem) = .{},

    pub fn init(allocator: std.mem.Allocator, source: []const u8) ProofItemStream {
        return .{
            .allocator = allocator,
            .parser = ProofScriptParser.init(allocator, source),
        };
    }

    pub fn next(self: *ProofItemStream) !?TopLevelItem {
        if (self.pending.items.len > 0) {
            return self.pending.pop().?;
        }
        return try self.parser.nextItem();
    }

    pub fn putBack(self: *ProofItemStream, item: TopLevelItem) void {
        self.pending.append(self.allocator, item) catch unreachable;
    }
};

pub fn validateDefinitionBody(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    term_stmt: TermStmt,
    diag_source: DiagnosticSource,
    diag_span: ?Span,
) !void {
    if (!term_stmt.is_def) return;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(parser, term_stmt);

    const body = term_stmt.body orelse return error.ExpectedDefinitionBody;
    const body_expr_id = try theorem.internParsedExpr(body);
    const body_info = try BindingValidation.currentDefExprInfo(
        env,
        &theorem,
        body_expr_id,
    );

    if (!std.mem.eql(u8, body_info.sort_name, term_stmt.ret_sort_name)) {
        var diag = Diagnostic{
            .kind = .invalid_definition_body,
            .err = error.SortMismatch,
            .name = term_stmt.name,
            .source = diag_source,
            .span = diag_span orelse
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            .detail = .{ .definition_body = .{
                .declared_sort_name = term_stmt.ret_sort_name,
                .actual_sort_name = body_info.sort_name,
                .body_deps = body_info.deps,
                .hidden_binder_count = term_stmt.dummy_args.len,
            } },
        };
        CompilerDiag.addNote(
            &diag,
            "the definition body must already have the declared result sort",
            .mm0,
            null,
        );
        self.setDiagnostic(diag);
        return error.SortMismatch;
    }

    if (body_info.deps != 0) {
        var diag = Diagnostic{
            .kind = .invalid_definition_body,
            .err = error.DepViolation,
            .name = term_stmt.name,
            .source = diag_source,
            .span = diag_span orelse
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            .detail = .{ .definition_body = .{
                .declared_sort_name = term_stmt.ret_sort_name,
                .actual_sort_name = body_info.sort_name,
                .body_deps = body_info.deps,
                .hidden_binder_count = term_stmt.dummy_args.len,
            } },
        };
        CompilerDiag.addNote(
            &diag,
            "definition bodies are checked before the def unify stream runs",
            .mm0,
            null,
        );
        CompilerDiag.addNote(
            &diag,
            "the body still depends on one or more hidden binders",
            .mm0,
            null,
        );
        self.setDiagnostic(diag);
        return error.DepViolation;
    }
}

pub const FilledPublicDef = struct {
    stmt: TermStmt,
    body_span: Span,
};

pub fn fillPublicDefBody(
    self: *CompilerContext,
    _: std.mem.Allocator,
    parser: *MM0Parser,
    proof_stream: *?ProofItemStream,
    term_stmt: TermStmt,
) !FilledPublicDef {
    const actual_proofs = if (proof_stream.*) |*proofs|
        proofs
    else {
        self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
            term_stmt.name,
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        ));
        return error.MissingPublicDefBody;
    };

    const item = actual_proofs.next() catch |err| {
        self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
            &actual_proofs.parser,
            term_stmt.name,
            err,
        ));
        return err;
    } orelse {
        self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
            term_stmt.name,
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        ));
        return error.MissingPublicDefBody;
    };

    switch (item) {
        .def => |def| {
            try rejectDefAnnotations(self, def);
            if (!std.mem.eql(u8, def.name, term_stmt.name)) {
                self.setDiagnostic(
                    CompilerDiag.publicDefBodyNameMismatchDiagnostic(
                        term_stmt.name,
                        def.name,
                        def.name_span,
                    ),
                );
                return error.PublicDefBodyNameMismatch;
            }
            if (def.header_tail != null) {
                self.setDiagnostic(
                    CompilerDiag.publicDefBodyHeaderDiagnostic(
                        def.name,
                        def.header_tail_span orelse def.name_span,
                    ),
                );
                return error.PublicDefBodyMustBeHeaderless;
            }
            const body_span = proofMathTextSpan(def.body.span);
            var filled = term_stmt;
            filled.body = parser.parsePublicDefBodyText(
                term_stmt,
                def.body.text,
                body_span,
            ) catch |err| {
                self.setDiagnostic(publicDefBodyParseDiagnostic(
                    parser,
                    def,
                    err,
                ));
                return err;
            };
            return .{ .stmt = filled, .body_span = def.body.span };
        },
        .block => {
            actual_proofs.putBack(item);
            self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
                term_stmt.name,
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            ));
            return error.MissingPublicDefBody;
        },
    }
}

pub fn proofMathTextSpan(span: Span) MathSpan {
    return .{
        .start = @min(span.start + 1, span.end),
        .end = if (span.end > span.start) span.end - 1 else span.end,
    };
}

pub fn publicDefBodyParseDiagnostic(
    parser: *const MM0Parser,
    def: DefItem,
    err: anyerror,
) Diagnostic {
    var diag = Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = def.name,
        .span = CompilerDiag.mathSpanToSpanOpt(parser.diagnosticSpan()) orelse
            def.body.span,
    };
    if (err == error.UnknownMathToken) {
        if (parser.mathError()) |math_err| {
            switch (math_err) {
                .unknown_token => |token| {
                    diag.detail = .{ .unknown_math_token = .{
                        .token = token.text,
                    } };
                },
                else => {},
            }
        }
    }
    return diag;
}

pub fn setExtraProofItemDiagnostic(self: *CompilerContext, item: TopLevelItem) anyerror {
    switch (item) {
        .block => |block| {
            self.setDiagnostic(
                CompilerDiag.extraProofBlockDiagnostic(block.name, block.name_span),
            );
            return error.ExtraProofBlock;
        },
        .def => |def| {
            self.setDiagnostic(
                CompilerDiag.extraProofDefDiagnostic(def.name, def.name_span),
            );
            return error.ExtraProofItem;
        },
    }
}

pub fn drainAnchoredLocalProofItems(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proof_stream: *?ProofItemStream,
    emit: ?*Output,
) !void {
    const proofs = if (proof_stream.*) |*actual| actual else return;
    const header = parser.peekNextPublicStmtHeader() orelse return;

    var locals = std.ArrayListUnmanaged(TopLevelItem){};
    defer locals.deinit(allocator);

    while (true) {
        const item = proofs.next() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proofs.parser,
                header.name,
                err,
            ));
            return err;
        } orelse {
            putBackItems(proofs, locals.items);
            return;
        };

        if (isLocalProofItem(item)) {
            try locals.append(allocator, item);
            continue;
        }

        const matches = locals.items.len > 0 and anchorMatches(header, item);
        if (!matches) {
            proofs.putBack(item);
            putBackItems(proofs, locals.items);
            return;
        }

        proofs.putBack(item);
        for (locals.items) |local| {
            try processLocalProofItem(
                self,
                allocator,
                parser,
                env,
                registry,
                rule_catalog,
                fresh_bindings,
                freshen_bindings,
                views,
                sort_vars,
                local,
                emit,
            );
        }
        return;
    }
}

fn putBackItems(proofs: *ProofItemStream, items: []const TopLevelItem) void {
    var idx = items.len;
    while (idx > 0) {
        idx -= 1;
        proofs.putBack(items[idx]);
    }
}

pub fn isLocalProofItem(item: TopLevelItem) bool {
    return switch (item) {
        .block => |block| block.kind == .lemma,
        .def => |def| def.header_tail != null,
    };
}

pub fn anchorMatches(header: PublicStmtHeader, item: TopLevelItem) bool {
    switch (item) {
        .block => |block| {
            if (block.kind != .theorem) return false;
            if (header.kind != .theorem) return false;
            const name = header.name orelse return false;
            return std.mem.eql(u8, name, block.name);
        },
        .def => |def| {
            if (def.header_tail != null) return false;
            if (header.kind != .def) return false;
            const name = header.name orelse return false;
            return std.mem.eql(u8, name, def.name);
        },
    }
}

pub fn processLocalProofItem(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    item: TopLevelItem,
    emit: ?*Output,
) !void {
    switch (item) {
        .block => |block| try processLocalProofBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            block,
            emit,
        ),
        .def => |def| try processLocalDefItem(
            self,
            allocator,
            parser,
            env,
            def,
            emit,
        ),
    }
}

pub fn processLocalDefItem(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    def: DefItem,
    emit: ?*Output,
) !void {
    try rejectDefAnnotations(self, def);

    const header_tail = def.header_tail orelse {
        self.setDiagnostic(CompilerDiag.unexpectedProofDefDiagnostic(
            def.name,
            def.name_span,
        ));
        return error.UnexpectedProofDefItem;
    };
    const term_stmt = parser.parseLocalDefText(
        def.name,
        .{ .start = def.name_span.start, .end = def.name_span.end },
        header_tail,
        def.body.text,
        proofMathTextSpan(def.body.span),
    ) catch |err| {
        self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
        return err;
    };

    validateDefinitionBody(
        self,
        allocator,
        parser,
        env,
        term_stmt,
        .proof,
        def.body.span,
    ) catch |err| return err;

    if (emit) |out| {
        const term_record = CompilerEmit.compileTermRecord(
            allocator,
            parser,
            term_stmt,
        ) catch |err| {
            self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
            return err;
        };
        try out.terms.append(allocator, term_record);
        const body = CompilerEmit.buildDefProofBody(
            allocator,
            parser,
            term_stmt,
        ) catch |err| {
            self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
            return err;
        };
        try out.statements.append(allocator, .{
            .cmd = .LocalDef,
            .body = body,
        });
    }

    env.addStmt(.{ .term = term_stmt }) catch |err| {
        self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
        return err;
    };

    const term_id = env.term_names.get(term_stmt.name) orelse {
        return error.UnknownTerm;
    };
    try CompilerLints.lintUnusedDefinitionParameters(
        self,
        allocator,
        &env.terms.items[term_id],
        def.name_span,
        .proof,
    );
}

pub fn rejectDefAnnotations(self: *CompilerContext, def: DefItem) !void {
    if (def.annotations.len == 0) return;
    self.setDiagnostic(CompilerDiag.unsupportedProofDefAnnotationDiagnostic(
        def.name,
        def.name_span,
    ));
    return error.UnsupportedProofDefAnnotation;
}

pub fn localDefParseDiagnostic(
    parser: *const MM0Parser,
    def: DefItem,
    err: anyerror,
) Diagnostic {
    var diag = Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = def.name,
        .span = CompilerDiag.mathSpanToSpanOpt(parser.diagnosticSpan()) orelse
            def.name_span,
    };
    if (err == error.UnknownMathToken) {
        if (parser.mathError()) |math_err| {
            switch (math_err) {
                .unknown_token => |token| {
                    diag.detail = .{ .unknown_math_token = .{
                        .token = token.text,
                    } };
                },
                else => {},
            }
        }
    }
    return diag;
}

pub fn processAssertion(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *SortVarRegistry,
    proof_parser: *?ProofItemStream,
    assertion: AssertionStmt,
    emit: ?*Output,
) !void {
    if (assertion.kind != .theorem) {
        return try processNonTheoremAssertion(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            assertion,
            emit,
        );
    }

    if (proof_parser.*) |*proofs| {
        var theorem = TheoremContext.init(allocator);
        defer theorem.deinit();

        try theorem.seedAssertion(assertion);
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
        const block = try nextTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            proofs,
            assertion.name,
            CompilerDiag.mathSpanToSpan(assertion.name_span),
            emit,
        );
        const checked = Check.checkTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            assertion,
            block,
            &theorem,
            theorem_concl,
        ) catch |err| {
            self.setIfMissing(
                CompilerDiag.theoremDiagnostic(
                    assertion.name,
                    block.name_span,
                    .proof,
                    err,
                ),
            );
            return err;
        };
        if (emit) |out| {
            const unify = try CompilerEmit.buildAssertionUnifyStream(
                allocator,
                &theorem,
                theorem_concl,
            );
            const args = try CompilerEmit.buildArgArray(parser, assertion.args);
            const hyp_names = try CompilerEmit.buildHypNames(
                allocator,
                assertion.hyps.len,
            );
            const body = CompilerEmit.buildTheoremProofBody(
                allocator,
                &theorem,
                env,
                checked,
            ) catch |err| {
                self.setIfMissing(
                    CompilerDiag.theoremDiagnostic(
                        assertion.name,
                        block.name_span,
                        .proof,
                        err,
                    ),
                );
                return err;
            };
            try out.theorems.append(allocator, .{
                .args = args,
                .unify = unify,
                .name = assertion.name,
                .var_names = try CompilerEmit.buildTheoremVarNames(
                    allocator,
                    assertion.arg_names,
                    theorem.theorem_dummies.items.len,
                ),
                .hyp_names = hyp_names,
            });
            try out.statements.append(allocator, .{
                .cmd = .Thm,
                .body = body,
            });
        }
    }

    try addAssertionToEnv(
        self,
        env,
        assertion,
        assertion.name,
        CompilerDiag.mathSpanToSpan(assertion.name_span),
        .mm0,
    );
    const rule_id = env.getRuleId(assertion.name) orelse {
        return error.MissingRule;
    };
    try CompilerLints.lintUnusedTheoremParameters(
        self,
        allocator,
        &env.rules.items[rule_id],
        CompilerDiag.mathSpanToSpan(assertion.name_span),
        .mm0,
    );
    try Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        parser.last_annotations,
    );
}

pub fn processNonTheoremAssertion(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    _: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    emit: ?*Output,
) !void {
    if (emit) |out| {
        var theorem = TheoremContext.init(allocator);
        defer theorem.deinit();
        try theorem.seedAssertion(assertion);
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
        const unify = try CompilerEmit.buildAssertionUnifyStream(
            allocator,
            &theorem,
            theorem_concl,
        );
        const args = try CompilerEmit.buildArgArray(parser, assertion.args);
        const hyp_names = try CompilerEmit.buildHypNames(
            allocator,
            assertion.hyps.len,
        );
        const body = try CompilerEmit.buildAxiomProofBody(
            allocator,
            &theorem,
            theorem_concl,
        );
        try out.theorems.append(allocator, .{
            .args = args,
            .unify = unify,
            .name = assertion.name,
            .var_names = try CompilerEmit.buildTheoremVarNames(
                allocator,
                assertion.arg_names,
                theorem.theorem_dummies.items.len,
            ),
            .hyp_names = hyp_names,
        });
        try out.statements.append(allocator, .{
            .cmd = .Axiom,
            .body = body,
        });
    }

    try addAssertionToEnv(
        self,
        env,
        assertion,
        assertion.name,
        CompilerDiag.mathSpanToSpan(assertion.name_span),
        .mm0,
    );
    try Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        parser.last_annotations,
    );
}

pub fn nextTheoremBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proofs: *ProofItemStream,
    theorem_name: []const u8,
    theorem_name_span: Span,
    emit: ?*Output,
) !TheoremBlock {
    while (true) {
        const item = proofs.next() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proofs.parser,
                theorem_name,
                err,
            ));
            return err;
        } orelse {
            self.setDiagnostic(CompilerDiag.missingProofBlockDiagnostic(
                theorem_name,
                theorem_name_span,
            ));
            return error.MissingProofBlock;
        };
        switch (item) {
            .block => |block| {
                if (block.kind == .lemma) {
                    try processLocalProofBlock(
                        self,
                        allocator,
                        parser,
                        env,
                        registry,
                        rule_catalog,
                        fresh_bindings,
                        freshen_bindings,
                        views,
                        sort_vars,
                        block,
                        emit,
                    );
                    continue;
                }
                if (!std.mem.eql(u8, block.name, theorem_name)) {
                    self.setDiagnostic(
                        CompilerDiag.theoremNameMismatchDiagnostic(
                            theorem_name,
                            block.name,
                            block.name_span,
                        ),
                    );
                    return error.TheoremNameMismatch;
                }
                return block;
            },
            .def => |def| {
                self.setDiagnostic(CompilerDiag.unexpectedProofDefDiagnostic(
                    def.name,
                    def.name_span,
                ));
                return error.UnexpectedProofDefItem;
            },
        }
    }
}

pub fn parseLemmaAssertion(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    block: TheoremBlock,
) !AssertionStmt {
    const src = try std.fmt.allocPrint(
        allocator,
        "theorem {s}{s};",
        .{ block.name, block.header_tail },
    );
    return parser.parseAssertionText(src, .theorem, true) catch |err| {
        self.setDiagnostic(CompilerDiag.proofBlockDiagnostic(
            block.name,
            block.header_span,
            err,
        ));
        return err;
    };
}

pub fn processLocalProofBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    block: TheoremBlock,
    emit: ?*Output,
) !void {
    const assertion = try parseLemmaAssertion(self, allocator, parser, block);

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(assertion);
    const theorem_concl = try theorem.internParsedExpr(assertion.concl);

    const checked = Check.checkTheoremBlock(
        self,
        allocator,
        parser,
        env,
        registry,
        rule_catalog,
        fresh_bindings,
        freshen_bindings,
        views,
        sort_vars,
        assertion,
        block,
        &theorem,
        theorem_concl,
    ) catch |err| {
        self.setIfMissing(
            CompilerDiag.theoremDiagnostic(
                assertion.name,
                block.header_span,
                .proof,
                err,
            ),
        );
        return err;
    };

    if (emit) |out| {
        const unify = try CompilerEmit.buildAssertionUnifyStream(
            allocator,
            &theorem,
            theorem_concl,
        );
        const args = try CompilerEmit.buildArgArray(parser, assertion.args);
        const hyp_names = try CompilerEmit.buildHypNames(
            allocator,
            assertion.hyps.len,
        );
        const body = CompilerEmit.buildTheoremProofBody(
            allocator,
            &theorem,
            env,
            checked,
        ) catch |err| {
            self.setIfMissing(
                CompilerDiag.theoremDiagnostic(
                    assertion.name,
                    block.header_span,
                    .proof,
                    err,
                ),
            );
            return err;
        };
        try out.theorems.append(allocator, .{
            .args = args,
            .unify = unify,
            .name = assertion.name,
            .var_names = try CompilerEmit.buildTheoremVarNames(
                allocator,
                assertion.arg_names,
                theorem.theorem_dummies.items.len,
            ),
            .hyp_names = hyp_names,
        });
        try out.statements.append(allocator, .{
            .cmd = .LocalThm,
            .body = body,
        });
    }

    try addAssertionToEnv(
        self,
        env,
        assertion,
        block.name,
        block.name_span,
        .proof,
    );
    const rule_id = env.getRuleId(assertion.name) orelse {
        return error.MissingRule;
    };
    try CompilerLints.lintUnusedTheoremParameters(
        self,
        allocator,
        &env.rules.items[rule_id],
        block.name_span,
        .proof,
    );
    Metadata.processAssertionMetadata(
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        block.annotations,
    ) catch |err| {
        env.removeLastRule(assertion.name);
        self.setIfMissing(
            CompilerDiag.proofBlockDiagnostic(
                block.name,
                block.header_span,
                err,
            ),
        );
        return err;
    };
}

pub fn addAssertionToEnv(
    self: *CompilerContext,
    env: *GlobalEnv,
    assertion: AssertionStmt,
    diag_name: []const u8,
    span: ?Span,
    source: DiagnosticSource,
) !void {
    env.addStmt(.{ .assertion = assertion }) catch |err| {
        if (err == error.DuplicateRuleName) {
            self.setDiagnostic(CompilerDiag.duplicateRuleNameDiagnostic(
                diag_name,
                span,
                source,
            ));
        }
        return err;
    };
}
