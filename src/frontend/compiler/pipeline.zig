const std = @import("std");
const GlobalEnv = @import("../env.zig").GlobalEnv;
const TheoremContext = @import("../expr.zig").TheoremContext;
const MmbWriter = @import("../mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const Metadata = @import("./metadata.zig");
const Sort = @import("../../trusted/sorts.zig").Sort;
const Expr = @import("../../trusted/expressions.zig").Expr;
const ArgInfo = @import("../parse_recovery.zig").ArgInfo;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const SortStmt = @import("../parse_recovery.zig").SortStmt;
const TermStmt = @import("../parse_recovery.zig").TermStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("../parse_recovery.zig").MM0Stmt;
const MathSpan = @import("../parse_recovery.zig").MathSpan;
const PublicStmtHeader = @import("../parse_recovery.zig").PublicStmtHeader;
const ProofScript = @import("../proof_script.zig");
const ProofScriptParser = ProofScript.Parser;
const TheoremBlock = ProofScript.TheoremBlock;
const DefItem = ProofScript.DefItem;
const TopLevelItem = ProofScript.TopLevelItem;
const Span = ProofScript.Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const BindingValidation = @import("../binding_validation.zig");
const CompilerEmit = @import("./emit.zig");
const Check = @import("./check.zig");
const RuleCatalog = @import("./rule_catalog.zig");
const CompilerVars = @import("./vars.zig");
const CompilerDiag = @import("./diag.zig");
const CompilerContext = @import("./context.zig").CompilerContext;
const CompilerLints = @import("./lints.zig");
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

const ProofItemStream = struct {
    allocator: std.mem.Allocator,
    parser: ProofScriptParser,
    pending: std.ArrayListUnmanaged(TopLevelItem) = .{},

    fn init(allocator: std.mem.Allocator, source: []const u8) ProofItemStream {
        return .{
            .allocator = allocator,
            .parser = ProofScriptParser.init(allocator, source),
        };
    }

    fn next(self: *ProofItemStream) !?TopLevelItem {
        if (self.pending.items.len > 0) {
            return self.pending.pop().?;
        }
        return try self.parser.nextItem();
    }

    fn putBack(self: *ProofItemStream, item: TopLevelItem) void {
        self.pending.append(self.allocator, item) catch unreachable;
    }
};

fn validateDefinitionBody(
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

const DependencyStatus = enum {
    ok,
    blocked,
};

const InvalidRuleSet = std.StringHashMap(void);

pub fn run(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    emit: ?*Output,
) !void {
    var parser = MM0Parser.init(self.source, allocator);
    var rule_catalog = RuleCatalog.build(allocator, self.source) catch
        RuleCatalog.Catalog.init(allocator);
    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    var fresh_bindings = std.AutoHashMap(u32, []const FreshDecl).init(
        allocator,
    );
    var freshen_bindings = std.AutoHashMap(u32, []const FreshenDecl).init(
        allocator,
    );
    var views = std.AutoHashMap(u32, ViewDecl).init(allocator);
    var sort_vars = SortVarRegistry.init(allocator);
    var proof_stream = if (self.proof_source) |proof|
        ProofItemStream.init(allocator, proof)
    else
        null;
    var last_stmt: ?MM0Stmt = null;

    while (true) {
        parser.prepareNextPublicStatement() catch |err| {
            self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(
                &parser,
                err,
            ));
            return err;
        };
        try drainAnchoredLocalProofItems(
            self,
            allocator,
            &parser,
            &env,
            &registry,
            &rule_catalog,
            &fresh_bindings,
            &freshen_bindings,
            &views,
            &sort_vars,
            &proof_stream,
            emit,
        );

        const stmt = parser.next() catch |err| {
            self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(
                &parser,
                err,
            ));
            return err;
        } orelse break;
        last_stmt = stmt;
        CompilerVars.validateSortVarCollisions(&parser, &sort_vars) catch |err| {
            self.setIfMissing(
                CompilerDiag.mm0StatementDiagnostic(&parser, stmt, err),
            );
            return err;
        };
        switch (stmt) {
            .sort => |sort_stmt| {
                const sort_stmt_copy = sort_stmt;
                if (emit) |out| {
                    try out.sort_names.append(allocator, sort_stmt.name);
                    try out.sorts.append(allocator, sort_stmt.modifiers);
                    try out.statements.append(allocator, .{
                        .cmd = .Sort,
                        .body = &.{},
                    });
                }
                env.addStmt(stmt) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .sort = sort_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
                Metadata.processSortMetadata(
                    &parser,
                    sort_stmt,
                    parser.last_annotations,
                    &sort_vars,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .sort = sort_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
            },
            .term => |term_stmt| {
                var filled_term_stmt = term_stmt;
                var filled_body_span: ?Span = null;
                if (term_stmt.is_def and term_stmt.body == null) {
                    const filled = try fillPublicDefBody(
                        self,
                        allocator,
                        &parser,
                        &proof_stream,
                        term_stmt,
                    );
                    filled_term_stmt = filled.stmt;
                    filled_body_span = filled.body_span;
                }

                const term_stmt_copy = filled_term_stmt;
                const term_diag_source: DiagnosticSource = if (filled_body_span != null)
                    .proof
                else
                    .mm0;
                const term_diag_span = filled_body_span;
                validateDefinitionBody(
                    self,
                    allocator,
                    &parser,
                    &env,
                    filled_term_stmt,
                    term_diag_source,
                    term_diag_span,
                ) catch |err| {
                    return err;
                };
                if (emit) |out| {
                    const term_record = CompilerEmit.compileTermRecord(
                        allocator,
                        &parser,
                        filled_term_stmt,
                    ) catch |err| {
                        self.setIfMissing(
                            CompilerDiag.mm0StatementDiagnostic(
                                &parser,
                                MM0Stmt{ .term = term_stmt_copy },
                                err,
                            ),
                        );
                        return err;
                    };
                    try out.terms.append(allocator, term_record);
                    const body = if (filled_term_stmt.is_def)
                        CompilerEmit.buildDefProofBody(
                            allocator,
                            &parser,
                            filled_term_stmt,
                        ) catch |err| {
                            self.setIfMissing(
                                CompilerDiag.mm0StatementDiagnostic(
                                    &parser,
                                    MM0Stmt{ .term = term_stmt_copy },
                                    err,
                                ),
                            );
                            return err;
                        }
                    else
                        &.{};
                    try out.statements.append(allocator, .{
                        .cmd = .TermDef,
                        .body = body,
                    });
                }
                env.addStmt(.{ .term = filled_term_stmt }) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
                if (filled_term_stmt.is_def) {
                    const term_id = env.term_names.get(
                        filled_term_stmt.name,
                    ) orelse {
                        return error.UnknownTerm;
                    };
                    try CompilerLints.lintUnusedDefinitionParameters(
                        self,
                        allocator,
                        &env.terms.items[term_id],
                        CompilerDiag.mathSpanToSpan(
                            filled_term_stmt.name_span,
                        ),
                        .mm0,
                    );
                }
                Metadata.processTermMetadata(
                    &env,
                    &registry,
                    filled_term_stmt,
                    parser.last_annotations,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
            },
            .assertion => |assertion| {
                processAssertion(
                    self,
                    allocator,
                    &parser,
                    &env,
                    &registry,
                    &rule_catalog,
                    &fresh_bindings,
                    &freshen_bindings,
                    &views,
                    &sort_vars,
                    &proof_stream,
                    assertion,
                    emit,
                ) catch |err| {
                    self.setIfMissing(
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .assertion = assertion },
                            err,
                        ),
                    );
                    return err;
                };
            },
        }
    }

    CompilerVars.validateSortVarCollisions(&parser, &sort_vars) catch |err| {
        if (last_stmt) |stmt| {
            self.setIfMissing(
                CompilerDiag.mm0StatementDiagnostic(&parser, stmt, err),
            );
        }
        return err;
    };

    if (proof_stream) |*proofs| {
        const item = proofs.next() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proofs.parser,
                null,
                err,
            ));
            return err;
        } orelse return;
        return setExtraProofItemDiagnostic(self, item);
    }
}

const FilledPublicDef = struct {
    stmt: TermStmt,
    body_span: Span,
};

fn fillPublicDefBody(
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

fn proofMathTextSpan(span: Span) MathSpan {
    return .{
        .start = @min(span.start + 1, span.end),
        .end = if (span.end > span.start) span.end - 1 else span.end,
    };
}

fn publicDefBodyParseDiagnostic(
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

fn setExtraProofItemDiagnostic(self: *CompilerContext, item: TopLevelItem) anyerror {
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

fn drainAnchoredLocalProofItems(
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

fn isLocalProofItem(item: TopLevelItem) bool {
    return switch (item) {
        .block => |block| block.kind == .lemma,
        .def => |def| def.header_tail != null,
    };
}

fn anchorMatches(header: PublicStmtHeader, item: TopLevelItem) bool {
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

fn processLocalProofItem(
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

fn processLocalDefItem(
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

fn rejectDefAnnotations(self: *CompilerContext, def: DefItem) !void {
    if (def.annotations.len == 0) return;
    self.setDiagnostic(CompilerDiag.unsupportedProofDefAnnotationDiagnostic(
        def.name,
        def.name_span,
    ));
    return error.UnsupportedProofDefAnnotation;
}

fn localDefParseDiagnostic(
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

const FreshBindingMap = std.AutoHashMap(u32, []const FreshDecl);
const FreshenBindingMap = std.AutoHashMap(u32, []const FreshenDecl);
const ViewMap = std.AutoHashMap(u32, ViewDecl);

const ProofAnalysisState = struct {
    allocator: std.mem.Allocator,
    invalid_rules: InvalidRuleSet,
    invalid_terms: InvalidRuleSet,
    parser: ProofScriptParser,
    pending: std.ArrayListUnmanaged(TopLevelItem) = .{},
    exhausted: bool = false,
    stream_aborted: bool = false,

    fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) ProofAnalysisState {
        return .{
            .allocator = allocator,
            .invalid_rules = InvalidRuleSet.init(allocator),
            .invalid_terms = InvalidRuleSet.init(allocator),
            .parser = ProofScriptParser.init(allocator, source),
        };
    }

    fn nextItem(self: *ProofAnalysisState) !?TopLevelItem {
        if (self.pending.items.len > 0) {
            return self.pending.pop().?;
        }
        return try self.parser.nextItem();
    }

    fn putBack(self: *ProofAnalysisState, item: TopLevelItem) void {
        self.pending.append(self.allocator, item) catch unreachable;
    }
};

const AnalysisState = struct {
    parser: MM0Parser,
    rule_catalog: RuleCatalog.Catalog,
    env: GlobalEnv,
    registry: RewriteRegistry,
    fresh_bindings: FreshBindingMap,
    freshen_bindings: FreshenBindingMap,
    views: ViewMap,
    sort_vars: SortVarRegistry,
    invalid_assertions: InvalidRuleSet,
    invalid_terms: InvalidRuleSet,
    proof: ?ProofAnalysisState = null,
    last_stmt: ?MM0Stmt = null,

    fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: ?[]const u8,
        comptime with_proof: bool,
    ) AnalysisState {
        return .{
            .parser = MM0Parser.init(source, allocator),
            .rule_catalog = RuleCatalog.build(allocator, source) catch
                RuleCatalog.Catalog.init(allocator),
            .env = GlobalEnv.init(allocator),
            .registry = RewriteRegistry.init(allocator),
            .fresh_bindings = FreshBindingMap.init(allocator),
            .freshen_bindings = FreshenBindingMap.init(allocator),
            .views = ViewMap.init(allocator),
            .sort_vars = SortVarRegistry.init(allocator),
            .invalid_assertions = InvalidRuleSet.init(allocator),
            .invalid_terms = InvalidRuleSet.init(allocator),
            .proof = if (with_proof)
                if (proof_source) |proof|
                    ProofAnalysisState.init(allocator, proof)
                else
                    null
            else
                null,
        };
    }
};

const WarningSnapshot = struct {
    warning_count: usize,
    dropped_warning_count: usize,

    fn capture(self: *CompilerContext) WarningSnapshot {
        return .{
            .warning_count = self.diagnostics.warning_count,
            .dropped_warning_count = self.diagnostics.dropped_warning_count,
        };
    }

    fn restore(
        self: WarningSnapshot,
        context: *CompilerContext,
    ) void {
        context.diagnostics.warning_count = self.warning_count;
        context.diagnostics.dropped_warning_count =
            self.dropped_warning_count;
    }
};

const TermRecoverySnapshot = struct {
    registry: RewriteRegistry,
    term_count: usize,

    fn capture(
        allocator: std.mem.Allocator,
        state: *const AnalysisState,
    ) !TermRecoverySnapshot {
        return .{
            .registry = try cloneRewriteRegistry(allocator, &state.registry),
            .term_count = state.env.terms.items.len,
        };
    }

    fn restore(
        self: TermRecoverySnapshot,
        state: *AnalysisState,
    ) void {
        state.registry = self.registry;
    }

    fn discardTerm(
        self: TermRecoverySnapshot,
        env: *GlobalEnv,
        name: []const u8,
    ) !void {
        if (env.terms.items.len > self.term_count) {
            env.invalidateLastTerm(name);
        } else {
            try env.appendInvalidTerm(name);
        }
    }
};

const AssertionRecoverySnapshot = struct {
    registry: RewriteRegistry,
    fresh_bindings: FreshBindingMap,
    freshen_bindings: FreshenBindingMap,
    views: ViewMap,
    rule_count: usize,

    fn capture(
        allocator: std.mem.Allocator,
        state: *const AnalysisState,
    ) !AssertionRecoverySnapshot {
        return .{
            .registry = try cloneRewriteRegistry(allocator, &state.registry),
            .fresh_bindings = try cloneAutoHashMap(
                []const FreshDecl,
                allocator,
                &state.fresh_bindings,
            ),
            .freshen_bindings = try cloneAutoHashMap(
                []const FreshenDecl,
                allocator,
                &state.freshen_bindings,
            ),
            .views = try cloneAutoHashMap(
                ViewDecl,
                allocator,
                &state.views,
            ),
            .rule_count = state.env.rules.items.len,
        };
    }

    fn restore(
        self: AssertionRecoverySnapshot,
        state: *AnalysisState,
    ) void {
        state.registry = self.registry;
        state.fresh_bindings = self.fresh_bindings;
        state.freshen_bindings = self.freshen_bindings;
        state.views = self.views;
    }

    fn rollbackRule(
        self: AssertionRecoverySnapshot,
        env: *GlobalEnv,
        name: []const u8,
    ) void {
        env.rollbackRulesToLen(self.rule_count, name);
    }
};

pub fn analyze(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
) !void {
    try analyzeInternal(self, allocator, true);
}

pub fn analyzeMm0(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
) !void {
    try analyzeInternal(self, allocator, false);
}

fn analyzeInternal(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    comptime with_proof: bool,
) !void {
    var state = AnalysisState.init(
        allocator,
        self.source,
        self.proof_source,
        with_proof,
    );

    parse_loop: while (true) {
        state.parser.prepareNextPublicStatement() catch |err| {
            if (!recoverFromMm0ParseFailure(self, &state.parser, err)) {
                return;
            }
            continue :parse_loop;
        };
        if (with_proof) {
            try analyzeDrainAnchoredLocalProofItems(
                self,
                allocator,
                &state,
            );
        }
        const next_stmt = state.parser.next() catch |err| {
            if (!recoverFromMm0ParseFailure(self, &state.parser, err)) {
                return;
            }
            continue :parse_loop;
        };
        const stmt = next_stmt orelse break;
        state.last_stmt = stmt;

        const warnings = WarningSnapshot.capture(self);

        CompilerVars.validateSortVarCollisions(
            &state.parser,
            &state.sort_vars,
        ) catch |err| {
            warnings.restore(self);
            recordPrimaryStatementFailure(self, &state.parser, stmt, err);
            continue;
        };

        switch (stmt) {
            .sort => |sort_stmt| try analyzeSortStatement(
                self,
                allocator,
                &state,
                stmt,
                sort_stmt,
                warnings,
            ),
            .term => |term_stmt| try analyzeTermStatement(
                self,
                allocator,
                &state,
                stmt,
                term_stmt,
                warnings,
            ),
            .assertion => |assertion| try analyzeAssertionStatement(
                self,
                allocator,
                &state,
                stmt,
                assertion,
                warnings,
            ),
        }
    }

    CompilerVars.validateSortVarCollisions(
        &state.parser,
        &state.sort_vars,
    ) catch |err| {
        if (state.last_stmt) |stmt| {
            recordPrimaryStatementFailure(self, &state.parser, stmt, err);
            return;
        }
        self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(&state.parser, err));
        return err;
    };

    if (state.proof) |*proof| {
        try analyzeExtraProofBlocks(self, proof);
    }
}

fn analyzeDrainAnchoredLocalProofItems(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
) !void {
    const proof = if (state.proof) |*actual| actual else return;
    const header = state.parser.peekNextPublicStmtHeader() orelse return;
    if (!analysisProofStreamLooksLocal(proof)) return;

    var locals = std.ArrayListUnmanaged(TopLevelItem){};
    defer locals.deinit(allocator);

    while (true) {
        const item = proof.nextItem() catch |err| {
            self.addPrimaryDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proof.parser,
                header.name,
                err,
            ));
            if (!proof.parser.recoverToNextItemBoundary()) {
                proof.exhausted = true;
                putBackAnalysisItems(proof, locals.items);
                return;
            }
            continue;
        } orelse {
            proof.exhausted = true;
            putBackAnalysisItems(proof, locals.items);
            return;
        };

        if (isLocalProofItem(item)) {
            try locals.append(allocator, item);
            continue;
        }

        const matches = locals.items.len > 0 and anchorMatches(header, item);
        if (!matches) {
            proof.putBack(item);
            putBackAnalysisItems(proof, locals.items);
            return;
        }

        proof.putBack(item);
        for (locals.items) |local| {
            try analyzeLocalProofItem(self, allocator, state, proof, local);
        }
        return;
    }
}

fn analysisProofStreamLooksLocal(proof: *const ProofAnalysisState) bool {
    if (proof.pending.items.len > 0) {
        return isLocalProofItem(proof.pending.items[proof.pending.items.len - 1]);
    }
    return proofNextItemLooksLocal(&proof.parser);
}

fn proofNextItemLooksLocal(parser: *const ProofScriptParser) bool {
    const src = parser.src;
    var pos = parser.pos;
    while (pos < src.len) {
        while (pos < src.len and
            (src[pos] == ' ' or src[pos] == '\t' or src[pos] == '\r' or
                src[pos] == '\n'))
        {
            pos += 1;
        }
        if (pos + 1 < src.len and src[pos] == '-' and src[pos + 1] == '-') {
            while (pos < src.len and src[pos] != '\n') pos += 1;
            continue;
        }
        break;
    }
    const word_start = pos;
    while (pos < src.len and isProofIdentChar(src[pos])) pos += 1;
    const word = src[word_start..pos];
    if (std.mem.eql(u8, word, "lemma")) return true;
    if (!std.mem.eql(u8, word, "def")) return false;

    while (pos < src.len and (src[pos] == ' ' or src[pos] == '\t')) pos += 1;
    while (pos < src.len and isProofIdentChar(src[pos])) pos += 1;
    const tail_start = pos;
    while (pos < src.len and src[pos] != '=' and src[pos] != '\n') pos += 1;
    if (pos >= src.len or src[pos] != '=') return false;
    return std.mem.trim(u8, src[tail_start..pos], " \t\r").len != 0;
}

fn isProofIdentChar(ch: u8) bool {
    return std.ascii.isAlphanumeric(ch) or ch == '_';
}

fn putBackAnalysisItems(
    proof: *ProofAnalysisState,
    items: []const TopLevelItem,
) void {
    var idx = items.len;
    while (idx > 0) {
        idx -= 1;
        proof.putBack(items[idx]);
    }
}

fn analyzeLocalProofItem(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    proof: *ProofAnalysisState,
    item: TopLevelItem,
) !void {
    switch (item) {
        .block => |block| try analyzeLocalProofBlock(
            self,
            allocator,
            state,
            proof,
            block,
        ),
        .def => |def| try analyzeLocalDefItem(
            self,
            allocator,
            state,
            proof,
            def,
        ),
    }
}

fn analyzeLocalProofBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    proof: *ProofAnalysisState,
    block: TheoremBlock,
) !void {
    const warnings = WarningSnapshot.capture(self);
    processLocalProofBlock(
        self,
        allocator,
        &state.parser,
        &state.env,
        &state.registry,
        &state.rule_catalog,
        &state.fresh_bindings,
        &state.freshen_bindings,
        &state.views,
        &state.sort_vars,
        block,
        null,
    ) catch |err| {
        warnings.restore(self);
        recordPrimaryProofFailure(
            self,
            &proof.invalid_rules,
            CompilerDiag.proofBlockDiagnostic(
                block.name,
                block.header_span,
                err,
            ),
        );
        try proof.invalid_rules.put(block.name, {});
        return;
    };
}

fn analyzeLocalDefItem(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    proof: *ProofAnalysisState,
    def: DefItem,
) !void {
    const warnings = WarningSnapshot.capture(self);
    const snapshot = try TermRecoverySnapshot.capture(allocator, state);
    const parser_term_count = state.parser.core.terms.items.len;

    processLocalDefItem(
        self,
        allocator,
        &state.parser,
        &state.env,
        def,
        null,
    ) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        try discardFailedLocalTerm(
            &state.env,
            &state.parser,
            parser_term_count,
            def.name,
        );
        try proof.invalid_terms.put(def.name, {});
        recordPrimaryLocalDefFailure(self, def, err);
        return;
    };
}

fn discardFailedLocalTerm(
    env: *GlobalEnv,
    parser: *const MM0Parser,
    parser_term_count: usize,
    name: []const u8,
) !void {
    if (parser.core.terms.items.len <= parser_term_count) return;
    while (env.terms.items.len + 1 < parser.core.terms.items.len) {
        try env.appendInvalidTerm(name);
    }
    if (env.terms.items.len < parser.core.terms.items.len) {
        try env.appendInvalidTerm(name);
    } else {
        env.invalidateLastTerm(name);
    }
}

fn recordPrimaryLocalDefFailure(
    self: *CompilerContext,
    def: DefItem,
    err: anyerror,
) void {
    const diag = self.getDiagnostic() orelse Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = def.name,
        .span = def.name_span,
    };
    self.restoreDiagnostic(null);
    self.addPrimaryDiagnostic(diag);
}

fn analyzeSortStatement(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    stmt: MM0Stmt,
    sort_stmt: SortStmt,
    warnings: WarningSnapshot,
) !void {
    const sort_vars_snapshot = try cloneSortVarRegistry(
        allocator,
        &state.sort_vars,
    );
    Metadata.processSortMetadata(
        &state.parser,
        sort_stmt,
        state.parser.last_annotations,
        &state.sort_vars,
    ) catch |err| {
        warnings.restore(self);
        state.sort_vars = sort_vars_snapshot;
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
        return;
    };
    state.env.addStmt(stmt) catch |err| {
        warnings.restore(self);
        state.sort_vars = sort_vars_snapshot;
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
    };
}

fn analyzeTermStatement(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    stmt: MM0Stmt,
    term_stmt: TermStmt,
    warnings: WarningSnapshot,
) !void {
    const snapshot = try TermRecoverySnapshot.capture(allocator, state);
    var actual_stmt = term_stmt;
    var proof_body_span: ?Span = null;

    if (term_stmt.is_def and term_stmt.body == null) {
        const filled = try analyzeFillPublicDefBody(self, state, term_stmt);
        if (filled == null) {
            warnings.restore(self);
            snapshot.restore(state);
            try snapshot.discardTerm(&state.env, term_stmt.name);
            try state.invalid_terms.put(term_stmt.name, {});
            recordPrimaryStatementFailure(self, &state.parser, stmt, error.InvalidTerm);
            return;
        }
        actual_stmt = filled.?.stmt;
        proof_body_span = filled.?.body_span;
    }

    switch (validateTermDependencies(&state.env, actual_stmt)) {
        .ok => {},
        .blocked => {
            warnings.restore(self);
            snapshot.restore(state);
            try snapshot.discardTerm(&state.env, actual_stmt.name);
            try state.invalid_terms.put(actual_stmt.name, {});
            return;
        },
    }

    validateDefinitionBody(
        self,
        allocator,
        &state.parser,
        &state.env,
        actual_stmt,
        if (proof_body_span != null) .proof else .mm0,
        proof_body_span,
    ) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        try snapshot.discardTerm(&state.env, actual_stmt.name);
        try state.invalid_terms.put(actual_stmt.name, {});
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
        return;
    };

    state.env.addStmt(.{ .term = actual_stmt }) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        try snapshot.discardTerm(&state.env, actual_stmt.name);
        try state.invalid_terms.put(actual_stmt.name, {});
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
        return;
    };

    if (actual_stmt.is_def) {
        const term_id = state.env.term_names.get(actual_stmt.name) orelse {
            return error.UnknownTerm;
        };
        try CompilerLints.lintUnusedDefinitionParameters(
            self,
            allocator,
            &state.env.terms.items[term_id],
            CompilerDiag.mathSpanToSpan(actual_stmt.name_span),
            .mm0,
        );
    }

    Metadata.processTermMetadata(
        &state.env,
        &state.registry,
        actual_stmt,
        state.parser.last_annotations,
    ) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        try snapshot.discardTerm(&state.env, actual_stmt.name);
        try state.invalid_terms.put(actual_stmt.name, {});
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
    };
}

fn analyzeFillPublicDefBody(
    self: *CompilerContext,
    state: *AnalysisState,
    term_stmt: TermStmt,
) !?FilledPublicDef {
    const proof = if (state.proof) |*actual| actual else {
        self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
            term_stmt.name,
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        ));
        return null;
    };

    const item = proof.nextItem() catch |err| {
        self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
            &proof.parser,
            term_stmt.name,
            err,
        ));
        if (!proof.parser.recoverToNextItemBoundary()) {
            proof.exhausted = true;
        }
        return null;
    } orelse {
        proof.exhausted = true;
        self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
            term_stmt.name,
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        ));
        return null;
    };

    switch (item) {
        .def => |def| {
            if (def.annotations.len != 0) {
                self.setDiagnostic(
                    CompilerDiag.unsupportedProofDefAnnotationDiagnostic(
                        def.name,
                        def.name_span,
                    ),
                );
                return null;
            }
            if (!std.mem.eql(u8, def.name, term_stmt.name)) {
                self.setDiagnostic(
                    CompilerDiag.publicDefBodyNameMismatchDiagnostic(
                        term_stmt.name,
                        def.name,
                        def.name_span,
                    ),
                );
                return null;
            }
            if (def.header_tail != null) {
                self.setDiagnostic(
                    CompilerDiag.publicDefBodyHeaderDiagnostic(
                        def.name,
                        def.header_tail_span orelse def.name_span,
                    ),
                );
                return null;
            }
            const body_span = proofMathTextSpan(def.body.span);
            var filled = term_stmt;
            filled.body = state.parser.parsePublicDefBodyText(
                term_stmt,
                def.body.text,
                body_span,
            ) catch |err| {
                self.setDiagnostic(publicDefBodyParseDiagnostic(
                    &state.parser,
                    def,
                    err,
                ));
                return null;
            };
            return .{ .stmt = filled, .body_span = def.body.span };
        },
        .block => {
            proof.putBack(item);
            self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
                term_stmt.name,
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            ));
            return null;
        },
    }
}

fn analyzeAssertionStatement(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    stmt: MM0Stmt,
    assertion: AssertionStmt,
    warnings: WarningSnapshot,
) !void {
    const snapshot = try AssertionRecoverySnapshot.capture(allocator, state);

    switch (validateAssertionDependencies(&state.env, assertion)) {
        .ok => {},
        .blocked => {
            warnings.restore(self);
            snapshot.restore(state);
            try markAssertionInvalid(state, assertion.name);
            return;
        },
    }

    if (state.proof) |*proof| {
        if (assertion.kind == .theorem) {
            const theorem_result = try analyzeTheoremProof(
                self,
                allocator,
                &state.parser,
                &state.env,
                &state.registry,
                &state.rule_catalog,
                &state.fresh_bindings,
                &state.freshen_bindings,
                &state.views,
                &state.sort_vars,
                proof,
                assertion,
            );
            if (theorem_result == null) {
                try markAssertionInvalid(state, assertion.name);
                return;
            }
            const theorem_warnings = theorem_result.?.warnings;

            addAssertionToEnv(
                self,
                &state.env,
                assertion,
                assertion.name,
                CompilerDiag.mathSpanToSpan(assertion.name_span),
                .mm0,
            ) catch |err| {
                theorem_warnings.restore(self);
                snapshot.restore(state);
                try markAssertionInvalid(state, assertion.name);
                recordPrimaryStatementFailure(
                    self,
                    &state.parser,
                    stmt,
                    err,
                );
                return;
            };

            const rule_id = state.env.getRuleId(assertion.name) orelse {
                return error.MissingRule;
            };
            try CompilerLints.lintUnusedTheoremParameters(
                self,
                allocator,
                &state.env.rules.items[rule_id],
                CompilerDiag.mathSpanToSpan(assertion.name_span),
                .mm0,
            );

            Metadata.processAssertionMetadata(
                allocator,
                &state.parser,
                &state.env,
                &state.registry,
                &state.fresh_bindings,
                &state.freshen_bindings,
                &state.views,
                assertion,
                state.parser.last_annotations,
            ) catch |err| {
                theorem_warnings.restore(self);
                snapshot.restore(state);
                state.env.removeLastRule(assertion.name);
                try markAssertionInvalid(state, assertion.name);
                if (!shouldSuppressAssertionMetadataFailure(
                    err,
                    state.parser.last_annotations,
                    &state.invalid_assertions,
                )) {
                    recordPrimaryStatementFailure(
                        self,
                        &state.parser,
                        stmt,
                        err,
                    );
                }
                return;
            };
            return;
        }
    }

    var no_proof_parser: ?ProofItemStream = null;
    processAssertion(
        self,
        allocator,
        &state.parser,
        &state.env,
        &state.registry,
        &state.rule_catalog,
        &state.fresh_bindings,
        &state.freshen_bindings,
        &state.views,
        &state.sort_vars,
        &no_proof_parser,
        assertion,
        null,
    ) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        snapshot.rollbackRule(&state.env, assertion.name);
        try markAssertionInvalid(state, assertion.name);
        if (!shouldSuppressAssertionMetadataFailure(
            err,
            state.parser.last_annotations,
            &state.invalid_assertions,
        )) {
            recordPrimaryStatementFailure(
                self,
                &state.parser,
                stmt,
                err,
            );
        }
        return;
    };
}

fn markAssertionInvalid(
    state: *AnalysisState,
    name: []const u8,
) !void {
    try state.invalid_assertions.put(name, {});
    if (state.proof) |*proof| {
        try proof.invalid_rules.put(name, {});
    }
}

const TheoremProofResult = struct {
    warnings: WarningSnapshot,
};

fn analyzeTheoremProof(
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
    proof: *ProofAnalysisState,
    assertion: AssertionStmt,
) !?TheoremProofResult {
    const theorem_name_span = CompilerDiag.mathSpanToSpan(assertion.name_span);
    if (proof.stream_aborted) {
        return null;
    }
    if (proof.exhausted and proof.pending.items.len == 0) {
        self.addPrimaryDiagnostic(CompilerDiag.missingProofBlockDiagnostic(
            assertion.name,
            theorem_name_span,
        ));
        return null;
    }

    var saw_parse_error = false;
    while (true) {
        const item = proof.nextItem() catch |err| {
            const suppressed = shouldSuppressProofParseFailure(
                &proof.parser,
                &proof.invalid_rules,
            );
            if (!suppressed) {
                self.addPrimaryDiagnostic(
                    CompilerDiag.proofParserDiagnostic(
                        &proof.parser,
                        assertion.name,
                        err,
                    ),
                );
                saw_parse_error = true;
            }
            if (!proof.parser.recoverToNextItemBoundary()) {
                proof.exhausted = true;
                if (suppressed) {
                    self.addPrimaryDiagnostic(
                        CompilerDiag.missingProofBlockDiagnostic(
                            assertion.name,
                            theorem_name_span,
                        ),
                    );
                } else {
                    proof.stream_aborted = true;
                }
                return null;
            }
            continue;
        } orelse {
            proof.exhausted = true;
            if (saw_parse_error) {
                proof.stream_aborted = true;
            } else {
                self.addPrimaryDiagnostic(
                    CompilerDiag.missingProofBlockDiagnostic(
                        assertion.name,
                        theorem_name_span,
                    ),
                );
            }
            return null;
        };

        switch (item) {
            .def => |def| {
                self.addPrimaryDiagnostic(
                    CompilerDiag.unexpectedProofDefDiagnostic(
                        def.name,
                        def.name_span,
                    ),
                );
                return null;
            },
            .block => |block| {
                if (block.kind == .lemma) {
                    const warnings = WarningSnapshot.capture(self);
                    processLocalProofBlock(
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
                        null,
                    ) catch |err| {
                        warnings.restore(self);
                        recordPrimaryProofFailure(
                            self,
                            &proof.invalid_rules,
                            CompilerDiag.proofBlockDiagnostic(
                                block.name,
                                block.header_span,
                                err,
                            ),
                        );
                        try proof.invalid_rules.put(block.name, {});
                        continue;
                    };
                    continue;
                }

                if (!std.mem.eql(u8, block.name, assertion.name)) {
                    if (proof.invalid_rules.contains(block.name)) {
                        continue;
                    }
                    proof.putBack(item);
                    if (!saw_parse_error) {
                        self.addPrimaryDiagnostic(
                            CompilerDiag.theoremNameMismatchDiagnostic(
                                assertion.name,
                                block.name,
                                block.name_span,
                            ),
                        );
                    }
                    return null;
                }

                const warnings = WarningSnapshot.capture(self);
                var theorem = TheoremContext.init(allocator);
                defer theorem.deinit();

                try theorem.seedAssertion(assertion);
                const theorem_concl = try theorem.internParsedExpr(
                    assertion.concl,
                );
                _ = Check.checkTheoremBlock(
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
                    warnings.restore(self);
                    recordPrimaryProofFailure(
                        self,
                        &proof.invalid_rules,
                        CompilerDiag.theoremDiagnostic(
                            assertion.name,
                            block.name_span,
                            .proof,
                            err,
                        ),
                    );
                    return null;
                };

                return .{
                    .warnings = warnings,
                };
            },
        }
    }
}

fn analyzeExtraProofBlocks(
    self: *CompilerContext,
    proof: *ProofAnalysisState,
) !void {
    if (proof.exhausted and proof.pending.items.len == 0) return;

    while (true) {
        const item = proof.nextItem() catch |err| {
            if (!shouldSuppressProofParseFailure(
                &proof.parser,
                &proof.invalid_rules,
            )) {
                self.addPrimaryDiagnostic(
                    CompilerDiag.proofParserDiagnostic(
                        &proof.parser,
                        null,
                        err,
                    ),
                );
            }
            if (!proof.parser.recoverToNextItemBoundary()) {
                return;
            }
            continue;
        } orelse return;
        switch (item) {
            .block => |block| {
                if (proof.invalid_rules.contains(block.name)) {
                    continue;
                }
                self.addPrimaryDiagnostic(CompilerDiag.extraProofBlockDiagnostic(
                    block.name,
                    block.name_span,
                ));
            },
            .def => |def| {
                if (proof.invalid_terms.contains(def.name)) {
                    continue;
                }
                self.addPrimaryDiagnostic(CompilerDiag.extraProofDefDiagnostic(
                    def.name,
                    def.name_span,
                ));
            },
        }
    }
}

fn processAssertion(
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

fn processNonTheoremAssertion(
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

fn nextTheoremBlock(
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

fn parseLemmaAssertion(
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

fn processLocalProofBlock(
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

fn addAssertionToEnv(
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

fn recoverFromMm0ParseFailure(
    self: *CompilerContext,
    parser: *MM0Parser,
    err: anyerror,
) bool {
    self.addPrimaryDiagnostic(CompilerDiag.mm0ParserDiagnostic(parser, err));
    parser.discardPendingAnnotations();
    parser.recoverToStatementBoundary() catch {
        return false;
    };
    return true;
}

fn recordPrimaryStatementFailure(
    self: *CompilerContext,
    parser: *MM0Parser,
    stmt: MM0Stmt,
    err: anyerror,
) void {
    const diag = self.getDiagnostic() orelse
        CompilerDiag.mm0StatementDiagnostic(parser, stmt, err);
    self.restoreDiagnostic(null);
    self.addPrimaryDiagnostic(diag);
}

fn recordPrimaryProofFailure(
    self: *CompilerContext,
    invalid_rules: *const InvalidRuleSet,
    fallback: CompilerDiag.Diagnostic,
) void {
    const diag = self.getDiagnostic() orelse fallback;
    self.restoreDiagnostic(null);
    if (shouldSuppressProofFailure(diag, invalid_rules)) return;
    self.addPrimaryDiagnostic(diag);
}

fn shouldSuppressProofFailure(
    diag: CompilerDiag.Diagnostic,
    invalid_rules: *const InvalidRuleSet,
) bool {
    switch (diag.err) {
        error.UnknownRule, error.RuleNotYetAvailable => {},
        else => return false,
    }
    const rule_name = diag.rule_name orelse return false;
    return invalid_rules.contains(rule_name);
}

fn shouldSuppressProofParseFailure(
    proofs: *const ProofScriptParser,
    invalid_rules: *const InvalidRuleSet,
) bool {
    const block_name = proofs.diagnosticBlockName() orelse return false;
    return invalid_rules.contains(block_name);
}

fn shouldSuppressAssertionMetadataFailure(
    err: anyerror,
    annotations: []const []const u8,
    invalid_assertions: *const InvalidRuleSet,
) bool {
    if (err != error.UnknownFallbackRule) return false;

    for (annotations) |ann| {
        var iter = std.mem.tokenizeScalar(u8, ann, ' ');
        const directive = iter.next() orelse continue;
        if (!std.mem.eql(u8, directive, "@fallback")) continue;

        const target_name = iter.next() orelse continue;
        if (iter.next() != null) continue;
        if (invalid_assertions.contains(target_name)) return true;
    }
    return false;
}

fn validateTermDependencies(
    env: *const GlobalEnv,
    stmt: TermStmt,
) DependencyStatus {
    if (!validateArgSortsAvailable(env, stmt.args)) return .blocked;
    if (!validateArgSortsAvailable(env, stmt.dummy_args)) return .blocked;
    if (!env.sort_names.contains(stmt.ret_sort_name)) return .blocked;
    const body = stmt.body orelse return .ok;
    if (!validateExprTermsAvailable(env, body)) return .blocked;
    return .ok;
}

fn validateAssertionDependencies(
    env: *const GlobalEnv,
    stmt: AssertionStmt,
) DependencyStatus {
    if (!validateArgSortsAvailable(env, stmt.args)) return .blocked;
    for (stmt.hyps) |hyp| {
        if (!validateExprTermsAvailable(env, hyp)) return .blocked;
    }
    if (!validateExprTermsAvailable(env, stmt.concl)) return .blocked;
    return .ok;
}

fn validateArgSortsAvailable(
    env: *const GlobalEnv,
    args: []const ArgInfo,
) bool {
    for (args) |arg| {
        if (!env.sort_names.contains(arg.sort_name)) return false;
    }
    return true;
}

fn validateExprTermsAvailable(
    env: *const GlobalEnv,
    expr: *const Expr,
) bool {
    switch (expr.*) {
        .variable => return true,
        .term => |term| {
            // Parsed expressions carry parser term ids, not frontend name
            // lookups. In recovery mode a rejected term may still occupy that
            // id as an unavailable placeholder, so we must reject the id here
            // instead of assuming every in-range slot is semantically valid.
            if (!env.hasAvailableTerm(term.id)) {
                return false;
            }
            for (term.args) |arg| {
                if (!validateExprTermsAvailable(env, arg)) return false;
            }
            return true;
        },
        .hole => return false,
    }
}

fn cloneStringHashMap(
    comptime V: type,
    allocator: std.mem.Allocator,
    src: *const std.StringHashMap(V),
) !std.StringHashMap(V) {
    var dst = std.StringHashMap(V).init(allocator);
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

fn cloneAutoHashMap(
    comptime V: type,
    allocator: std.mem.Allocator,
    src: *const std.AutoHashMap(u32, V),
) !std.AutoHashMap(u32, V) {
    var dst = std.AutoHashMap(u32, V).init(allocator);
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

fn cloneAutoHashMapKV(
    comptime K: type,
    comptime V: type,
    allocator: std.mem.Allocator,
    src: *const std.AutoHashMap(K, V),
) !std.AutoHashMap(K, V) {
    var dst = std.AutoHashMap(K, V).init(allocator);
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

fn cloneSortVarRegistry(
    allocator: std.mem.Allocator,
    src: *const SortVarRegistry,
) !SortVarRegistry {
    return .{
        .allocator = allocator,
        .tokens = try cloneStringHashMap(
            CompilerVars.SortVarDecl,
            allocator,
            &src.tokens,
        ),
        .pools = try cloneStringHashMap(
            CompilerVars.SortVarPool,
            allocator,
            &src.pools,
        ),
    };
}

fn cloneRewriteRegistry(
    allocator: std.mem.Allocator,
    src: *const RewriteRegistry,
) !RewriteRegistry {
    return .{
        .allocator = allocator,
        .relations = try cloneStringHashMap(
            @import("../rewrite_registry.zig").RelationBundle,
            allocator,
            &src.relations,
        ),
        .rewrites_by_head = try cloneAutoHashMapKV(
            u32,
            std.ArrayListUnmanaged(
                @import("../rewrite_registry.zig").RewriteRule,
            ),
            allocator,
            &src.rewrites_by_head,
        ),
        .alpha_by_head = try cloneAutoHashMapKV(
            u32,
            std.ArrayListUnmanaged(
                @import("../rewrite_registry.zig").AlphaRule,
            ),
            allocator,
            &src.alpha_by_head,
        ),
        .congr_by_head = try cloneAutoHashMapKV(
            u32,
            @import("../rewrite_registry.zig").CongruenceRule,
            allocator,
            &src.congr_by_head,
        ),
        .fallbacks = try cloneAutoHashMapKV(
            u32,
            u32,
            allocator,
            &src.fallbacks,
        ),
        .acui_by_head = try cloneAutoHashMapKV(
            u32,
            @import("../rewrite_registry.zig").StructuralCombiner,
            allocator,
            &src.acui_by_head,
        ),
    };
}
