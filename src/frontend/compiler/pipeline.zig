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
const AssertionStmt = @import("../../trusted/parse.zig").AssertionStmt;
const SortStmt = @import("../../trusted/parse.zig").SortStmt;
const TermStmt = @import("../../trusted/parse.zig").TermStmt;
const MM0Parser = @import("../../trusted/parse.zig").MM0Parser;
const MM0Stmt = @import("../../trusted/parse.zig").MM0Stmt;
const ProofScriptParser = @import("../proof_script.zig").Parser;
const TheoremBlock = @import("../proof_script.zig").TheoremBlock;
const Span = @import("../proof_script.zig").Span;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const BindingValidation = @import("../binding_validation.zig");
const CompilerEmit = @import("./emit.zig");
const Check = @import("./check.zig");
const RuleCatalog = @import("./rule_catalog.zig");
const CompilerVars = @import("./vars.zig");
const CompilerDiag = @import("./diag.zig");
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

fn validateDefinitionBody(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    term_stmt: TermStmt,
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
            .span = CompilerDiag.mathSpanToSpan(term_stmt.name_span),
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
            .span = CompilerDiag.mathSpanToSpan(term_stmt.name_span),
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
    self: anytype,
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
    var proof_parser = if (self.proof_source) |proof|
        ProofScriptParser.init(allocator, proof)
    else
        null;
    var last_stmt: ?MM0Stmt = null;

    while (true) {
        const stmt = parser.next() catch |err| {
            self.setDiagnostic(CompilerDiag.mm0ParserDiagnostic(
                &parser,
                err,
            ));
            return err;
        } orelse break;
        last_stmt = stmt;
        CompilerVars.validateSortVarCollisions(&parser, &sort_vars) catch |err| {
            CompilerDiag.setIfMissing(
                self,
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
                    CompilerDiag.setIfMissing(
                        self,
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
                    CompilerDiag.setIfMissing(
                        self,
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
                const term_stmt_copy = term_stmt;
                validateDefinitionBody(
                    self,
                    allocator,
                    &parser,
                    &env,
                    term_stmt,
                ) catch |err| {
                    return err;
                };
                if (emit) |out| {
                    const term_record = CompilerEmit.compileTermRecord(
                        allocator,
                        &parser,
                        term_stmt,
                    ) catch |err| {
                        CompilerDiag.setIfMissing(
                            self,
                            CompilerDiag.mm0StatementDiagnostic(
                                &parser,
                                MM0Stmt{ .term = term_stmt_copy },
                                err,
                            ),
                        );
                        return err;
                    };
                    try out.terms.append(allocator, term_record);
                    const body = if (term_stmt.is_def)
                        CompilerEmit.buildDefProofBody(
                            allocator,
                            &parser,
                            term_stmt,
                        ) catch |err| {
                            CompilerDiag.setIfMissing(
                                self,
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
                env.addStmt(stmt) catch |err| {
                    CompilerDiag.setIfMissing(
                        self,
                        CompilerDiag.mm0StatementDiagnostic(
                            &parser,
                            MM0Stmt{ .term = term_stmt_copy },
                            err,
                        ),
                    );
                    return err;
                };
                if (term_stmt.is_def) {
                    const term_id = env.term_names.get(term_stmt.name) orelse {
                        return error.UnknownTerm;
                    };
                    try CompilerLints.lintUnusedDefinitionParameters(
                        self,
                        allocator,
                        &env.terms.items[term_id],
                        CompilerDiag.mathSpanToSpan(term_stmt.name_span),
                        .mm0,
                    );
                }
                Metadata.processTermMetadata(
                    &env,
                    &registry,
                    term_stmt,
                    parser.last_annotations,
                ) catch |err| {
                    CompilerDiag.setIfMissing(
                        self,
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
                    &proof_parser,
                    assertion,
                    emit,
                ) catch |err| {
                    CompilerDiag.setIfMissing(
                        self,
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
            CompilerDiag.setIfMissing(
                self,
                CompilerDiag.mm0StatementDiagnostic(&parser, stmt, err),
            );
        }
        return err;
    };

    if (proof_parser) |*proofs| {
        const block = proofs.nextBlock() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                proofs,
                null,
                err,
            ));
            return err;
        } orelse return;
        self.setDiagnostic(CompilerDiag.extraProofBlockDiagnostic(
            block.name,
            block.name_span,
        ));
        return error.ExtraProofBlock;
    }
}

const FreshBindingMap = std.AutoHashMap(u32, []const FreshDecl);
const FreshenBindingMap = std.AutoHashMap(u32, []const FreshenDecl);
const ViewMap = std.AutoHashMap(u32, ViewDecl);

const ProofAnalysisState = struct {
    invalid_rules: InvalidRuleSet,
    parser: ProofScriptParser,
    pending_block: ?TheoremBlock = null,
    exhausted: bool = false,
    stream_aborted: bool = false,

    fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) ProofAnalysisState {
        return .{
            .invalid_rules = InvalidRuleSet.init(allocator),
            .parser = ProofScriptParser.init(allocator, source),
        };
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

    fn capture(self: anytype) WarningSnapshot {
        return .{
            .warning_count = self.warning_count,
            .dropped_warning_count = self.dropped_warning_count,
        };
    }

    fn restore(
        self: WarningSnapshot,
        sink: anytype,
    ) void {
        sink.warning_count = self.warning_count;
        sink.dropped_warning_count = self.dropped_warning_count;
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
    self: anytype,
    allocator: std.mem.Allocator,
) !void {
    try analyzeInternal(self, allocator, true);
}

pub fn analyzeMm0(
    self: anytype,
    allocator: std.mem.Allocator,
) !void {
    try analyzeInternal(self, allocator, false);
}

fn analyzeInternal(
    self: anytype,
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

fn analyzeSortStatement(
    self: anytype,
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
    self: anytype,
    allocator: std.mem.Allocator,
    state: *AnalysisState,
    stmt: MM0Stmt,
    term_stmt: TermStmt,
    warnings: WarningSnapshot,
) !void {
    const snapshot = try TermRecoverySnapshot.capture(allocator, state);

    switch (validateTermDependencies(&state.env, term_stmt)) {
        .ok => {},
        .blocked => {
            warnings.restore(self);
            snapshot.restore(state);
            try state.env.appendInvalidTerm(term_stmt.name);
            return;
        },
    }

    state.env.addStmt(stmt) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        try snapshot.discardTerm(&state.env, term_stmt.name);
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
        return;
    };

    if (term_stmt.is_def) {
        const term_id = state.env.term_names.get(term_stmt.name) orelse {
            return error.UnknownTerm;
        };
        try CompilerLints.lintUnusedDefinitionParameters(
            self,
            allocator,
            &state.env.terms.items[term_id],
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            .mm0,
        );
    }

    Metadata.processTermMetadata(
        &state.env,
        &state.registry,
        term_stmt,
        state.parser.last_annotations,
    ) catch |err| {
        warnings.restore(self);
        snapshot.restore(state);
        try snapshot.discardTerm(&state.env, term_stmt.name);
        recordPrimaryStatementFailure(self, &state.parser, stmt, err);
    };
}

fn analyzeAssertionStatement(
    self: anytype,
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

    var no_proof_parser: ?ProofScriptParser = null;
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
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proof: *ProofAnalysisState,
    assertion: AssertionStmt,
) !?TheoremProofResult {
    const theorem_name_span = CompilerDiag.mathSpanToSpan(assertion.name_span);
    if (proof.stream_aborted) {
        return null;
    }
    if (proof.exhausted and proof.pending_block == null) {
        self.addPrimaryDiagnostic(CompilerDiag.missingProofBlockDiagnostic(
            assertion.name,
            theorem_name_span,
        ));
        return null;
    }

    var saw_parse_error = false;
    while (true) {
        const block = takePendingOrNextProofBlock(proof) catch |err| {
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
            if (!proof.parser.recoverToNextBlockBoundary()) {
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
            proof.pending_block = block;
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
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
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
    }
}

fn analyzeExtraProofBlocks(
    self: anytype,
    proof: *ProofAnalysisState,
) !void {
    if (proof.exhausted and proof.pending_block == null) return;

    while (true) {
        const block = takePendingOrNextProofBlock(proof) catch |err| {
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
            if (!proof.parser.recoverToNextBlockBoundary()) {
                return;
            }
            continue;
        } orelse return;
        if (proof.invalid_rules.contains(block.name)) {
            continue;
        }
        self.addPrimaryDiagnostic(CompilerDiag.extraProofBlockDiagnostic(
            block.name,
            block.name_span,
        ));
    }
}

fn takePendingOrNextProofBlock(
    proof: *ProofAnalysisState,
) !?TheoremBlock {
    if (proof.pending_block) |pending| {
        proof.pending_block = null;
        return pending;
    }
    return try proof.parser.nextBlock();
}

fn processAssertion(
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *SortVarRegistry,
    proof_parser: *?ProofScriptParser,
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
            CompilerDiag.setIfMissing(
                self,
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
                CompilerDiag.setIfMissing(
                    self,
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
    self: anytype,
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
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proofs: *ProofScriptParser,
    theorem_name: []const u8,
    theorem_name_span: Span,
    emit: ?*Output,
) !TheoremBlock {
    while (true) {
        const block = proofs.nextBlock() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                proofs,
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
            self.setDiagnostic(CompilerDiag.theoremNameMismatchDiagnostic(
                theorem_name,
                block.name,
                block.name_span,
            ));
            return error.TheoremNameMismatch;
        }
        return block;
    }
}

fn parseLemmaAssertion(
    self: anytype,
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
    self: anytype,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
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
        CompilerDiag.setIfMissing(
            self,
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
            CompilerDiag.setIfMissing(
                self,
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
}

fn addAssertionToEnv(
    self: anytype,
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
    self: anytype,
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
    self: anytype,
    parser: *MM0Parser,
    stmt: MM0Stmt,
    err: anyerror,
) void {
    const diag = self.last_diagnostic orelse
        CompilerDiag.mm0StatementDiagnostic(parser, stmt, err);
    self.last_diagnostic = null;
    self.addPrimaryDiagnostic(diag);
}

fn recordPrimaryProofFailure(
    self: anytype,
    invalid_rules: *const InvalidRuleSet,
    fallback: CompilerDiag.Diagnostic,
) void {
    const diag = self.last_diagnostic orelse fallback;
    self.last_diagnostic = null;
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
    stmt: @import("../../trusted/parse.zig").TermStmt,
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
    args: []const @import("../../trusted/parse.zig").ArgInfo,
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
        .normalize_specs = try cloneAutoHashMapKV(
            u32,
            @import("../rewrite_registry.zig").NormalizeSpec,
            allocator,
            &src.normalize_specs,
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
