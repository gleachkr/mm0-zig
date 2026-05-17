const std = @import("std");
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const Metadata = @import("../metadata.zig");
const Expr = @import("../../../trusted/expressions.zig").Expr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const SortStmt = @import("../../parse_recovery.zig").SortStmt;
const TermStmt = @import("../../parse_recovery.zig").TermStmt;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("../../parse_recovery.zig").MM0Stmt;
const ProofScript = @import("../../proof_script.zig");
const ProofScriptParser = ProofScript.Parser;
const TheoremBlock = ProofScript.TheoremBlock;
const DefItem = ProofScript.DefItem;
const TopLevelItem = ProofScript.TopLevelItem;
const Span = ProofScript.Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const Check = @import("../check.zig");
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerVars = @import("../vars.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CompilerLints = @import("../lints.zig");
const Recovery = @import("recovery.zig");
const Common = @import("common.zig");

const Diagnostic = CompilerDiag.Diagnostic;
const FreshDecl = Metadata.FreshDecl;
const FreshenDecl = Metadata.FreshenDecl;
const ViewDecl = Metadata.ViewDecl;
const SortVarRegistry = CompilerVars.SortVarRegistry;
const WarningSnapshot = Recovery.WarningSnapshot;
const TermRecoverySnapshot = Recovery.TermRecoverySnapshot;
const AssertionRecoverySnapshot = Recovery.AssertionRecoverySnapshot;
const ProofItemStream = Common.ProofItemStream;
const addAssertionToEnv = Common.addAssertionToEnv;
const anchorMatches = Common.anchorMatches;
const isLocalProofItem = Common.isLocalProofItem;
const processAssertion = Common.processAssertion;
const processLocalDefItem = Common.processLocalDefItem;
const processLocalProofBlock = Common.processLocalProofBlock;
const proofMathTextSpan = Common.proofMathTextSpan;
const publicDefBodyParseDiagnostic = Common.publicDefBodyParseDiagnostic;
const validateDefinitionBody = Common.validateDefinitionBody;

const FilledPublicDef = Common.FilledPublicDef;
const DependencyStatus = enum {
    ok,
    blocked,
};
const InvalidRuleSet = std.StringHashMap(void);

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
    const sort_vars_snapshot = try Recovery.cloneSortVarRegistry(
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
