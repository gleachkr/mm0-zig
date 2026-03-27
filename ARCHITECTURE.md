# Architecture

This project is a single Zig module, `src/lib.zig`, with several thin
frontends built on top of it:

- native verifier: `mm0-zig`
- native compiler: `mm0-zigc`
- wasm verifier for the web demo
- wasm compiler for the web demo

The important point is that the application logic lives in the shared
library, not in the CLI or wasm entrypoints. The binaries mostly do I/O,
argument handling, and JSON formatting.

## High-level shape

There are three closely related subsystems:

1. MMB parsing
2. MMB verification
3. MM0 + proof-script compilation to MMB

The verifier and compiler are intentionally not separate codebases. The
compiler leans on the verifier's data model and on MMB's operational
model so that generated files are checked by the same machinery we
already trust.

## Directory layout

The shared library is organized into three groups.

### Trusted code: `src/trusted/`

This directory contains code that the verifier depends on to decide
whether an MMB file is valid.

Current trusted files are:

- `args.zig`
- `check.zig`
- `constants.zig`
- `conversion.zig`
- `entry.zig`
- `expressions.zig`
- `headers.zig`
- `heap.zig`
- `hypothesis.zig`
- `mmb.zig`
- `parse.zig`
- `proof.zig`
- `sorts.zig`
- `stack.zig`
- `terms.zig`
- `theorems.zig`
- `uheap.zig`
- `unify_replay.zig`
- `ustack.zig`
- `verifier.zig`

This is the auditable core. Changes here need a high bar.

In particular, shared code is still trusted if the verifier imports it.
`unify_replay.zig` is the main example: it is reused by frontend code,
but it remains trusted because verifier behavior depends on it.

### Untrusted frontend code: `src/frontend/`

This directory contains source-facing logic whose bugs should at worst
produce bad diagnostics, failed compilation, or invalid output that the
verifier rejects.

The current frontend is split by concern rather than by one file per
phase.

Orchestration and theorem checking:

- `compiler.zig`
- `compiler_check.zig`
- `compiler_inference.zig`
- `compiler_normalize.zig`
- `compiler_emit.zig`
- `compiler_diag.zig`
- `debug.zig`

Compiler-side data models:

- `compiler_env.zig`
- `compiler_expr.zig`
- `compiler_rules.zig`
- `compiler_views.zig`
- `compiler_dummies.zig`
- `derived_bindings.zig`

Elaboration engines and shared helpers:

- `def_ops.zig`
- `def_ops/mirror_support.zig`
- `inference_solver.zig`
- `normalizer.zig`
- `canonicalizer.zig`
- `acui_support.zig`
- `rewrite_registry.zig`

Parsing and output:

- `proof_script.zig`
- `mmb_writer.zig`
- `term_annotations.zig`

`term_annotations.zig` is still a placeholder. Term-level annotations are
not implemented yet.

### Wiring: `src/lib.zig` and `src/bin/`

`src/lib.zig` re-exports the shared module API and provides the
`VerificationSession` convenience wrapper.

`src/bin/` contains the native and wasm entrypoints for the compiler and
verifier.

## Trust boundary

The trust boundary is intentionally narrower than the full user-facing
feature set.

### Trusted claim

The trusted core accepts or rejects an MMB file according to the MMB
proof format and verification rules implemented in `src/trusted/`.

When verifying an MM0/MMB pair, the trusted core also checks that the
binary contents match the source declarations and unify streams from the
MM0 file.

### Untrusted layers

The following layers are intentionally outside the kernel trust boundary:

- source proof parsing
- theorem argument inference
- rewrite automation and normalization
- view recovery and derived bindings
- MMB generation from source proofs

These layers are still useful and heavily tested, but they are not part
of the small auditable core.

One practical consequence is that `src/trusted/verifier.zig` still does
not import the checker type directly. The proof-stream entrypoint accepts
any checker object with the expected interface, which keeps the verifier
module boundary simple without changing the trust story.

## Core trusted components

### Trusted MMB parser and verifier

`src/trusted/mmb.zig` parses the binary file structure.

`src/trusted/verifier.zig` executes proof streams and unify streams as a
stack-machine program over arena-allocated expression nodes. This is the
implementation of MMB semantics proper.

A useful way to think about the trusted core is:

- `mmb.zig` checks file layout
- `verifier.zig` checks proof semantics

#### Alignment of loaded MMB bytes

The MMB spec gives alignment guarantees for several binary tables,
including `term`, `thm`, `arg`, and index data. Those guarantees are
properties of offsets within the file format.

The native verifier and file-based integration tests preserve these
properties at load time by allocating the `.mmb` byte buffer with `Arg`
alignment. That lets the parser and verifier recover natural alignment
internally for ordinary file-backed verification.

The public library API still accepts MMB input as `[]const u8`, though,
so callers that bypass those loaders are not forced by the type system
to provide an aligned backing buffer.

If we later want to make this uniform, the right place to do it is at
the file-loading boundary or in a stronger byte-slice API, not by
silently assuming that an arbitrary `[]u8` already has the required base
alignment.

### Trusted MM0 parser

`src/trusted/parse.zig` parses `.mm0` files and also parses math strings
using the notation environment defined by the file.

This parser is reused in several places:

- MM0 / MMB cross-checking
- compiler front-end processing
- theorem-local parsing of proof-line assertions and explicit bindings

The parser produces ordinary expression trees using `Expr` nodes in
`src/trusted/expressions.zig`.

### Trusted MM0 / MMB cross-checker

`src/trusted/check.zig` streams through the MM0 source and ensures that
binary MMB contents match the source declarations: sorts, terms,
assertions, argument metadata, and unify streams.

This split is still important:

- `mmb.zig` and `verifier.zig` check internal MMB validity
- `check.zig` checks that the MMB matches the MM0 source

All of that is now part of the trusted story for pair verification.
`lib.verifyPair` wires these pieces together in one session for
convenience.

## Compiler front end

### Statement-order lockstep

The compiler processes the `.mm0` file and the source proof file in
statement order. It does not build a separate global proof database.
Instead, it streams through declarations, and when it encounters a
statement it either records metadata immediately or, for a theorem,
reads the next proof block and compiles it right away.

That statement-order lockstep model is a major simplifying choice.

`Compiler.check` and `Compiler.compileMmb` share the same theorem-block
checker. One path stops after validation; the other lowers the checked
lines into an MMB proof stream.

### Global declarations

`compiler_env.zig` stores compiler-side declarations for sorts, terms,
and rules.

Terms and rules are stored as binder-indexed templates, not as raw parser
nodes. `compiler_rules.zig` defines `TemplateExpr`, which is the common
shape used by:

- rule hypotheses and conclusions
- def bodies
- view signatures
- rewrite and normalization metadata

This keeps explicit instantiation, inference, view recovery, and rewrite
machinery tied to the same source of truth.

### Theorem-local DAG

`compiler_expr.zig` provides a theorem-local expression interner.

Parsed expressions from proof lines are converted into `ExprId`s in a
local, hash-consed DAG. This matters because MMB equality in important
places is identity-based, not structural.

The surprising consequence is that sharing is not an optimization
detail. It is part of correctness.

If two occurrences are supposed to be the same node for `URef` or
`Refl`, the compiler must preserve that sharing. The theorem-local
interner is the mechanism that makes this possible.

### Proof-script parsing

`proof_script.zig` parses the textual proof format.

A proof line contains:

- a label
- an asserted formula
- a cited rule
- optional explicit named bindings
- references to theorem hypotheses or prior lines

The explicit binding list is optional. If omitted, it means "infer all
binders that can be inferred".

## Theorem checking pipeline

`compiler_check.zig` is the center of theorem-block checking.

For each proof line it does roughly this:

1. parse the asserted expression into the theorem-local DAG
2. resolve the cited rule and referenced hypotheses
3. parse explicit bindings
4. apply dummy annotations and, when relevant, view annotations
5. infer omitted binders if needed
6. instantiate the rule's expected hypotheses and conclusion
7. insert transport or normalization lines when metadata permits a
   non-exact comparison
8. store a `CheckedLine` representation that later emission can lower to
   MMB

The checker does not adopt a general alpha-equivalence policy. Any extra
flexibility is consumed earlier by symbolic matching or is turned into
explicit transport proof lines.

### Checked-line IR and emission boundary

The theorem checker records two kinds of checked lines:

- direct rule applications
- transport lines

A transport line says that the source line proves an expression that can
be converted to the needed target expression. This is the bridge between
frontend elaboration and backend proof emission.

`compiler_emit.zig` later lowers this IR to ordinary MMB commands. It
uses the same theorem-local DAG, so emission is still identity-sensitive.

## Omitted binder inference

### Exact replay fast path

`compiler_inference.zig` still has an exact replay path based on the
trusted unify-stream walker in `unify_replay.zig`.

`InferenceContext` behaves like verifier-style unify replay except for
one deliberate difference: the first encounter with an omitted binder
records its value.

This path is exact. It does not open defs. It is still the default for
ordinary rules that do not request the heavier machinery.

### Advanced rule matching for views and `@normalize`

When a rule has a view or normalization metadata, omitted binder
inference goes through `def_ops.zig` first, not through raw replay.

The key abstraction is `RuleMatchSession`.

A rule-match session can:

- match rule templates against concrete theorem expressions
- look through transparent defs while matching
- keep hidden-dummy witnesses (i.e. witnesses for the "dot variables" that 
  occur in certain definitions) symbolic until the whole match succeeds
- compare normalized forms for rule parts that are explicitly marked by
  `@normalize`

This is the current semantic center for binder-aware, def-aware matching.

#### Match-local symbolic state

All symbolic witness state is match-local.

Internally, `def_ops.zig` uses a `MatchSession` with:

- binder assignments
- symbolic hidden-dummy metadata
- witness maps for materialization
- backtracking snapshots

That state does not live as ambient mutable context on the solver or on
`DefOps.Context`. Each matching problem owns its own witness identity.

#### Binding modes and representatives

A solved binder is not always stored as a bare `ExprId` during matching.

Internally, `def_ops.zig` distinguishes:

- exact bindings
- transparent bindings
- normalized bindings

For semantic bindings, the session keeps both the raw matched expression
and a chosen representative. Representative choice is deterministic and
may use:

- recursive representative rebuilding
- canonicalization via `canonicalizer.zig`
- compression back to a def-headed form when possible

This is what keeps semantically matched binders stable enough to survive
later dependency checks without falling back to post-hoc repair passes.

#### Finalization stays concrete

The symbolic layer is strictly internal.

After a successful rule match, finalization returns an ordinary concrete
`[]const ExprId` binding list. Only after that do the usual sort,
boundness, and dependency checks run.

Nothing symbolic escapes into proof emission or into the trusted kernel.

### Normalized comparison inside a rule match

For `@normalize`-marked hypotheses or conclusions, a rule-match session
can create a mirrored theorem context using `def_ops/mirror_support.zig`.

The mirrored theorem serves one narrow purpose: it lets the frontend
instantiate template placeholders, normalize both sides, and then map the
result back into the original theorem's binding session.

This is not a kernel feature. It is an internal frontend device used only
while solving omitted binders.

### Advanced search solver

`inference_solver.zig` is still the last-resort search engine for hard
cases.

It is mainly responsible for cases where omitted-binder inference needs:

- ACUI remainder reasoning
- branching over multiple template matches
- view-derived bindings
- rewrite/canonicalization guidance beyond the direct rule-match session

The solver keeps branch-local binding arrays plus ACUI interval
constraints, uses `canonicalizer.zig` and `def_ops.zig` as helper
predicates, and then requires a unique concrete solution.

## Definition-aware comparison and conversion

`def_ops.zig` is the main implementation point for transparent defs.

The central design principles here are:

- there is no general frontend API that means "open this def body with no
  target"
- hidden-dummy defs (i.e. defs with "dot variables") are only exposed toward a 
  concrete witness problem

In practice, `def_ops.zig` provides three related services:

- template matching through defs
- witness-directed instantiation of defs toward a concrete expression or
  ACUI item
- conversion planning between expressions that differ only by def
  unfolding and congruent sub-conversions

The conversion planner is proof-oriented rather than equality-oriented.
It does not just answer "are these equivalent?". It builds a tree of
steps that the MMB emitter lowers to ordinary conversion commands such
as:

- `Unfold`
- `Cong`
- `Symm`
- `Refl`
- `Conv`

That keeps transparent unfolding outside the trusted frontend while still
reusing the verifier's native conversion machinery.

## Shared ACUI semantics

`acui_support.zig` owns the non-proof-producing ACUI item semantics shared by:

- `canonicalizer.zig`
- `normalizer.zig`
- parts of omitted-binder inference that need canonical ACUI reasoning

This shared module is important because the project previously had a real
risk of drift between the canonicalizer and the proof-producing
normalizer.

The current shared ACUI model includes:

- exact cancellation of matching items
- deterministic same-side absorption by def-bearing leaves
- support for wrapped leaves by building non-ACUI common targets inside
  those leaves when needed
- ordinary ACUI rebuilding and canonical sorting by `compareExprIds`

The key policy point is that ACUI support may use witness-directed def
instantiation for leaf coverage, but it still does not introduce a global
"open every def" semantics.

## Rewrite metadata, normalization, and transport

`rewrite_registry.zig` parses `--|` annotations and records metadata for:

- relation bundles, keyed by sort
- oriented rewrite rules, indexed by LHS head term
- congruence rules, indexed by head term
- structural ACUI combiner metadata, indexed by head term
- normalization specs for theorem applications

### Canonicalizer

`canonicalizer.zig` computes symbolic canonical forms used by inference
and representative selection. It is non-proof-producing.

Its job is to answer questions like "which concrete representative should
this semantically solved binder keep?", not to emit proof lines.

### Normalizer

`normalizer.zig` is the proof-producing counterpart used during theorem
checking.

It emits ordinary proof lines that justify normalization using:

- rewrite theorems
- structural assoc / comm / unit / idem theorems
- congruence theorems
- reflexivity
- transitivity
- symmetry when a reverse step is needed
- transport when a relation proof must become a proof of a provable
  formula

The recent ACUI fixes matter here:

- wrapped def-bearing leaves can be paired through a non-ACUI common
  target search
- rewritten ACUI children are normalized again before the final exact
  structural pass
- same-side def-bearing detection sees through wrappers such as
  `hyp (...)`

### Checker-facing normalization helpers

`compiler_normalize.zig` is the thin layer between theorem checking and
`normalizer.zig`.

It packages the common checker operations:

- build a normalized conversion between two concrete expressions
- normalize an expected theorem expression and transport an existing ref
  to it
- normalize a rule conclusion and then transport the emitted theorem line
  back to the user-written line

This keeps `compiler_check.zig` smaller and avoids mixing proof
construction details directly into the line checker.

## Views, dummies, and derived bindings

`compiler_views.zig`, `compiler_dummies.zig`, and
`derived_bindings.zig` handle source-level annotations that sit on top of
ordinary theorem application.

Views are stored as their own binder-indexed templates, together with a
map from view binders back to rule binders and any `@recover` or
`@abstract` derived-binding instructions.

This is all frontend elaboration only. Successful elaboration still has
to reduce to an ordinary theorem application plus any needed transport or
normalization proof lines.

## Backend emission

`compiler_emit.zig` lowers checked frontend IR to actual MMB bytes.

Important pieces are:

- `UnifyEmitter` for theorem unify streams
- `ExprProofEmitter` for concrete expression construction
- `TheoremProofEmitter` for theorem proof bodies

Theorem proof emission is recursive over checked-line dependencies.
Transport lines become `Conv` proofs, and the conversion subproof is
recovered from `def_ops.zig` as a concrete plan.

This is the main architectural invariant of the frontend/backend split:

- the frontend may search, normalize, and elaborate
- the backend still emits only ordinary MMB proof commands

## Shared reuse points

### Shared unify-stream walker

`src/trusted/unify_replay.zig` is a small but important abstraction.

It owns only opcode decoding and traversal order for unify streams. The
actual opcode meaning is provided by the context object.

It is used by:

- `verifier.zig` for real MMB unification
- `check.zig` for trusted MM0/MMB cross-checking
- `compiler_inference.zig` for exact omitted-binder replay

This reuse is deliberate. The traversal order is subtle enough that
having multiple handwritten opcode loops would be a maintenance hazard.
Because the verifier depends on it, it remains part of the trusted set.
