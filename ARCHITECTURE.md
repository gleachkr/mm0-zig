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

Current frontend files are:

- `canonicalizer.zig`
- `compiler.zig`
- `compiler_diag.zig`
- `compiler_env.zig`
- `compiler_expr.zig`
- `compiler_rules.zig`
- `compiler_views.zig`
- `compiler_dummies.zig`
- `def_ops.zig`
- `derived_bindings.zig`
- `inference_solver.zig`
- `mmb_writer.zig`
- `normalizer.zig`
- `proof_script.zig`
- `rewrite_registry.zig`
- `term_annotations.zig`

This is where we can iterate more freely.

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
- MMB generation from source proofs

These layers are still useful and heavily tested, but they are not part
of the small auditable core.

One practical consequence is that `src/trusted/verifier.zig` still does
not import the checker type directly. The proof-stream entrypoint accepts
any checker object with the expected interface, which keeps the verifier
module boundary simple without changing the trust story.

## Core components

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

### Untrusted compiler front end

The compiler lives mostly in:

- `src/frontend/compiler.zig`
- `src/frontend/compiler_env.zig`
- `src/frontend/compiler_expr.zig`
- `src/frontend/compiler_rules.zig`
- `src/frontend/def_ops.zig`
- `src/frontend/mmb_writer.zig`
- `src/frontend/normalizer.zig`
- `src/frontend/proof_script.zig`
- `src/frontend/rewrite_registry.zig`
- `src/frontend/term_annotations.zig`

The compiler processes the `.mm0` file and the source proof file in
statement order. It does not build a separate global proof database.
Instead, it streams through declarations, and when it encounters a
statement it either records metadata immediately or, for a theorem,
reads the next proof block and compiles it right away.

That statement-order lockstep model is a major simplifying choice.

`Compiler.check` and `Compiler.compileMmb` share the same theorem-block
checker. One path stops after validation; the other lowers the checked
lines into an MMB proof stream.

## Compiler data flow

### Global declarations

`compiler_env.zig` stores compiler-side declarations for terms and rules.

Rules are stored as binder-indexed templates, not as raw parser trees.
This keeps explicit instantiation, inference, and rewrite automation tied
to the same source of truth.

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

### Explicit checking and inference

`compiler.zig` checks proof lines in two stages:

1. parse and resolve the line assertion, cited rule, and references
2. obtain concrete rule arguments, either from explicit bindings or by
   inference

There are now three matching layers.

1. Fast path: replay the cited rule's unify stream against:
   - the asserted conclusion
   - the referenced hypotheses

   This replay is exact. It does not open defs while recovering omitted
   binders.

2. Def-aware helper paths: `def_ops.zig` still handles theorem-
   application checking after binders are known, direct `@view`
   matching, and conversion planning across def boundaries.

3. Normalization-aware path: use the frontend solver in
   `inference_solver.zig` when omitted binders must be solved modulo
   rewriting, structural ACUI context matching, transparent def opening,
   `@view`, `@recover`, `@abstract`, or `@dummy`.

The fast path is not full unification. It is closer to pattern matching
guided by MMB's unify opcodes.

The def-aware helper paths and the normalization-aware path are still
frontend elaboration only. They use theorem templates plus local search
rather than handwritten rule-specific logic, then return to ordinary
theorem-application checking.

After inference, the compiler still validates each solved argument
against its declared sort and boundness requirements. Dependency checks
remain verifier-side, because they are relative to the cited theorem's
own bound-variable ordering.

### Definition-aware matching and transport

`def_ops.zig` centralizes three related frontend operations:

- opening concrete defs inside theorem-local `ExprId` expressions
- matching templates modulo def unfolding
- planning conversion proofs between expressions that differ only by def
  unfolding plus congruent sub-conversions

This is the main implementation point for transparent def unfolding.
All defs participate when the compiler checks theorem applications,
matches `@view`s, or compares the final proof line against the theorem
conclusion. Strict unify replay for omitted-binder inference is exact;
any remaining def-aware inference lives in the higher-level solver and
view machinery rather than in replay itself.

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

`term_annotations.zig` is currently a no-op placeholder for future
term-level annotations.

Transparent opening is theorem-scoped rather than helper-scoped. Each
`TheoremContext` keeps stable representatives for def-opening work so
the same concrete def application opens consistently everywhere inside a
single theorem. That matters most for hidden-dummy defs, where theorem
matching and final conversion both need to see the same representative.

### Rewrite metadata and normalization

`rewrite_registry.zig` parses `--|` annotations and records five kinds of
metadata:

- relation bundles, keyed by sort
- oriented rewrite rules, indexed by LHS head term
- congruence rules, indexed by head term
- structural ACUI combiner metadata, indexed by head term
- normalization specs for theorem applications

`canonicalizer.zig` computes symbolic canonical forms used by the
inference solver. It can mix ordinary rewrite canonicalization with ACUI
context canonicalization, but it does not open defs on its own.

`normalizer.zig` is the proof-producing counterpart used during theorem
application checking. It emits ordinary proof lines that justify
normalization using:

- rewrite theorems
- structural assoc / comm / unit / idem theorems
- congruence theorems
- reflexivity
- transitivity
- symmetry when hypothesis normalization needs a reverse step
- transport when a relation proof must turn into a proof of a provable
  formula
- ordinary checked proof lines only; def unfolding is handled by the
  dedicated transparent-comparison paths rather than by visible
  normalization itself

Hidden dummy opening now uses an asymmetric policy. The first hidden
dummy stays fresh, while later hidden dummies may reuse compatible
bound theorem vars. Keeping the first binder fresh avoids verifier
DV-condition failures for eliminators like `all_elim`; reusing later
binders preserves user-facing theorem vars when an inner binder survives
into the final formula.

This is the key architectural choice for normalization: the frontend
owns all search and proof assembly, and the backend still emits ordinary
MMB proofs.

## Shared reuse points

### Shared unify-stream walker

`src/trusted/unify_replay.zig` is a small but important abstraction.

It owns only opcode decoding and traversal order for unify streams. The
actual opcode meaning is provided by the context object.

It is used by:

- `verifier.zig` for real MMB unification
- `check.zig` for trusted MM0/MMB cross-checking
- `compiler.zig` for argument inference

This reuse is deliberate. The traversal order is subtle enough that
having multiple handwritten opcode loops would be a maintenance hazard.
Because the verifier depends on it, it remains part of the trusted set.

### Shared expression model, different identity domains

There are two expression representations:

- verifier / cross-checker side: pointer-based `Expr*`
- compiler side: theorem-local interned `ExprId`

These are different representations, but they mirror the same
operational needs. In both cases, identity matters.

One slightly surprising wrinkle is that parser term ids are local to the
parser's declaration order, while MMB term ids are global binary ids.
`check.zig` therefore records a remapping so that unify-stream checks
compare against the real MMB ids.

## Surprising things worth remembering

### 1. Theorem unify hypotheses are replayed in reverse storage order

`UHyp` is easy to misunderstand.

The unify stream for a theorem is emitted as:

- conclusion first
- then repeated `UHyp` markers followed by hypotheses

To make hypotheses replay in source order overall, the encoded
hypotheses are stored in reverse order. Both the compiler and
cross-checker need to consume them from the end.

This is the single most non-obvious control-flow detail in the project.

### 2. Sharing is semantically relevant

MMB uses identity-based checks in places like:

- `URef`
- `Refl`

That means repeated substituted subexpressions must often be represented
by shared nodes, not merely equal trees. The theorem-local interner and
the save/ref emitters exist for this reason.

### 3. Inference still needs concrete arguments for emission

Inference uses a nullable heap prefix for theorem arguments: omitted
bindings start out unknown and are solved on first matching `URef`.

But proof emission still needs an actual expression for every theorem
binder. So a binder that stays unsolved after replay is still an error,
even if it was logically vacuous in the source rule.

### 4. Rewrite, structural normalization, and transparent def opening
###    are frontend elaboration, not new kernel equality rules

Normalized theorem applications are compiled into extra ordinary proof
lines before MMB emission. Transparent def mismatches are compiled into
ordinary MMB conversion steps such as `Unfold`, `Cong`, and `Conv`. The
verifier never sees a special rewrite opcode, structural-matching opcode,
frontend rewrite table, or magical notion of source-level definitional
equality.

### 5. Trusted and untrusted code are intentionally mixed by `lib.zig`

`lib.zig` is a convenience surface, not a trust-boundary marker.

It is expected to re-export both trusted and untrusted modules. The real
boundary is the `src/trusted/` versus `src/frontend/` split.

## Documentation map

The current source proof format is described in `specs/proof.md`.

The current rewrite system and annotation syntax are described in
`docs/rewrite_system.md`.

The `@view`, `@recover`, `@abstract`, and `@dummy` annotations are
described in `docs/view_recover.md`.

Transparent def unfolding is described in `docs/transparent_defs.md`.
The staged migration away from `@abbrev` is tracked in `GUIDE.md`.

## Web demo

The web app is just another frontend over the same library.

For ACUI-aware omitted-binder inference, the frontend solver now treats
concrete structural contexts as canonical sets of items. Explicit ACUI
obligations may reuse the same concrete item, and at most one unbound
remainder binder is solved from accumulated interval constraints of the
form:

- `L ⊆ Γ ⊆ U`

When the binder is otherwise unconstrained, the solver chooses the
minimal principal solution `Γ = L`. That keeps inference stable across
hypothesis reordering and idempotent overlap cases without pushing ACUI
logic into the trusted verifier.

Remainder-sort binders that are already bound from earlier constraints
(e.g. from premise matching) are treated as pre-required concrete items
rather than as remainders. This allows templates like `Γ , Δ` in a
conclusion where both `Γ` and `Δ` were determined by premises, and
templates like `Γ , Π` where `Γ` is solved and `Π` is not reduce to
the single-remainder case.

The wasm entrypoints in `src/bin/compiler/wasm.zig` and
`src/bin/verifier/wasm.zig` expose a tiny allocation API plus one
exported operation each:

- compile MM0 + proof to MMB
- verify MM0 + MMB

The browser UI in `web/` calls both wasm modules and displays
information from the same compiler and verifier paths used by the native
binaries. The shipped fixtures currently include:

- the Hilbert propositional example
- the Hilbert-Russell example
- a natural-deduction proof of excluded middle
- a natural-deduction quantifier/equality demo
- a sequent-calculus proof of Peirce's law
- a sequent-calculus ∀/∃ quantifier demo

## Build and test layout

`build.zig` defines:

- native verifier and compiler
- wasm verifier and compiler
- `web-demo`
- unit tests
- integration tests

The unit tests exercise the source proof compiler directly using
`tests/proof_cases`, including inference, normalization, and
transparent def-unfolding.

That suite also keeps stage-specific regression cases around the old
`@abbrev` behavior so the migration can record which cases now fail,
which still pass through ordinary def transparency, and which still need
follow-up work.

The integration tests use external MM0 examples and then feed the
resulting MM0/MMB pairs back through this verifier.

That feedback loop is one of the main architectural choices in the
project: generated or imported MMB should always be checked by the same
verifier we ship.
