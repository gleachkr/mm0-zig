# Proof holes

Holes let an Aufbau proof line omit a subexpression that the compiler can
recover from the cited rule, refs, and surrounding context. They are a
frontend elaboration aid: the trusted MMB verifier never sees a hole, and
neither does the checked theorem IR. Successful elaboration always emits an
ordinary fully-concrete proof.

## Mental model

A hole is a placeholder for **one concrete theorem-local subexpression**.
The user writes a registered token in place of that subtree, and the
compiler fills it from whatever the selected rule application produces.

```mm0
--| @hole _wff
provable sort wff;
axiom and_elim (a b: wff): $ a ∧ b $ > $ b $;

theorem t (p r s: wff): $ p ∧ (r ∨ s) $ > $ r ∨ s $;
```

```proof
t
-

l1: $ _wff $ by and_elim [#1]
```

The user writes `_wff` in place of `r ∨ s`. After matching `and_elim`
against the cited reference `p ∧ (r ∨ s)`, the compiler binds `b` to
`r ∨ s`, instantiates the conclusion, and fills `_wff` from that concrete
subtree.

The same idea covers more interesting cases:

- a witness that `@view` / `@recover` / `@abstract` extract from a
  normalized rule shape;
- a context expression (`_ctx`) on every line of a natural-deduction
  derivation, so the user does not have to retype the context;
- ordered fallback rule chains, where the first candidate to fully
  succeed is the one that fills the holes.

Holes are intentionally *not* a proof-search facility. Each hole is
filled by exactly one rule application, by reading the concrete
subtree that the application's binders force into that position.

---

## `@hole`

Holes are opt-in per sort. Attach a `@hole` annotation to a sort
declaration with exactly one raw math token after the tag:

```mm0
--| @hole _wff
provable sort wff;

--| @hole _ctx
sort ctx;
```

The token is any single raw math token that does not collide with
existing syntax. It does not have to be derived from the sort name —
`?` would be valid if it is otherwise unused.

A sort without `@hole` does not have a hole token. `_wff` and `_ctx`
remain ordinary math tokens unless explicitly registered.

### Validity rules

- exactly one token follows `@hole` (errors: `InvalidHoleAnnotation`);
- at most one `@hole` per sort (`DuplicateHoleAnnotation`);
- the token must not already be claimed by another sort
  (`DuplicateHoleToken`);
- the token must not collide with a `@vars` token, term name,
  notation token, or formula marker (`HoleTokenNameCollision`).

### Anonymous identity

Each occurrence of a hole token is a **fresh, independent hole**. So:

```proof
$ _wff -> _wff $
```

is two holes, not one shared hole. There is no way to write a named
or shared hole in v1.

---

## Where holes may appear

### Allowed

- proof-line assertions in `.auf` files;
- ordinary expression positions, including subexpressions under an
  object-language binder (e.g. `sb a x _wff`);
- whole-context positions on sorts that have ACUI metadata
  (e.g. `_ctx ⊢ A`).

### Rejected

- inside `.mm0` source — holes are a proof-side feature only;
- in bound-variable positions of a binder (e.g. `sb a _wff x` where
  the second argument is a bound variable);
- in refs (only the assertion may contain holes);
- in explicit binding formulas like `(name := $ _wff $)`.

A line whose holes can be filled in more than one consistent way is
rejected as ambiguous, with one exception for ACUI contexts described
below.

---

## Elaboration

### Parse once, fill late

A holey assertion is parsed once into a surface `Expr` tree (the trusted
parser exposes a hole-aware entry point that admits registered hole
tokens). Hole identity belongs to the user's line, not to any one
candidate rule, so the same parsed surface expression is shared across
the entire `@fallback` chain.

The theorem-local interner stays concrete-only: a holey surface
expression is never lowered into the theorem DAG until every hole has
been filled. As a result, the checked IR and MMB emitter remain unchanged.

### Hole-free fast path is preserved

If the parsed assertion has no holes, the compiler keeps using the
existing pipeline unchanged — including strict unify replay where it
already applies. Hole-aware machinery activates only when the assertion
actually contains a hole.

### Candidate-local fill

For a holey line, every candidate (the named rule plus any
`@fallback` rules) goes through this loop:

1. match the candidate's hypotheses against the cited refs;
2. match the visible (non-hole) structure of the user's assertion
   against the candidate's conclusion template, using `@view`,
   `@recover`, `@abstract`, and `@normalize` exactly as for an
   ordinary line;
3. instantiate the candidate's concrete conclusion;
4. compare that concrete conclusion against the holey surface
   assertion: every visible position must match (exactly or via
   transparent-def conversion); each hole position records the
   concrete subtree it covers;
5. each hole's recorded sort must match the concrete subtree's sort
   (`HoleSortMismatch`);
6. if any hole is unresolved or any constraint disagrees, reject
   the candidate.

The first candidate that fully succeeds wins. Its concrete conclusion
is what the rest of the checked-line pipeline sees, and holes are
gone from that point on.

### Diagnostics surface for failed lines

When no candidate succeeds, the compiler raises one of:

- `HoleyInferenceMismatch` — the visible structure of the line
  could not be reconciled with any candidate's conclusion or
  hypotheses;
- `HoleConclusionMismatch` — visible structure agreed, but the
  candidate's instantiated conclusion does not actually fit the
  holey assertion;
- a hole-specific failure such as `HoleSortMismatch`, recovered with
  enough span information to point at the offending hole token.

`@fallback` diagnostics still walk every candidate, so a failure
report includes which rule was attempted and where filling failed.

---

## Interaction with view/recover/abstract

Holes do not change how `@view`, `@recover`, or `@abstract` work; they
just give the matcher fewer concrete starting positions. The user's
visible structure still drives the view match, the cited refs still
provide concrete witness data, and derived bindings still consume the
resolved view state.

The new piece is that some surface positions are deferred. When the
candidate's concrete conclusion is finally instantiated, the holes are
filled from whatever subtree sits at each hole position — including
witnesses that `@recover` extracted from refs or that `@abstract` rebuilt
as a one-hole context.

Worked example with `@recover`:

```mm0
--| @hole _obj
sort obj;

term rel (a: obj): wff;
term all {x: obj} (p: wff x): wff;
prefix all: $A.$ prec 41;

def hidden_rel {.a: obj}: wff = $ A. a (rel a) $;
axiom hidden_rel_ax: $ hidden_rel $;

--| @view {x: obj} (t: obj) (p: wff x) (q: wff): $ A. x p $ > $ q $
--| @recover t q p x
axiom pick_hidden (t: obj) (q: wff):
  $ hidden_rel $ > $ q $;
```

```proof
l1: $ rel _obj $ by pick_hidden (q := $ rel u $) [#1]
```

`@view`/`@recover` recover `t = u` from the explicit binding for `q`
and the hidden body of `hidden_rel`. The hole `_obj` is then filled
from the resulting concrete conclusion `rel u`.

---

## Interaction with `@normalize`

Holey surface expressions are **not** normalized directly. The compiler
still normalizes the candidate's instantiated conclusion (and any
`@normalize`-marked hypotheses) as it does for hole-free lines. The
holey assertion is then compared against the normalized concrete result.

If the visible, non-hole part of the assertion is already in the form the
user wants to write, but a hole covers a normalized position such as an
ACUI context, the compiler may fill the hole from the raw candidate and
then let the ordinary normalized conclusion check validate the filled
line. This keeps the normalized proof line user-shaped while still
requiring the final checked line to be a concrete, verifier-justified
rule application.

This avoids inventing rewrite semantics for `.hole`, and it lines up
with user intent: a hole means "fill whatever subtree belongs here
once the rule has been elaborated", not "normalize a placeholder".

---

## Interaction with ACUI contexts

Context holes such as `_ctx` are especially convenient for
natural-deduction-style systems where the context combiner is annotated
with `@acui`. Each line can omit the context entirely:

```proof
l1: $ _ctx ==> _ctx $ by pair_cut [#1, #2]
l2: $ _ctx ==> a , b $ by discharge [#1]
```

ACUI matching can sometimes admit more than one valid context
binding — for example, both `g = ∅` and `g = P` may satisfy
`g ⊢ P → Q` when the cited ref is `P ⊢ Q`. The compiler does not
treat that as ambiguity. Instead the matcher applies a preference
order to the *rule binder* before filling the hole:

1. prefer a subset-minimal residual context;
2. break ties by smaller canonical context size;
3. if multiple equally preferred fills remain, pick the first stable
   solver result and emit an ambiguity warning.

So `_ctx` ordinarily resolves to the discharged context the user
expects (e.g. `∅` for `imp_intro`), and an explicit user-written
binder can still override the chosen residual.

This preserves the principle that holes do not introduce new ACUI
search beyond what the matcher already does for the rule itself.

---

## Interaction with `@fallback`

Holey lines respect declared fallback order. The compiler:

- tries the named rule first, with hole filling as part of "did this
  candidate fully succeed";
- on failure rolls back and tries each fallback in turn;
- accepts the first candidate whose elaboration succeeds end-to-end,
  including hole filling.

There is no separate "best candidate" search. Fallback order matters
more for holey lines than for hole-free lines, which is the right
semantics for ordered rule families such as

```text
$ Δ , q ⊢ p $ > $ Δ ⊢ q → p $
$ Δ ⊢ p $     > $ Δ ⊢ q → p $
```

where the first rule should always win when it applies and the second
should fill the holes only when the first cannot.

---

## Interaction with `@fresh` and hidden witnesses

A hole is not an existential theorem variable. The compiler does **not**
allocate a fresh theorem-local dummy merely because a hole is present.
When holey matching has produced enough information to instantiate a
candidate, hidden-witness finalization uses the same dependency-aware
`@vars`-pool path used by ordinary advanced inference.

For a holey line, freshness is computed from the visible surface
assertion, the cited refs, explicit bindings, and any concrete data
collected during matching. The holes themselves do not contribute dummy
variables or dependencies.

If a hidden witness escape genuinely needs a theorem-local variable,
that allocation goes through the same `@vars`-pool path used by
`@fresh` and view escape. Holes never silently turn into fresh vars.

---

## What never sees a hole

The trust boundary holds:

- the theorem-local DAG is concrete; only the surface `Expr` carries
  `.hole`;
- `compiler/checked_ir.zig` and `compiler/emit.zig` reject any leftover
  surface placeholder, so a bug that lets a hole survive surfaces as a
  loud frontend error rather than as suspect MMB output;
- the trusted MMB verifier and MM0/MMB cross-checker are unchanged.

Holes are an elaboration aid that disappears at the boundary between
checked IR and proof emission.

---

## Limits and non-goals

This is the v1 surface. The following are deliberately out of scope:

- holes in `.mm0` source;
- a generic untyped `_`;
- holes in bound-variable positions or in explicit binding formulas;
- named or shared holes;
- proof search beyond existing inference, view, normalization, and
  fallback machinery;
- theorem-local dummy creation triggered by a hole.

These restrictions keep holes a local, line-scoped elaboration step
that fits the existing frontend without changing trusted proof
emission.
