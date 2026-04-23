# Rewrite System and Annotation Syntax

The compiler includes a proof-producing rewrite system that automates
normalization of expressions during theorem application. It is entirely a
frontend concern: the verifier and the MMB binary format are unchanged.
Every rewrite step the system takes is compiled down to ordinary theorem
applications that the verifier checks in the usual way.

## Mental model

### Axiom instantiation

Every proof line in the Aufbau script applies a named rule — an axiom
or a previously proved theorem — to produce a new assertion. Before
the rewrite system enters the picture, the compiler needs to determine
the *concrete arguments* to that rule application: what expressions to
substitute for each binder declared by the rule.

There are four mechanisms that can supply these arguments, and they
compose:

1. **Explicit bindings.** The proof line names arguments directly:
   `(x := $ x $, t := $ S zer $, p := $ x = zer $)`. These take precedence
   over everything else.

2. **Unification replay.** If some arguments are omitted, the compiler
   replays the rule's unify stream against the expression the user wrote and
   the expressions they cited as references. This is the standard MM0
   unification mechanism: the compiler walks the rule's conclusion and
   hypotheses in parallel with the user's line and refs, solving for any
   unspecified binders. This path is exact: it does not open defs or do
   rewrite / canonicalization search.

3. **`@view` matching.** A `@view` annotation provides an alternative surface
   shape for the same rule. The compiler matches this alternate shape against
   the user's line and refs in a def-aware rule-match session, then maps the
   solved binders back to the underlying rule's argument list. `@recover` and
   `@abstract` run on that resolved view state and can derive additional
   binders from it. See `docs/view_recover.md` for the details.

4. **`@fresh` annotations.** For omitted bound binders that serve only as
   fresh local variables (no inference can solve them), `@fresh` tells the
   compiler to choose a theorem-local variable from the binder sort's `@vars`
   pool rather than requiring the user to name one.

Once all arguments are known, the compiler *instantiates* the rule: it
substitutes the concrete expressions for each binder throughout the rule's
conclusion and hypotheses, producing fully concrete expressions. That
instantiated conclusion is then subject to normalization.

If the application still fails, the compiler may retry with a fallback rule.
An axiom or theorem annotated with `@fallback other_rule` says: "if applying
this rule to a proof line fails, try the same proof line again using
`other_rule`." This retry happens after ordinary binding inference and line
checking have been attempted for the original rule.

### How normalization fits in

When a rule is marked `@normalize conc`, the instantiated conclusion may be
in a "raw" form that differs from what the user wrote. Both the raw
instantiated conclusion and the user's assertion are normalized using the
registered rewrite and congruence rules, and the two *normalized* forms must
match. The compiler then emits the full chain of proof steps — the raw rule
application, every intermediate rewrite and congruence step, and a final
transport step — so the verifier can confirm the whole thing.

To make this concrete, consider `ax_inst`:
```
--| @normalize conc
axiom ax_inst {x: nat} (t: nat) (p: wff x):
  $ A. x p $ > $ sb_f t x p $;
```

The shape of this rule is: given a proof of `A. x p`, produce `sb_f t x p`
— a raw substitution term with `p` not yet reduced.

Now suppose you write:
```
l1: $ S zer = zer $ by ax_inst (x := $ x $, t := $ S zer $, p := $ x = zer $) [#1]
```

Three distinct expressions are in play:

| Stage | Expression |
|-------|------------|
| **Instantiated conclusion (before normalization)** | `sb_f (S zer) x (x = zer)` |
| **User assertion (before normalization)** | `S zer = zer` |
| **Both sides after normalization** | `S zer = zer` |

The normalizer reduces `sb_f (S zer) x (x = zer)` by applying `sb_f_eq`,
`sb_t_var`, and `sb_t_zer` with their associated congruence rules, arriving
at `S zer = zer`. The user's assertion `S zer = zer` is already in normal
form. The two normalized forms agree, so the line is accepted.

## Overview of the annotation vocabulary

| Annotation      | Attaches to         | Purpose |
|-----------------|---------------------|---------|
| `@relation`     | `axiom`             | Declares an equivalence relation on a sort |
| `@rewrite`      | `axiom`             | Marks an axiom as an oriented rewrite rule |
| `@congr`        | `axiom`             | Marks an axiom as a congruence rule for a term constructor |
| `@acui`         | `term`              | Marks a binary combiner for structural AU / ACU / AUI / ACUI normalization |
| `@normalize`    | `axiom` / `theorem` | Specifies which positions should be auto-normalized |
| `@fallback`     | `axiom` / `theorem` | Retries theorem application through another named rule |
| `@alpha`        | `axiom`             | Registers an alpha-renaming lemma for freshening |

Transparent def unfolding at theorem-application boundaries is covered
in `docs/transparent_defs.md`. `@view`, `@recover`, and `@abstract` are
covered in `docs/view_recover.md`. `@fresh` and `@freshen` are covered in
`docs/fresh_binders.md`.

---

## `@alpha`

### Purpose

`@alpha` registers a theorem as an alpha-renaming lemma that the frontend
may use when a rule application fails a binder dependency check. The
trusted verifier does not gain any new primitive here: the compiler is
just allowed to reuse an ordinary proved relation such as
`∀ x p ↔ ∀ y ([x/y] p)` or `∃ x p ↔ ∃ y ([x/y] p)` as a targeted rewrite.

This is used together with `@freshen`. A `@freshen g x` annotation says
that if a concrete binding for regular argument `g` depends on bound
binder `x`, the compiler may try to alpha-rename `g` to a fresh binder.
`@alpha` supplies the relation proof that justifies that rewrite.

### Syntax

```
--| @alpha <old-binder> <new-binder>
```

Example:

```
--| @alpha x y
axiom all_alpha {x y: obj} (p: wff x y):
  $ ∀ x p ↔ ∀ y ([x/y] p) $;
```

### Requirements

The annotated rule must satisfy these frontend checks:

- both named arguments exist
- both are bound binders
- both have the same sort
- the rule has no hypotheses
- the conclusion is a binary relation already understood by the rewrite
  / transport machinery
- the left-hand side has a visible head term, so the compiler can index
  the rule as a rewrite candidate for that constructor

### Operational model

When the freshening helper inspects a concrete expression, it only looks
at `@alpha` rules whose left-hand side head matches the expression's head
constructor. It then instantiates the annotated old binder with the
blocked binder and the annotated new binder with the chosen fresh binder.
If the left-hand side matches, the compiler emits an ordinary theorem
application of the alpha lemma, then uses the existing congruence and
transport pipeline to lift that local rewrite through the surrounding
formula.

This search is intentionally narrow:

- no broad rewrite search
- no backtracking over many alpha rules in v1
- no new trusted alpha primitive

The same `@alpha` lemmas may also be used at theorem boundaries during
final-conclusion reconciliation. That lets a proof end at a convenient
alpha-equivalent result and then transport back to the declared theorem
conclusion, provided the compiler can build the needed conversion proof
from the registered relation, rewrite, and congruence metadata.

---

## `@relation`

### Purpose

Before the normalizer can emit any proof steps, it needs to know which
equivalence relation governs each sort — which axioms are reflexivity,
transitivity, symmetry, and (optionally) a modus-ponens-style transport rule.
`@relation` supplies that information.

### Syntax
```
--| @relation <sort> <rel_term> <refl> <trans> <symm> <transport>
```

| Field | Meaning |
|-------|---------|
| `sort` | The sort this relation operates on |
| `rel_term` | The binary relation term (e.g. `bi` for biconditional) |
| `refl` | Reflexivity: `rel(a, a)` |
| `trans` | Transitivity: `rel(a,b) > rel(b,c) > rel(a,c)` |
| `symm` | Symmetry: `rel(a,b) > rel(b,a)` |
| `transport` | Modus ponens: `rel(a,b) > a > b`, or `_` if not applicable |

### Provable sorts, non-provable sorts, and why transport matters

**For a provable sort** (like `wff`), normalization ultimately needs to
deliver a *proof* of the user's assertion, not merely a proof that the raw
conclusion is equivalent to it. After normalization the compiler holds two
things: a proof of the raw conclusion (from the rule application) and a proof
of `rel(raw, normalized)` (from the normalization chain). Transport is the
axiom that combines these — `rel(a, b) > a > b` — to produce a proof of the
normalized form. Without transport there would be no way to cross from "I
know `raw` and I know `raw <-> normalized`" to "I have proved `normalized`".

**For a non-provable sort** (like `nat`), the situation is different in a
fundamental way. There is no notion of "a proof of a nat". The relation
`nat_eq(a, b)` lives in `wff`, not in `nat`, so you cannot write an axiom of
the form `nat_eq(a, b) > a > b` — the `a` and `b` are terms, not
propositions. But this is fine: nat-level normalization is never the *final*
step in a proof. It always feeds upward into a congruence rule that lifts the
nat-level equivalence into a `wff`-level proof. For example, `eq_congr` takes
two `nat_eq` proofs and produces a `bi`-level proof about `wff`. The `wff`
relation has transport, so the chain can be completed at the `wff` level.
Write `_` as the transport sentinel for any sort where this pattern applies.

**Example — provable sort with transport:**
```
term bi (a b: wff): wff;
--| @relation wff bi biid bitr bisym mpbi

axiom biid (a: wff): $ a <-> a $;
axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
```

**Example — non-provable sort without transport:**
```
term nat_eq (a b: nat): wff;
--| @relation nat nat_eq nat_eq_refl nat_eq_trans nat_eq_sym _
```

`nat_eq` produces a `wff`, not a `nat`, so no transport axiom exists or is
needed. Nat-level equivalences are always consumed by a congruence step that
lifts them into the `wff` level, where `mpbi` can close the proof.

---

## `@rewrite`

### Purpose

`@rewrite` marks an axiom as an oriented rewrite rule. The axiom's conclusion
must have the form `rel(lhs, rhs)` where `rel` is a relation previously
declared with `@relation`. The normalizer interprets this as "whenever you
see an expression matching `lhs`, replace it with `rhs`."

### Syntax
```
--| @rewrite
axiom sb_im (a b c: wff): $ sb a (b -> c) <-> (sb a b -> sb a c) $;
```

### How the normalizer applies rewrite rules

Rules are indexed by the *head term* of the LHS — that is, the outermost
function symbol of the left-hand side. When the normalizer encounters an
expression, it looks up all rules whose head term matches the top-level
constructor of that expression and tries them in declaration order. The first
rule whose LHS pattern unifies with the expression fires. After a rule fires,
the normalizer recursively normalizes the resulting RHS and then re-checks
the same expression for more applicable rules from the beginning. This
continues until no rules apply (fixed-point normalization).

This lookup is driven by the **visible** head of the current expression. The
normalizer does not generally unfold defs first in order to expose more rewrite
redexes. Transparent def comparison is a separate mechanism.

There is no backtracking: if the first matching rule leads to a form that
doesn't match the user's assertion, the compiler does not retry with a
different rule. See *Rule Selection and Ordering* for guidance on rule
ordering when rules overlap.

### Multi-sort example

Rewrite rules are not restricted to a single sort. A single `.mm0` file can
have rules for both wff-level and nat-level relations:
```
-- wff-level rule: sb_f distributes over equality (uses bi)
--| @rewrite
axiom sb_f_eq {x: nat} (t: nat) (a b: nat x):
  $ sb_f t x (a = b) <-> (sb_t t x a = sb_t t x b) $;

-- nat-level rule: sb_t distributes through successor (uses nat_eq)
--| @rewrite
axiom sb_t_suc {x: nat} (t: nat) (a: nat x):
  $ nat_eq (sb_t t x (S a)) (S (sb_t t x a)) $;
```

The normalizer selects the correct relation for each subexpression based on
its sort, so wff-level and nat-level rules interoperate transparently.

An important limitation is that this still works on visible syntax. If a
rewrite would become available only after exposing a def, ordinary
normalization will not discover it automatically.

---

## `@congr`

### Purpose

Rewrite rules reduce the head of an expression, but they cannot descend into
the arguments of a compound expression on their own. `@congr` provides the
axioms that justify rewriting *inside* a term constructor: given proofs that
each argument changed, a congruence rule combines them into a proof that the
whole application changed.

### Syntax
```
--| @congr
axiom im_congr (a b c d: wff):
  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
```

### Binder pairing convention

The binders of a congruence axiom follow a specific interleaved pattern that
the normalizer depends on: for each *regular* (non-bound) argument of the
term constructor, provide the *before* value and then the *after* value. Bound
arguments appear once (they cannot change). This gives the pattern
`a1, b1, a2, b2, ...` for a binary constructor with two regular arguments.

For `im_congr` above, `a` is the before-value of the first argument, `b` is
the after-value of the first argument, `c` is the before-value of the second,
and `d` is the after-value of the second.

When an argument does not change, the normalizer supplies a reflexivity proof
for it automatically; you do not need a separate congruence axiom for every
possible combination of changed and unchanged arguments.

### Cross-sort congruence

A congruence axiom for a wff-level term constructor can have nat-level
hypotheses. The normalizer resolves the appropriate relation for each argument
based on its declared sort:
```
--| @congr
axiom eq_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ (a = c) <-> (b = d) $;

--| @congr
axiom suc_congr (a b: nat):
  $ nat_eq a b $ > $ nat_eq (S a) (S b) $;
```

Here `eq_congr` justifies rewriting inside `=` (a wff-level term) when
nat-level arguments change, and `suc_congr` justifies rewriting inside `S`
(a nat-level term) when its nat-level argument changes.

---

## `@acui`

### Purpose

Some term constructors are used to build structured "collections" — contexts,
multisets, resource environments — where the proof-relevant notion of equality
is not syntactic identity but equivalence modulo associativity, commutativity,
unit elements, and possibly idempotence. `@acui` marks such a constructor so
the normalizer can canonicalize it structurally rather than relying solely on
rewrite rules.

### Syntax
```
--| @acui <assoc> <comm-or-_> <unit> <idem-or-_>
```

The positional order is **A C U I** (Assoc, Comm, Unit, Idem).

| Field | Meaning |
|-------|---------|
| `assoc` | Axiom proving `(a ∘ b) ∘ c ~ a ∘ (b ∘ c)` |
| `comm-or-_` | Axiom proving `a ∘ b ~ b ∘ a`, or `_` if the combiner is not commutative |
| `unit` | The nullary unit term |
| `idem-or-_` | Axiom proving `a ∘ a ~ a`, or `_` if no idempotence |

**Example:**
```
term emp: ctx;
term join (g h: ctx): ctx;
--| @acui ctx_assoc ctx_comm emp ctx_idem
```

### What the normalizer does with an ACUI combiner

When the normalizer encounters an expression built from an ACUI combiner, it
performs the following steps:

1. **Normalize children first.** Each element is normalized using the
   appropriate rules before the structural pass begins.
2. **Flatten nested uses.** `(a ∘ b) ∘ c` and `a ∘ (b ∘ c)` are treated as
   the flat list `[a, b, c]`.
3. **Remove supported unit elements.** The normalizer drops a left unit
   only when it has discovered a proof of `unit ∘ a ~ a`, and drops a right
   unit only when it has discovered a proof of `a ∘ unit ~ a`. If the
   combiner is commutative, either side can be derived from the other by
   first commuting.
4. **Sort deterministically** (if commutativity is declared). Elements are
   ordered using a canonical comparison, making the normal form
   order-independent.
5. **Deduplicate** (if idempotence is declared). Equal adjacent elements in
   the sorted list are merged.
6. **Rebuild right-associated.** The canonical list is reassembled as a
   right-associated binary tree: `a ∘ (b ∘ (c ∘ ...))`.

A proof is emitted for every structural step — associativity rearrangements,
unit eliminations, commutativity swaps, and idempotence merges — and composed
via transitivity into a single relation proof `rel(original, canonical)`.

In the current implementation, the ACUI path is also more def-aware than plain
head-rewrite lookup. It can do exact cancellation of common items, same-side
absorption by def-bearing items, and non-ACUI common-target search inside
wrapped leaves. But this still falls short of a general "rewrite through defs"
engine.

### Supported subsets

Associativity (A) is mandatory, because flattening is unjustified without
it. The `unit` field names the nullary term to use for empty rebuilt lists,
but unit *elimination* is structural only when matching unit laws are
available. Commutativity (C) and idempotence (I) are optional and independent:

| Declared | Behavior |
|----------|----------|
| AU   | Flatten; eliminate only the discovered left/right unit sides |
| ACU  | Flatten; eliminate supported units; sort canonically |
| AUI  | Flatten; eliminate supported units; deduplicate |
| ACUI | Flatten; eliminate supported units; sort; deduplicate |

For non-commutative AU and AUI combiners, left and right unit support are
distinct. A theorem of shape `unit ∘ a ~ a` does not justify dropping
`a ∘ unit`. For commutative ACU and ACUI combiners, one side can be derived
from the other using the declared commutativity theorem.

**Example — AU (non-commutative monoid):**
```
term id: mor;
term comp (f g: mor): mor;
--| @acui comp_assoc _ id _
```

This is suitable for morphism composition: `(f ∘ g) ∘ h` normalizes to
`f ∘ (g ∘ h)`. If the file contains a theorem of shape `id ∘ f ~ f`, then
`id ∘ f` normalizes to `f`; if it also contains `f ∘ id ~ f`, then trailing
identities normalize away as well. The order of distinct morphisms is
preserved.

### Required companions

A term annotated with `@acui` must also have:
- A `@relation` declared for its result sort (so the normalizer knows which
  relation to use for the proof steps).
- A `@congr` rule (so the normalizer can justify rewriting inside a larger
  expression that contains the combiner).

---

## `@normalize`

### Purpose

`@normalize` marks an axiom or theorem so that its conclusion and/or specified
hypotheses are automatically normalized after instantiation. Without this
annotation, the compiler checks proof lines by exact equality between the
raw instantiated form and the expression you wrote. With it, both sides are
normalized first and the normalized forms are compared.

### Syntax
```
--| @normalize conc
--| @normalize hyp0
--| @normalize conc hyp0 hyp1
```

- `conc`: normalize the conclusion after instantiation
- `hyp0`, `hyp1`, ...: normalize the hypothesis at the given 0-based index

Multiple positions can appear on a single annotation line.

### What happens at a normalized proof line

Given:
```
--| @normalize conc
axiom ax_inst {x: nat} (t: nat) (p: wff x):
  $ A. x p $ > $ sb_f t x p $;
```

When you write a proof line like:
```
l1: $ S zer = zer $ by ax_inst (x := $ x $, t := $ S zer $, p := $ x = zer $) [#1]
```

the compiler performs these steps:

1. **Instantiate** `ax_inst`'s conclusion with the given bindings:
   `sb_f (S zer) x (x = zer)`
2. **Normalize** the instantiated expression using the registered rewrite and
   congruence rules:
   - `sb_f_eq` rewrites to `sb_t (S zer) x x = sb_t (S zer) x zer`
   - `sb_t_var` rewrites `sb_t (S zer) x x` to `S zer`
   - `sb_t_zer` rewrites `sb_t (S zer) x zer` to `zer`
   - `eq_congr` and `suc_congr` provide congruence proofs for each step
3. **Compare** the normalized result to what you wrote (`S zer = zer`).
4. **Emit** the full proof chain: the raw `ax_inst` application, each
   intermediate rewrite step as a theorem application, and a final transport
   step that converts the raw conclusion to the normalized form.

If the normalized result does not match your assertion, the compiler reports
a `ConclusionMismatch` error.

### Hypothesis normalization

When `hyp0` (or another hypothesis index) is listed, the same process applies
in reverse: the compiler normalizes the *expected* hypothesis form (from the
rule's instantiated signature) and checks that your cited reference, after
normalization, matches it. A transport step is emitted to bridge the gap
before the reference is fed into the theorem application.

---

## `@fallback`

### Purpose

`@fallback` lets one rule delegate theorem application to another rule when
its own application fails. This is useful when several rules have the same
hypotheses but different conclusions or different inference behavior, and you
want to expose them under one user-facing rule name.

A typical use is to group several elimination rules under a single entry
point. For example, `and_elim` can fall back to `and_elim_right` if applying
`and_elim` itself does not match the user's proof line.

### Syntax
```
--| @fallback <other-rule>
```

The target must be the name of an axiom, theorem, or earlier lemma already in
scope at the annotation site.

### Semantics

When a proof line cites a rule `R`, the compiler first tries to apply `R`
normally, including:

- explicit argument bindings
- omitted-binder inference
- `@view`, `@recover`, and `@abstract`
- `@fresh`
- `@normalize`

If that whole attempt fails, and `R` has `@fallback S`, the compiler throws
away the failed tentative state and retries the same proof line using `S`.
The proof line text, explicit bindings, and references are unchanged; only the
candidate rule changes.

Fallbacks can chain:
```
--| @fallback and_elim_right
axiom and_elim_mid (a b: wff): $ and a b $ > $ fst a b $;

--| @fallback and_elim_mid
axiom and_elim (a b: wff): $ and a b $ > $ fst a b $;
```

A line such as
```
l1: $ snd a b $ by and_elim [#1]
```
first tries `and_elim`, then `and_elim_mid`, and finally
`and_elim_right`.

If every candidate in the chain fails, the diagnostic from the **first**
failed attempt is reported. This keeps the error anchored to the rule name the
user actually wrote.

### Constraints

- `@fallback` takes exactly one rule name.
- Only one `@fallback` annotation may be attached to a rule.
- The target is resolved eagerly while processing MM0 metadata, so forward
  references are not allowed.
- Cycles in the fallback chain are rejected when the chain is used.

`@fallback` affects theorem application only. It is unrelated to rewrite-rule
selection inside the normalizer.

---

## Mixed and multi-sort normalization

The normalizer supports multiple active relations simultaneously — one per
sort. When normalizing a compound expression, each child is normalized using
the relation for its own sort, determined from the parent term's argument
declarations. This allows seamless composition across sort boundaries.

**Example — normalizing `sb_f t x (S x = S x)`:**

1. The top-level expression has sort `wff`, so the `bi` relation governs head
   rewrites.
2. `sb_f_eq` fires, rewriting to `sb_t t x (S x) = sb_t t x (S x)`.
3. The normalizer descends into each argument of `=`, which have sort `nat`,
   so the `nat_eq` relation is used there.
4. `sb_t_suc` and `sb_t_var` reduce each `sb_t t x (S x)` to `S t`.
5. `suc_congr` and `eq_congr` assemble the nat-level and wff-level congruence
   proofs.

If no relation is registered for a sort, the normalizer leaves children of
that sort unrewritten and does not require a congruence proof for them.

---

## Proof generation

The normalizer is proof-producing: every transformation it performs becomes
a sequence of ordinary theorem applications in the MMB output. The verifier
sees no normalization opcodes — only axiom/theorem invocations it can check
independently.

The components of a generated normalization proof are:

| Component | When emitted |
|-----------|--------------|
| **Rewrite step** | Each successful `@rewrite` rule application |
| **Reflexivity** | For unchanged subexpressions inside a congruence step |
| **Congruence** | Combining child-level proofs via a `@congr` axiom |
| **Transitivity** | Composing sequential steps into a single relation proof |
| **Symmetry** | Used when normalizing a hypothesis (the proof direction reverses) |
| **Transport** | Converting `rel(a, b)` plus a proof of `a` into a proof of `b` |

For ACUI combiners, the structural steps (associativity rearrangements, unit
eliminations, commutativity swaps, idempotence merges) each emit their
respective axiom applications and are composed via transitivity in the same
way as rewrite steps.

---

## Rule selection and ordering

When multiple `@rewrite` rules share the same LHS head term, the normalizer
tries them in **declaration order** — the order the `@rewrite` annotations
appear in the `.mm0` file. The first rule whose LHS pattern matches the
current expression fires. After it fires, the normalizer recursively
normalizes the RHS, then returns to check for further applicable rules on the
resulting expression. There is no backtracking.

This means **more specific rules should come before more general ones:**
```
-- Specific: sb_t on the bound variable itself yields the substitution term
--| @rewrite
axiom sb_t_var {x: nat} (t: nat): $ nat_eq (sb_t t x x) t $;

-- General: sb_t distributes through successor
--| @rewrite
axiom sb_t_suc {x: nat} (t: nat) (a: nat x):
  $ nat_eq (sb_t t x (S a)) (S (sb_t t x a)) $;
```

In practice, overlapping rules are uncommon because rules are indexed by their
head term — `sb_t_var` and `sb_t_suc` both match `sb_t` at the head, but
their LHS substructure (`x` vs `S a`) already disambiguates them via pattern
matching. Still, when genuine overlap exists, declaration order is the
tiebreaker.

---

## Termination and step limits

The normalizer does **not** guarantee termination. A set of rules that cycle
(`a ~ b` and `b ~ a`) or that expand indefinitely will not terminate on their
own.

To prevent infinite loops, the normalizer enforces a **step limit** of 1000
rewrite steps per normalization invocation. Each successful rule application
counts as one step. When the limit is reached, normalization halts and returns
whatever expression has been reached so far.

If the partially-normalized expression does not match your assertion, the
compiler reports a `ConclusionMismatch` (or `HypothesisMismatch`) error as
usual. The error message does not currently distinguish "step limit reached"
from "normalization completed but result doesn't match". If you suspect a step
limit issue, check for cycles or unbounded expansion in your rule set.

The step limit is shared across all recursive normalization within a single
`@normalize` invocation: descending into children and assembling
reflexivity/transitivity proofs do not consume steps, but every head rewrite
rule application does.

---

## Worked example

### The axiom
```
--| @normalize conc
axiom ax_inst {x: nat} (t: nat) (p: wff x):
  $ A. x p $ > $ sb_f t x p $;
```

The rule takes a proof of `A. x p` and produces the raw substitution term
`sb_f t x p` — `p` with `t` substituted for `x`, not yet reduced.

### The theorem and proof line
```
theorem inst_suc {x: nat}:
  $ A. x (S x = S x) $ > $ S (S zer) = S (S zer) $;
```
```
l1: $ S (S zer) = S (S zer) $
      by ax_inst (x := $ x $, t := $ S zer $, p := $ S x = S x $) [#1]
```

### The three expressions

| | Expression |
|-|------------|
| **Instantiated conclusion (raw)** | `sb_f (S zer) x (S x = S x)` |
| **User assertion** | `S (S zer) = S (S zer)` |
| **Both after normalization** | `S (S zer) = S (S zer)` |

### Normalization trace
```
sb_f(Sz, x, eq(suc(x), suc(x)))

  -- sb_f_eq (wff level, bi relation) -->
     eq(sb_t(Sz,x,suc(x)), sb_t(Sz,x,suc(x)))

  -- left child (nat level, nat_eq relation):
     sb_t(Sz, x, suc(x))
       -- sb_t_suc --> suc(sb_t(Sz, x, x))
       -- sb_t_var --> suc(Sz)
     proof: suc_congr assembles nat_eq(sb_t(Sz,x,suc(x)), suc(Sz))

  -- right child: identical steps, same result

  -- eq_congr assembles:
     bi(eq(sb_t(Sz,x,suc(x)), sb_t(Sz,x,suc(x))),
        eq(suc(Sz), suc(Sz)))
  -- i.e.: sb_f(Sz,x,S x = S x) <-> S(S zer) = S(S zer)
```

The user's assertion `S (S zer) = S (S zer)` is already normal. Both sides
agree, so the compiler emits:

1. The raw `ax_inst` application, producing `sb_f (S zer) x (S x = S x)`
2. `sb_f_eq`, `sb_t_suc`, `sb_t_var` as rewrite steps
3. `suc_congr` and `eq_congr` as congruence steps, composing via transitivity
4. A transport step via `mpbi`: from the `bi`-proof and the proof of the
   raw conclusion, derive a proof of `S (S zer) = S (S zer)`
