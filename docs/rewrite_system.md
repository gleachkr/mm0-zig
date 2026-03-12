# Rewrite System and Annotation Syntax

The compiler includes a proof-producing rewrite system that automates
normalization of expressions during theorem application. It operates
entirely in the frontend — the verifier and MMB format are unchanged.

## Overview

The rewrite system allows axioms and theorems to be annotated with
special comments (`--|`) that declare:

- **Relations**: equivalence relations on a sort (reflexivity,
  transitivity, symmetry, and optionally transport)
- **Rewrite rules**: oriented equations that the normalizer applies
  left-to-right
- **Congruence rules**: theorems justifying rewriting inside term
  constructors
- **Structural ACUI combiners**: context-like constructors normalized
  modulo assoc / comm / unit / optional idem
- **Normalize specs**: which positions (conclusion, hypotheses) of a
  rule application should be automatically normalized

When a proof line applies a rule marked with `@normalize`, the compiler
normalizes the instantiated conclusion or marked hypotheses using the
mixed frontend normalizer. That normalizer can combine registered
rewrite rules with structural ACUI normalization, then emits the chain
of proof steps as ordinary theorem applications in the MMB output.

## Annotation Syntax

Annotations are written as `--|` comments on the line immediately before
the statement they annotate. Multiple annotations can precede a single
statement.

### `@relation`

Declares an equivalence relation on a sort.

```
--| @relation <sort> <rel_term> <refl> <trans> <symm> <transport>
```

- `sort`: the sort this relation operates on
- `rel_term`: the binary relation term (e.g., `bi` for biconditional)
- `refl`: reflexivity axiom — `rel(a, a)`
- `trans`: transitivity axiom — `rel(a,b) > rel(b,c) > rel(a,c)`
- `symm`: symmetry axiom — `rel(a,b) > rel(b,a)`
- `transport`: modus-ponens-like axiom — `rel(a,b) > a > b`. Use `_`
  if the sort is not provable and transport is not applicable.

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

The `_` sentinel indicates no transport theorem. This is appropriate for
sorts like `nat` where the relation (`nat_eq`) produces a `wff`, not a
`nat`, so there is no meaningful transport.

### `@rewrite`

Marks an axiom as an oriented rewrite rule. The axiom's conclusion must
have the form `rel(lhs, rhs)` where `rel` is a registered relation
term. The normalizer applies the rule left-to-right: when it encounters
an expression matching `lhs`, it rewrites to `rhs`.

```
--| @rewrite
axiom sb_im (a b c: wff): $ sb a (b -> c) <-> (sb a b -> sb a c) $;
```

Rules are indexed by the head term of the LHS. The normalizer tries all
rules for a given head term and applies the first one that matches, then
restarts. This continues until no more rules apply (fixed-point
normalization).

Rewrite rules can use any registered relation, not just the one for the
sort they appear to "belong to". The normalizer determines which
relation to use based on the sort of the expression being normalized.

**Multi-sort example:**

```
-- wff-level rule (uses bi as relation)
--| @rewrite
axiom sb_f_eq {x: nat} (t: nat) (a b: nat x):
  $ sb_f t x (a = b) <-> (sb_t t x a = sb_t t x b) $;

-- nat-level rule (uses nat_eq as relation)
--| @rewrite
axiom sb_t_suc {x: nat} (t: nat) (a: nat x):
  $ nat_eq (sb_t t x (S a)) (S (sb_t t x a)) $;
```

### `@congr`

Marks an axiom as a congruence rule for a specific term constructor. The
conclusion must have the form `rel(f(a1..an), f(b1..bn))`. The
normalizer uses congruence rules to justify rewriting inside compound
expressions.

```
--| @congr
axiom im_congr (a b c d: wff):
  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
```

The congruence rule's hypotheses must provide a relation proof for each
argument of the term constructor, in order. Unchanged arguments get a
reflexivity proof.

**Cross-sort congruence** is supported. A congruence rule for a
wff-level term can have nat-level relation hypotheses:

```
--| @congr
axiom eq_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ (a = c) <-> (b = d) $;

--| @congr
axiom suc_congr (a b: nat):
  $ nat_eq a b $ > $ nat_eq (S a) (S b) $;
```

The congruence rule's binders follow the pattern `a1, b1, a2, b2, ...`
— pairs of original and rewritten values for each argument.

### `@acui`

Marks a binary constructor as a structural combiner to be normalized
modulo assoc / comm / unit / optional idempotence.

```
--| @acui <assoc> <comm-or-_> <unit> <idem-or-_>
```

The positional order is mnemonic: `A C U I`.

- `assoc`: theorem proving associativity of the combiner
- `comm-or-_`: theorem proving commutativity, or `_` if absent
- `unit`: the nullary unit term
- `idem-or-_`: theorem proving idempotence, or `_` if absent

Example:

```
term emp: ctx;
term join (g h: ctx): ctx;
--| @acui ctx_assoc ctx_comm emp ctx_idem
```

The associated relation for the constructor's result sort must also be
registered with `@relation`, and the constructor itself usually needs a
`@congr` theorem.

During normalization the compiler:

1. normalizes children first
2. flattens nested uses of the combiner
3. removes unit terms
4. sorts children deterministically when commutativity is available
5. deduplicates equal children when idempotence is available
6. rebuilds a canonical right-associated form

The proof-producing normalizer emits ordinary theorem applications for
assoc / comm / unit / idem and composes them with congruence,
transitivity, symmetry, and transport as needed.

### `@normalize`

Marks a rule so that its conclusion and/or hypotheses are automatically
normalized after instantiation.

```
--| @normalize conc
--| @normalize hyp0
--| @normalize conc hyp0 hyp1
```

- `conc`: normalize the conclusion
- `hyp0`, `hyp1`, ...: normalize the hypothesis at the given index
  (0-based)

Multiple positions can be listed on a single annotation line.

**Example:**

```
--| @normalize conc
axiom ax_inst {x: nat} (t: nat) (p: wff x):
  $ A. x p $ > $ sb_f t x p $;
```

When the user writes:
```
l1: $ S zer = zer $ by ax_inst (x := $ x $, t := $ S zer $, p := $ x = zer $) [#1]
```

The compiler:
1. Instantiates `ax_inst`'s conclusion: `sb_f (S zer) x (x = zer)`
2. Normalizes it using rewrite rules:
   - `sb_f_eq` rewrites to `sb_t (S zer) x x = sb_t (S zer) x zer`
   - `sb_t_var` rewrites `sb_t (S zer) x x` to `S zer`
   - `sb_t_zer` rewrites `sb_t (S zer) x zer` to `zer`
   - Congruence via `eq_congr` combines them
3. Checks the normalized result matches the user's assertion (`S zer = zer`)
4. Emits transport from the raw conclusion to the normalized form

## Mixed and Multi-Sort Normalization

The normalizer supports multiple relations — one per sort — and can mix
ordinary rewriting with structural ACUI normalization in the same
expression. When normalizing a compound expression, each child is
normalized using the relation for its sort (determined from the parent
term's argument declarations).

This enables compositional rewriting across sort boundaries. For
example, normalizing `sb_f t x (S x = S x)`:

1. The top-level expression has sort `wff`, so the `bi` relation is used
   for head rules
2. `sb_f_eq` rewrites to `sb_t t x (S x) = sb_t t x (S x)`
3. Recursively normalizing the `eq` children: each `sb_t t x (S x)` has
   sort `nat`, so the `nat_eq` relation is used
4. `sb_t_suc` and `sb_t_var` reduce each to `S t`
5. `suc_congr` and `eq_congr` provide the congruence proofs

If no relation is registered for a sort, the normalizer skips that
child (no rewriting, no congruence proof needed).

## Proof Generation

The normalizer is proof-producing. Every rewrite step emits a proof line
referencing the rewrite axiom with concrete bindings. The full
normalization proof is composed from:

- **Rewrite steps**: direct applications of `@rewrite` axioms
- **Reflexivity**: `refl(a)` for unchanged subexpressions
- **Congruence**: `@congr` rules combining child proofs
- **Transitivity**: composing sequential rewrite steps
- **Symmetry**: reversing a normalization direction (used in hypothesis
  normalization)
- **Transport**: converting a relation proof `rel(a,b)` plus a proof of
  `a` into a proof of `b`

All generated proof steps are ordinary theorem applications. The
verifier sees no rewriting — only a sequence of axiom/theorem
invocations.

## Rule Selection and Ordering

When multiple `@rewrite` rules share the same LHS head term, the
normalizer tries them in **declaration order** — the order the `@rewrite`
annotations appear in the `.mm0` file. It applies the first rule whose
LHS pattern matches the current expression, then restarts from the
beginning of the rule list for that head term. This is a standard
first-match strategy.

If more than one rule could match at a given step, only the first
matching rule fires. The remaining rules are not tried for that step
(though they may fire on subsequent iterations if the expression
changes). There is no backtracking: if the first matching rule leads to
a normal form that doesn't match the user's assertion, the normalizer
does not try alternative rule orderings.

This means rule ordering matters. If you have overlapping rules, place
the more specific rule before the more general one:

```
-- Specific case first: sb_t on a variable gives the substitution term
--| @rewrite
axiom sb_t_var {x: nat} (t: nat): $ nat_eq (sb_t t x x) t $;

-- General case: sb_t distributes through successor
--| @rewrite
axiom sb_t_suc {x: nat} (t: nat) (a: nat x):
  $ nat_eq (sb_t t x (S a)) (S (sb_t t x a)) $;
```

In practice, overlapping rules are uncommon because rules are indexed by
head term — `sb_t_var` and `sb_t_suc` both match `sb_t` at the head,
but their LHS substructure (`x` vs `S a`) disambiguates them via
pattern matching.

## Termination and Step Limits

The normalizer does **not** guarantee termination. A set of rewrite
rules that cycle (e.g., `a ~ b` and `b ~ a`) or that expand
indefinitely will not terminate on their own.

To prevent infinite loops, the normalizer enforces a **step limit** of
1000 rewrite steps per normalization call. Each successful rule
application counts as one step. When the limit is reached, the
normalizer stops applying head rules and returns whatever expression it
has reached so far.

If the partially-normalized expression does not match the user's
assertion, the compiler reports a `ConclusionMismatch` (or
`HypothesisMismatch`) error as usual. The error message does not
currently distinguish "normalization was incomplete due to step limit"
from "normalization completed but the result doesn't match". If you
suspect a step limit issue, check whether your rules have cycles or
unbounded expansion.

The step limit is shared across all recursive normalization within a
single `@normalize` invocation. For example, if normalizing the
conclusion of a rule triggers recursive normalization of
subexpressions, all of those steps count toward the same 1000-step
budget.

Congruence steps (descending into children) and reflexivity/transitivity
proof assembly do not count toward the step limit — only successful
head rewrite rule applications are counted.

## Worked Example

Given:
```
theorem inst_suc {x: nat}:
  $ A. x (S x = S x) $ > $ S (S zer) = S (S zer) $;
```

Proof:
```
l1: $ S (S zer) = S (S zer) $ by ax_inst (x := $ x $, t := $ S zer $, p := $ S x = S x $) [#1]
```

The compiler normalizes `sb_f (S zer) x (S x = S x)`:

```
sb_f(Sz, x, eq(suc(x), suc(x)))
  -- sb_f_eq -->  eq(sb_t(Sz,x,suc(x)), sb_t(Sz,x,suc(x)))
  -- child 0: sb_t(Sz,x,suc(x))
     -- sb_t_suc -->  suc(sb_t(Sz,x,x))
     -- sb_t_var -->  Sz
     -- suc_congr -->  suc(Sz) = S(S zer)
  -- child 1: same as child 0
  -- eq_congr -->  eq(S(Sz), S(Sz))
= S (S zer) = S (S zer)
```

This matches the user's assertion, so the compiler emits the full proof
chain and a transport step.
