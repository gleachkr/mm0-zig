# `@fresh` and `@vars`

These annotations help the proof compiler fill in bound binder arguments
that serve as local variables. They are frontend features: the trusted
verifier sees only ordinary theorem applications with concrete dummy
variables already in place.

---

## `@vars`

### Purpose

`@vars` is a sort-level annotation that registers math tokens as automatic
variable names. When a registered token appears in proof math and is not
otherwise known, the compiler lazily creates a theorem-local dummy of the
annotated sort and adds it to the theorem variable map.

This is useful for systems with a variable convention: a set of tokens
that readers understand to be variables of a particular sort, without
needing each theorem to redeclare them.

The same pools also back a newer hidden-dummy path: when advanced
matching keeps a bound hidden witness symbolic for most of elaboration,
final rule instantiation may still need to materialize that witness as a
real theorem-local variable. That escape path reuses the sort's `@vars`
pool instead of inventing an unnamed theorem dummy.

### Syntax

```
--| @vars <token> <token> ...
sort nat;
```

Annotations are attached to sort declarations via `--|` comment lines.
Multiple `@vars` annotations may appear on the same sort. Each one lists
one or more space-separated tokens.

```
--| @vars x y z
--| @vars α β γ
sort obj;
```

Tokens are raw math tokens, as split by the math-string tokenizer, not
identifiers. So unicode tokens like `α` work naturally even though they
are not valid declaration-syntax identifiers.

### Behavior

When the compiler processes a proof line, it scans the raw math text of
each assertion and binding formula before handing it to the trusted
parser. For each token:

1. If it is already in the theorem variable map, skip it.
2. If it is a known formula marker, notation token, or term name, skip
   it.
3. If it matches a `@vars` entry, create or reuse a theorem-local bound
   dummy of that sort and add it to the theorem variable map.
4. Otherwise, leave it for the existing parser to handle or reject.

Creation is lazy: the dummy appears only when the token is actually used
in proof math for the current theorem. Unused `@vars` tokens consume no
dependency slots.

### Scope

`@vars` tokens are available in proof-body math only. They do not affect
statement parsing in the `.mm0` file. A `@vars` token cannot appear in a
source theorem conclusion or hypothesis unless it was declared there by
ordinary theorem binders.

### Sort restrictions

`@vars` may only be used on sorts that permit theorem-local dummies:

- `strict` sorts are rejected
- `free` sorts are rejected

### Collision rules

The compiler rejects a `@vars` token at sort-annotation time if:

- the same token is already claimed by a different sort's `@vars`
- the token collides with an existing term name, formula marker, or
  notation token

This prevents silent shadowing. In `parsePrefixExpr`, variables are
checked before notations and terms, so a colliding `@vars` token would
otherwise win unexpectedly.

### Dependency budget

Theorem-local dummies consume tracked bound-variable dependency slots, 55
maximum. Because allocation is lazy, declaring many `@vars` tokens is
harmless as long as each theorem's proof only uses a modest number of
them. If a proof triggers too many dummy allocations, the existing
`DependencySlotExhausted` error fires.

### Example

```mm0
delimiter $ ( ) $;
provable sort wff;

--| @vars x y z
sort nat;

term eq (a b: nat): wff;
infixl eq: $=$ prec 50;

axiom eq_refl (a: nat): $ a = a $;

theorem example (t: nat): $ t = t $;
```

```proof
example
-------

l1: $ x = x $ by eq_refl
l2: $ t = t $ by eq_refl
```

Line `l1` is the `@vars` case: `x` is not declared in the theorem
statement, so when the compiler encounters it in proof math it looks up
`x` in the `nat` pool, creates a theorem-local dummy, and adds it to the
variable map before parsing the line.

Line `l2` is the ordinary case: `t` is already a theorem binder, so no
`@vars` allocation happens.

In both lines, the omitted binder `a` of `eq_refl` is inferred from the
written assertion — `@vars` only makes a name available in proof math; it does 
not itself force a rule binder to be filled.

### Unicode tokens

Because `@vars` uses math-string tokenization rather than identifier
parsing, unicode tokens work:

```mm0
--| @vars α β γ
sort obj;
```

A proof line mentioning `α` will auto-create a dummy of sort `obj`.

---

## `@fresh`

### Purpose

`@fresh` is a rule-level annotation for the opposite situation from the
`eq_refl` example above.

If an omitted binder still appears in the user-written proof line, then
ordinary inference can usually recover it directly from the line and the
cited references. `@fresh` is useful when the omitted binder is a bound
local variable that does not appear anywhere in the proof text the user
writes.

This comes up most often with substitution-style rules. The raw rule may
have a binder like `{x: ...}` because it literally talks about
substituting for `x`, but the user-facing line mentions only the fully
normalized result, with the substitution operator and its bound variable
already gone.

In that situation there is nothing for ordinary inference to read off the
surface syntax, so `@fresh` fills the hidden bound binder by choosing a
variable from that sort's `@vars` pool.

The compiler tries to reuse an already-allocated theorem-local dummy when
that dummy does not appear in the concrete inputs to the current rule
application. This avoids burning a new dependency slot when a suitable
pool variable is already available.

### Syntax

```
--| @fresh <binder-name>
```

The named binder must be a real bound rule binder in a sort that permits
local theorem dummies.

### Selection rule

For one rule application, the compiler looks at the current concrete
inputs:

- the proof line assertion
- the cited references
- the explicit binder assignments on the line

Then it examines the binder's sort's `@vars` pool in declaration order.

1. If a pool token already names a theorem-local dummy and that dummy does
   not occur in the current concrete inputs, reuse it.
2. Otherwise, if a pool token has not yet been allocated in the current
   theorem, allocate it and use it.
3. If every pool token is already present in the current concrete inputs,
   report an error.

Multiple `@fresh` binders on one rule application reserve distinct pool
variables. They never alias one another.

### Precedence

An explicit binding on the proof line overrides `@fresh`.

### Sort restrictions

`@fresh` rejects binders whose sort is `strict` or `free`.

### Relationship to `@vars`

`@fresh` depends on `@vars`. If a binder's sort has no `@vars` pool, the
rule application fails. If the pool exists, `@fresh` first tries to reuse
an already-allocated token and otherwise allocates the first unused token
in declaration order.

Failure happens only when there is a pool but every token in it is already
allocated and also appears in the current concrete inputs, so none of them
is fresh for this application.

---

## `@freshen`

### Purpose

`@freshen` handles a different problem from `@fresh`.

`@fresh` fills in an omitted bound binder directly. `@freshen` instead
repairs a rule application that already has concrete bindings, but those
bindings fail MM0's dependency check because some regular argument still
depends on a bound binder.

This is necessary in some cases because of how MM0 checks theorem
applications. Suppose a rule has a bound binder `{x : obj}` and also a
regular argument `(p : wff)` which does not declare any dependence on
`x`.

Then the expression substituted for `p` is not allowed to use the variable `x` 
*at all*. This is the surprising part: MM0 checks dependency against all 
variable occurrences, even occurrences where a variable like `x` is itself 
bound by an quantifier. So if the candidate expression for `p` contains `x` 
anywhere, whether free or attached to a quantifier, the application can fail.

For rules like ∀-introduction, that is often stricter than the usual
textbook presentation, where we only care that the generalized variable
does not occur *free* in the surrounding context. A context or
hypothesis that would be fine after α-renaming can therefore still fail
in MM0 when it is written using the same binder name `x`.

`@freshen` bridges that gap. It tells the frontend that, for a
specified pair of rule arguments, it may try to α-rename the offending
subexpression to use a fresh binder first, and then retry the rule
application.

For more background, see section 2.3 of Mario Carneiro's *Metamath
Zero: The Cartesian Theorem Prover*, and the MM0 specs in Mario's repo:
[`mm0.md`, under
"Verification"](https://github.com/digama0/mm0/blob/master/mm0.md#verification)
and [`mmb.md`, under
"Proof Checking"](https://github.com/digama0/mm0/blob/master/mm0-c/mmb.md#proof-checking).

If a regular rule argument still depends on a bound binder, the application is 
rejected unless the frontend can rewrite that regular argument to an 
alpha-equivalent fresh form first.

`@freshen` declares exactly which `(regular argument, bound binder)` pair
may be repaired that way.

### Syntax

```
--| @freshen <target-arg> <blocker-binder>
```

Example:

```
--| @freshen g x
axiom all_intro (g: ctx) {x: obj} (p: wff x):
  $ g ⊢ p $ > $ g ⊢ ∀ x p $;
```

This means: if applying `all_intro` fails because the concrete binding for
`g` depends on `x`, the compiler may try to alpha-rename `g` to remove
that dependency.

### Requirements

The annotation is accepted only when:

- `target-arg` names a regular rule argument
- `blocker-binder` names a bound rule binder

The annotation does not itself say how to perform the rewrite. It only
marks that dependency pair as eligible. The actual rewrite still needs:

- a fresh replacement binder from the sort's `@vars` pool
- a matching `@alpha` rule for the relevant constructor
- successful transport of hypotheses and conclusion through the rewritten
  rule application

### Operational model

Rule application still starts the ordinary way.

1. infer or read the concrete rule bindings
2. run the normal dependency checks
3. if there is no dependency violation, succeed normally
4. if there is a dependency violation, inspect the first failing pair
5. if that pair matches a declared `@freshen` annotation, choose one fresh
   replacement binder using the same pool policy as `@fresh`
6. use a matching `@alpha` lemma to rewrite the blocked regular argument
7. retry the rule application in that freshened world
8. emit transport steps so the final proof still checks against the user's
   original line

The search is deliberately narrow and deterministic: one declared pair,
then one chosen fresh binder, then the first successful alpha rewrite.

### Relation to `@vars`, `@fresh`, and `@alpha`

- `@vars` supplies the pool of names from which a fresh replacement binder
  may be chosen
- `@fresh` creates or reuses a local dummy when an omitted bound binder
  itself needs a value
- `@freshen` rewrites an already-concrete regular argument that depends on
  the wrong binder
- `@alpha` provides the proven relation used to justify that rewrite

### Example shape

A typical pair looks like this:

```mm0
--| @alpha x y
axiom all_alpha {x y: obj} (p: wff x y):
  $ ∀ x p ↔ ∀ y ([x/y] p) $;

--| @freshen g x
axiom all_intro (g: ctx) {x: obj} (p: wff x):
  $ g ⊢ p $ > $ g ⊢ ∀ x p $;
```

If a proof line tries to use `all_intro` with a concrete context binding
like `∀ x P x , Q y`, the compiler may alpha-rename the `∀ x P x` part to
use a fresh theorem-local binder before retrying the rule.

### Hidden def witnesses and recover-hole seeds

The same `@vars` pools are also used outside explicit `@fresh`
annotations.

#### Finalizing hidden def witnesses

Def-aware matching may keep hidden binders symbolic while it compares a
rule against concrete proof data. That is deliberate: most hidden
witnesses never need to escape into the theorem context at all.

If final rule instantiation still needs a *bound* hidden witness as a
concrete theorem expression, the compiler uses the same sort pool and the
same dependency-aware selection policy described above:

1. reuse an already-allocated theorem-local dummy when it is fresh for
   the current application;
2. otherwise allocate the first unused pool token;
3. otherwise report an error.

Two failure modes matter:

- if the sort has no `@vars` pool, the witness stays unresolved and the
  rule application is rejected;
- if the pool exists but every token is blocked by the current concrete
  inputs, the compiler reports `HiddenWitnessNoAvailableVar`.

This is why hidden-dummy support does not create theorem-local dummies
just because a def was unfolded. Escape happens only at the final
instantiation boundary.

#### Seeding omitted recover holes

There is one earlier use of the same pools: when a `@recover` hole is an
omitted *bound* binder, the compiler may pre-seed that hole from the
relevant `@vars` pool before view matching runs.

That seeding is still conservative:

- only omitted bound holes are eligible;
- explicit user bindings still win;
- multiple seeded holes reserve distinct pool variables.

The goal is not to finalize a hidden witness early. It is to give the
view / recover pipeline a stable local variable when the rule design
already makes it clear that the missing binder has to be bound.

### Example: CNF demo

A real use appears in `tests/proof_cases/tseitin.mm0`.

```mm0
--| @vars X
provable sort wff;

term iff (a b: wff): wff;
term sb (t: wff) {x: wff} (r: wff x): wff;

--| @view {x: wff} (a b: wff) (r: wff x) (p q: wff):
--|   $ a ↔ b $ > $ p ↔ q $
--| @abstract r p q x a b
--| @fresh x
--| @normalize conc
axiom iff_subst {x: wff} (a b: wff) (r: wff x):
  $ a ↔ b $ > $ [x/a] r ↔ [x/b] r $;
```

And the proof uses it like this:

```proof
l1: $ (P → (Q ∧ ¬ R)) ↔ (¬ P ∨ (Q ∧ ¬ R)) $ by imp_as_or
l2: $ S ∨ ¬ (P → (Q ∧ ¬ R)) ↔ S ∨ ¬ (¬ P ∨ (Q ∧ ¬ R)) $
      by iff_subst [l1]
```

The important point is that line `l2` does not mention the raw
substitution binder `x` anywhere. The user writes only the before-and-
after formulas. The visible information is enough for `@view` and
`@abstract` to recover:

- `a` and `b`, the expressions being substituted
- `r`, the surrounding context

But the raw rule still has the hidden bound binder `{x: wff}` because its
conclusion is stated as `[x/a] r ↔ [x/b] r`. After normalization, that raw
substitution syntax disappears from the user-facing line, so ordinary
inference has no surface occurrence from which to recover `x`.

`@fresh x` fills that gap. The compiler chooses `X` from the `wff`
`@vars` pool, instantiates the raw rule with `x := X`, and then
normalizes the substitution expressions away.

Without `@fresh`, the rule application would still be missing a concrete
value for `x` even though the user-facing formulas and the cited equality
already determine everything else.

### Another real use: calculus demo

The same pattern appears in `tests/proof_cases/leibniz`
for equality substitution:

```mm0
--| @vars r v w
sort real;

--| @view {x: real} (a b: real) (r: real x) (p q: real):
--|   $ a = b $ > $ p = q $
--| @abstract r p q x a b
--| @fresh x
--| @normalize conc
axiom eq_subst {x: real} (a b: real) (r: real x):
  $ a = b $ > $ [x | a] r = [x | b] r $;
```

With proof lines such as:

```proof
l8: $ lim h ((fh - f) / h) + lim h ((gh - g) / h) =
      df + lim h ((gh - g) / h) $ by eq_subst [#1]
```

Again, the line does not mention the raw binder `x`. It mentions only the
concrete equality before and after substitution. `@fresh` supplies the
hidden bound variable needed by the raw substitution rule, while
`@view`/`@abstract` recover the visible parts.
