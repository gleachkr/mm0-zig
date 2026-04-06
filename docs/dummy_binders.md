# `@dummy`, `@fresh`, and `@vars`

These annotations help the proof compiler fill in bound binder arguments
that serve as local variables. They are frontend features: the trusted
verifier sees only ordinary theorem applications with concrete dummy
variables already in place.

---

## `@dummy`

### Purpose

Some rules have bound binders that serve only as a structural placeholder
— a local variable introduced to mark a hole — with no value that
inference or view matching could discover. `@dummy` tells the compiler to
fill such a binder with a fresh theorem-local dummy variable
automatically, rather than requiring the user to name one on every proof
line.

### Syntax
```
--| @dummy <binder-name>
```

The named binder must be a real bound rule binder in a sort that permits
local theorem dummies: not `strict` and not `free`.

```
--| @view {x: wff} (a b: wff) (r: wff x) (p q: wff):
--|   $ a <-> b $ > $ p $ > $ q $
--| @abstract r p q x a b
--| @dummy x
--| @normalize hyp1 conc
axiom ax_ctx {x: wff} (a b: wff) (r: wff x):
  $ a <-> b $ > $ sb a x r $ > $ sb b x r $;
```

Here `x` is the hole variable in the substitution context. The user never
needs to name it; `@dummy` allocates a fresh one for each rule
application.

### Precedence

An explicit binding on the proof line overrides `@dummy`. If no explicit
binding is given, `@dummy` fills the binder before inference runs. Each
rule application gets its own fresh dummy; they are never shared across
lines.

### Sort restrictions

`@dummy` rejects binders whose sort is `strict` or `free`, since those
sorts do not permit theorem-local dummy variables.

### Status

`@dummy` still works, but it is expensive in long proofs: every rule
application allocates a new theorem-local dummy and therefore burns a
tracked bound-variable dependency slot. In many situations `@fresh` is a
better fit.

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

l1: $ x = x $ by eq_refl (a := $ x $)
l2: $ t = t $ by eq_refl (a := $ t $)
```

Here `x` is not declared in the theorem statement. When the compiler
encounters `x` in line `l1`, it finds `x` in the `@vars` registry for
sort `nat`, creates a theorem-local dummy, and adds it to the variable
map. The trusted parser then accepts `x` as a bound variable.

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

`@fresh` is a rule-level annotation that fills an omitted bound binder by
choosing a variable from that binder's sort's `@vars` pool.

Unlike `@dummy`, `@fresh` tries to reuse an already-allocated theorem-
local dummy when that dummy does not appear in the concrete inputs to the
current rule application. This avoids burning a new dependency slot when a
suitable pool variable is already available.

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
2. Otherwise, allocate the first unallocated pool token.
3. If no pool token is available, report an error.

Multiple `@fresh` binders on one rule application reserve distinct pool
variables. They never alias one another.

### Precedence

An explicit binding on the proof line overrides `@fresh`, just as it does
for `@dummy`.

### Sort restrictions

`@fresh` rejects binders whose sort is `strict` or `free`.

### Relationship to `@vars`

`@fresh` depends on `@vars`. If a binder's sort has no `@vars` pool, or if
all pool tokens are already present in the current concrete inputs, the
rule application fails.

So `@fresh` is a bounded, pool-based strategy, while `@dummy` is an
unbounded, always-allocate strategy.

### Example

```mm0
delimiter $ ( ) $;
provable sort wff;

--| @vars x y z
sort obj;

term eq (a b: obj): wff;
infixl eq: $=$ prec 50;
term top: obj;

axiom eq_refl (a: obj): $ a = a $;
--| @fresh x
axiom use_fresh {x: obj}: $ x = x $;

theorem demo: $ top = top $;
```

```proof
demo
----

l1: $ x = x $ by eq_refl (a := $ x $)
l2: $ y = y $ by use_fresh []
l3: $ top = top $ by eq_refl (a := $ top $)
```

On line `l2`, the binder `x` of `use_fresh` is omitted. The compiler
looks at the `obj` pool `x y z`. Token `x` is already present in the
current theorem and also appears in the concrete inputs to line `l2`, so
it cannot be reused. Token `y` is available, so the compiler binds the
rule's omitted binder to `y`.

If a later line uses `@fresh` again and `y` is absent from that line's
inputs, `y` can be reused instead of allocating a new dummy.

---

## How the three features differ

- **Annotation target**
  - `@dummy`: rule binder
  - `@fresh`: rule binder
  - `@vars`: sort
- **Role**
  - `@dummy`: always allocate a fresh dummy
  - `@fresh`: reuse or allocate from a pool
  - `@vars`: declare the pool tokens
- **Scope**
  - `@dummy`: one rule application
  - `@fresh`: one rule application
  - `@vars`: whole theorem proof body
- **Naming**
  - `@dummy`: anonymous
  - `@fresh`: named by the chosen pool token
  - `@vars`: named by the token
- **Reuse across lines**
  - `@dummy`: never
  - `@fresh`: yes, when absent from current inputs
  - `@vars`: yes
- **Failure mode**
  - `@dummy`: only the 55-slot limit
  - `@fresh`: may fail if the pool is exhausted
  - `@vars`: not applicable
- **Typical use**
  - `@dummy`: hole variables that must be globally fresh
  - `@fresh`: hole variables that only need to be fresh relative to the
    current line
  - `@vars`: variable-convention tokens

A useful rule of thumb is:

- use `@vars` to define the token pool
- use `@fresh` when a rule wants a local variable that should avoid
  burning new slots when possible
- use `@dummy` only when the rule really needs a globally new theorem-
  local dummy every time
