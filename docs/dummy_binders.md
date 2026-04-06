# `@dummy` and `@vars`

These annotations help the proof compiler fill in bound binder arguments
that serve as fresh local variables. Both are frontend features: the trusted
verifier sees only ordinary theorem applications with concrete dummy
variables already in place.

---

## `@dummy`

### Purpose

Some rules have bound binders that serve only as a structural placeholder —
a fresh local variable introduced to mark a hole — with no value that
inference or view matching could discover. `@dummy` tells the compiler to
fill such a binder with a fresh theorem-local dummy variable automatically,
rather than requiring the user to name one on every proof line.

### Syntax
```
--| @dummy <binder-name>
```

The named binder must be a real bound rule binder in a sort that permits
dummy variables (not strict, not free).
```
--| @view {x: wff} (a b: wff) (r: wff x) (p q: wff): $ a <-> b $ > $ p $ > $ q $
--| @abstract r p q x a b
--| @dummy x
--| @normalize hyp1 conc
axiom ax_ctx {x: wff} (a b: wff) (r: wff x):
  $ a <-> b $ > $ sb a x r $ > $ sb b x r $;
```

Here `x` is the hole variable in the substitution context. The user never
needs to name it; `@dummy` allocates a fresh one for each rule application.

### Precedence

An explicit binding on the proof line overrides `@dummy`. If no explicit
binding is given, `@dummy` fills the binder before inference runs. Each rule
application gets its own fresh dummy; they are never shared across lines.

### Sort restrictions

`@dummy` rejects binders whose sort is `strict` or `free`, since those
sorts do not permit theorem-local dummy variables.

---

## `@vars`

### Purpose

`@vars` is a sort-level annotation that registers math tokens as automatic
dummy variable names. When a registered token appears in proof math (line
assertions or binder assignments) and is not otherwise known, the compiler
lazily creates a theorem-local dummy of the annotated sort, as if the user
had declared a bound binder in the theorem statement.

This is useful for systems with a "variable convention" — a set of tokens
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

Tokens are raw math tokens (as split by the math-string tokenizer), not
identifiers. This means unicode tokens like `α` work naturally, even though
they are not valid declaration-syntax identifiers.

### Behavior

When the compiler processes a proof line, it scans the raw math text of
each assertion and binding formula before handing it to the trusted parser.
For each token:

1. If it is already in the theorem variable map, skip it.
2. If it is a known formula marker, notation token, or term name, skip it.
3. If it matches a `@vars` entry, create a theorem-local bound dummy of
   that sort and add it to the theorem variable map.
4. Otherwise, leave it for the existing parser to handle (or reject).

The dummy is created lazily — only when the token actually appears in proof
math for the current theorem. Unused `@vars` tokens consume no dependency
slots.

### Scope

`@vars` tokens are available in proof-body math only. They do not affect
theorem statement parsing in the `.mm0` file. A `@vars` token cannot appear
in a theorem conclusion or hypothesis in the source `.mm0` file — it can
only appear in the `.proof` file's line assertions and binder assignments.

### Sort restrictions

`@vars` may only be used on sorts that permit theorem-local dummies:

- **strict** sorts are rejected
- **free** sorts are rejected

### Collision rules

The compiler rejects a `@vars` token at sort-annotation time if:

- the same token is already claimed by a different sort's `@vars`
- the token collides with an existing term name, formula marker, or
  notation token (prefix or infix)

This prevents silent shadowing: in `parsePrefixExpr`, variables are checked
before notations and terms, so a `@vars` token that matched a notation
would silently win. The collision check makes this an explicit error.

### Dependency budget

Theorem-local dummies consume tracked bound-variable dependency slots (55
maximum). Because allocation is lazy, declaring many `@vars` tokens is
harmless as long as each theorem's proof only uses a modest number of them.
If a proof triggers too many dummy allocations, the existing
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
encounters `x` in line l1's assertion text, it finds `x` in the `@vars`
registry for sort `nat`, creates a theorem-local dummy, and adds it to the
variable map. The trusted parser then accepts `x` as a bound variable.

### Unicode tokens

Because `@vars` uses math-string tokenization (not identifier parsing),
unicode tokens work:

```mm0
--| @vars α β γ
sort obj;
```

A proof line mentioning `α` will auto-create a dummy of sort `obj`.

---

## How `@dummy` and `@vars` differ

| | `@dummy` | `@vars` |
|---|---|---|
| **Annotation target** | Rule (axiom/theorem) binder | Sort declaration |
| **Scope** | One rule's applications | All proof lines |
| **Naming** | Anonymous (fresh each application) | Named by the token |
| **Reuse across lines** | No — each application gets a fresh dummy | Yes — same token reuses the same theorem-local dummy |
| **Typical use** | Hole variables in substitution-based rules | "Variable convention" tokens (`x`, `y`, `α`, `β`) |
