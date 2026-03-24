# Transparent def unfolding and `@abbrev`

The compiler now treats definitions as transparent at theorem-application
boundaries.

That means a proof line can use a defined form where the cited rule expects an
expanded form, or use an expanded form where the cited rule expects a defined
form, and the compiler will elaborate the gap into an ordinary MMB conversion
proof.

This is a frontend feature. The verifier still checks the resulting MMB in the
usual way. There is no new trusted equality notion.

There are really two related features here:

1. **Transparent def unfolding** for theorem application checking,
   omitted-binder inference, `@view` matching, and final theorem checking.
   This applies to **all** defs.
2. **`@abbrev`** for source-level normalization and canonicalization.
   This is an **opt-in** annotation on defs.

The distinction matters. All defs are transparent when the compiler decides
whether a rule application is valid. But only `@abbrev` defs are opened by the
frontend normalizer and canonicalizer as part of rewrite / ACUI search.

---

## Mental model

A rule application has two different layers:

- the **raw instantiated rule**, which is what the cited theorem or axiom
  literally says after substituting concrete binders
- the **user-facing expression**, which is what the proof author wrote on the
  line or in a cited reference

Before this feature, those two layers had to agree syntactically, unless
`@normalize` explicitly allowed the compiler to rewrite one side.

Now there is an extra bridge:

- if the two expressions differ only by unfolding defs, the compiler accepts
  the line
- it then inserts the required conversion proof internally
- the emitted MMB uses ordinary conversion machinery such as `Conv`,
  `Unfold`, `Cong`, `Refl`, and `Symm`

So transparent def unfolding is not a shortcut around proof checking. It is an
elaboration step that constructs a proof of equivalence between the raw and
user-facing expressions.

---

## What is transparent by default?

Transparent def unfolding is used in all of the places where the compiler has
previously compared expressions directly during theorem application:

- the proof line's asserted conclusion against the cited rule's instantiated
  conclusion
- each cited reference against the cited rule's instantiated hypotheses
- omitted-binder inference from the line assertion and cited references
- `@view` matching
- final theorem checking, where the last line is compared with the theorem's
  declared conclusion
- normalization-aware omitted-binder inference when the frontend solver needs
  a def-aware equality test

This applies to **all** defs, not only `@abbrev` defs.

### Basic conclusion example

```
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
def id (a: wff): wff = $ a -> a $;
axiom ax_expanded (a: wff): $ a -> a $;
theorem def_unfold_line (a: wff): $ id a $;
```

Proof:
```
l1: $ id a $ by ax_expanded []
```

`ax_expanded` produces the raw conclusion `a -> a`.
The proof line asserts `id a`.

The compiler accepts this because `id a` unfolds to `a -> a`. It emits the raw
rule application and then a conversion from `a -> a` to `id a`.

The reverse direction works too:

```
axiom ax_id (a: wff): $ id a $;
theorem def_unfold_final_reverse (a: wff): $ a -> a $;
```

Proof:
```
l1: $ id a $ by ax_id []
```

Here the final proof line is `id a`, but the theorem statement is `a -> a`.
The compiler inserts the final conversion automatically.

### Hypothesis example

Transparent unfolding also applies to cited references:

```
axiom use_id (a: wff): $ id a $ > $ a $;
```

Proof:
```
l1: $ a -> a $ by ax_expanded []
l2: $ a $ by use_id (a := $ a $) [l1]
```

`use_id` expects a reference proving `id a`, but the cited line proves
`a -> a`. The compiler inserts a transport line that turns the cited proof into
one with the expected shape before applying `use_id`.

### Definitions with dummy binders

Defs with hidden dummy binders also work as expected.

```
def exists_preimage (f y: obj) {.x: obj}: wff
  = $ A. x (((g f x) = y) -> (x = x)) $;

axiom ax_pre (f y: obj): $ exists_preimage f y $;

theorem def_unfold_dummy (f y: obj) {x: obj}:
  $ A. x (((g f x) = y) -> (x = x)) $;
```

Proof:
```
l1: $ A. x (((g f x) = y) -> (x = x)) $ by ax_pre []
```

Each unfolding automatically fills in variables for the bound dummies, based on 
the term that the defined term needs to match.

---

## Omitted-binder inference through defs

Transparent def unfolding is also used when explicit binder assignments are
omitted.

### Expected side is defined

```
def id (a: wff): wff = $ a -> a $;
axiom ax_id (a: wff): $ id a $;
theorem def_infer_expected (a: wff): $ a -> a $;
```

Proof:
```
l1: $ a -> a $ by ax_id []
```

The omitted binder `a` is recovered even though the cited rule conclusion is
`id a` and the proof line assertion is `a -> a`.

### Actual side is defined

```
def id (a: wff): wff = $ a -> a $;
axiom ax_expanded (a: wff): $ a -> a $;
theorem def_infer_actual (a: wff): $ id a $;
```

Proof:
```
l1: $ id a $ by ax_expanded []
```

This is the opposite direction: the rule is expanded, the proof line uses the
def, and omitted-binder inference still succeeds.

### Nested user-side defs

Inference is not limited to top-level defs. If the user writes a nested def,
the compiler may unfold under matching heads in order to recover omitted
binders.

For example, with:

```
def double (a: wff): wff = $ a -> a $;
axiom use_nested (a b: wff): $ (a -> b) $ > $ ((a -> b) -> a) $;
```

this proof is accepted:

```
l1: $ (double a) -> a $ by use_nested [#1]
```

because `double a` unfolds to `a -> a`, allowing the hypothesis match to
recover the omitted binders.

### Ambiguity is still an error

Transparent unfolding does **not** mean the compiler guesses when several
solutions remain possible.

In particular, when def unfolding combines with ACUI context matching, two or
more omitted-binder assignments may survive all constraints. In that case the
compiler rejects the line as ambiguous rather than picking one arbitrarily.

---

## Interaction with `@view`

`@view` matching is now def-aware as well.

```
def id (a: wff): wff = $ a -> a $;
--| @view (a b: wff): $ a -> b $ > $ a $ > $ b $
axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
axiom ax_id (a: wff): $ id a $;
```

Proof:
```
l1: $ id a $ by ax_id []
l2: $ a $ by ax_mp [l1, #1]
```

The view expects its first hypothesis to look like `a -> b`, but the cited
line is `id a`. Since `id a` unfolds to `a -> a`, view matching can solve
`a := a` and `b := a` and continue normally.

This is useful because view annotations are often the user-facing shape of a
rule. If defs were opaque there, you would still end up needing explicit
bindings in places where the theorem application itself was otherwise obvious.

---

## Interaction with `@normalize`

Transparent def unfolding and `@normalize` solve different problems.

- transparent def unfolding bridges **defined** and **expanded** forms
- `@normalize` bridges expressions related by registered rewrite,
  congruence, and ACUI rules

They compose.

### Def-aware normalized conclusion

Suppose a rule is normalized on the conclusion, but the user writes a def in
that normalized position:

```
def id (a: wff): wff = $ a -> a $;
--| @normalize conc
axiom all_elim (a b: wff): $ sb a b $;

theorem def_rewrite_concl (a: wff): $ id Q $;
```

Proof:
```
l1: $ id Q $ by all_elim (a := $ Q $, b := $ P -> P $) []
```

The compiler first instantiates the raw rule, then uses normalization to reach
its normalized expected form, and finally uses transparent def conversion if
needed to bridge between that normalized form and what the user wrote.

### Def-aware normalized hypothesis

The same applies to normalized hypotheses:

```
axiom ax_id (a: wff): $ id a $;
--| @normalize hyp0
axiom use_sub (a b: wff): $ sb a b $ > $ a $;
```

Proof:
```
l1: $ id Q $ by ax_id (a := $ Q $) []
l2: $ Q $ by use_sub (a := $ Q $, b := $ P -> P $) [l1]
```

The expected hypothesis is normalized, then the cited reference may still be
bridged by transparent unfolding before it is fed into the theorem
application.

---

## `@abbrev`

### Purpose

`@abbrev` is a separate feature.

All defs are transparent for theorem application checking, but expanding every
def during rewrite search would be noisy and expensive. Many defs are genuine
logical definitions, not just user-facing notation. The frontend normalizer and
canonicalizer therefore open defs only when the def is explicitly marked as an
abbreviation.

Use `@abbrev` for defs that should behave like notation during source-level
normalization and canonicalization.

### Syntax

Attach `@abbrev` to a `def`:

```
--| @abbrev
def dbl (a: wff): ctx = $ a , a $;
```

Attaching `@abbrev` to a non-def term is an error.

### What `@abbrev` changes

`@abbrev` affects the two frontend components that perform source-level search:

- `canonicalizer.zig`, which computes symbolic canonical forms for omitted-
  binder inference
- `normalizer.zig`, which builds proof-producing normalization chains for
  `@normalize`

In those components, an `@abbrev` def may be opened even if no explicit
rewrite rule names that def head.

This lets short notation defs participate naturally in rewrite and ACUI-based
checking.

### ACUI example

```
--| @abbrev
def dbl (a: wff): ctx = $ a , a $;

--| @normalize conc
axiom dup_ax (g: ctx) (a: wff): $ g , a , a ⇒ a $;

theorem abbrev_assoc (a: wff): $ dbl a , emp ⇒ a $;
```

Here `dbl a` is opened by the normalizer to `a , a`, after which the ACUI
normalization on contexts can eliminate `emp`, reassociate, and compare against
what `dup_ax` expects.

### Rewrite example

```
--| @abbrev
def pp: wff = $ P -> P $;

--| @normalize conc
axiom all_elim (a b: wff): $ sb a b $;

theorem abbrev_rewrite: $ Q -> Q $;
```

A proof line can instantiate `all_elim` with `b := $ pp $`. During
normalization, `pp` is opened to `P -> P`, which then exposes the rewrite redex
needed by the substitution rules.

### Priority and search order

`@abbrev` opening is intentionally conservative.

The frontend canonicalizer and normalizer first try to make progress using the
ordinary machinery already attached to the current expression:

- explicit rewrite rules
- structural ACUI normalization
- congruence-driven descent into children

Only when that direct machinery cannot make further progress at the current
head do they try opening an `@abbrev` def.

This keeps explicit rewrite rules in charge of the main normalization strategy,
while still allowing notation-like defs to expose the redexes that those rules
need.

### Nested and dummy-argument abbreviations

`@abbrev` defs can be nested inside other `@abbrev` defs, and they can also
have hidden dummy binders. Each opening allocates fresh dummies exactly as an
ordinary def unfolding would, so matching remains alpha-aware.

---

## What the verifier sees

The verifier does **not** get a new opaque "transparent def" rule.

After elaboration, the emitted MMB contains only ordinary proof machinery:

- theorem applications
- conversion commands
- definition unfolding commands
- congruence / symmetry / reflexivity steps as needed

So the trust story is unchanged:

- the compiler is responsible for finding and assembling the conversion
- the verifier is responsible for checking the resulting MMB proof stream

---

## Limits and intended use

A few boundaries are worth keeping in mind.

- Transparent unfolding is only about defs. It does not replace the rewrite
  system, congruence rules, or ACUI metadata.
- `@abbrev` only affects frontend normalization and canonicalization. It is not
  needed for ordinary theorem application transparency.
- Omitted-binder inference still requires a unique solution. Def-aware matching
  can fail with ambiguity.
- The normalizer still has the same step limit and termination caveats as the
  rest of the rewrite system.

In short:

- use **transparent def unfolding** when you want proof authors to move freely
  between defined and expanded forms at theorem-application boundaries
- use **`@abbrev`** when you also want a def to behave like notation inside
  frontend rewrite / ACUI normalization
