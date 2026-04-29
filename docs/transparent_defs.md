# Transparent def unfolding

The compiler now treats definitions as transparent at theorem-application
boundaries.

That means a proof line can use a defined form where the cited rule expects an
expanded form, or use an expanded form where the cited rule expects a defined
form, and the compiler will elaborate the gap into an ordinary MMB conversion
proof.

This is a frontend feature. The verifier still checks the resulting MMB in the
usual way. There is no new trusted equality notion.

Transparent def unfolding is used for theorem application checking,
`@view` matching, final theorem checking, and higher-level inference
helpers outside strict replay. This applies to **all** defs.


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

## Where transparent def support applies

"Transparent" does not mean that every frontend phase opens defs in the same
way. Different subsystems ask for different strengths of comparison:

- **Theorem-application boundary checks:** yes. The compiler can bridge
  defined and expanded forms when comparing a proof line against the cited
  rule's instantiated conclusion or hypotheses, and when comparing the final
  proof line against the theorem statement.
- **`@view` matching:** yes. View matching is def-aware and may also use the
  same semantic comparison machinery that higher-level inference uses.
- **`@recover` / `@abstract`:** partially. They first compare the resolved
  view expressions structurally. If that fails, they get one narrow retry that
  unfolds concrete defs without hidden dummy args and then canonicalizes.
- **Normalization-aware higher-level inference:** yes, when the frontend
  solver explicitly asks for a def-aware comparison.
- **Strict omitted-binder replay:** no. Replay stays exact and does not open
  defs.
- **Plain `@normalize`:** no eager def exposure. Normalization still does not
  unfold defs merely to create new rewrite redexes.

This still applies to **all** defs at theorem-application boundaries, but the
hidden-dummy cases remain witness-driven rather than eager or global.

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

Defs with hidden dummy binders also work, but the mechanism is more specific
than ordinary concrete def unfolding.

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

When the compiler compares a hidden-dummy def against a concrete target, it
solves those hidden binders relative to that comparison problem. During
matching, the witnesses stay match-local and symbolic for as long as possible;
they are not forced back into theorem-local expressions merely because a def
was opened. If final instantiation later needs a bound witness to escape into
the theorem, it must do so through the sort's `@vars` pool, using the same
selection policy as `@fresh`. This is still targeted, witness-driven exposure
rather than a general-purpose "open this hidden-dummy def" operation.

---

## Omitted-binder inference

There are several omitted-binder paths now, and this distinction is
important:

- **Exact replay fast path.** For ordinary rules, the compiler replays the
  cited rule's unify stream against the line assertion and cited references.
  This path is exact: it requires the same concrete heads that the rule
  expects, and it does not open defs.
- **Transparent fallback after replay.** If strict replay fails without a
  hard diagnostic, ordinary rules may get a def-aware rule-match fallback
  seeded by whatever replay had already learned.
- **Advanced inference paths.** Rules with `@view` or `@normalize`, and some
  harder solver-driven cases, go through the frontend's def-aware matching
  machinery and structural solver instead of relying only on raw replay.

So the old broad statement "omitted-binder inference is transparent" is too
coarse, but so is "all omitted-binder inference is exact". What is exact is
the replay path itself.

### Defined and expanded forms can infer through fallback matching

```
def id (a: wff): wff = $ a -> a $;
axiom ax_id (a: wff): $ id a $;
theorem def_infer_expected (a: wff): $ a -> a $;
```

This proof is accepted:

```
l1: $ a -> a $ by ax_id []
```

Strict replay itself still sees the rule conclusion headed by `id` and
the proof line headed by `->`, so the exact path stops at that mismatch.
Because the strict failure did not already produce a hard diagnostic, the
compiler then tries a transparent rule-match fallback and can solve
`a := a` through the def boundary.

The opposite direction works for the same reason:

```
def id (a: wff): wff = $ a -> a $;
axiom ax_expanded (a: wff): $ a -> a $;
theorem def_infer_actual (a: wff): $ id a $;
```

```
l1: $ id a $ by ax_expanded []
```

The distinction is that replay is still exact, while the surrounding
omitted-binder pipeline may fall back to a def-aware match when that is a
safe local inference problem.

### Harder def/rewrite cases still need metadata

Transparent inference does not mean the compiler unfolds defs and then
runs arbitrary rewrite search to discover binders. If the only way to
recover a binder is to expose a def body and then use rewrite, ACUI, view,
or recover/abstract structure, the rule should say so with the relevant
metadata. Explicit binders are still the simplest way to disambiguate
cases that are not local transparent matches.

### Higher-level solver paths are separate

The examples above are local transparent matches after exact replay has
failed. They do not require the heavier solver.

Higher-level solver paths such as `@view`-guided matching,
normalization-aware inference, and structural inference under an `@acui`
combiner may still use separate def-aware logic when they are solving a
different kind of comparison problem. This structural path now respects the
declared fragment semantics: AU, ACU, AUI, or ACUI. In particular, a rule
with `@view` or `@normalize` does not have to live or die by raw unify
replay: the compiler may switch to a `RuleMatchSession`-based path that can
compare through defs when that is part of the intended rule behavior.

### Ambiguity is still constrained

Def-aware higher-level inference still does **not** mean the compiler makes
arbitrary guesses when several solutions remain possible.

For ordinary non-structural binders, unresolved ambiguity remains an
inference failure. For structural binders under an `@acui` combiner, the
solver ranks surviving solutions by minimal structural residual. If more
than one distinct solution survives, the compiler chooses the ranked
solution and emits an ambiguity warning describing the alternatives.

---

## Interaction with `@view`, `@recover`, and `@abstract`

`@view` matching is def-aware as well.

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

After the initial view match, `@recover` and `@abstract` work from the
resolved view state rather than from eagerly-finalized theorem expressions.
That matters for hidden-dummy defs: matching across an unfolded def may create
match-local symbolic witnesses, and derived bindings are allowed to inspect the
resolved structure those witnesses justify without forcing them to escape early
into theorem space.

If raw structural comparison is not enough, derived bindings get one narrow
retry path that unfolds concrete defs without hidden dummy args and then
canonicalizes. This is enough for many unfold-then-rewrite recovery cases, but
it is still not a general "rewrite through defs everywhere" mechanism. See
`docs/view_recover.md` for the full pipeline.

---

## Interaction with `@normalize`

Transparent def unfolding and `@normalize` solve different problems.

- transparent def unfolding bridges **defined** and **expanded** forms
- `@normalize` bridges expressions related by registered rewrite,
  congruence, and ACUI rules

They compose in a limited way. The checker can compare normalized expressions
and can still bridge a def gap afterwards when ordinary transparent conversion
is enough. But the normalizer does **not** generally unfold defs first in order
to discover more rewrites. Rewriting still works on the visible instantiated
expression.

If you need witness recovery only after an unfold / rewrite alignment, that is
usually a job for `@view` plus `@recover` or `@abstract`, not for plain
`@normalize` alone.

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

What it does **not** do is generally unfold a def first just to expose a new
rewrite redex. If the required rewrite only becomes visible after def
exposure, that case is currently outside the ordinary normalization path.

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

The checker can build the same normalized conversion for hypothesis
references that final theorem-application validation uses. In practice,
the cited reference may be normalized and then bridged by transparent
unfolding before it is fed into the theorem application. This can happen
when the conversion is provable even if the consuming rule did not mark
that specific hypothesis with `@normalize`.

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
- The frontend does not generally rewrite *through* defs in order to expose new
  rewrite redexes.
- Omitted-binder inference still requires a determined solution. Ordinary
  ambiguity can fail the line, while structural ACUI ambiguity is ranked by
  minimal residual context and reported as a warning when alternatives remain.
- The normalizer still has the same step limit and termination caveats as the
  rest of the rewrite system.

In short:

- use **transparent def unfolding** when you want proof authors to move freely
  between defined and expanded forms at theorem-application boundaries
- do **not** assume that `@normalize` will unfold defs first in order to
  discover more rewrites
