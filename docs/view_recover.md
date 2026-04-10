# `@view`, `@recover`, and `@abstract`

These annotations let the proof compiler recover rule arguments from the
shape of a proof line, even when ordinary unification is not a good fit.
They are all frontend features: the trusted verifier sees only ordinary
theorem applications.

## Mental model

### The core problem

Every rule has a *raw form* — the conclusion as literally stated in the
`.mm0` file — and a *user-facing form* — the expression a proof author
actually wants to write. For simple rules these are the same thing, and
ordinary unification suffices to recover any omitted arguments. For more
complex rules, especially rules whose conclusions are subject to
`@normalize`, the two can diverge significantly.

Consider a universal instantiation rule:
```
--| @normalize conc
axiom ax_inst {x: set} (t: set) (p: wff x):
  $ A. x p -> sb t x p $;
```

The raw conclusion is `sb t x p` — a substitution term. After normalization
it reduces to something like `P u`, with `t` no longer syntactically visible.
Ordinary unification matches the user's line against the raw conclusion, so
it cannot recover `t` from `P u`. The user would be forced to supply `t`
explicitly every time.

`@view`, `@recover`, and `@abstract` address this problem in three ways,
covering progressively more complex shapes of "witness hidden by
normalization":

- **`@view`** provides an alternative surface shape for the rule that the
  compiler can match against the user's line and cited references. It solves
  the common case where the witness is directly readable from the user-facing
  form of the rule, even if it is not recoverable from the raw conclusion
  alone.

- **`@recover`** handles the case where normalization has buried the witness
  inside a structured term. It reconstructs the witness by walking the
  solved view expressions in parallel and extracting the subtree that
  corresponds to the hole.

- **`@abstract`** handles the case where the missing argument is not a
  subtree but a *one-hole context* — a shared surrounding structure that
  explains the difference between two solved expressions.

**`@fresh`** is a simpler companion documented in
`docs/fresh_binders.md`. It handles omitted *bound* binders that serve
only as local variables and cannot be recovered by any matching strategy.
`@fresh` chooses from the binder sort's `@vars` pool, reusing an
existing theorem-local dummy when one is available and absent from the
current concrete inputs.

### Elaboration pipeline

When the compiler processes a proof line, it determines the concrete rule
arguments in the following order:

1. **Explicit bindings** from the proof line are recorded first and cannot
   be overridden by later steps.
2. **`@fresh` annotations** fill omitted bound binders before
   inference begins. `@fresh` selects a suitable variable from the binder
   sort's `@vars` pool, preferring reuse when the chosen variable is
   absent from the current concrete inputs.
3. **`@view` matching** unifies the view's conclusion and hypotheses against
   the user's line and cited references, solving view binders. If a view
   binder maps to a real rule binder, the solution is copied across. When
   all arguments can be determined directly from the line and refs, this
   matching takes a simple direct path. When normalization-aware inference
   is needed — because some omitted binders can only be recovered after
   normalization — the view constraints are fed into the frontend solver
   together with the raw rule constraints.
4. **`@recover` and `@abstract` rules** run in a fixed-point loop over the
   view bindings, deriving additional binders from the ones already solved.
5. **Standard unification replay** fills any remaining omitted rule binders
   by replaying the rule's unify stream against the user's line and refs.
6. **Validation** checks all resolved bindings against the rule's sort and
   boundness constraints.
7. **Normalization** (if `@normalize` is present) normalizes the instantiated
   conclusion and/or hypotheses and checks against the user's expressions.

If any real rule binder is still unresolved after all of these steps, the
compiler reports an inference failure.

### What users can rely on

The practical contract for these annotations is:

- explicit bindings still win; `@view`, `@recover`, and `@abstract` do not
  override a user-written `(name := ...)` assignment;
- `@view` only sees the proof line assertion and the cited references for that
  application;
- `@recover` and `@abstract` only run after `@view` has solved the binders they
  depend on;
- derived bindings work from the current resolved view state before any final
  representative projection or theorem-local dummy creation;
- raw structural matching is tried first, with one narrow unfold /
  canonicalize retry when that is needed to line up concrete structure; and
- if a real rule binder is still not determined after the full pipeline, the
  line is rejected.

So these annotations extend ordinary theorem application, but they do not turn
it into open-ended proof search.

---

## `@view`

### Purpose

`@view` declares an alternative signature that the compiler can match against
the user's proof line instead of the raw rule conclusion. This is useful when
the natural way to apply a rule differs from its literal statement — for
instance, when the raw conclusion contains unexpanded substitution terms that
are invisible in the normalized form the user writes.

This matching is also def-aware: if a view expects an expanded expression and
a cited line or user assertion uses a def, the compiler may unfold through
that boundary. See `docs/transparent_defs.md` for the def-specific rules.

### Syntax
```
--| @view <binders> : <hypotheses> > <conclusion>
```

The text after `@view` is parsed as a theorem-like signature: it may declare
binders, has zero or more hypotheses separated by `>`, and ends with a
conclusion. The whole annotation must fit on one line.
```
--| @view (a b: wff): $ a -> b $ > $ a $ > $ b $
axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
```

A view must declare exactly as many hypotheses as the underlying rule, since
it is providing an alternative shape for the same application, not adding or
removing cited references.

### Binder mapping and phantom binders

Each view binder is matched to a rule binder by name. If the names agree, the
view binder is *mapped*: solving it in the view also solves the corresponding
rule binder. If a view binder name does not appear among the rule's binders,
it is a *phantom* binder — local to the view, used only to help recover other
binders via `@recover` or `@abstract`.

| View binder | Rule binder with same name exists? | Effect |
|-------------|-------------------------------------|--------|
| Mapped | Yes | Solving it solves the rule binder |
| Phantom | No | Local to view; used by `@recover`/`@abstract` |

**Example:**
```
--| @view {x: set} (t: set) (p: wff x) (q: wff): $ A. x p -> q $
axiom ax_inst {x: set} (t: set) (p: wff x): $ A. x p -> sb t x p $;
```

Here `x`, `t`, and `p` are mapped binders (they appear in the rule). `q` is
a phantom binder: it captures what the user wrote as the consequent of the
implication, which after normalization of `sb t x p` will be the normalized
form. The phantom `q` can then be used by `@recover` to extract `t`.

### Explicit bindings coexist with `@view`

Explicit binder assignments on the proof line take precedence. If the user
supplies `(t := $ u $)` and the view would solve `t` to a different value,
the compiler reports a binding conflict. Partial explicit assignments are
fine: the view fills in what is missing.

### Validation still applies

Bindings inferred through a view are checked against the rule's actual sort
and boundness constraints. A view does not relax these requirements. For
example, a rule requiring a bound variable for `x` will still reject a
non-bound expression even if the view matched successfully:
```
--| @view {x: nat} (p: wff x): $ p $ > $ A. x p $
axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
```

A proof line writing `A. n p` (where `n` is a regular variable, not bound)
will fail the boundness check even though the view matched `x` to `n`.

---

## `@recover`

### Purpose

`@recover` handles the case where the witness for a rule binder is visible
inside a view expression but has been structurally buried. After `@view`
matching has solved both a *source* expression (what the user wrote) and a
*pattern* expression (the corresponding raw form), `@recover` walks them in
parallel and extracts the subtree of the source that sits where a designated
*hole* binder appears in the pattern.

The motivating case is a normalized instantiation rule: the raw conclusion
contains `sb t x p` and the user writes `P u`. After view matching, the
compiler has solved `p` to `P x` (the raw body) and `q` to `P u` (the
normalized result). `@recover` compares these two expressions, finds `x`
inside `p`, and extracts the corresponding subtree `u` from `q` as the value
of `t`.

### Syntax

`@recover` must follow a `@view` annotation on the same rule:
```
--| @view {x: set} (t: set) (p: wff x) (q: wff): $ A. x p -> q $
--| @recover t q p x
axiom ax_inst {x: set} (t: set) (p: wff x): $ A. x p -> sb t x p $;
```

The four names are positional:

| Position | Name | Meaning |
|----------|------|---------|
| 1 | `target` | The real rule binder to solve |
| 2 | `source` | A solved view expression (what the user wrote) |
| 3 | `pattern` | A solved view expression containing the hole |
| 4 | `hole` | The binder that marks where `target` should be found |

All four names refer to view binders. The target must map to a real rule
binder. The target and hole must have the same sort.

### Structural algorithm

The compiler walks the current resolved expressions for `source` and
`pattern` in parallel:

1. Whenever the pattern expression reaches the current resolved value of
   `hole`, record the corresponding subtree of the source as a candidate for
   `target`.
2. If `hole` occurs more than once, all candidates must agree.
3. If the structures diverge (different head terms, different arities), the
   recovery fails.
4. If no occurrence of `hole` is found, the recovery fails.

If `target` already has an explicit binding, recovery is skipped for that
binder.

### What `@recover` can and cannot do

A few behavioral details are worth keeping in mind:

- `@recover` only runs once `source`, `pattern`, and `hole` are already solved
  in the view state.
- It works from the current resolved view expressions, not from eagerly-
  finalized theorem expressions.
- It first tries direct structural comparison. If that fails, it retries after
  narrowly preprocessing the compared expressions by unfolding concrete defs
  without hidden dummy args and canonicalizing the result.
- It does not invent fresh theorem-local dummies just to make a hidden witness
  concrete. Hidden-dummy witnesses stay match-local until the final
  rule-instantiation path decides they really need to escape.

### Worked example
```
term all {x: set} (p: wff x): wff; prefix all: $A.$ prec 41;
term pred (t: set): wff; prefix pred: $P$ prec 50;
term sb (t: set) {x: set} (p: wff x): wff;

--| @rewrite
axiom sb_pred (t: set) {x: set}: $ sb t x (P x) <-> P t $;

--| @view {x: set} (t: set) (p: wff x) (q: wff): $ A. x p -> q $
--| @recover t q p x
--| @normalize conc
axiom ax_inst {x: set} (t: set) (p: wff x): $ A. x p -> sb t x p $;
```

With this setup, a proof line like:
```
l1: $ A. x (P x) -> P u $ by ax_inst []
```

is elaborated as follows:

- The view conclusion `A. x p -> q` matches the user's line `A. x (P x) -> P u`,
  solving `p` to `P x` and `q` to `P u`.
- `@recover t q p x` compares `q = P u` with `p = P x`: the hole `x` appears
  under `P`, and the corresponding subtree in `q` is `u`. So `t` is solved
  to `u`.
- The compiler instantiates `ax_inst` with `t = u`, `p = P x`, producing the
  raw conclusion `sb u x (P x)`.
- `@normalize conc` reduces `sb u x (P x)` via `sb_pred` to `P u`, which
  matches the user's assertion.

---

## `@abstract`

### Purpose

`@abstract` addresses a related but structurally different problem. Where
`@recover` extracts a *subtree*, `@abstract` recovers a *one-hole context*
— the shared surrounding structure that explains the difference between two
solved expressions. The motivating shape is Leibniz-style substitution: given
`C[a]` on the left and `C[b]` on the right, recover the context `C[x]`.

This arises naturally with context-sensitive rewrite rules where the rule
operates on `sb a x r` and `sb b x r`, but the user writes the already-
normalized forms. After view matching the compiler has the normalized left
and right expressions; `@abstract` walks them in parallel, identifies where
`a` and `b` appear, and reconstructs `r` by replacing those positions with
the hole variable `x`.

### Syntax

`@abstract` must follow a `@view` annotation on the same rule:
```
--| @view {x: wff} (a b: wff) (r: wff x) (p q: wff): $ a <-> b $ > $ p $ > $ q $
--| @abstract r p q x a b
--| @normalize hyp1 conc
axiom ax_ctx {x: wff} (a b: wff) (r: wff x):
  $ a <-> b $ > $ sb a x r $ > $ sb b x r $;
```

The six names are positional:

| Position | Name | Meaning |
|----------|------|---------|
| 1 | `target` | The real rule binder to solve (the context) |
| 2 | `left` | A solved view expression containing `left_plug` |
| 3 | `right` | A solved view expression containing `right_plug` |
| 4 | `hole` | The binder that will mark the abstracted position |
| 5 | `left_plug` | The expression abstracted to `hole` on the left |
| 6 | `right_plug` | The corresponding expression on the right |

All six names refer to view binders. The target must map to a real rule
binder. The target and hole must have the same sort. The hole and both plug
binders must also have the same sort.

### Structural algorithm

The compiler walks the current resolved expressions for `left` and `right`
in parallel:

1. If the current pair is exactly `(left_plug, right_plug)`, return the
   current resolved value of `hole`. This is the abstracted position.
2. If the current pair is the same variable on both sides, keep it as-is.
3. If the current pair has the same term constructor and arity on both sides,
   recurse on the arguments and rebuild.
4. Otherwise fail — the structures are incompatible and cannot be explained
   by a single plug pair.

At least one occurrence of the plug pair must be found. Multiple occurrences
are allowed; each becomes a separate use of the hole binder in the recovered
context, which is the correct behavior for multi-hole substitution.

### What `@abstract` can and cannot do

The same operational limits apply here:

- `@abstract` only runs once `left`, `right`, `hole`, and both plug binders
  are already solved in the view state.
- It works from the current resolved view expressions, not from eagerly-
  finalized theorem expressions.
- It first tries direct structural comparison. If that fails, it retries after
  the same narrow preprocess step used by `@recover`: unfold concrete defs
  without hidden dummy args, then canonicalize.
- It does not allocate theorem-local dummies merely to expose hidden witness
  structure.

### Example
```
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
term top: wff;
term sb (t: wff) {x: wff} (r: wff x): wff;

--| @rewrite
axiom sb_var (t: wff) {x: wff}: $ sb t x x <-> t $;
--| @rewrite
axiom sb_top (t: wff) {x: wff}: $ sb t x top <-> top $;
--| @rewrite
axiom sb_imp (t: wff) {x: wff} (a b: wff x):
  $ sb t x (a -> b) <-> (sb t x a -> sb t x b) $;

--| @view {x: wff} (a b: wff) (r: wff x) (p q: wff): $ a <-> b $ > $ p $ > $ q $
--| @abstract r p q x a b
--| @normalize hyp1 conc
axiom ax_ctx {x: wff} (a b: wff) (r: wff x):
  $ a <-> b $ > $ sb a x r $ > $ sb b x r $;
```

A proof line:
```
l1: $ b -> top $ by ax_ctx [#1, #2]
```

where `#1 : a <-> b` and `#2 : a -> top`.

- The view matches `p` to `a -> top` and `q` to `b -> top`.
- `@abstract r p q x a b` walks `(a -> top, b -> top)` in parallel. At the
  head of the implication, the left child is `a` and the right is `b` —
  exactly the plug pair. The hole `x` is substituted there, recovering
  `r = x -> top`.
- The compiler instantiates `ax_ctx` with `r = x -> top`, producing
  hypotheses `sb a x (x -> top)` and conclusion `sb b x (x -> top)`.
- `@normalize hyp1 conc` reduces these via `sb_var`, `sb_top`, and `sb_imp`
  to `a -> top` and `b -> top` respectively, matching `#2` and the user's
  assertion.

---

## How the annotations compose

The full elaboration pipeline for a proof line applying a rule with view
annotations is:

1. **Parse explicit bindings.** Any `(name := $ expr $)` assignments are
   recorded. These are final and cannot be overridden.

2. **Seed `@fresh` binders.** For each bound binder with this
   annotation and no explicit assignment, fill it before view matching.
   `@fresh` chooses from the binder sort's `@vars` pool, preferring
   reuse when the chosen variable is absent from the current concrete
   inputs.

3. **Match the `@view`.** Unify the view's conclusion and hypotheses against
   the user's line and cited references. Map solved view binders to their
   corresponding rule binders. Check for conflicts with explicit bindings.
   When all arguments can be determined directly from the line and refs, this
   matching takes a simple direct path. When normalization-aware inference is
   needed — because some omitted binders can only be recovered after
   normalization — the view constraints are fed into the frontend solver
   together with the raw rule constraints.

4. **Run `@recover` and `@abstract` in a fixed-point loop.** Each derived-
   binding rule checks whether its required source expressions are solved yet;
   if so, it attempts to solve its target. The loop continues until no
   further progress is made.

5. **Run standard unification replay.** Replay the rule's unify stream
   against the user's line and refs to fill any remaining unsolved rule
   binders.

6. **Validate all bindings.** Check sort and boundness constraints for every
   resolved binder.

7. **Instantiate the rule** with the final concrete bindings.

8. **Normalize** marked hypotheses and/or the conclusion (if `@normalize` is
   present), check against the user's expressions, and emit transport steps.

At any step, a conflict or failure produces a diagnostic identifying the
annotation responsible.

---

## Unfold / rewrite behavior in the view pipeline

The points above describe the user-facing model. For rules that interact with
transparent defs, rewrites, and normalization, the internal process is a bit
more specific.

### 1. `@view` seeding happens before ordinary omitted-binder inference

When a proof line omits some rule binders, the compiler first
tries to seed as many of them as it can from the view. This happens in a
def-aware matching session, before the general omitted-binder solver runs.

The important consequence is that `@view`, `@recover`, and `@abstract` are not
an optional postprocessing step. They are part of how the solver gets its
starting information.

### 2. View matching is def-aware, and may use semantic steps

The initial view pass matches:

- the view conclusion against the user's proof line assertion, and
- each view hypothesis against the cited reference expression for that slot.

Each part first tries transparent matching. If that fails, the matcher may use
semantic search. In practice this means the view layer can look through
transparent defs and can also follow registered rewrite / structural steps when
those are needed to relate the view shape to the concrete proof expression.

So, for example, a view can match a user-facing expression that only appears
*after* a def body is unfolded and a rewrite is applied.

### 3. Bindings stay on a resolved, non-escaping path during view reuse

After the initial view match, the compiler resolves the current optional view
bindings, but it does **not** immediately finalize them into main-theorem
expressions.

That distinction matters for hidden-dummy defs.

When a def body contains hidden binders, matching against the expanded body may
create symbolic dummy slots inside the matching session. Those slots are useful
for continuing the match, but they are not yet a concrete witness that should
be committed to the theorem.

So the view pipeline intentionally prefers a *resolved* result:

- if a binder has a concrete expression, the resolved binding is that expr;
- if a binder still depends on unresolved hidden symbolic witnesses, the
  resolved binding remains `null`;
- no fresh theorem-local dummy vars are allocated merely because the view was
  inspected.

Only explicit finalization paths are allowed to escape from symbolic match
state back into theorem-local expressions.

### 4. `@recover` and `@abstract` run on the resolved bindings

Derived bindings are applied after the initial view match.

- `@recover` compares a solved source expr against a solved pattern expr and
  extracts the subtree that sits where the hole binder occurs.
- `@abstract` compares solved left / right exprs and reconstructs the shared
  one-hole context that explains the plug pair.

The key point is that these operations run on the resolved expressions coming
out of view matching, not on eagerly-finalized witnesses.

That keeps the derived-binding step from inventing fresh theorem dummies just
because a hidden witness has not been pinned down yet.

For hidden-dummy defs, the recover pattern may still contain symbolic dummy
slots rather than ordinary theorem expressions. In that case the derived-
binding step follows the current dummy-witness snapshot from the same match
session, not just the raw dummy-slot numbers. This matters because repeated def
exposure can allocate fresh slot numbers for the same hidden binder; the
resolved witness is the stable thing, not the temporary slot id.

### 5. Derived bindings get an unfold / canonicalize retry path

Raw structural comparison is tried first. If that fails, the compiler retries
with a preprocessed version of the relevant expressions.

That preprocessing is intentionally narrow:

- repeatedly unfold concrete defs that have no hidden dummy args,
- recursively preprocess children,
- canonicalize with the rewrite / ACUI registry, and then
- try structural recovery / abstraction again.

This is the path that lets `@recover` or `@abstract` succeed when the source
and pattern only line up *after* a concrete def has been exposed and rewrite /
ACUI normalization has aligned the two shapes.

In other words, the annotations do not require the raw stored exprs to already
have identical syntax. They get one more chance after the compiler has exposed
and canonicalized the relevant concrete structure.

### 6. Replaying refs is useful; replaying the conclusion is dangerous

After the first full view match, the compiler replays the cited references once
more against the view hypotheses. This is not a second proof check; it is a
heuristic meant to bias still-symbolic witnesses toward the concrete cited proof
shapes.

This helps because the references are usually where the concrete information
needed by `@recover` / `@abstract` lives.

The compiler deliberately does **not** replay the view conclusion a second
time.

That extra conclusion replay looks harmless, but under unfold / rewrite it can
re-open the same transparent def body again, which may allocate a fresh set of
hidden symbolic dummy slots. Those fresh slots are distinct from the ones that
were created during the first pass, so they can fight the bindings already in
session state instead of refining them.

This was exactly the failure mode in the unfold-then-rewrite recover cases: the
first conclusion match found the right structure, and the second conclusion
replay destabilized it by introducing fresh hidden symbolic witnesses.

So the current rule is:

- do the full conclusion match once,
- replay only the refs, and
- let explicit guidance refine unresolved derived bindings.

### 7. Unresolved recover patterns are guided toward the cited source expr

After the initial replay of the refs, the compiler runs derived bindings in a
small fixed-point loop.

If a `@recover` target is still unresolved, the compiler takes the recover
pattern binder and tries to guide its symbolic binding toward the concrete
source expression from the cited proof. After that guidance step, it resolves
bindings again and reruns derived binding application.

This is more precise than replaying the whole conclusion again:

- it acts only on the binder that `@recover` needs,
- it uses the concrete source expr that actually contains the missing witness,
  and
- it avoids reopening the conclusion-side def body and minting fresh hidden
  dummy slots.

### 8. The general solver starts from the view-derived seeds

Once the view pipeline has done everything it can, the resulting rule bindings
are copied into the ordinary omitted-binder inference path.

Two details matter here:

- if view seeding already solved every omitted binder, the compiler validates
  those bindings immediately and returns;
- otherwise the general solver starts from the seeded bindings, not from the
  original unseeded partial binding array.

Additionally, bindings that came directly from the view are treated as exact
seeds, while bindings produced by `@recover` / `@abstract` are allowed to act
as semantic seeds. This lets later matching respect the information the view
already discovered without forcing unnecessary re-parsing of the same witness.

### 9. Where finalization actually happens

The final concrete instantiation of the rule still happens later, after the
view-derived seeds and the ordinary solver have agreed on the rule binders.

That is the stage where the compiler may need to finalize a symbolic binding
into a concrete theorem expression. If a hidden symbolic witness truly has to
escape into theorem space, this is where that happens.

The practical guideline is simple:

- matching, view reuse, `@recover`, and `@abstract` should stay resolved and
  non-escaping for as long as possible;
- only the final rule-instantiation path should force escape.

For bound witnesses, that final escape path reuses or allocates a token from
the sort's `@vars` pool, using the same dependency-aware policy as `@fresh`.
If no suitable pool entry exists, the witness remains unresolved instead of
silently inventing a theorem-local dummy.

This keeps the compiler from spending theorem-local dummy slots on witnesses
that were only temporary artifacts of def unfolding.

### 10. Authoring guidance for annotated rules

When writing a rule that combines `@view` with unfold / rewrite behavior, the
annotations are easiest to reason about if you keep the roles separate:

- use `@view` to expose the user-facing shape that the proof line and refs will
  actually mention;
- use `@recover` when a missing witness is present as a subtree of some solved
  concrete expr;
- use `@abstract` when the missing witness is a context shared by two solved
  concrete exprs;
- prefer cited refs, not the conclusion, as the concrete evidence that should
  drive recover / abstract guidance;
- and avoid designs that require a hidden def witness to escape early, because
  that usually means the rule is leaning on implementation artifacts rather
  than on concrete proof data.

---

## Interaction with structural contexts

`@view` is often the cleanest way to expose a user-facing rule shape for
systems with first-class contexts — natural deduction, sequent calculus, or
resource-sensitive logics where a context combiner collects hypotheses.

Consider a raw rule that mentions a context combiner explicitly:
```
axiom imp_intro (g: ctx) (a b: wff): $ nd (g , a) b $ > $ nd g (a -> b) $;
```

When the context combiner is annotated with:
```
--| @acui ctx_assoc ctx_comm emp ctx_idem
term join (g h: ctx): ctx;
```

both inference and post-inference checking treat contexts modulo assoc /
comm / unit / idem. This means a proof line can write the hypotheses in any
order and omit redundant structural bookkeeping — the compiler normalizes the
context to its canonical form, checks that it matches, and emits the
necessary conversion steps. The user sees a clean, order-independent rule
application; the verifier sees a fully elaborated sequence of ordinary
theorem applications.

`@view` and `@acui` therefore combine naturally: `@view` handles the
user-facing shape of the rule's *formula* arguments, while `@acui` handles
the structural normalization of the *context* arguments. Neither requires
the other, but systems that use both get proof lines that are nearly as
concise as informal natural deduction.

---

## Limits and intended use

These annotations are deliberately narrow in scope. They are well suited for:

- Rules whose natural user-facing shape differs from the raw binder list.
- Rules where normalization hides a witness that can be recovered by
  structural matching against the view.
- Rules where the missing witness is a shared one-hole context recoverable
  from two solved expressions.

They are **not** a general higher-order inference mechanism:

- `@view` only matches the proof line assertion and cited references.
- `@fresh` only fills omitted *bound* binders from a finite `@vars`
  pool, reusing theorem-local dummies when they are absent from the
  current concrete inputs.
- `@recover` performs structural subtree recovery relative to exactly one
  designated hole binder.
- `@abstract` performs structural one-hole context recovery for exactly one
  designated plug pair.

Any real rule binder left unsolved after the full pipeline is still an error.
The annotations extend what the compiler can infer; they do not remove the
requirement that every binder be determined.
