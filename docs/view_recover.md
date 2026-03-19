# `@view`, `@recover`, `@abstract`, and `@dummy`

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

**`@dummy`** is a simpler companion that handles a different problem: omitted
*bound* binders that serve only as fresh local variables and cannot be
recovered by any matching strategy. It tells the compiler to allocate a
fresh dummy variable rather than requiring the user to name one.

### Elaboration pipeline

When the compiler processes a proof line, it determines the concrete rule
arguments in the following order:

1. **Explicit bindings** from the proof line are recorded first and cannot
   be overridden by later steps.
2. **`@dummy` annotations** fill any omitted bound binders with fresh
   theorem-local dummy variables, before inference begins.
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

The compiler walks the concrete expressions for `source` and `pattern` in
parallel:

1. Whenever the pattern expression reaches the concrete value of `hole`,
   record the corresponding subtree of the source as a candidate for `target`.
2. If `hole` occurs more than once, all candidates must agree.
3. If the structures diverge (different head terms, different arities), the
   recovery fails.
4. If no occurrence of `hole` is found, the recovery fails.

If `target` already has an explicit binding, recovery is skipped for that
binder.

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

The compiler walks the concrete expressions for `left` and `right` in
parallel:

1. If the current pair is exactly `(left_plug, right_plug)`, return the
   concrete value of `hole`. This is the abstracted position.
2. If the current pair is the same variable on both sides, keep it as-is.
3. If the current pair has the same term constructor and arity on both sides,
   recurse on the arguments and rebuild.
4. Otherwise fail — the structures are incompatible and cannot be explained
   by a single plug pair.

At least one occurrence of the plug pair must be found. Multiple occurrences
are allowed; each becomes a separate use of the hole binder in the recovered
context, which is the correct behavior for multi-hole substitution.

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

2. **Seed `@dummy` binders.** For each bound binder marked `@dummy` that
   has no explicit assignment, allocate a fresh dummy variable.

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
- `@dummy` only fills omitted *bound* binders with fresh local dummy
  variables.
- `@recover` performs structural subtree recovery relative to exactly one
  designated hole binder.
- `@abstract` performs structural one-hole context recovery for exactly one
  designated plug pair.

Any real rule binder left unsolved after the full pipeline is still an error.
The annotations extend what the compiler can infer; they do not remove the
requirement that every binder be determined.
