# `@view` and `@recover`

These annotations let the proof compiler recover rule arguments from the
shape of a proof line, even when ordinary unify-style inference is not a
good fit.

They are frontend features. The compiler uses them to elaborate an
ordinary theorem application. The trusted verifier does not see a
special `@view` or `@recover` opcode.

## Why `@view` exists

Some rules are easier to apply from an alternate surface shape than from
their raw binder list.

A simple example is modus ponens:

```mm0
--| @view (a b: wff): $ a -> b $ > $ a $ > $ b $
axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
```

With that annotation, a proof line can omit explicit binder assignments:

```proof
l5: $ a -> a $ by ax_mp [l4, l2]
```

The compiler matches the line assertion and referenced hypotheses
against the view, solves `a` and `b`, and then applies `ax_mp` with the
resulting concrete bindings.

Without `@view`, the compiler would still try ordinary inference, but
`@view` gives a more direct pattern for the rule application.

## `@view`

### Syntax

Attach `@view` to an axiom or theorem annotation block:

```mm0
--| @view {x: set} (t: set) (p: wff x) (q: wff): $ A. x p -> q $
axiom ax_inst {x: set} (t: set) (p: wff x): $ A. x p -> sb t x p $;
```

The text after `@view` is parsed as a theorem-like signature:

- it may declare binders
- it has zero or more hypotheses
- it has one conclusion

In other words, it looks like the right-hand side of an `axiom` or
`theorem` declaration, but without the keyword and name.

### Binder mapping

A view binder is matched to a real rule binder by name.

If a view binder name matches one of the annotated rule's binder names,
it is treated as another way to solve that rule argument.

If a view binder name does not match any real rule binder, it is a
view-local phantom binder. Phantom binders can still be solved while
matching the view, and `@recover` can refer to them, but they are not
emitted as theorem arguments.

In this example:

```mm0
--| @view {x: set} (t: set) (p: wff x) (q: wff): $ A. x p -> q $
axiom ax_inst {x: set} (t: set) (p: wff x): $ A. x p -> sb t x p $;
```

- `x`, `t`, and `p` are real rule binders
- `q` is a phantom binder that exists only in the view

### Application order

When the compiler checks a proof line for a rule with `@view`, it uses
this order:

1. Parse any explicit named bindings from the proof line.
2. If the application is simple, match the proof line assertion and refs
   directly against the view.
3. If omitted-bindings require normalization-aware inference, feed the
   view constraints into the frontend solver together with the raw rule
   constraints.
4. Copy any solved real binders from the view into the rule bindings.
5. Run `@recover` inside the solver's fixed-point loop when enough view
   binders are known.
6. Validate the final bindings against the rule's sort and boundness
   constraints.

This means `@view` is partial and compositional.

It does not replace explicit bindings, and it does not have to solve
everything by itself.

### Explicit bindings are allowed

`@view` does not forbid explicit assignments.

For example, this is valid:

```proof
l4: $ (a -> (a -> a)) -> (a -> a) $ by ax_mp
  (a := $ a -> ((a -> a) -> a) $,
   b := $ (a -> (a -> a)) -> (a -> a) $) [l3, l1]
```

The compiler seeds the rule bindings from the explicit assignments and
then runs the view matcher. If the view would solve a real binder to a
different expression, the application fails with a binding-conflict
error.

### Hypothesis count

A view must have the same number of hypotheses as the underlying rule.

The point of the view is to give another shape for matching the same
rule application, not to add or remove cited refs.

### Validation still happens

Bindings inferred through a view are still checked against the rule's
actual binder declarations.

So `@view` does not bypass sort or boundness constraints.

This matters for rules like generalization:

```mm0
--| @view {x: nat} (p: wff x): $ p $ > $ A. x p $
axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
```

A proof line such as:

```proof
l1: $ A. n p $ by ax_gen [#1]
```

still fails, because the solved binder for `x` is not a bound variable of
the right kind.

## `@recover`

### Why it exists

Sometimes a useful witness is visible in the view shape, but not in the
final theorem conclusion.

This comes up when a rule's raw conclusion will later be normalized.
Before normalization, the witness is present in some structured term.
After normalization, it may disappear into a simpler expression.

`@recover` lets the compiler reconstruct a real rule binder from a
phantom binder and a structural pattern inside the view.

### Syntax

`@recover` must appear after a preceding `@view` on the same rule:

```mm0
--| @view {x: set} (t: set) (p: wff x) (q: wff): $ A. x p -> q $
--| @recover t q p x
--| @normalize conc
axiom ax_inst {x: set} (t: set) (p: wff x): $ A. x p -> sb t x p $;
```

The four names mean:

- `target`: the real rule binder to solve
- `source`: a solved concrete view expression
- `pattern`: another solved concrete view expression that contains the
  hole binder
- `hole`: the designated hole inside the pattern

All four names refer to binders from the `@view`, not directly to the
rule.

The target must correspond to a real rule binder. The target and hole
must also have the same sort.

### Intuition

Think of `@recover t q p x` as saying:

- we know the concrete expression matched for `q`
- we know the concrete expression matched for `p`
- inside the pattern for `p`, the binder `x` marks where `t` should be
  found
- walk both concrete expressions in parallel and extract the subtree of
  `q` that sits where `x` appears inside `p`

### Structural algorithm

The compiler does the following:

1. Take the solved concrete expressions for `source` and `pattern`.
2. Traverse them in parallel.
3. Whenever the concrete `pattern` expression reaches the concrete value
   of `hole`, record the corresponding subtree from `source` as a
   candidate for `target`.
4. If the hole occurs more than once, all candidates must agree.
5. If the structures do not line up, recovery fails.
6. If no hole occurrence is found, recovery fails.

If the target binder already has an explicit binding, recovery leaves it
alone.

## Worked example

This is the main motivating shape:

```mm0
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

Now consider this proof line:

```proof
l1: $ A. x (P x) -> P u $ by ax_inst []
```

The raw rule conclusion is `sb t x p`, so plain omitted-binder inference
cannot read `t` directly from the line assertion `P u`.

But the view binds:

- `p` to `P x`
- `q` to `P u`
- `x` to the bound variable `x`

Then `@recover t q p x` compares `q = P u` with `p = P x`, sees that the
hole `x` sits under `P`, and extracts the corresponding subtree `u` from
`q`. So it solves `t := u`.

After that, the compiler can instantiate the real rule and normalize its
conclusion as usual.

## Limits and intended use

`@view` and `@recover` are deliberately narrow.

They are good for:

- theorem applications whose "natural" user-facing shape differs from
  the raw binder list
- rules whose binders are visible from the line and refs by structural
  matching
- rules where normalization hides a witness that can still be recovered
  from a designated pattern

They are not a general higher-order inference mechanism.

In particular:

- `@view` only matches the proof line assertion and cited refs
- `@recover` only performs structural subtree recovery relative to one
  designated hole binder
- any real rule binder left unsolved after view and ordinary inference is
  still an error

## Interaction with other annotations

`@view` and `@recover` fit into the same frontend elaboration model as
`@normalize`.

A typical pipeline is:

1. parse explicit bindings
2. feed raw-rule and view constraints into inference
3. run recover rules inside the solver loop
4. obtain concrete real rule binders
5. instantiate the real rule
6. normalize marked hypotheses or conclusion
7. emit ordinary proof lines

If a rule application does not need normalization-aware inference, the
compiler can still use the simpler direct path for `@view` matching.

The trusted verifier only checks the resulting ordinary theorem
applications.

## Interaction with structural contexts

`@view` is often the cleanest way to expose a user-facing rule shape for
systems with first-class contexts.

For example, a raw rule may mention a context combiner explicitly:

```mm0
axiom imp_intro (g: ctx) (a b: wff): $ nd (g , a) b $ > $ nd g (a -> b) $;
```

When the context combiner is annotated with:

```mm0
--| @acui ctx_assoc ctx_comm emp ctx_idem
```

both inference and post-inference checking can treat contexts modulo
assoc / comm / unit / idem. That lets proof lines omit pointless
structural bookkeeping while still elaborating to an ordinary theorem
application plus generated conversion lines.
