# Witness-driven def exposure and rewriting

## Purpose

This note records a limitation of the current frontend and the shape of a
more general fix.

The motivating unsupported proof case is:

- `unsupported_def_unfold_then_rewrite_concl`

That case needs the compiler to accept a rule application whose
instantiated conclusion is a hidden-dummy def, but where the rewrite that
would justify the user-written line only appears after that def is exposed.

## Current model

Today the frontend has two separate mechanisms.

### 1. Transparent def comparison

`def_ops.zig` supports witness-driven comparison through defs.

This is used for theorem-application checking, `@view` matching, final
conclusion checking, and several inference helpers.

For defs with hidden dummy arguments, exposure is still targeted:

- there is no standalone API that just opens the def body
- hidden dummies are only realized while solving a concrete matching or
  conversion problem

### 2. Proof-producing normalization

`normalizer.zig` supports rewrites, congruence, and ACUI structural
normalization.

Rewrite lookup is driven by the visible head symbol of the current
expression. The normalizer does not generally unfold defs first in order
to discover more rewrite opportunities.

## The missing capability

The unsupported case needs something neither mechanism currently does on
its own:

- expose a def toward a concrete comparison problem
- keep any hidden-dummy variables symbolic while doing so
- allow newly exposed rewrites to fire inside the exposed witness
- continue matching against the target without forcing global
  normalization

This is broader than a checker-side special case for one `@normalize`
conclusion. A realistic design would have to work during witness-driven
comparison itself, not only after the comparison has already committed to a
concrete witness.

## Why a small patch is the wrong fix

A narrow patch for the current unsupported case would likely teach the
checker to:

- expose the outer def once
- normalize the exposed result
- then compare again

That is not a good semantic center.

It would overfit a single artificial case and would not address the more
interesting situations where:

- rewrites matter in non-head positions
- exact matching should still win if it already succeeds
- def exposure and matching need to interleave before hidden-dummy
  witnesses are materialized

## The right general direction

If this feature becomes important, the right place to add it is inside the
witness-driven comparison engine.

The core idea would be:

- while opening a def toward a target, keep the exposed form symbolic
- allow rewrite opportunities exposed by that symbolic witness to
  participate in matching
- do this without turning the whole frontend into a globally normalized or
  transparently rewriting system

In practice, that likely means extending the internal match session in
`def_ops.zig`, rather than adding more checker-side recovery logic.

## Non-goals for the current system

The current frontend deliberately does not support:

- general rewrite search through defs
- automatic def exposure just to discover more rewrites
- root-level special cases for one hidden-dummy def pattern

Until a more general witness-driven design exists, proof cases in this
family should stay classified as unsupported rather than as ordinary bugs.
