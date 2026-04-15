# Aufbau proof script format

This document describes the current text format accepted by the Aufbau
compiler for `.auf` proof scripts.

It is a project-level frontend format, not part of the MM0 core spec.
The MM0 and MMB format specs remain in `specs/mm0.md` and
`specs/mmb.md`.

Related docs:

- `docs/rewrite_system.md`
- `docs/transparent_defs.md`
- `docs/view_recover.md`
- `docs/fresh_binders.md`

In particular, `@alpha` and `@freshen` are frontend-only annotations used
for targeted alpha-renaming retries during rule application.

## Scope

The `.mm0` file remains the source of truth for:

- sorts
- terms and definitions
- theorem and axiom declarations
- theorem binders
- theorem hypotheses
- theorem conclusions
- notation and coercions

The `.auf` file supplies proof bodies for public theorems declared in the
`.mm0` file.

It may also declare top-level `lemma` blocks. These are proof-only local
rules. They may be cited by later proof blocks and are emitted as local
MMB theorems.

## Processing model

The compiler processes the `.mm0` file and the `.auf` file in statement
order.

This means:

- each public theorem block in the `.auf` stream must match the next
  public theorem declaration in the `.mm0` stream
- zero or more `lemma` blocks may appear before the next public theorem
  block
- proof blocks may reference only earlier proof lines in the same block
- proof blocks may reference only axioms, public theorems, and earlier
  lemmas already declared
- no forward references are permitted

The frontend therefore streams through the MM0 declarations and proof
blocks together. It does not build a separate global proof database
before checking begins.

## Comments and whitespace

Blank lines are ignored.

Line comments begin with `--` and run to the end of the line, matching
MM0 comment syntax. Standalone comment lines may appear between blocks or
between proof lines. Trailing comments are also allowed on theorem
headers, lemma headers, and proof lines.

Outside math strings, a proof line must stay on one physical line.
Newlines are allowed inside `$ ... $` math strings.

## Top-level blocks

An Aufbau script is a sequence of theorem blocks, lemma blocks, blank
lines, and comments.

```text
aufbau-script ::= (theorem-block | lemma-block | blank | comment)*
comment ::= '--' (any char except newline)* newline
```

### Theorem blocks

A public theorem block names the theorem being proved.

```text
theorem-block ::= theorem-name newline underline? newline* proof-line*
underline ::= '-' '-'+
```

The underline is optional and cosmetic. If present, the parser ignores
its exact length.

Example:

```text
main
----
l1: $ a -> a $ by id []
```

### Lemma blocks

A lemma block declares a proof-only local rule.

```text
lemma-block ::= 'lemma' identifier lemma-binders? ':' assertion-tail
                newline underline? newline* proof-line*

assertion-tail ::= formula ('>' formula)*
```

`lemma-binders?` and `assertion-tail` use the same binder and theorem-tail
syntax as MM0 assertions.

Example:

```text
lemma id (a: wff): $ a -> a $
---------------------------
l1: $ a -> a $ by ax_id (a := $ a $) []
```

## Proof lines

Each proof line has the form:

```text
proof-line ::= label ':' formula 'by' rule-name
               ('(' arg-bindings ')')?
               ('[' refs ']')?
               comment? newline*
```

Where:

- `label` is a local proof-line label
- `formula` is an MM0 math string, written as `$ ... $`
- `rule-name` is an axiom, public theorem, or earlier lemma name
  (possibly one that carries `@fallback` metadata)
- `arg-bindings` is an optional comma-separated named argument list
- `refs` is an optional comma-separated reference list

If the `[...]` section is omitted, it is treated as an empty reference
list. The checker still requires the final reference count to match the
cited rule's hypothesis count.

Example:

```text
l1: $ a -> a $ by ax_1 (a := $ a $, b := $ a $) []
l2: $ a $ by ax_mp (a := $ a $, b := $ a $) [#1, l1]
```

## References

References inside `[...]` may be either theorem hypotheses or previous
proof lines.

```text
ref ::= hyp-ref | line-ref
hyp-ref ::= '#' number
line-ref ::= identifier
```

Meaning:

- `#1`, `#2`, ... refer to the hypotheses of the theorem being proved
- inside a lemma block, `#1`, `#2`, ... refer to the lemma hypotheses
- `l1`, `l2`, ... refer to prior proof lines in the current block

Hypotheses are numbered in the order they appear in the theorem or lemma
header after MM0 parsing.

## Named argument bindings

Argument bindings are named substitutions for the binders of the cited
rule.

```text
arg-bindings ::= empty | arg-binding (',' arg-binding)*
arg-binding ::= binder-name ':=' formula
```

If explicit bindings are omitted, the compiler tries to infer every
missing binder from the line assertion, cited references, and any rule
metadata.

In the current implementation:

- the order of explicit bindings does not matter
- duplicate bindings are an error
- unknown binder names are an error
- if omitted bindings cannot be inferred, the proof line is rejected

## Rule application semantics

A proof line

```text
L: $ C $ by RULE (ARG_BINDINGS) [R1, ..., Rn]
```

is checked roughly as follows:

1. Resolve `RULE` to a previously declared axiom, theorem, or lemma.
2. Resolve and parse any explicit argument bindings.
3. Parse `$ C $` in the local assertion context.
4. Resolve `R1, ..., Rn` to theorem hypotheses or earlier proof lines.
5. Infer any omitted rule binders.
6. Instantiate the rule's hypotheses and conclusion with those concrete
   binders.
7. Compare the instantiated rule against the user's line and refs,
   allowing frontend features such as transparent defs, views, recover /
   abstract bindings, fresh binders, targeted alpha-freshening, and
   normalization when the rule's metadata permits them.
8. If that attempt fails and the cited rule has `@fallback`, retry the
   whole line with the fallback target, then continue through the
   fallback chain if needed.
9. Record label `L` as proving `C`.

The line formula is always explicit and must be written out by the user.
The compiler may elaborate the application internally, but it does not
infer the whole asserted formula from the cited rule.

Fallback metadata is resolved eagerly while processing the `.mm0` file,
so `@fallback target_rule` may refer only to a rule already in scope at
the annotation site. See `docs/rewrite_system.md` for the annotation
details.

## Final-line condition

A public theorem block is accepted if and only if its final proof line
proves the theorem conclusion from the corresponding `.mm0`
declaration.

A lemma block is accepted if and only if its final proof line proves the
lemma conclusion from the lemma header.

## Internal representation note

Implementations should intern proof expressions into a per-theorem DAG,
not plain trees.

This matters because MMB proof checking uses identity-sensitive
operations in places such as `URef` in unify streams and `Refl` in
conversion proofs. Repeated substituted subexpressions therefore often
need to be represented by shared internal nodes so the emitted MMB can
preserve the required sharing.
