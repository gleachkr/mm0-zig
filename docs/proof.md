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
- `docs/holes.md`

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

Outside math strings, newlines may be mixed with other whitespace inside
one proof line. A new proof line must still begin on a fresh line with
its label. Comments are allowed in these continuation positions.
Newlines are also allowed inside `$ ... $` math strings.

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
theorem-block ::= theorem-name newline underline newline* proof-line*
underline ::= hspace? '-' '-' '-'* hspace? newline
```

The underline is required. It must appear on the line immediately after
the theorem header, contain only dashes plus optional leading or
trailing horizontal whitespace, and be at least 3 dashes long. Trailing
comment text is not allowed on underline lines.

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
                newline underline newline* proof-line*

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
proof-line ::= label ':' formula 'by' rule-application
               comment? newline*

rule-application ::= rule-name ('(' arg-bindings ')')? ('[' refs ']')?
```

The parser treats spaces, newlines, blank lines, and `--` comments as
interchangeable separators between proof-line components. In particular,
it is legal to break before or after `by`, and within binding and
reference lists.

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

l3:
  $ a $
  -- break before and after `by`
  by
  ax_id
  []
```

## References

References inside `[...]` may be theorem hypotheses, previous proof
lines, or inline rule applications.

```text
refs ::= empty | ref (',' ref)*
ref ::= hyp-ref | line-ref | inline-application
hyp-ref ::= '#' number
line-ref ::= identifier
inline-application ::= rule-application
```

Meaning:

- `#1`, `#2`, ... refer to the hypotheses of the theorem being proved
- inside a lemma block, `#1`, `#2`, ... refer to the lemma hypotheses
- `l1`, `l2`, ... refer to prior proof lines in the current block
- `rule [...]` applies `rule` anonymously and uses its conclusion as the
  reference expression

Hypotheses are numbered in the order they appear in the theorem or lemma
header after MM0 parsing.

A bare identifier in a reference list is always a line reference, even if
it is also the name of a rule. This preserves the older syntax. A
zero-hypothesis inline application with no explicit bindings must
therefore use a reference delimiter:

```text
l1: $ top $ by keep [top_i []]
```

If an inline application has an explicit binding list, the binding list
already disambiguates it from a line reference. Its reference list is
optional when it has no references:

```text
l1: $ p $ by keep [make_p (a := $ p $)]
```

## Chained rule applications

An inline rule application is an anonymous proof line inserted before the
application that uses it. For example:

```text
l1: $ c $ by outer [inner [#1], #2]
```

behaves like a proof with an unnamed intermediate line proving the
conclusion of `inner [#1]`, followed by `outer` using that hidden line as
its first reference. Hidden lines have no user-visible label and cannot
be referenced later.

Inline applications may be nested arbitrarily and may use explicit
bindings, omitted-binder inference, theorem-hypothesis refs, prior line
refs, and other inline applications:

```text
l2: $ c $ by outer [middle (a := $ t $) [inner [l1]], #1]
```

The checker may give the child a contextual hint from the parent rule's
expected hypothesis when the parent conclusion and explicit bindings make
that hypothesis predictable. The child first tries to use that expected
conclusion as an extra inference constraint. If the hinted attempt fails,
the child falls back to ordinary inference from its own rule name,
bindings, refs, and metadata.

This is still not global proof search. The parent does not backtrack
over child choices, and the child must still elaborate to one concrete
hidden line before the parent application can finish. After that, the
parent checks whether the child's conclusion matches the corresponding
parent hypothesis.

Fallback remains candidate-local. If an inline application cites a rule
with `@fallback`, the compiler tries the written rule first. If that
whole candidate fails, including its nested children, the compiler rolls
back the hidden lines and theorem-local mutations from that candidate and
tries the fallback rule. The same rule applies independently at each
nesting level.

Inline applications use the same rule-application pipeline as top-level
proof lines. Rule metadata such as `@view`, `@recover`, `@abstract`,
`@fresh`, `@alpha`, and `@fallback` applies in the usual way. Automatic
normalized validation is also available. The only difference is the assertion
mode: a top-level line has a user-written assertion, while an inline
application infers its whole conclusion from the selected candidate rule.

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

1. Parse `$ C $` in the local assertion context.
2. Resolve `RULE` to a previously declared axiom, theorem, or lemma.
3. Check the syntactic reference count against that rule's hypotheses.
4. Resolve and parse any explicit argument bindings for this candidate.
5. Use the assertion and those partial bindings to compute any expected
   reference expressions that can guide nested inline applications.
6. Elaborate `R1, ..., Rn`. A ref may recursively elaborate an inline
   application and return the hidden line proving its conclusion.
7. Infer any omitted rule binders from the line assertion, elaborated
   refs, contextual hints, and rule metadata.
8. Instantiate the rule's hypotheses and conclusion with those concrete
   binders.
9. Compare the instantiated rule against the user's line and refs,
   allowing frontend features such as transparent defs, views, recover /
   abstract bindings, fresh binders, targeted alpha-freshening, and
   normalization when the rule's metadata permits them.
10. If that attempt fails and the cited rule has `@fallback`, retry the
    whole application with the fallback target, then continue through the
    fallback chain if needed.
11. Record label `L` as proving `C`.

Top-level proof-line formulas are always explicit and must be written
out by the user. Inline applications are the exception: they have no
source assertion, so the compiler accepts the selected rule's instantiated
conclusion as the hidden line's assertion.

Fallback metadata is resolved eagerly while processing the `.mm0` file,
so `@fallback target_rule` may refer only to a rule already in scope at
the annotation site. See `docs/rewrite_system.md` for the annotation
details.

## Final-line condition

A public theorem block is accepted if and only if its final proof line
proves the theorem conclusion from the corresponding `.mm0`
declaration, either directly or after theorem-boundary reconciliation.

That reconciliation is proof-producing. The compiler may emit ordinary
rule applications that convert the proved final line into the declared
theorem conclusion using the same frontend machinery available
elsewhere, including transparent defs, normalization, and
alpha-renaming cleanup driven by relation, rewrite, and congruence
metadata.

This flexibility applies only at the outer theorem boundary. Interior
proof lines are still checked in the ordinary way against the cited
rule application, and a lemma block is accepted if and only if its
final proof line proves the lemma conclusion from the lemma header.

## Internal representation note

Implementations should intern proof expressions into a per-theorem DAG,
not plain trees.

This matters because MMB proof checking uses identity-sensitive
operations in places such as `URef` in unify streams and `Refl` in
conversion proofs. Repeated substituted subexpressions therefore often
need to be represented by shared internal nodes so the emitted MMB can
preserve the required sharing.
