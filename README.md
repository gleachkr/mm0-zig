# mm0-zig

A Metamath Zero (MM0/MMB) toolkit written in Zig.

## Usage

Verifier:

`mm0-zig FILE.mmb < FILE.mm0`

Compiler:

`mm0-zigc compile INPUT.mm0 INPUT.proof OUTPUT.mmb`

## Building

The shared logic lives in the reusable Zig module in `src/lib.zig`.
There are two binaries built on top of it:

- `mm0-zig` in `src/bin/verifier/`
- `mm0-zigc` in `src/bin/compiler/`

Build both with:

`zig build -Doptimize=ReleaseFast`

## Testing

This project has separate unit and integration test steps:

- `zig build test-unit -Doptimize=ReleaseFast`
- `zig build test-integration -Doptimize=ReleaseFast`
- `zig build test -Doptimize=ReleaseFast`

Integration tests scan `third_party/mm0/examples` for `.mm1` files, compile
with `mm0-rs`, and verify corresponding `.mm0`/`.mmb` pairs where a matching
`.mm0` exists.

To run one subset while iterating locally, use:

`MM0_ZIG_EXAMPLE_FILTER=peano zig build test-integration`

If you cloned without submodules, run:

`git submodule update --init --recursive`

## Status

- Verifier: working against the current MM0/MMB specs.
- Compiler: supports the source proof format in `specs/proof.md`,
  omitted-binder inference, `@view` / `@recover`, and mixed rewrite /
  structural normalization.
- Web demo: ships several proof-case fixtures from `tests/proof_cases`.
