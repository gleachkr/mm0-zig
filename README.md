# Aufbau

Aufbau is a Metamath Zero (MM0/MMB) toolkit written in Zig.

## Usage

Verifier:

`mm0-zig FILE.mmb < FILE.mm0`

Compiler:

`abc compile INPUT.mm0 INPUT.auf OUTPUT.mmb`

## Building

The shared logic lives in the reusable Zig module in `src/lib.zig`.
There are two binaries built on top of it:

- `mm0-zig` in `src/bin/verifier/`
- `abc` in `src/bin/compiler/`

Build both with:

`zig build -Doptimize=ReleaseFast`

## Documentation

- `ARCHITECTURE.md` — project structure and trust boundary
- `docs/proof.md` — Aufbau proof-script format
- `docs/rewrite_system.md` — rewrite metadata and normalization
- `docs/transparent_defs.md` — transparent def handling
- `docs/view_recover.md` — `@view`, `@recover`, `@abstract`
- `docs/fresh_binders.md` — `@vars` and `@fresh`

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
- Compiler: supports the Aufbau script format in `docs/proof.md`,
  omitted-binder inference, transparent defs, hidden-dummy witness
  resolution, `@view` / `@recover` / `@abstract` / `@vars` /
  `@fresh`, and mixed rewrite / structural normalization.
- Web demo: ships several proof-case fixtures from `tests/proof_cases`.
