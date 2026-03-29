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

## Benchmarking

There is a small harness for verifier timing comparisons:

- `tools/bench_peano.sh`
- `tools/bench_verify.sh --mm0 FILE.mm0 --mmb FILE.mmb`

`bench_peano.sh` rebuilds `mm0-zig`, compiles `peano.mm1` to
`.bench-cache/peano.mmb` with `mm0-rs`, smoke-checks both verifiers,
and then runs `hyperfine`.

Example:

`tools/bench_peano.sh --runs 10 --warmup 2 --repeat 100`

To include `perf stat` in the same run:

`tools/bench_peano.sh --runs 10 --warmup 2 --repeat 100 --perf`

The harness builds with repo-local Zig caches:

`--cache-dir .zig-cache-local --global-cache-dir .zig-cache-global`

## Status

- Verifier: working against the current MM0/MMB specs.
- Compiler: supports the source proof format in `specs/proof.md`,
  omitted-binder inference, `@view` / `@recover` / `@abstract` /
  `@dummy`, and mixed rewrite / structural normalization.
- Web demo: ships several proof-case fixtures from `tests/proof_cases`.
