# mm0-zig

A Metamath Zero (MM0/MMB) toolkit written in Zig.

## Usage

Verifier:

`mm0-zig FILE.mmb < FILE.mm0`

Compiler skeleton:

`mm0-zigc compile INPUT.mm0 OUTPUT.mmb`

## Building

The shared logic lives in the reusable Zig module in `src/lib.zig`.
There are now two binaries built on top of it:

- `mm0-zig` in `src/main.zig`/`src/command.zig`
- `mm0-zigc` in `src/compiler_main.zig`/
  `src/compiler_command.zig`

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
- Compiler: front-end skeleton only for now; emission is not implemented yet.

Verified against peano.mmb and peano.mm0 in ~8ms (versus ~6ms for mm0-c).
