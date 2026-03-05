# mm0-zig

A Metamath Zero (MM0/MMB) proof verifier written in Zig.

## Usage

mm0-zig FILE.mmb < FILE.mm0

## Building

zig build -Doptimize=ReleaseFast

## Testing

This project has separate unit and integration test steps:

- `zig build test-unit`
- `zig build test-integration`
- `zig build test`

Integration tests scan `third_party/mm0/examples` for `.mm1` files, compile
with `mm0-rs`, and verify corresponding `.mm0`/`.mmb` pairs where a matching
`.mm0` exists.

To run one subset while iterating locally, use:

`MM0_ZIG_EXAMPLE_FILTER=peano zig build test-integration`

If you cloned without submodules, run:

`git submodule update --init --recursive`

## Status

Working verifier for MMB proofs with MM0 specs.

Verified against peano.mmb and peano.mm0 in ~8ms (versus ~6ms for mm0-c).
