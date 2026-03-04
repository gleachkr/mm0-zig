# mm0-zig

A Metamath Zero (MM0/MMB) proof verifier written in Zig.

## Usage

mm0-zig FILE.mmb < FILE.mm0

## Building

zig build -Doptimize=ReleaseFast

## Status

Working verifier for MMB proofs with MM0 specs.

Verified against peano.mmb and peano.mm0 in ~8ms (versus ~6ms for mm0-c).
