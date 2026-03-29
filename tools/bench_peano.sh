#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BENCH_DIR="$ROOT/.bench-cache"
MM0="$ROOT/third_party/mm0/examples/peano.mm0"
MM1="$ROOT/third_party/mm0/examples/peano.mm1"
MMB="$BENCH_DIR/peano.mmb"

if ! command -v mm0-rs >/dev/null 2>&1; then
  echo "missing required command: mm0-rs" >&2
  exit 1
fi

mkdir -p "$BENCH_DIR"

echo "==> Compiling peano.mm1 to peano.mmb" >&2
(
  cd "$ROOT/third_party/mm0/examples"
  mm0-rs compile "$(basename "$MM1")" "$MMB"
)

exec "$ROOT/tools/bench_verify.sh" \
  --mm0 "$MM0" \
  --mmb "$MMB" \
  "$@"
