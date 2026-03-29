#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: tools/bench_verify.sh --mm0 FILE.mm0 --mmb FILE.mmb [options]

Options:
  --runs N         Hyperfine measurement runs. Default: 10.
  --warmup N       Hyperfine warmup runs. Default: 2.
  --repeat N       Verifications per sample. Default: 100.
  --perf           Also run perf stat loops.
  --perf-reps N    perf stat repetition count. Default: 5.
  --no-build       Skip rebuilding mm0-zig.
  --mm0c PATH      mm0-c binary. Default: mm0-c from PATH.
  --mm0zig PATH    mm0-zig binary. Default: zig-out/bin/mm0-zig.
  -h, --help       Show this help.

Environment overrides:
  MM0C_BIN, MM0ZIG_BIN, HYPERFINE_BIN, PERF_BIN.
EOF
}

need_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "missing required command: $1" >&2
    exit 1
  fi
}

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
MM0=
MMB=
RUNS=10
WARMUP=2
REPEAT=100
DO_PERF=0
PERF_REPS=5
DO_BUILD=1
MM0C_BIN=${MM0C_BIN:-mm0-c}
MM0ZIG_BIN=${MM0ZIG_BIN:-"$ROOT/zig-out/bin/mm0-zig"}
HYPERFINE_BIN=${HYPERFINE_BIN:-hyperfine}
PERF_BIN=${PERF_BIN:-perf}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --mm0)
      MM0=$2
      shift 2
      ;;
    --mmb)
      MMB=$2
      shift 2
      ;;
    --runs)
      RUNS=$2
      shift 2
      ;;
    --warmup)
      WARMUP=$2
      shift 2
      ;;
    --repeat)
      REPEAT=$2
      shift 2
      ;;
    --perf)
      DO_PERF=1
      shift
      ;;
    --perf-reps)
      PERF_REPS=$2
      shift 2
      ;;
    --no-build)
      DO_BUILD=0
      shift
      ;;
    --mm0c)
      MM0C_BIN=$2
      shift 2
      ;;
    --mm0zig)
      MM0ZIG_BIN=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [[ -z "$MM0" || -z "$MMB" ]]; then
  echo "both --mm0 and --mmb are required" >&2
  usage >&2
  exit 1
fi

need_cmd "$MM0C_BIN"
need_cmd "$HYPERFINE_BIN"
need_cmd python3

if [[ $DO_PERF -eq 1 ]]; then
  need_cmd "$PERF_BIN"
fi

MM0=$(cd "$(dirname "$MM0")" && pwd)/$(basename "$MM0")
MMB=$(cd "$(dirname "$MMB")" && pwd)/$(basename "$MMB")

if [[ ! -f "$MM0" ]]; then
  echo "missing mm0 file: $MM0" >&2
  exit 1
fi

if [[ ! -f "$MMB" ]]; then
  echo "missing mmb file: $MMB" >&2
  exit 1
fi

if [[ $DO_BUILD -eq 1 ]]; then
  need_cmd zig
  echo "==> Building mm0-zig" >&2
  (
    cd "$ROOT"
    zig build -Doptimize=ReleaseFast \
      --cache-dir .zig-cache-local \
      --global-cache-dir .zig-cache-global
  )
fi

if [[ ! -x "$MM0ZIG_BIN" ]]; then
  echo "mm0-zig binary is not executable: $MM0ZIG_BIN" >&2
  exit 1
fi

echo "==> Smoke checking mm0-c" >&2
"$MM0C_BIN" "$MMB" < "$MM0" > /dev/null 2>&1

echo "==> Smoke checking mm0-zig" >&2
"$MM0ZIG_BIN" "$MMB" < "$MM0" > /dev/null 2>&1

printf -v MM0C_CMD \
  'for ((i = 0; i < %d; i++)); do %q %q < %q > /dev/null 2>&1; done' \
  "$REPEAT" "$MM0C_BIN" "$MMB" "$MM0"
printf -v MM0ZIG_CMD \
  'for ((i = 0; i < %d; i++)); do %q %q < %q > /dev/null 2>&1; done' \
  "$REPEAT" "$MM0ZIG_BIN" "$MMB" "$MM0"

mkdir -p "$ROOT/.bench-cache"
JSON=$(mktemp "$ROOT/.bench-cache/hyperfine.XXXXXX.json")
trap 'rm -f "$JSON"' EXIT

echo "==> Running hyperfine" >&2
"$HYPERFINE_BIN" \
  --warmup "$WARMUP" \
  --runs "$RUNS" \
  --export-json "$JSON" \
  -n "mm0-c x$REPEAT" "$MM0C_CMD" \
  -n "mm0-zig x$REPEAT" "$MM0ZIG_CMD"

echo >&2
echo "==> Approximate per-verification means" >&2
python3 - "$JSON" "$REPEAT" <<'PY'
import json
import sys

json_path = sys.argv[1]
repeat = int(sys.argv[2])
labels = ['mm0-c', 'mm0-zig']
with open(json_path, 'r', encoding='utf-8') as fh:
    data = json.load(fh)

for index, result in enumerate(data['results']):
    label = labels[index] if index < len(labels) else result['command']
    mean_ms = result['mean'] * 1000.0
    std_ms = result['stddev'] * 1000.0
    per_mean = mean_ms / repeat
    per_std = std_ms / repeat
    print(
        f"{label}: {per_mean:.3f} ms ± {per_std:.3f} ms "
        f"per verification"
    )
PY

if [[ $DO_PERF -eq 1 ]]; then
  echo >&2
  echo "==> Running perf stat for mm0-c" >&2
  "$PERF_BIN" stat -r "$PERF_REPS" \
    bash --norc --noprofile -lc "$MM0C_CMD"

  echo >&2
  echo "==> Running perf stat for mm0-zig" >&2
  "$PERF_BIN" stat -r "$PERF_REPS" \
    bash --norc --noprofile -lc "$MM0ZIG_CMD"
fi
