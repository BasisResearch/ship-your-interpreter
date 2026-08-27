#!/usr/bin/env bash
# elab_profile.sh — per-file elaboration-time witness (the elab-budget gate, mechanized).
#
# WHY: the exponentiation strategy hinges on "constant elab cost per row" (fast-reflection
# rule 7). You cannot enforce a budget you do not measure. This gives per-FILE wall time and
# per-DECLARATION elaboration time (via the kernel profiler) so we target the REAL offenders
# instead of inferring cost from `decide` counts.
#
# SAFETY (hard-won, see experiments/RESUME-after-restart.md): STRICTLY SERIAL. One `lean` at a
# time. `pkill -9 lean` between files. NEVER run under a parallel `lake build`. Assumes the tree
# is already built & current (deps' oleans present) so each file recompiles in isolation — this
# is O(one file), NOT the 15-min full build.
#
# USAGE:
#   scripts/elab_profile.sh                 # profile the default offender set
#   scripts/elab_profile.sh Vsa/Sim/Foo.lean [Vsa/Sim/Bar.lean ...]
#   THRESHOLD=200 scripts/elab_profile.sh … # per-decl profiler threshold in ms (default 100)
#
# OUTPUT: appends a table row per file to experiments/elab-timings.tsv and prints the top
# per-declaration costs, so a regression (>10% vs the recorded baseline) is visible at a glance.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

THRESHOLD="${THRESHOLD:-100}"
OUT=experiments/elab-timings.tsv
TOPN="${TOPN:-15}"

DEFAULT_SET=(
  Vsa/Sim/Code/Eval_expr.lean        # 12.4k lines — giant mem-conjunction code image (suspected #1)
  Vsa/Sim/Code/SvfprintfSlice.lean   # 7.2k lines — same generated shape
  Vsa/Sim/StrcmpSites.lean           # 714 raw `decide` — site battery
  Vsa/Sim/rows/EvalGtRow.lean        # decide + omega in match arms
  Vsa/Sim/BlockMem.lean              # the reflection layer — should be CHEAP (control)
)

FILES=("$@")
[ ${#FILES[@]} -eq 0 ] && FILES=("${DEFAULT_SET[@]}")

mkdir -p experiments
[ -f "$OUT" ] || printf 'file\twall_s\tstatus\ttimestamp\n' > "$OUT"

echo "== elab_profile: ${#FILES[@]} file(s), serial, per-decl threshold ${THRESHOLD}ms =="
for f in "${FILES[@]}"; do
  if [ ! -f "$f" ]; then echo "SKIP (missing): $f"; continue; fi
  pkill -9 lean 2>/dev/null; sleep 1
  echo "---- $f ----"
  log=$(mktemp)
  start=$(date +%s)
  # -Dprofiler prints per-declaration elaboration/compilation time to stderr.
  lake env lean -Dprofiler=true -Dprofiler.threshold="$THRESHOLD" "$f" >"$log" 2>&1
  status=$?
  end=$(date +%s)
  wall=$((end - start))
  ts=$(date +%Y-%m-%dT%H:%M:%S)
  printf '%s\t%s\t%s\t%s\n' "$f" "$wall" "$status" "$ts" >> "$OUT"
  echo "wall=${wall}s status=${status}"
  # Top per-decl costs (profiler lines look like: "elaboration took 1.23s" / "took 456ms").
  grep -iE 'took [0-9]' "$log" | sort -t' ' -k1 | \
    awk '{print}' | sort -rk3 2>/dev/null | head -n "$TOPN"
  # Surface the heaviest named declarations if the profiler tagged them.
  grep -iE '\[Elab|typeck|took' "$log" | grep -iE 'took ([0-9]{3,}ms|[0-9.]+s)' | head -n "$TOPN"
  rm -f "$log"
done
pkill -9 lean 2>/dev/null
echo "== done. baseline table: $OUT =="
