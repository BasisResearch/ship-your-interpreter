#!/usr/bin/env bash
# difftest.sh — check the BMC encoder against the proof model, end to end.
#
#   scripts/difftest.sh [--out DIR] [--mine] [--per-pc N] [--jobs N] [wl ...]
#
# `experiments/smt/DIFFTEST-PLAN.md`.  Builds one traceable ELF per `.wl`
# program (padded to the proof script's length so the code image is the proof
# ELF's, byte for byte), runs each under the emulator's traced loop, then:
#
#   phase 1  do the declared spans exist?  (span reachability, dispatch arms)
#   phase 2  do the summary clauses hold on real (pre, post) pairs?
#   phase 3  does the encoder's step semantics agree with the machine?
#
# Exits non-zero on any disagreement.  With no `.wl` arguments it uses the
# standing corpus (`c/tests` + `c/difftests`).
#
# Cost on this machine: ~30 s to emit the encoder's artifacts, ~20 s to trace
# the corpus in parallel, ~50 s for the three phases.  `--mine` adds ~60 s of Z3
# to re-mine the clause sets instead of reusing `experiments/smt/bmc/clauses.json`.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT=/tmp/difftest
MINE=0
PER_PC=24
JOBS=""
WLS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="$2"; shift 2;;
    --mine) MINE=1; shift;;
    --per-pc) PER_PC="$2"; shift 2;;
    --jobs) JOBS="--jobs $2"; shift 2;;
    -h|--help) sed -n '2,20p' "$0"; exit 0;;
    *) WLS+=("$1"); shift;;
  esac
done
if [ ${#WLS[@]} -eq 0 ]; then
  WLS=(c/tests/*.wl c/difftests/*.wl)
fi

PROOF_ELF=c/while-riscv-htif.elf
EXPECT_SHA=b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0
EMU=riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator

fail() { echo "difftest: $*" >&2; exit 1; }

# ---------------------------------------------------------------- 0. the ELF
sha=$(shasum -a 256 "$PROOF_ELF" | cut -d' ' -f1)
[ "$sha" = "$EXPECT_SHA" ] || fail "the proof ELF changed: $sha != $EXPECT_SHA"
echo "[difftest] proof ELF ${sha:0:12}… ok"

# ------------------------------------------------------- 1. the emulator
if [ ! -x "$EMU" ]; then
  echo "[difftest] building the emulator…"
  (cd riscv-lean/lean_emulator && lake build) >/dev/null || fail "emulator build failed"
fi

mkdir -p "$OUT"

# --------------------------------------------- 2. the encoder's own answers
echo "[difftest] emitting the encoder's step table + span facts…"
cat > "$OUT/emit.lean" <<LEAN
import experiments.smt.DiffTest
#emit_bmc "$OUT/bmc" 60
#emit_encoder_facts "$OUT/enc"
#emit_step_table "$OUT/enc" 0x80000000 0x80018be0
#emit_loop_facts "$OUT/enc" "$OUT/bmc"
LEAN
for m in ReflectSpan ReflectResiduals DiffTest; do
  lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:.\" lean -o experiments/smt/$m.olean experiments/smt/$m.lean" \
    || fail "experiments/smt/$m.lean does not elaborate"
done
lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:.\" lean $OUT/emit.lean" || fail "emission failed"

# The clause sets phase 2 checks against.  Re-mining is a minute of Z3; by
# default reuse the campaign's own, which is what the verdicts rest on.
if [ "$MINE" = 1 ]; then
  echo "[difftest] mining clause sets…"
  python3 scripts/houdini_summary.py "$OUT/bmc" --phase mine >/dev/null || fail "mining failed"
elif [ -f experiments/smt/bmc/clauses.json ]; then
  cp experiments/smt/bmc/clauses.json "$OUT/bmc/clauses.json"
fi

# ------------------------------------------------------- 3. corpus + traces
echo "[difftest] building ${#WLS[@]} corpus ELFs…"
mkdir -p "$OUT/elfs" "$OUT/traces"
python3 scripts/difftest.py corpus "${WLS[@]}" --out "$OUT/elfs" --workdir "$OUT/c" \
  | sed 's/^/  /' || fail "corpus build failed"

# Traces are cached on (ELF, emulator) so a re-run only re-traces what changed.
# Bounded parallelism: each trace is a whole program run in the proof model and
# ninety at once just thrash.
emusha=$(shasum -a 256 "$EMU" | cut -d' ' -f1)
NPAR=${DIFFTEST_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)}
running=0
for e in "$OUT"/elfs/*.elf; do
  n=$(basename "$e" .elf)
  stamp="$OUT/traces/$n.stamp"
  esha=$(shasum -a 256 "$e" | cut -d' ' -f1)
  if [ -f "$stamp" ] && [ "$(cat "$stamp")" = "$esha:$emusha" ]; then continue; fi
  ( python3 scripts/difftest.py trace "$e" --out "$OUT/traces/$n.trace.tsv" >/dev/null \
      && echo "$esha:$emusha" > "$stamp" ) &
  running=$((running + 1))
  if [ "$running" -ge "$NPAR" ]; then wait -n 2>/dev/null || wait; running=0; fi
done
wait
echo "[difftest] traced $(ls "$OUT"/traces/*.trace.tsv | wc -l | tr -d ' ') programs"

# ------------------------------------------------------------- 4. the phases
rc=0
python3 scripts/difftest.py phase1 --traces "$OUT/traces" --enc "$OUT/enc" \
  --bmc "$OUT/bmc" --out "$OUT/phase1.tsv" || rc=1
python3 scripts/difftest.py phase2 --traces "$OUT/traces" --enc "$OUT/enc" \
  --bmc "$OUT/bmc" --out "$OUT/clause-witness.tsv" || rc=1
python3 scripts/difftest.py phase3 --traces "$OUT/traces" --enc "$OUT/enc" \
  --per-pc "$PER_PC" --chunk 400 $JOBS --out "$OUT/phase3.tsv" || rc=1

if [ $rc = 0 ]; then echo "[difftest] OK — the encoder agrees with the machine"
else echo "[difftest] FAILED — see $OUT/{phase1,clause-witness,phase3}.tsv"; fi
exit $rc
