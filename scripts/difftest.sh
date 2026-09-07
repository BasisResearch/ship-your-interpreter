#!/usr/bin/env bash
# difftest.sh — check the BMC encoder against the proof model, end to end.
#
#   VSA_PRIVATE_BUILD=DIR scripts/difftest.sh --segment-authority DIR
#       --emulator-receipt FILE [--out DIR] [--mine]
#       [--per-pc N] [--jobs N] [wl ...]
#
# Builds one traceable ELF per `.wl`
# program (padded to the proof script's length so the code image is the proof
# ELF's, byte for byte), runs each under the emulator's traced loop, then:
#
#   phase 1  do the declared spans exist?  (span reachability, dispatch arms)
#   phase 2  do the summary clauses hold on real (pre, post) pairs?
#   phase 3  does the encoder's step semantics agree with the machine?
#   phase 3b does `state_exit` agree with the machine, and the write footprint?
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
SEGMENT_AUTHORITY=""
EMULATOR_RECEIPT="${VSA_EMULATOR_RECEIPT:-}"
AUTHORITY_ARGS=()
PER_PC=24
PER_SPAN=6
JOBS=""
WLS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="$2"; shift 2;;
    --mine) MINE=1; shift;;
    --segment-authority) SEGMENT_AUTHORITY="$2"; shift 2;;
    --emulator-receipt) EMULATOR_RECEIPT="$2"; shift 2;;
    --per-pc) PER_PC="$2"; shift 2;;
    --per-span) PER_SPAN="$2"; shift 2;;
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

fail() { echo "difftest: $*" >&2; exit 1; }

# The caller supplies an independent export from the checked Lean build.
# Never derive this path from the campaign or mint authority from its metadata.
[ -n "$SEGMENT_AUTHORITY" ] || fail "--segment-authority DIR is required; emit it from the fingerprint-checked Lean build"
[ -f "$SEGMENT_AUTHORITY/segment-authority.json" ] || fail "missing independent segment authority"
AUTHORITY_ARGS=(--segment-authority "$SEGMENT_AUTHORITY")
[ -n "${VSA_PRIVATE_BUILD:-}" ] || fail "VSA_PRIVATE_BUILD must identify the current private Lean build"
python3 scripts/check_validation.py --backend "$VSA_PRIVATE_BUILD" --verify-backend-only \
  || fail "private Lean backend is missing or stale; refresh it with scripts/build_private.py"
[ -n "$EMULATOR_RECEIPT" ] || fail "--emulator-receipt FILE required; first run python3 scripts/difftest.py build-emulator --receipt /private/tmp/vsa-emulator-build.json"
python3 scripts/difftest.py verify-emulator --receipt "$EMULATOR_RECEIPT" \
  || fail "emulator receipt is missing or stale; run python3 scripts/difftest.py build-emulator --receipt '$EMULATOR_RECEIPT'"

# ---------------------------------------------------------------- 0. the ELF
sha=$(shasum -a 256 "$PROOF_ELF" | cut -d' ' -f1)
[ "$sha" = "$EXPECT_SHA" ] || fail "the proof ELF changed: $sha != $EXPECT_SHA"
echo "[difftest] proof ELF ${sha:0:12}… ok"

mkdir -p "$OUT"

# --------------------------------------------- 2. the encoder's own answers
echo "[difftest] emitting the encoder's step table + span facts…"
LEAN_OUT=$(mktemp -d "$OUT/lean.XXXXXX") || fail "cannot create emission directory"
mkdir -p "$LEAN_OUT/experiments/smt"
cat > "$OUT/emit.lean" <<LEAN
import experiments.smt.DiffTest
#emit_bmc "$OUT/bmc" 60
#emit_encoder_facts "$OUT/enc"
#emit_step_table "$OUT/enc" 0x80000000 0x80018be0
#emit_loop_facts "$OUT/enc" "$OUT/bmc"
LEAN
for m in ReflectSpan ReflectResiduals DiffTest; do
  lake env sh -c 'LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}" lean -o "$3" "$4"' \
    difftest "$VSA_PRIVATE_BUILD" "$LEAN_OUT" \
    "$LEAN_OUT/experiments/smt/$m.olean" "experiments/smt/$m.lean" \
    || fail "experiments/smt/$m.lean does not elaborate"
done
lake env sh -c 'LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}" lean "$3"' \
  difftest "$VSA_PRIVATE_BUILD" "$LEAN_OUT" "$OUT/emit.lean" || fail "emission failed"

# Reject stale authority or incompatible descriptors before mining or tracing.
python3 - "$OUT/bmc" "$SEGMENT_AUTHORITY" <<'PYTHON' || fail "segment certificate validation failed"
from scripts.segment_certificates import load_segment_certificates
import sys
load_segment_certificates(sys.argv[1], authority_dir=sys.argv[2])
PYTHON

# The clause sets phase 2 checks against.  Re-mining is a minute of Z3; by
# default reuse the campaign's own, which is what the verdicts rest on.
if [ "$MINE" = 1 ]; then
  echo "[difftest] mining clause sets…"
  python3 scripts/houdini_summary.py "$OUT/bmc" --phase mine "${AUTHORITY_ARGS[@]}" >/dev/null || fail "mining failed"
elif [ -f experiments/smt/bmc/clauses.json ]; then
  cp experiments/smt/bmc/clauses.json "$OUT/bmc/clauses.json"
fi

# ------------------------------------------------------- 3. corpus + traces
echo "[difftest] building ${#WLS[@]} corpus ELFs…"
mkdir -p "$OUT/elfs" "$OUT/traces"
python3 scripts/difftest.py corpus "${WLS[@]}" --out "$OUT/elfs" --workdir "$OUT/c" \
  | sed 's/^/  /' || fail "corpus build failed"

# A fresh directory prevents old traces from standing in for failed or removed
# corpus cases. Retain every run for diagnosis.
TRACE_DIR=$(mktemp -d "$OUT/traces/run.XXXXXX") || fail "cannot create trace directory"
NPAR=${DIFFTEST_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)}
[[ "$NPAR" =~ ^[1-9][0-9]*$ ]] || fail "DIFFTEST_JOBS must be positive"
pids=()
trace_failed=0
wait_traces() {
  for pid in "${pids[@]}"; do
    wait "$pid" || trace_failed=1
  done
  pids=()
}
for wl in "${WLS[@]}"; do
  n=$(basename "$wl" .wl)
  e="$OUT/elfs/$n.elf"
  [ -f "$e" ] || fail "missing requested corpus ELF: $e"
  python3 scripts/difftest.py trace "$e" --emulator-receipt "$EMULATOR_RECEIPT" --out "$TRACE_DIR/$n.trace.tsv" >/dev/null &
  pids+=("$!")
  if [ "${#pids[@]}" -ge "$NPAR" ]; then wait_traces; fi
done
wait_traces
[ "$trace_failed" = 0 ] || fail "one or more emulator runs failed; see $TRACE_DIR"
echo "[difftest] traced ${#WLS[@]} requested programs in $TRACE_DIR"

# ------------------------------------------------------------- 4. the phases
rc=0
python3 scripts/difftest.py phase1 --traces "$TRACE_DIR" --enc "$OUT/enc" \
  --bmc "$OUT/bmc" --out "$OUT/phase1.tsv" || rc=1
python3 scripts/difftest.py phase2 --traces "$TRACE_DIR" --enc "$OUT/enc" \
  --bmc "$OUT/bmc" --out "$OUT/clause-witness.tsv" || rc=1
python3 scripts/difftest.py phase3 --traces "$TRACE_DIR" --enc "$OUT/enc" \
  --per-pc "$PER_PC" --chunk 400 $JOBS --out "$OUT/phase3.tsv" || rc=1
python3 scripts/difftest.py phase3b --traces "$TRACE_DIR" --enc "$OUT/enc" \
  --bmc "$OUT/bmc" "${AUTHORITY_ARGS[@]}" --per-span "$PER_SPAN" --out "$OUT/phase3b.tsv" || rc=1

# Do not report success if sources or the executable changed during validation.
python3 scripts/check_validation.py --backend "$VSA_PRIVATE_BUILD" --verify-backend-only || rc=1
python3 scripts/difftest.py verify-emulator --receipt "$EMULATOR_RECEIPT" || rc=1

if [ $rc = 0 ]; then echo "[difftest] OK — sampled encoder checks passed on the requested startup-program traces"
else echo "[difftest] FAILED — see $OUT/{phase1,clause-witness,phase3,phase3b}.tsv"; fi
exit $rc
