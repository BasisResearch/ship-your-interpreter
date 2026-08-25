#!/usr/bin/env bash
# check_all.sh — the CI gate for the Vsa Lean development.
#
# Usage: scripts/check_all.sh [--skip-build]
#
# Stages (all must pass; exits nonzero with a message on the first failure):
#   (a) `lake build`                — the full tree compiles
#                                     (skipped with --skip-build, e.g. when
#                                     another process owns the build lock and
#                                     oleans are known-fresh);
#   (b) grep gate                   — no `sorry`, no `native_decide`, and no
#                                     `axiom` declarations anywhere under Vsa/
#                                     or in Vsa.lean.  Comments/docstrings and
#                                     string literals are stripped first, so
#                                     "NO sorry/native_decide" prose is fine;
#   (c) `#print axioms`             — every key top-level spec theorem depends
#                                     only on {propext, Classical.choice,
#                                     Quot.sound}.  Extend THEOREMS below as
#                                     capstones land (e.g. ssprint_iov2_spec
#                                     once SnprintfSpec20 is wired into
#                                     Vsa.lean).
#
# Dependencies: bash, grep, python3, lake/lean (elan toolchain).

set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

SKIP_BUILD=0
for arg in "$@"; do
  case "$arg" in
    --skip-build) SKIP_BUILD=1 ;;
    -h|--help) echo "usage: $0 [--skip-build]"; exit 0 ;;
    *) echo "usage: $0 [--skip-build]" >&2; exit 2 ;;
  esac
done

fail() { echo "check_all: FAIL: $*" >&2; exit 1; }

# ---------------------------------------------------------------- (a) build
if [ "$SKIP_BUILD" -eq 0 ]; then
  echo "== stage a: lake build"
  lake build || fail "stage a: lake build failed"
else
  echo "== stage a: lake build SKIPPED (--skip-build)"
fi

# ------------------------------------------------------------ (b) grep gate
echo "== stage b: sorry / native_decide / axiom gate"
python3 - <<'PYEOF' || fail "stage b: forbidden token(s) found (see above)"
import pathlib, re, sys

files = sorted(pathlib.Path("Vsa").rglob("*.lean"))
if pathlib.Path("Vsa.lean").exists():
    files.append(pathlib.Path("Vsa.lean"))

def strip_comments_and_strings(src: str) -> str:
    """Blank out line comments (`--`), (nested) block comments (`/- -/`,
    incl. `/--`/`/-!` docstrings) and string literals, preserving newlines
    so line numbers survive."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; i += 2; continue
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; i += 2; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src[i] == '"':
            out.append(" "); i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2; continue
                if src[i] == '"':
                    i += 1; break
                out.append("\n" if src[i] == "\n" else " "); i += 1
            continue
        out.append(src[i]); i += 1
    return "".join(out)

bad = []
for f in files:
    code = strip_comments_and_strings(f.read_text(encoding="utf-8"))
    for lineno, line in enumerate(code.splitlines(), 1):
        for tok in ("sorry", "native_decide"):
            if re.search(rf"\b{tok}\b", line):
                bad.append(f"{f}:{lineno}: forbidden `{tok}`")
        if re.match(r"\s*axiom\b", line):
            bad.append(f"{f}:{lineno}: `axiom` declaration")
print(f"stage b: scanned {len(files)} .lean files")
if bad:
    print("\n".join(bad), file=sys.stderr)
    sys.exit(1)
PYEOF
echo "stage b: OK"

# ------------------------------------------------------- (c) #print axioms
echo "== stage c: #print axioms on the key spec theorems"
THEOREMS=(
  # strlen family (StrlenSpec / StrlenSpecU)
  Vsa.Sim.strlen_spec
  Vsa.Sim.strlen_full_spec
  # strcpy capstone (StrcpySpec)
  Vsa.Sim.strcpy_bytehead_from_head
  # newlib memmove forward path (SnprintfSpec18)
  Vsa.Sim.memmove_fwd_spec
  # __ssputs_r fast path (SnprintfSpec19)
  Vsa.Sim.ssputs_fast_spec
  # env_get HIT tail + found composition (EnvGetSpec6)
  Vsa.Sim.env_get_hit_tail
  Vsa.Sim.env_get_found_spec
  # snprintf %lld pipeline capstones
  Vsa.Sim.decimalLoop_spec                      # SnprintfSpec3
  Vsa.Sim.entryToDigits_spec                    # SnprintfSpec5
  Vsa.Sim.signToDigits_neg_spec                 # SnprintfSpec6
  Vsa.Sim.exitToPrint_spec                      # SnprintfSpec7
  Vsa.Sim.entryToPrint_neg_default_width_spec   # SnprintfSpec8
  Vsa.Sim.parseToPrintEntry_spec                # SnprintfSpec16
  Vsa.Sim.parseToPrint_neg_default_width_spec   # SnprintfSpec16
  Vsa.Sim.iov2ToSsprintCall_spec                # SnprintfSpec17
  Vsa.Sim.ssprint_iov2_spec                     # SnprintfSpec20
  Vsa.Sim.svfprintf_flushReturn_spec            # SnprintfSpec25 (flush return path)
  Vsa.Sim.iov2ToSvfprintfRet_spec               # SnprintfSpec26 (0x800078ac → svfprintf ret)
  Vsa.Sim.svfPrologue_spec                      # SnprintfSpec35 (0x80007654 → 0x80007728)
  Vsa.Sim.svfPrologueParse_spec                 # SnprintfSpec36 (0x80007654 → 0x80008534)
  Vsa.Sim.svfEntryToSsprintCall_spec            # SnprintfSpec37 (0x80007654 → 0x8000e908, PreSr)
  Vsa.Sim.svfprintf_lld_spec                    # SnprintfSpec38 (FULL svfprintf: ABI entry → ret, a0 = 1+n2)
  Vsa.Sim.svfprintf_buffer_eq_intToString       # SnprintfSpec39 (byte list = intToString.toUTF8)
  Vsa.Sim.svfprintf_lld_intToString_spec        # SnprintfSpec39 (svfprintf byte-for-byte capstone)
  Vsa.Sim.snprintfPreCall_spec                  # SnprintfSpec40 (snprintf entry → jal _svfprintf_r)
  Vsa.Sim.snprintfPostCall_spec                 # SnprintfSpec41 (svfprintf return → snprintf ret + NUL)
  Vsa.Sim.snprintf_lld_spec                     # SnprintfSpec42 (WRAPPER CAPSTONE: snprintf ABI entry → ret, buffer = intToString.toUTF8 ++ [0]; ALL v < 0)
  Vsa.Sim.fastToPrint_neg_spec                  # SnprintfSpec43 (single-digit fast path, neg arm: 0x80008100 → 0x8000782c)
  Vsa.Sim.entryToPrint_neg_any_spec             # SnprintfSpec44 (0x800080e4 → 0x8000782c, ANY negative magnitude)
  Vsa.Sim.entryToPrintNN_fast_spec              # SnprintfSpec45 (NONNEG single-digit arm: 0x800080e4 → 0x8000782c, no sign iovec)
  Vsa.Sim.exitToPrintNN_spec                    # SnprintfSpec46 (exit-restore + hops, NONNEG: beqz t5 taken, a6 = len)
  Vsa.Sim.armEntryNN_spec                       # SnprintfSpec47 (nonneg arm entry: 0x800080e4 → 0x80008100)
  Vsa.Sim.entryToPrintNN_any_spec               # SnprintfSpec48 (NONNEG arm, ANY magnitude → PRINT entry)
  Vsa.Sim.printToSsprintNN_spec                 # SnprintfSpec49 (1-iovec PRINT segment: 0x8000782c → 0x8000e908)
  Vsa.Sim.ssprint_iov1_spec                     # SnprintfSpec50 (__ssprint_r 1-iovec flush, ONE iteration)
  Vsa.Sim.svfprintf_flushReturn1_spec           # SnprintfSpec51 (1-iovec flush + return path → svfprintf ret)
  Vsa.Sim.svfEntryToSsprintCallNN_spec          # SnprintfSpec52 (0x80007654 → 0x8000e908, PreSr1, NONNEG)
  Vsa.Sim.svfprintf_lld_nn_spec                 # SnprintfSpec53 (FULL svfprintf, NONNEG: a0 = n1, digits only)
  Vsa.Sim.svfprintf_buffer_eq_intToString_nn    # SnprintfSpec54 (nonneg byte list = intToString.toUTF8)
  Vsa.Sim.snprintf_lld_nn_spec                  # SnprintfSpec54 (WRAPPER, NONNEG: buffer = intToString.toUTF8 ++ [0])
  Vsa.Sim.snprintf_lld_total_spec               # SnprintfSpec55 (THE TOTAL CAPSTONE: ALL v : BitVec 64)
)

AXFILE="$(mktemp /tmp/vsa_axiom_check.XXXXXX)".lean
mv "${AXFILE%.lean}" "$AXFILE"
{
  echo "import Vsa"
  for t in "${THEOREMS[@]}"; do echo "#print axioms $t"; done
} > "$AXFILE"

AXOUT="$(lake env lean "$AXFILE" 2>&1)"
AXSTATUS=$?
if [ "$AXSTATUS" -ne 0 ]; then
  echo "$AXOUT" >&2
  fail "stage c: lean failed on $AXFILE (unknown theorem or elaboration error)"
fi

AX_OUT="$AXOUT" AX_EXPECTED="${#THEOREMS[@]}" python3 - <<'PYEOF' || fail "stage c: axiom audit failed (see above)"
import os, re, sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
expected = int(os.environ["AX_EXPECTED"])
out = os.environ["AX_OUT"]
bad, seen = [], 0
for line in out.splitlines():
    m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        seen += 1
        axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
        extra = axs - allowed
        if extra:
            bad.append(f"{m.group(1)}: disallowed axioms {sorted(extra)}")
        continue
    m = re.search(r"'([^']+)' does not depend on any axioms", line)
    if m:
        seen += 1
        continue
    if re.search(r"\berror\b", line, re.IGNORECASE):
        bad.append(f"lean error: {line.strip()}")
if seen != expected:
    bad.append(f"expected {expected} '#print axioms' reports, saw {seen}")
print(f"stage c: {seen}/{expected} theorems audited, allowed = {sorted(allowed)}")
if bad:
    print("\n".join(bad), file=sys.stderr)
    sys.exit(1)
PYEOF

rm -f "$AXFILE"
echo "stage c: OK"
echo "check_all: OK"
