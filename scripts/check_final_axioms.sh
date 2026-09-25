#!/usr/bin/env bash
# check_final_axioms.sh — the axiom audit of THE final theorem and its
# concrete-boundary witnesses, on the Iris route (VsaIris), which
# check_all.sh's stage c (`import Vsa` only) cannot see.
#
# Usage: scripts/check_final_axioms.sh          (needs `lake build VsaIris`)
#
# Prints each `#print axioms` report and fails if any theorem depends on an
# axiom outside {propext, Classical.choice, Quot.sound}, or is unknown.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
THEOREMS=(
  Vsa.Sim.EndToEnd.endToEnd_refinement            # VsaIris/Interp/EndToEnd.lean: THE theorem (at `fillZero c`)
  Vsa.Sim.EndToEnd.endToEnd_refinement_loaded     # the same at a literally `Loaded` configuration
  Vsa.Densify.halts_fillZero                      # P3: Halts invariant under the fill-with-zero (Vsa/Densify.lean)
  Vsa.Densify.diverges_fillZero                   # P3: Diverges invariant under the fill-with-zero
  Vsa.Densify.stepOnce_resp                       # P3: stepOnce never inspects byte presence
  VsaIris.Interp.interpSim_iris                   # InterpSim at the concrete layout from IrisHoles
  VsaIris.Interp.term_sim_of                      # term_sim from Supplies + NewlibHoles
  VsaIris.Interp.stuck_sim_of                     # stuck_sim from Supplies + NewlibHoles
  VsaIris.Interp.supplies_of                      # every callee spec closed from IrisHoles
  Vsa.Refine.refinement                           # the generic composition (Vsa/Refinement.lean)
  Vsa.Sim.NativeNameAudit.Control.loaded          # the control witness of `Loaded interpRunLayout`
  Vsa.Sim.NativeNameAudit.Control.loaded_fill     # the same at `fillZero heapConfig` (THE theorem's hypothesis)
  Vsa.Sim.LayoutInstance.all_stackFits            # ProgramStackFits at every c/tests/*.wl embedding
  VsaIris.Interp.ctl_world_counted                # world_of_boundary at the control, counted regime
  VsaIris.Interp.ctl_world_uncounted              # world_of_boundary at the control, uncounted regime
  Vsa.Sim.ConsoleStreamAt.orient                  # P1: the first write orients stdout (agreement form)
  Vsa.Sim.ConsoleStreamAt.orient_logWH            # P1: ORIENT's reflected log (sw; sh) orients stdout
  Vsa.Sim.ConsoleStreamAt.orient_logHW            # P1: ORIENT's reflected log (sh; sw, __swbuf_r)
  Vsa.Sim.orientVfprintf_log                      # P1: _vfprintf_r's ORIENT block, decided
  VsaIris.Stdio.StdioOKAt.orient                  # P1: the image form
  Vsa.Sim.Code.FixedRodataLoaded.byteAt           # P2: the rodata pin after the script
)
AXFILE="$(mktemp /tmp/vsa_final_axioms.XXXXXX)".lean
mv "${AXFILE%.lean}" "$AXFILE"
{
  echo "import VsaIris.Interp.EndToEnd"
  echo "import VsaIris.Interp.WorldVacuity"
  echo "import Vsa.Sim.NativeNameAudit.ControlLoaded"
  echo "import Vsa.Sim.StackAdmissibleWitness"
  echo "import VsaIris.Vsa.StdioOrient"
  for t in "${THEOREMS[@]}"; do echo "#print axioms $t"; done
} > "$AXFILE"
OUT="$(lake env lean "$AXFILE" 2>&1)"; STATUS=$?
rm -f "$AXFILE"
echo "$OUT"
[ "$STATUS" -eq 0 ] || { echo "check_final_axioms: lean failed" >&2; exit 1; }
AX_OUT="$OUT" AX_NAMES="$(printf '%s\n' "${THEOREMS[@]}")" python3 - <<'PYEOF'
import os, re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
out = re.sub(r"\n[ \t]+", " ", os.environ["AX_OUT"])
names = set(os.environ["AX_NAMES"].splitlines()); seen = set(); bad = []
for line in out.splitlines():
    m = re.search(r"'(.*)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        seen.add(m.group(1))
        extra = {a.strip() for a in m.group(2).split(",") if a.strip()} - allowed
        if extra: bad.append(f"{m.group(1)}: disallowed axioms {sorted(extra)}")
    elif re.search(r"\berror\b", line, re.I):
        bad.append(f"lean error: {line.strip()}")
if seen != names: bad.append(f"missing reports for {sorted(names - seen)}")
print(f"check_final_axioms: {len(seen)}/{len(names)} theorems audited, allowed = {sorted(allowed)}")
if bad:
    print("\n".join(bad), file=sys.stderr); sys.exit(1)
PYEOF
