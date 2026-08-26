#!/usr/bin/env bash
# abs_inventory.sh — emit a paste-ready "CURRENTLY AVAILABLE ABSTRACTIONS" block for subagent prompts.
# RUN THIS BEFORE EVERY DISPATCH. The abstraction stack grows over time as the parallel coder commits;
# each new subagent must be told what exists so it reuses (never reinvents). COMMITTED files are safe to
# depend on; UNTRACKED files are another workstream's in-flight work — do NOT import them yet.
cd "$(dirname "$0")/.." || exit 2
echo "### CURRENTLY AVAILABLE ABSTRACTIONS — reuse by name (COMMITTED only). HEAD $(git rev-parse --short HEAD)"
echo "# recent stack commits:"
git log --oneline -15 | grep -iE 'abstraction|geom|segeval|seg[- ]?eval|framecalc|frame|heapops|realloc|derive|loopstep|reflect|marshal' | sed 's/^/#   /' || true
FILES=$(ls Vsa/Sim/GeomFacts.lean Vsa/Sim/SegEval*.lean Vsa/Sim/FrameCalc.lean Vsa/Sim/DeriveCase.lean \
           Vsa/Sim/LoopStep.lean Vsa/Sim/HeapOps.lean Vsa/Sim/ReallocSpec.lean Vsa/Sim/EnvDefineClose.lean \
           Vsa/Sim/ErrorSites.lean 2>/dev/null)
for p in $FILES; do
  if git ls-files --error-unmatch "$p" >/dev/null 2>&1; then
    echo "# [COMMITTED — reuse] $p — public API:"
    grep -hE '^(def|theorem|lemma|structure|abbrev|macro|elab|syntax|scoped|class|instance) ' "$p" \
      | sed -E 's/[[:space:]]*(:=|where).*$//' | cut -c1-110 | sed 's/^/#   /' | head -26
  elif [ -f "$p" ]; then
    echo "# [UNTRACKED — do NOT import yet, another workstream mid-edit] $p"
  fi
done
echo "# fast-elab rules: memory/fast-reflection-rules.md (7 laws) — every abstraction file obeys them."
