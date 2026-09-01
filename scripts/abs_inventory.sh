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
           Vsa/Sim/ErrorSites.lean \
           Vsa/Sim/DeriveCallSeg.lean Vsa/Sim/DeriveLoop.lean Vsa/Sim/DeriveErrorSite.lean \
           Vsa/Sim/DeriveCaseRow.lean Vsa/Sim/ChainFactsTac.lean \
           Vsa/Sim/FrameMeta.lean Vsa/Sim/BridgeSeg.lean Vsa/Sim/BridgeSegFramed.lean Vsa/Sim/WidenMeta.lean \
           Vsa/Sim/SegReadback.lean Vsa/Sim/TermBundles.lean Vsa/Sim/TermImageGeom.lean \
           Vsa/Sim/EnvDefSeg.lean Vsa/Sim/EnvGetMarshal.lean Vsa/Sim/WriteLogNF.lean \
           Vsa/Sim/StepCount.lean Vsa/Sim/MidArmCombinator.lean Vsa/Sim/EvalChildFieldCombinator.lean \
           Vsa/Sim/ArmSegSplit*.lean Vsa/Sim/StagePreSuppliers*.lean \
           Vsa/Sim/ArmStagesPartial.lean Vsa/Sim/ArmStagesWave34.lean Vsa/Sim/SeqHeadStages.lean \
           Vsa/Sim/ApproxArmResidGapAssembly.lean Vsa/Sim/StoreSeg.lean \
           Vsa/Sim/DeriveMetaTowers.lean Vsa/Sim/DeriveRow.lean \
           Vsa/Sim/rows/ArmPostGeom.lean Vsa/Sim/rows/LoopSteps.lean \
           Vsa/Sim/rows/BinArmBridge.lean Vsa/Sim/rows/UnaryLogicalArmBridge.lean \
           Vsa/Sim/rows/ConcatSeams.lean Vsa/Sim/rows/BlockCConcat.lean \
           Vsa/Sim/rows/FnArmClosureBuild.lean 2>/dev/null)
for p in $FILES; do
  if git ls-files --error-unmatch "$p" >/dev/null 2>&1; then
    echo "# [COMMITTED — reuse] $p — public API:"
    grep -hE '^(def|theorem|lemma|structure|abbrev|macro|elab|syntax|scoped|class|instance) ' "$p" \
      | sed -E 's/[[:space:]]*(:=|where).*$//' | cut -c1-110 | sed 's/^/#   /' | head -26
  elif [ -f "$p" ]; then
    echo "# [UNTRACKED — do NOT import yet, another workstream mid-edit] $p"
  fi
done
echo "### GENERATED seg rows (rows/*Gen.lean) — these segs ALREADY EXIST; NEVER re-derive their spans:"
for g in Vsa/Sim/rows/*Gen.lean; do
  [ -f "$g" ] || continue
  if git ls-files --error-unmatch "$g" >/dev/null 2>&1; then tag="COMMITTED"; else tag="UNTRACKED — do NOT import yet"; fi
  echo "# [$tag] $g:"
  grep -hE '^#derive_case|^def |^theorem ' "$g" | sed -E 's/[[:space:]]*(:=|where).*$//' | cut -c1-110 | sed 's/^/#     /' | head -6
done
echo "### ALL #derive_case seg names in the repo — grep this list BEFORE writing any new seg (name AND span):"
git grep -h '^#derive_case' -- 'Vsa/**/*.lean' 2>/dev/null | awk '{print "#   " $2}' | sort -u
echo "# fast-elab rules: memory/fast-reflection-rules.md (7 laws) — every abstraction file obeys them."
echo "# MANDATORY task-shape->tool table + discipline laws: CLAUDE.md (gate-enforced, check_all stage a4)."
echo "# missing-general-fact observations channel: experiments/observations.md (append at the moment of noticing)."
