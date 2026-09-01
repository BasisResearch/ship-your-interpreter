# Wave 38 — gen_stagepre + exec-side stmt* class + argsHead + board push

## Board on entry (from wave 37)
- eval-child: 7/14 machine-composed (unary, binaryL, binaryR, logicalL, logicalR,
  assignE, callF). Remaining 7: argsHead, stmtExpr, stmtRet, stmtVarInit,
  stmtIfCond, stmtWhileCond, flCond.
- non-eval (11 exec/args/for fields): named.
- SqEntry: seqHead wired; stmtBlock/callBody named.
- flStep: named.

## ITEM 1 — gen_stagepre.py — DONE + VALIDATED

`scripts/gen_stagepre.py` emits the WHOLE `rows/<Stem>ArmStagePre.lean` 3-step-class
file from a 5-tuple TOML row. The tuple: `{armPC0, operand_off, buf_off, callee, node
naming}`. ALL other literals derived:
- 4 head PCs = armPC0 + {0,4,8,12}
- ld/addi/sd/jal decode words + LE byte splits = read from experiments/disasm.txt
  (`lib.parse_disasm()`, `Instr.word`)
- DecodeTable.Batch imports = looked up per decode word by grepping DecodeTable/
- 21-bit jal J-immediate = decoded from the jal word (`_jimm21`)
- frame sub-constant = 1088 - buf_off
- payload bound = operand_off + 8

Self-verifies (--verify): `lake env lean` + grep sorryAx + axiom-set check, HARD-ERROR
on failure (model = gen_arm_bridge.py).

### Validation (twins regenerated, hand files untouched as guards)
- `scripts/genseg/stagepre/assign.toml` → /tmp/AssignArmStagePreGen.lean:
  GREEN + axiom-clean ({propext, Classical.choice, Quot.sound}). head words
  ld=01063603 addi=0f010513 sd=00d13023 jal=cddff0ef jimm=0x1ffcdc.
- `scripts/genseg/stagepre/call.toml` → /tmp/CallArmStagePreGen.lean:
  GREEN + axiom-clean. head words ld=00863603 addi=06010513 sd=00d13023
  jal=fa9ff0ef jimm=0x1fffa8.
- Semantic diff (code-only, doc-stripped) of generated-vs-hand = IDENTICAL modulo
  two internal hypothesis renames (`hexprHi`/`hexprHi'` vs `hexprHi24`/`hexprHi`,
  self-consistent). Hand files `git status` clean (untouched).
- emitted-vs-hand count: 2 emitted twins reproduce the 2 hand files exactly.

VERDICT: the clone the wave-37 observation flagged is now a mail-merge. Any future
eval-side 3-step `ld+addi+sd→jal` arm-head cut is a 12-line TOML row, not a 380-line
hand clone.

## ITEM 2 — exec-side stmt* class — VERDICT: distinct class, NOT built (recorded)

Surveyed the 6 exec-eval EvalChildStages fields (stmtExpr/stmtRet/stmtVarInit/
stmtIfCond/stmtWhileCond/flCond) at their exec_stmt/for_loop arm PCs.
TWO machine-confirmed obstructions (full detail in observation
`exec-eval-stagepre-frameshift-and-nonuniform`):
- FRAME SHIFT: exec_stmt lowers sp by 176 (@0x80003fe0), not 1088. JalPreBundle
  hardwires x2 = sp-1088 + spill window sp-8..sp-32. Reconcilable only by
  JalPreBundle-ghost `sp := (exec x2)+1088` + a per-frame proof mapping exec_stmt's
  176-byte spill layout (ra@168 s0@160 s1@152 s2@144 s3@136) into the window fields.
  NOT a clone of the eval battery.
- NON-UNIFORM HEADS: surveyed all 6 — they differ in instruction ORDER (mv/addi
  swapped), presence of a mid-head `beqz` null-check (stmtVarInit/…), and even a
  MISSING ld (0x800042dc — a2 preset). ~5 distinct sub-shapes.
UNIFORMITY VERDICT: <3 uniform → do NOT extend gen_stagepre; a separate
`gen_exec_stagepre.py` over a richer head-schema + a reusable `execFrameShift`
core is the right factoring, but the frame-shift lemma is the real risk and must
be proved feasible FIRST (hand, over stmtExpr). Deferred — out of the eval 3-step
scope this wave was chartered for.

## ITEM 3 — argsHead — BLOCKED on the crux agent's arg-loop layer (recorded)

argsHead needs `AEntryC (e::es) → LandedN 1 (JalPreBundle e)` where the arm head is
NOT the 3-instr shape: it is the arg-loop body span 0x800031dc→jal@0x80003220 (~17
instrs of index arithmetic: sext.w, 4× slli/add, addi imm 976, 4 spills), gated by
the loop-entry `blez a5` @0x800031d8. This overlaps the crux agent's `CallArgLoopInv`
(rows/CallClosureSplice.lean, READ-ONLY) at `evalArgsLoopPC`. Building it now would
duplicate their arg-loop work; their layer does not yet EXPOSE a JalPreBundle-landing
cut to consume. Deferred to consume the crux interface once landed (Law 3: factor,
don't clone the third instance).

## ITEM 4 — capstone wiring — no new field this wave

The generator REPRODUCES the two already-wired hand fields (assignE/callF are wired
in `evalChildStages_ublrac_wired`, 7/14). exec+argsHead are deferred (items 2/3), so
no NEW field closed → nothing new to thread into `divFamily_wave34`. The 7/14 builder
`evalChildStages_ublrac_wired` remains the current best. `divFamily_wave34` re-verified
green + axiom-clean (unchanged).

## Board on exit (UNCHANGED field-count; new INFRASTRUCTURE)
- eval-child: **7/14** machine-composed (unary, binaryL, binaryR, logicalL, logicalR,
  assignE, callF). Remaining 7: argsHead (blocked on crux arg-loop), stmtExpr, stmtRet,
  stmtVarInit, stmtIfCond, stmtWhileCond, flCond (all 6 = deferred exec-eval class).
- non-eval (11): named. SqEntry: seqHead wired; stmtBlock/callBody named. flStep: named.
- NEW: `gen_stagepre.py` closes the eval 3-step clone class as a mail-merge.

## Deliverables + verify
- scripts/gen_stagepre.py — the 3-step eval-arm-head stagePre emitter (self-verifying)
- scripts/genseg/stagepre/{assign,call}.toml — the two validation rows
- both regenerated twins GREEN + axiom-clean vs untouched hand guards
- Vsa/Sim/ArmStagesWave34.lean — re-verified green (unchanged)
- observation `exec-eval-stagepre-frameshift-and-nonuniform` appended

## Wiring lines (report-only; Vsa.lean/check_all.sh NOT touched)
No new Vsa.lean import needed (no new .lean row landed; generated twins validated in
/tmp and removed). If a future exec/args stagePre file is emitted, wire it exactly as
AssignArmStagePre: `import Vsa.Sim.rows.<Stem>ArmStagePre` + check_all axiom entries
`Vsa.Sim.blockB_<name>_stagePre` + `Vsa.Sim.<field>_field_of_dispatch`.
