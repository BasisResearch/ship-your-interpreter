# Wave 37 — hEntry : Triple Pre AllocBuildEntry (EX_FN malloc splice)

## Goal
Build `hEntry` = the malloc splice as first production consumer of the Wave-36
splice layer (CallSpec / CallFrameMeta / SpliceFold). Deliver
`Vsa/Sim/rows/AllocBuildEntrySplice.lean`, instantiate `allocClosureContract_of`,
probe `fnArmSeamRun_of_allocClosure` → `fnArmGeom_hArm_of_seam`.

## Geometry (from disasm.txt + Eval_expr code pins)
- Pre = `fun c => ∃ o ment vv8 vv9 vv18, ArmEntryK g N A SL φf φc' st armPC calleeLoaded (.fn ...) sp r sret aExpr aEnv vv8 vv9 vv18 o m0 ment c` (from FnArmSeamReduce / FnArmGeomReduce).
- Target = `AllocBuildEntry ...` parked at 0x800033d8.
- Chain:
  1. arm-front: armPC → 0x800033c4 (FN arm's own front: `a3 := φf env` decode). OFF-PATH machine.
  2. malloc call seg 0x800033c4→callee: `li a0,16 ; sd a3,0(sp) ; jal malloc` (fnArmMallocCallBridge, GEN).
  3. MallocContract.spec: callee→0x800033d0. (mallocCallSpec_sat EXISTS)
  4. reload block 0x800033d0→0x800033d8: `ld a3,0(sp) ; beqz a0,0x80003e1c` NOT-taken.
     beqz not-taken ⇔ a0≠0 ⇔ no-OOM (M.nonNull_of_bounded, 16≤maxReq).
  5. lands AllocBuildEntry.

## Design decisions
- Reload block: ONE `#derive_case` seg `[ld a3,0(sp)] ▷ beqz(false)` — model EnvDefBridges4.appendHeadSeg (branch-terminated, in-model TKind, no bridgeOfSeg).
- Everything genuinely off-path (arm-front `a3:=φf env` decode; the malloc CallStep marshalling; the AllocBuildEntry field reconstruction from the run) → NAMED doc-commented premises.

## Progress

## LANDED (all axiom-clean {propext, Classical.choice, Quot.sound})
File: `Vsa/Sim/rows/AllocBuildEntrySplice.lean` (223 lines total, 176 code).
`lake env lean Vsa/Sim/rows/AllocBuildEntrySplice.lean` → 3 theorems, all axiom-clean:

1. `fnArmReloadSeg` (#derive_case) + `fnArmReloadRow` — the reload span
   `0x800033d0: ld a3,0(sp) ▷ 0x800033d4: beqz a0,OOM (NOT taken)` → `0x800033d8`.
   Branch-terminated, in-model (TKind.br), NO bridgeOfSeg. Model: EnvDefBridges4.appendHeadSeg.
   beqz decodes BTYPE(0x0a48#13, rs2=0, rs1=10, BEQ) via decode_240504e3.
2. `allocBuildEntry_hEntry` — the malloc splice `Pre → AllocBuildEntry`, ONE spliceFold
   over `SpliceChain.callStep (mallocCallSpec M) g (mallocCallSpec_sat M) staging (.tail tail)`.
   Premises: M (MallocContract), g (MallocG — carries 16≤maxReq via g.hn), staging, tail.
3. `fnArmSeamRun_of_hEntry` — probe: threads hEntry → allocClosureContract_of →
   fnArmSeamRun_of_allocClosure → FnArmSeamRun (== fnArmGeom_hArm_of_seam's hSeam input).
   Confirms the whole downstream pipeline closes modulo ONLY staging + tail.

## hEntry premise list + suppliers
- `M : MallocContract A SL gpv headroom maxReq` — the malloc contract (final-thm hypothesis).
- `g : MallocG maxReq` — malloc ghost pack: n:=16, hn:16≤maxReq (the no-OOM prune input,
  NO separate premise), sp:=sp-1088, r:=0x800033d0, m0:=mMalloc.
- `staging : Triple Pre (mallocCallSpec M).EntryP g` — arm front (`a3:=φf env` decode)
  ≫ fnArmMallocCallBridge (li a0,16; sd a3,0(sp); jal malloc) landing malloc's EntryP.
  SUPPLIER: the arm's own front + the GENERATED fnArmMallocCallBridge.
- `tail : Triple (mallocCallSpec M).ExitPost g AllocBuildEntry` — malloc's NULL-or-success
  ExitP ≫ fnArmReloadRow (reload a3, beqz not-taken = success branch) → AllocBuildEntry@0x800033d8.
  SUPPLIER: the fnArmReloadRow (landed here) + the caller's AllocBuildEntry field reconstruction.

## evalFnSim end-state (what remains for a CLOSED row)
The whole EX_FN arm run `EvalEntry → PreEpilogueV … (.closure a)` is now:
  fnArmGeom_hArm_of_seam (front armEntry_widen + dispatch data + back preEpilogueV_of_writeLog)
    ∘ fnArmSeamRun_of_hEntry (this file)
modulo ONLY the two named machine runs `staging` and `tail`, PLUS
fnArmGeom_hArm_of_seam's own dispatch data (hkind/hslot/hcallee/hcalleeSurv/hexprSurv/
harmAl/htableStk — the jump-table dispatch facts, standard leaf-arm shape shared with
int/null/bool/str). To make evalFnSim a closed row: supply `staging` (arm-front a3-decode
+ malloc-call bridge — the fnArmMallocCallBridge hfacts/hjalSeam residuals) and `tail`
(reload readback: the AllocBuildEntry ~30 fields reconstructed from the malloc-success
ExitP + the reload run — the genuinely off-path field marshalling, analogous to the
strdup StrdupMemcpyContent bundle).

## CallSpec-layer payoff MEASUREMENT
- `allocBuildEntry_hEntry` (the malloc splice proper): 2 machine-run premises
  (staging, tail) + M + g. Proof body = ONE spliceFold line.
- strdup-tail hand equivalent `stringifyStrdupTailContract_closed`
  (StrdupTailContractClose.lean:642): 28 premise lines, incl. THREE distinct
  `hAInvStable*` window-stability families, hjalmem code-survival, hfacts, hmMalloc,
  the memcpy bridge + epilogue bundles; StrdupTailContractClose.lean = 709 lines,
  StrdupTailSpliceFold.lean = 182, EnvDefCompose per-callee splice zoo = 559.
- VERDICT: the CallSpec layer PAYS. malloc rides `mallocCallSpec_sat` verbatim (no
  bespoke MallocPre/MallocPost re-statement, cf. the DUPLICATED ConcatMallocPre/Post
  the doc flagged); the no-OOM prune is g.hn INSIDE the ghost pack (not a threaded
  side-premise); the reload is a 1-block seg. The residual staging/tail seams are the
  IRREDUCIBLE off-path machine (arm-front decode + AllocBuildEntry field marshalling),
  which no combinator can remove — but they are now 2 clean NAMED Triples vs the
  strdup route's 28-line hypothesis tower.

## WIRING (report-only, NOT applied — do not touch Vsa.lean/check_all.sh)
- Vsa.lean: add `import Vsa.Sim.rows.AllocBuildEntrySplice`
  (after `import Vsa.Sim.rows.FnArmSeamReduce` / `import Vsa.Sim.rows.AllocClosureInhab`).
- scripts/check_all.sh axiom list: add
  `Vsa.Sim.fnArmReloadRow`, `Vsa.Sim.allocBuildEntry_hEntry`, `Vsa.Sim.fnArmSeamRun_of_hEntry`.
