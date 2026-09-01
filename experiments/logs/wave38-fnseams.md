# Wave 38 — close evalFnSim: the `staging` and `tail` seams of `allocBuildEntry_hEntry`

## Goal
`AllocBuildEntrySplice.lean` (committed) delivered `allocBuildEntry_hEntry` = ONE
spliceFold taking two Triple premises:
- `staging : Triple Pre (mallocCallSpec M).EntryP g`
- `tail : Triple (mallocCallSpec M).ExitPost g AllocBuildEntry`
Close both (or maximally reduce them to named typed premises), then give the
evalFnSim verdict.

## Geometry (disasm.txt)
FN closure-alloc arm — reached by `jr a5` (jump table) landing at 0x800033c4:
```
  armPC → 0x800033c4      arm-front: a3 := φf env decode  (OFF-PATH, small span; armPC is a FREE var in the pipeline)
  800033c4: li a0,16      \
  800033c8: sd a3,0(sp)    } fnArmMallocCallSeg + fnArmMallocCallBridge (GEN, landed)
  800033cc: jal malloc    /   → malloc EntryP @ mallocEntry(0x80004790), link 0x800033d0
  ← malloc ret 0x800033d0     mallocCallSpec_sat (Wave-36)
  800033d0: ld a3,0(sp)   \  fnArmReloadSeg + fnArmReloadRow (landed in AllocBuildEntrySplice)
  800033d4: beqz a0,OOM   /   NOT taken (no-OOM edge, g.hn:16≤maxReq)
  800033d8 = AllocBuildEntry
```

## KEY FINDINGS (mechanisms available)
- `mallocCallSpec M` (CallSpec.lean): EntryP fields = good/tick/pc/args/ra/raAligned/abi/mem/side.
  - prePins g = [(10, ofNat g.n), (2, g.sp), (3, gpv)]  → a0=16, sp, gp
  - entry g = ofNat mallocEntry;  ret g = g.r;  mem0 g = g.m0
  - preSide g c = StackOK SL g.sp headroom ∧ M.AInv c.σ g.exts
  - foot g a = M.privFoot a ∨ (SL.lo ≤ a ∧ a < g.sp.toNat)   ← the red-zone footprint
- ExitP fields = good/tick/pc(=ret g)/rets/frame/memOut/side.
  - postSide = NULL(res=0) ∨ success(res≠0 ∧ res%16=0 ∧ A.contains res n ∧ disjoint ∧ AInv (res::exts))
  - M.nonNull_of_bounded collapses the disjunction to success for n ≤ maxReq.
- `fnArmMallocCallBridge` (GEN): from a config pinned at 0x800033c4 (x2=sp',x13=a3),
  runs `li a0,16; sd a3,0(sp)` and jal-seams to malloc entry 0x80004790, link 0x800033d0.
  Residuals hfacts (chain_facts) + hjalSeam (JalStep off the callee site obs).
- `fnArmReloadRow` (landed): SegPre @ 0x800033d0 (x2=sp',x10=a0) → FnArmReloadPost @ 0x800033d8.
- `rzSeamFrame_of_run` + `LogInRZ` (CallFrameMeta): the ONE frame metatheorem for
  spill-window disjointness / AInv / code survival — use instead of hand hAInvStable* threading.

## Design: what's mechanizable vs irreducible
- The malloc EntryP register pins a0=16/sp/gp, ra, mem=mMalloc: come from the arm-front +
  fnArmMallocCallBridge landing. The arm-front itself (armPC→0x800033c4 with a3:=φf env,
  a0/sp/gp set) is genuinely off-path AND armPC is a FREE var (caller-instantiated), so it
  cannot be a concrete seg here — it is a NAMED premise (the arm-front linkage bundle).
- The reload + no-OOM prune + AllocBuildEntry ~30-field reconstruction: fnArmReloadRow lands
  the config at 0x800033d8; the fields (hExprRepr/hOld/hCodeSurvive/hMpreFrame/hSpillReads/
  hframe geometry) transport ExprRepr/StoreRepr/code across the malloc call via the CallSpec
  ExitP.memOut (reads outside foot unchanged) — the transport the CallSpec `foot`/memOut is FOR.

## Progress

### LANDED (tail side) — Vsa/Sim/rows/FnArmSeams.lean, axiom-clean
- `prune_of_exit` — malloc ExitPost disjunction → success block via M.nonNull_of_bounded.
  Returns p + geometry + memOut (the transport clause). Reusable.
- `AllocBuildTailFacts` — named-field bundle (~28 fields) = the arm-entry-carried facts
  that the reload span + ExitP cannot manufacture (ExprRepr/StoreRepr/sret-geom/spills/
  x8/x13/x9 + the malloc-result geometry pnz/align/arena). Transported across malloc via
  ExitP.memOut. This IS the `tail`-seam analog of StrdupMemcpyContent.
- `allocBuildEntry_tail` — the `tail` seam CLOSED modulo ONE caller linkage `hReload`
  (reload run on the pruned config → 0x800033d8 + the bundle survives) + the bundle.
  Body = consume hReload, refine AllocBuildEntry from named fields. NO positional nav.
  GREEN, axiom-clean {propext, Classical.choice, Quot.sound}.

KEY: `tail`'s post fixes `p` (= φc' store.size, the store-side alloc index) as a
parameter, so malloc's result MUST land at `p`. The result-vs-p tie is folded into the
`hReload` linkage (its x10 = ofNat p output), not a separate fragile ofNat-injectivity.

### LANDED (staging side) — Vsa/Sim/rows/FnArmSeams.lean, axiom-clean
- `AllocBuildStagingLink` — named-field bundle = the arm-front residual (Pre → config
  at 0x800033c4, x13=a3=φf env, x2=sp, gp, ABI frame, mem=m0, StackOK, AInv-at-entry
  survival closure, hjalSeam + key-hygiene). armPC is FREE ⇒ the front cannot be a seg;
  it is this named premise.
- `staging_of_link` — runs `fnArmMallocCallBridge` off the link config, assembles malloc's
  canonical `EntryP` at mallocEntry(0x80004790), link 0x800033d0. a0=16 via
  sign_extend 0x010 = ofNat gMal.n (probed by rfl); sp/gp/ra/mem/abi/StackOK/AInv all
  derived. Needs gMal.n=16, gMal.r=0x800033d0. GREEN, axiom-clean.

### LANDED (capstone) — fnArmSeamRun_of_seams
- Threads staging_of_link + allocBuildEntry_tail into fnArmSeamRun_of_hEntry
  (AllocBuildEntrySplice) → FnArmSeamRun. GREEN, axiom-clean.

## evalFnSim VERDICT
NOT a fully closed row yet. The pipeline to `FnArmSpec` (= evalFnSim's hArm premise) is:
  fnArmSeamRun_of_seams → FnArmSeamRun
    → fnArmGeom_hArm_of_seam (FnArmGeomReduce) → FnArmGeom.hArm
      → fnArmSpec_of_geom (ArmSpecBridge) → FnArmSpec → evalFnSim (hArm hAlloc)

REMAINING named premises for a CLOSED evalFnSim row:
1. **The two off-path machine bundles (this wave's residuals, IRREDUCIBLE)**:
   - `hLink : Triple Pre (AllocBuildStagingLink Malloc gMal a3)` — arm-front a3:=φf env
     decode + AInv survival + jal seam. armPC free ⇒ no combinator removes it.
   - `hReload` = the reload run (fnArmReloadRow on the pruned config → 0x800033d8) +
     `AllocBuildTailFacts` bundle (~28 arm-entry-carried fields transported via ExitP.memOut).
2. **fnArmGeom_hArm_of_seam's 8 dispatch facts** (hkle/hklt/hkind/hslot/hcallee/
   hcalleeSurv/hexprSurv/harmAl/htableStk) — the STANDARD leaf-arm jump-table dispatch
   shape shared with int/null/bool/str; a mechanical clone, NOT new work.
3. **fnArmSpec_of_geom's hfr/hcl** (store-size monotonicity) — trivial from allocClosure
   (frames unchanged, closures +1).
4. `_hEval` (the EvalE.fn spec-side judgment) + hAlloc (allocClosure = (store',a)) — the
   recursor's own premise, supplied by the mutual-recursor scaffolding.

So this wave reduced `staging`/`tail` from "the two premises of allocBuildEntry_hEntry"
to two clean NAMED bundles (AllocBuildStagingLink + AllocBuildTailFacts) each consumed
through a single destructurer, and confirmed (by construction, axiom-clean) that the
ENTIRE FnArmSeamRun→FnArmSpec pipeline closes modulo (1)+(2)+(3)+(4). No sorry anywhere.

## WIRING (report-only, NOT applied)
- Vsa.lean: add `import Vsa.Sim.rows.FnArmSeams`
  (after `import Vsa.Sim.rows.AllocBuildEntrySplice`).
- scripts/check_all.sh axiom list: add
  `Vsa.Sim.prune_of_exit`, `Vsa.Sim.allocBuildEntry_tail`,
  `Vsa.Sim.staging_of_link`, `Vsa.Sim.fnArmSeamRun_of_seams`.

## COMPLETE (2026-09-01)
`Vsa/Sim/rows/FnArmSeams.lean` — 5 theorems + 3 named-field structures, all GREEN via
`lake env lean`, all axiom-clean {propext, Classical.choice, Quot.sound}, discipline OK
(R7 allow with justification — every new post/entry IS a named-field structure; residual
∃ are run-witnesses + verbatim relays of landed signatures). No sorry/axiom/native/bv.

DELIVERED:
- `prune_of_exit`, `AllocBuildTailFacts`, `allocBuildEntry_tail` — the `tail` seam.
- `AllocBuildReloadPost` — named reload-linkage post (R7-compliant).
- `AllocBuildStagingLink`, `staging_of_link` — the `staging` seam.
- `fnArmSeamRun_of_seams` — capstone: whole FnArmSeamRun modulo the two named bundles.

## SIGNALS / lessons
- The CallSpec `foot`/`memOut` transport IS the tool for carrying ExprRepr/StoreRepr/
  code/spills across the malloc call — but it needs the arm-entry VALUES as inputs, so
  the transport still bottoms out in a caller-supplied named bundle (AllocBuildTailFacts).
  No combinator removes that; it is the irreducible off-path field marshalling the doc
  comments anticipated (analog of StrdupMemcpyContent).
- `tail`'s post fixing `p` (store-side alloc index) means malloc's result MUST land at p;
  folded into the reload linkage output (x10=ofNat p), avoiding a fragile ofNat-injective
  Nat identity — the reload run already reads x10 as ofNat p from the pruned exit.
- probe: `sign_extend 0x010 = 16#64 = ofNat gMal.n` (gMal.n=16) by decide; a0 reads back
  via gholds_lookup + this rewrite — the standard li/mv reflect idiom.
- gprGet c.σ 10 = c.σ.regs.get? Register.x10 definitionally, but `rw [hx10]` on a `get?`
  target fails to find the `gprGet` LHS — restate the hyp with `have : get? = ...` first.

## BLOCKERS (for a fully CLOSED evalFnSim row)
NONE new. The remaining premises are (1) the two irreducible off-path bundles landed here
as named residuals, (2) fnArmGeom_hArm_of_seam's 8 jump-table dispatch facts (a mechanical
int/null/bool/str-shaped clone), (3) fnArmSpec_of_geom's trivial store-size monotonicity,
(4) the recursor's own hEval/hAlloc. evalFnSim is NOT yet a closed row, but the whole
FnArmSeamRun→FnArmSpec pipeline is confirmed (axiom-clean, by construction) to close
modulo exactly these.
