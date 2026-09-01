# Wave 36 — CallSpec calling-convention layer (design + pilot)

Task: design + pilot the CallSpec layer (function-verification exponentiator).
Deliverables: (1) `Vsa/Sim/CallSpec.lean` core + 3 thin pilot instances,
(2) red-zone frame metatheorem (`CallFrameMeta.lean`), (3) `spliceFold`,
(4) pilot re-seat of the strdup tail. This log is the recovery seed.

## Contract survey (done, 2026-09-01)

Studied: `strlen_pre/post` + `strlen_spec_framed` (StrlenSpec.lean:2132/3235),
`PreDispatch`/`memcpy_bytepath_post` + `memcpy_spec_framed_byte`
(MemcpySpec4.lean:340, MemcpySpec.lean:782, MemcpySpecFramed.lean:295),
`MallocContract.spec/freeSpec` (Vsa/Alloc.lean:80/139), `EnvDefFrame` +
the splice zoo (EnvDefCompose.lean), the hand route
(rows/StringifyStrdupTail.lean + rows/StrdupTailContractClose.lean),
`FrameMeta` (abiFrame_of_wrChain / memFrame_of_chain), `WriteLogNF`
(OutL/writeLog_out), `bridgeOfSeg` (BridgeSeg.lean:215), `GRegs/GHolds/gprGet`
(BlockPilot.lean), `storeChainList` (StoreSeg.lean:152 — the fold precedent),
`ConcatMallocPre/Post` (rows/ConcatSeams.lean — the duplication CallSpec kills).

## Canonical ABI-call shape extracted (common to all surveyed contracts)

ENTRY: GoodState ∧ tick<2 ∧ PC=entry ∧ arg-reg pins ∧ x1=ret ∧ ret%4=0 ∧
  (∀R AbiPreserved → get? R = gm R) ∧ mem = m0 ∧ domain side conds.
EXIT: GoodState ∧ tick<2 ∧ PC=ret ∧ result-reg pins(ghosts, res) ∧
  (∀R AbiPreserved ∧ ¬clobber R → get? R = gm R) ∧
  (∀a ∉ foot → mem[a]? = m0[a]?) ∧ domain post(res).

## Design decisions

- `CallSpec (G Res : Type)` is DATA. The ghost pack G carries ALL per-call
  ghosts including the return address (`ret : G → BitVec 64`) and the ABI
  register ghost (`ghost : G → (R : Register) → Option (RegisterType R)`) —
  folding gm/r into G lets `preSide`/`postSide` mention them (memcpy's
  `PreDispatch.hframe` ties NotWrittenB ⊋ AbiPreserved regs to gm; impossible
  if gm were a separate quantifier outside the record's reach).
- Register pins as `GRegs` (= List (Nat × BitVec 64)) + `GHolds` — reuses the
  house pin machinery (gholds_lookup); GPR-only, which all ABI args are.
- `clobber : Register → Bool` — EXPLICIT clobber set = ABI-preserved registers
  the callee is nonetheless allowed to change (∅ for true callees; {x8} would
  have made the strdup s0-reseat falsity unrepresentable-as-a-bug).
- `foot : G → Nat → Prop` — footprint must be Prop-valued, NOT a region list:
  malloc's footprint is `privFoot ∪ stack-window` with privFoot abstract.
- `mem0 : G → Mem` + EntryP demands `c.σ.mem = mem0 g`: canonicalizes the
  memory-transform baseline as THE entry memory. memcpy's PreDispatch is laxer
  (only meminv-outside agreement); instance is narrower — recorded in audit.
- EntryP/ExitP are named-field `structure … : Prop` (R6). Result witness `res`
  is a parameter of ExitP; `ExitPost := fun c => ∃ res, ExitP … res c` (the
  WidenMeta data-field gotcha: Prop structures can't hold data).
- malloc Res := Nat with 0 encoding NULL (postSide carries the null/fresh
  disjunction) — one pin shape `x10 = ofNat res` covers both branches.
- `AInvStableOn AInv exts F` = the ONE canonical (gp-agree ∧ mem-agree-outside-F)
  stability shape; `.mono` transfers big-footprint stability down. Cannot be
  PROVED against MallocContract.AInv (it is an abstract structure field) — it
  stays a premise, but ONE named shape replaces every bespoke hAInvStable*.

## Progress

- [x] survey + design (above)
- [x] CallSpec.lean core + strlen/malloc/memcpy pilots — GREEN, axiom-clean,
      1.4s wall (`lake env lean`). Gotchas hit: `GRegs` needs explicit
      `import Vsa.Sim.BlockPilot`; bare `Arena` ambiguous → `open
      Vsa.RuntimeRepr (Arena)`; record-projection footprints must be unfolded
      by a defeq `have`/`show` before `omega`/`rw` (structure-instance fields
      don't unfold for tactics automatically).
- [x] CallFrameMeta.lean red-zone metatheorem — GREEN, axiom-clean, 1.0s
- [x] SpliceFold.lean — GREEN, axiom-clean, 1.1s
- [x] pilot re-seat rows/StrdupTailSpliceFold.lean — GREEN, axiom-clean, 1.2s
- [x] discipline: `scripts/check_discipline.py` OK (8 rules) with all 4 files
- [x] observations.md: 2 entries appended
      (loaded-batteries-lack-footprint-stability-lemmas,
       record-projection-fields-opaque-to-tactics)

## Measured comparison (pilot re-seat, deliverable 4)

- Elab wall (lake env lean, warm oleans): hand route
  rows/StringifyStrdupTail.lean 1.45s vs new rows/StrdupTailSpliceFold.lean
  1.24s — a WASH; both are pure Triple algebra, imports dominate. The win is
  NOT elaboration time.
- Lines: the new corollary's PROOF is 8 lines (one spliceFold chain, callees
  verbatim). The hand route's proof is 7 lines BUT consumes 3 bespoke
  per-callee splice theorems (envDefStrlenSplice 8 + envDefMallocSplice 33 +
  envDefMemcpyFramedSplice 10 = ~51 lines in EnvDefCompose that exist only to
  nest callSeg around one callee each). Statement/premise size is identical by
  construction (the premises ARE the honest content). NET: every FUTURE call
  sequence saves the entire per-callee splice zoo (~15-35 lines/callee) and
  the fold scales to any arity with zero new theorems.
- RZ metatheorem witnesses on the real strdup staging log:
  strdupMallocSpill_logInRZ (containment, ~12 lines incl. the sext normal
  form) + strdupAInvStableSpill_of_rz (the old hAInvStableSpill premise shape
  DERIVED from one AInvStableOn premise — the per-window family is dead).

## Wiring lines (NOT applied — return to coordinator)

Vsa.lean imports (after the rows/StringifyStrdupTail block):
  import Vsa.Sim.CallSpec
  import Vsa.Sim.CallFrameMeta
  import Vsa.Sim.SpliceFold
  import Vsa.Sim.rows.StrdupTailSpliceFold
check_all axiom-list entries:
  Vsa.Sim.strlenCallSpec_sat  Vsa.Sim.mallocCallSpec_sat
  Vsa.Sim.memcpyByteCallSpec_sat  Vsa.Sim.rzSeamFrame_of_run
  Vsa.Sim.loaded_writeLog_of_rz  Vsa.Sim.spliceFold
  Vsa.Sim.stringifyStrdupTailContract_viaSpliceFold
  Vsa.Sim.strdupMallocSpill_logInRZ  Vsa.Sim.strdupAInvStableSpill_of_rz

## Expressiveness audit (9 contracts vs the CallSpec canonical shape)

1. `strlen_spec_framed` — FITS exactly (pilot landed: `strlenCallSpec_sat`).
   Res=Unit, foot=∅, clobber=∅.
2. `memcpy_spec_framed_byte` — FITS (pilot landed: `memcpyByteCallSpec_sat`).
   Res = the exit register ghost g'; the wider-than-ABI `NotWrittenB` entry tie
   lives in `preSide` — possible ONLY because the register ghost is a G
   projection (`ghost : G → …`), the key record-shape decision. Note: the
   instance is NARROWER than the theorem — EntryP pins `mem = m0` where
   `PreDispatch` only demands meminv-outside agreement; no real use site is
   lost (all instantiate m0 := entry memory).
3. `MallocContract.spec` — FITS (pilot landed: `mallocCallSpec_sat`).
   Res=Nat with 0 ⇒ NULL (one pin shape covers the post disjunction);
   foot = privFoot ∪ stack-window (why foot must be Nat → Prop, not a region
   list); bounded-request proof `hn` is a Prop FIELD of the ghost pack.
4. `MallocContract.freeSpec` — fits, same pattern as 3 (Res=Unit, foot =
   privFoot ∪ freed chunk ∪ stack-window). Not instantiated (no consumer yet).
5. `ReallocOps.grow` — ReallocPre is exactly canonical; post fits with
   postPins=[] and the result surfacing through Res+postSide
   (ReallocGrowResult). memOut needs a small adapter deriving outside-agreement
   from HeapPublicFrame with foot := complement of the heap-public region. Not
   instantiated.
6. `ReallocOps.null` — as 5.
7. `StrcpyContract` (Cpw) — fits, memcpy-pattern: the `StrcpyNotWritten ⊇
   AbiPreserved` tie in preSide/postSide keyed to the G-projected ghost;
   foot=[dst,dst+len+1); Res=Unit. (This is the contract whose NotWritten alias
   was a falsity — under CallSpec the frame alias would have been an explicit
   clobber literal.)
8. `value_str_spec_full` — fits WITH two notes: (a) its exit PC is
   `BitVec.update (r + sext 0) 0 0#1`, = r only under r%4=0 — CallSpec's
   canonical `raAligned` makes the normalization sound but the Sat proof needs
   a small BitVec adapter; (b) it carries `sailOutput = out0` invariance, which
   has no canonical field — expressible in postSide (out0 in G), but console-
   output invariance recurs across the value_* family and may deserve a
   canonical optional field in a v2.
9. `value_equal_spec_full` — expected to fit with foot = the str-handler's
   stack window (its post is a stack-window post); not audited field-by-field.

Staging spans with clobbers (the strdup `mv s0,a0` reseat, AbiExceptS0/S2S3):
representable as CallSpec instances with `clobber := (· == x8)` etc. + postPins
pinning the reseated value — the falsity class becomes explicit data.

## Notes / findings (append as they happen)

- RZ metatheorem design note: AInv gp-agreement should need NO extra premise —
  x3 is AbiPreserved, so the seam's own ABI frame supplies it (vs the per-splice
  hAInvStable* threading which each re-derived gp-agree by hand).
- SpliceChain must be an `inductive … : Prop` (dependent list; a `List` of
  homogeneous rows cannot thread the changing mid-predicates). Prop→Prop
  elimination is fine since Triple is a Prop.
