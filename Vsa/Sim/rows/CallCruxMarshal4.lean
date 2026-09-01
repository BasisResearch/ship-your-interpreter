import Vsa.Sim.rows.CallCruxMarshal2
import Vsa.Sim.rows.CallClosureBodyEntry
import Vsa.Sim.EvalNullSim

/-!
# `CallCruxMarshal4` — the value_null handoff splice (wave 43, items 2+3)

The fold-exit → `BodyHandoff` leg of the amended `hFoldToHandoff`
(`callClosureEntrySplice`, wave-43 amendment): from the value_null staging
config (`0x80003324`, post-fold, s6 restored) run

```
addi a0,sp,144 ▷ jal value_null            (the staging seg + the jal seam)
value_null                                  (the REAL `value_null_spec_full`)
ld a6,32(s5); li s0,0; lw a5,16(a6) ▷ bgtz  (body entry, TAKEN — cd.body ≠ [])
```

and land the FULL `BodyHandoff` at `callBodyLoopPC` — g' := the actual machine
registers, `PhiExtends`, the stack/arena memory frame, `BodyGhostTie`,
`CallerSpillSlots`, and the body `SegEntry` (bound store via the carrier's
`store_survives`, `OutRepr` via the sailOutput thread).

## The bricks

* §1 **`JalStepO`** + **`bridgeOfSegOut`** — the sailOutput-carrying twins of
  `BridgeSeg.JalStep`/`bridgeOfSeg` (the same
  `rowpost-drops-sailoutput-blocks-outrepr` class as wave-42's
  `segToTripleOut`: `bridgeOfSeg`'s conclusion and `JalStep` both DROP the
  output, so `OutRepr` could not cross any jal bridge).  Built on
  `segEval_sound` directly; `JalStepO`'s supplier is the SAME region `site_*`
  jal obs (M6-owned) that supplies `JalStep` — the machine `jal` writes no
  output.
* §2 the enriched body-entry pin list `valueNullBodyL` (x2/x9/x18/x21 — the
  wave-38 row's 1-pin list dropped the pass-throughs `BodyGhostTie` reads) +
  `gprGet_x9`.
* §3 **`ValueNullStage`** — the named-field carrier at `0x80003324`
  (CLAUDE.md R6).  The c-dependent machine residuals (`ChainFacts` of the two
  segs — code-byte pins, M6 class — and the jal seam) are FIELDS, the
  `FoldDefineReturn.spill` idiom; the survival-function fields
  (`store_survives`, `bodyReads`) are the `EvalEntry.store_survives` idiom.
* §4 **`valueNullHandoffSplice`** — the composition, a `Triple` into the REAL
  `BodyHandoff`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no heartbeat raise.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
-- discipline: allow(R7-conj-tower-def) the ∃s here are (a) `JalStepO`/
-- `bridgeOfSegOut` mirroring the FROZEN `BridgeSeg.JalStep`/`bridgeOfSeg`
-- data-carrying shapes (Prop structures cannot carry the ∃-bound MState/fuel,
-- the WidenMeta gotcha), (b) one ∃-pair `spill` field (the sanctioned
-- `FoldDefineReturn.spill` idiom), (c) per-field minstret ∃s.  Every carrier
-- here IS a named-field structure; no anonymous post tower is defined.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The sailOutput-carrying jal bridge -/

/-- **`JalStepO`** — `BridgeSeg.JalStep` + the sailOutput clause.  The machine
`jal` writes only `x1`/PC/minstret, so the region `site_*` obs that supplies
`JalStep` supplies this too; naming it separately keeps the frozen `BridgeSeg`
untouched (the `segToTripleOut` precedent). -/
def JalStepO (calleeEntry link : BitVec 64) (σp : MState) (ip up : Nat) : Prop :=
  ∃ (σ2 : MState) (i2 : Nat),
    Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
    σ2.mem = σp.mem ∧
    σ2.sailOutput = σp.sailOutput ∧
    σ2.regs.get? Register.PC = some calleeEntry ∧
    σ2.regs.get? Register.x1 = some link ∧
    (∃ w, σ2.regs.get? Register.minstret = some w) ∧
    (∀ (n : Nat), 1 ≤ n → n ≤ 31 → n ≠ 1 →
      ∀ (w : BitVec 64), gprGet σp n = some w → gprGet σ2 n = some w) ∧
    (∀ R, AbiPreserved R = true → σ2.regs.get? R = σp.regs.get? R)

/-- **`bridgeOfSegOut`** — `bridgeOfSeg` with the sailOutput threaded through
both the seg body (`segEval_sound` proves it) and the jal step (`JalStepO`).
Everything else is field-for-field `bridgeOfSeg`. -/
theorem bridgeOfSegOut (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (σ : MState) (i u : Nat) (pc0 calleeEntry link vm : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m0)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hi : i < 2)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hAvoid : WrChainAvoidAbi bs)
    (hKeysOut : KeysOK (keysG (evalBlocks bs (SegEvalState.init L lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hjal : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      JalStepO calleeEntry link σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel bs + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some calleeEntry ∧
      σ2.regs.get? Register.x1 = some link ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks bs (SegEvalState.init L lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log ∧
      σ2.sailOutput = σ.sailOutput ∧
      (∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  have habiBody : ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
    abiFrame_of_wrChain hAvoid hframe
  rw [hmem] at hmem'
  obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hout2, hpc2, hra2, hmi2, hnonra2, habiJal⟩ :=
    hjal σ' i' (u + evalBlocksFuel bs) hG' hi' hpc' hmi' hmem' hregs
  refine ⟨σ2, i2, Steps.trans hs (Steps.single hstep2), hi2, hG2, hpc2, hra2, hmi2,
    ?_, ?_, ?_, ?_⟩
  · exact gholds_of_jal hnonra2 _ hKeysOut hRaOut hregs
  · rw [hmem2]; exact hmem'
  · rw [hout2]; exact hout'
  · intro R hR; exact (habiJal R hR).trans (habiBody R hR)

#print axioms bridgeOfSegOut

/-! ## §2. The enriched body-entry pin list -/

/-- The body-entry pin list with the pass-throughs `BodyHandoff` reads at the
exit: `x2` (sp), `x9` (s1, the CALL sret — `BodyGhostTie.sret`), `x18` (s2, the
interp pointer — `BodyGhostTie.interp`), `x21` (s5, the closure record the seg
itself reads at `32(s5)`).  The wave-38 row's 1-pin list is unchanged; this
list re-states the SAME seg through `segToTripleOut` (the task's prescribed
re-statement). -/
def valueNullBodyL (sp sretv ipv clp : BitVec 64) : GRegs :=
  [(2, sp), (9, sretv), (18, ipv), (21, clp)]

/-- The missing battery entry (wave-42 battery has 2/8/10/15/18/19/21/22/23). -/
theorem gprGet_x9 (σ : MState) : gprGet σ 9 = σ.regs.get? Register.x9 := rfl

/-! ## §3. The value_null staging carrier -/

/-- **`ValueNullStage`** — the named-field pin bundle at the value_null staging
entry `0x80003324` (post-fold, `s6` restored; also the no-params route's
landing).  Everything the handoff splice (§4) consumes:

* register pins: `sp`, the CALL sret `sretv` (x9) and interp `ipv` (x18) —
  never written on the closure route past the dispatch, read back at the
  body-loop head by `BodyGhostTie` — and the closure record `clp` (x21).
* `store_survives` — the bound child store's representation, stable under any
  memory change confined to the value_null buffer `[sp+144, sp+168)` (the ONLY
  write left on this leg); the `EvalEntry.store_survives` idiom.
* the three caller spill-slot images (`gs5`@1032, `gs3`@1048, the `s7`@1016
  `m0`-carry) — what `CallerSpillSlots` re-reads at the body-loop head.
* the machine residuals as fields (the `FoldDefineReturn.spill` idiom, all
  M6/code-pin class): `loaded` (value_null's code), `stagefacts` (the staging
  seg's `ChainFacts` — code-byte pins), `jalSeam` (the `jal value_null` obs,
  `JalStepO`-shaped), `bodyReads` (the body-entry seg's `ChainFacts` at any
  buffer-agreeing memory — the `cd->body`/count AST readbacks + the
  `bgtz`-TAKEN guard from `cd.body ≠ []`). -/
structure ValueNullStage
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp sretv ipv clp gs5 gs3 : BitVec 64)
    (bodyLds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x80003324#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  spReg : c.σ.regs.get? Register.x2 = some sp
  sret : c.σ.regs.get? Register.x9 = some sretv
  interp : c.σ.regs.get? Register.x18 = some ipv
  closReg : c.σ.regs.get? Register.x21 = some clp
  /-- The FULLY BOUND child store is represented, stably under the value_null
  buffer write (`EvalEntry.store_survives` idiom). -/
  store_survives : ∀ m' : Mem,
    (∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf' φc (closureBoundStore store' cd vs frame)
  out : OutRepr c.σ st
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?
  /-- `1032..1039(sp)`: the arm ghost's `s5` (spilled at `0x8000328c`). -/
  slot5 : ∀ i : Nat, i < 8 →
    c.σ.mem[sp.toNat + 1032 + i]? = some (gs5.extractLsb' (8 * i) 8)
  /-- `1048..1055(sp)`: the arm ghost's `s3` (spilled at `0x800032ac`). -/
  slot3 : ∀ i : Nat, i < 8 →
    c.σ.mem[sp.toNat + 1048 + i]? = some (gs3.extractLsb' (8 * i) 8)
  /-- `1016..1023(sp)`: the `s7` slot, untouched since the dispatch entry. -/
  slot7 : ∀ i : Nat, i < 8 →
    c.σ.mem[sp.toNat + 1016 + i]? = m0[sp.toNat + 1016 + i]?
  /-- value_null's code loaded (code pin, M6 class). -/
  loaded : Value_nullLoaded c.σ.mem
  /-- The staging seg's `ChainFacts` (code-byte pins at `0x80003324`). -/
  stagefacts : ChainFacts c.σ.mem c.σ.mem (callClosureValueNullCallL sp) []
    callClosureValueNullCallSeg
  /-- The `jal value_null @0x80003328` seam (the region `site_*` obs,
  `JalStepO`-shaped so the output thread survives the step). -/
  jalSeam : ∀ (σ' : MState) (i' u' : Nat),
    GoodState σ' → i' < 2 →
    σ'.regs.get? Register.PC = some (evalBlocksPC 0x80003324#64
      (SegEvalState.init (callClosureValueNullCallL sp) [])
      callClosureValueNullCallSeg) →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    σ'.mem = writeLog c.σ.mem (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).log →
    GHolds σ' (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).regs →
    JalStepO 0x800027ec#64 0x8000332c#64 σ' i' u'
  /-- The body-entry seg's `ChainFacts` at ANY memory agreeing outside the
  value_null buffer: the `ld a6,32(s5)` / `lw a5,16(a6)` AST readbacks
  (`bodyLds`) + the `bgtz`-TAKEN guard (`cd.body ≠ []`) + the code-byte pins
  at `0x8000332c` — all buffer-disjoint, hence stable. -/
  bodyReads : ∀ m2 : Mem,
    (∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = m2[k]?) →
    ChainFacts m2 m2 (valueNullBodyL sp sretv ipv clp) bodyLds
      callClosureBodyEntrySeg

/-! ## §4. The handoff splice -/

/-- **`valueNullHandoffSplice`** — the fold-exit → `BodyHandoff` leg: from the
staging carrier run `addi a0,sp,144 ▷ jal value_null ≫ value_null ≫ body-entry
(bgtz TAKEN)` and land the REAL `BodyHandoff` at `callBodyLoopPC`, with
`g' :=` the reached machine registers.  The g-links (`hgx2`/`hgx9`/`hgx18` for
`BodyGhostTie`, `hgs5`/`hgs3` for `CallerSpillSlots`) and the layout facts
(`hspw` no-wrap, `hNR` buffer region, `hbufStack` buffer ⊆ stack window,
`hdb`/`hab` budgets) are c-independent premises; the machine residuals live in
the carrier (§3). -/
theorem valueNullHandoffSplice
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (d dLeft aLeft : Nat)
    (sp sretv ipv clp gs5 gs3 : BitVec 64)
    (bodyLds : List (List (BitVec 8))) (m0 : Mem)
    (hspw : sp.toNat + 1088 < 2 ^ 64)
    (hNR : NullRegion (sp + 144#64))
    (hbufStack : SL.lo ≤ sp.toNat + 144 ∧ sp.toNat + 168 ≤ SL.hi)
    (hpe : PhiExtends φf φf' st.store.frames.size)
    (hgx2 : g Register.x2 = some sp)
    (hgx9 : g Register.x9 = some sretv)
    (hgx18 : g Register.x18 = some ipv)
    (hgs5 : g Register.x21 = some gs5)
    (hgs3 : g Register.x19 = some gs3)
    (hdb : d + 1 + (dLeft - 1) = maxCallDepth)
    (hab : A.lo + (aLeft - 1) ≤ A.hi) :
    Triple
      (fun c => ValueNullStage N A SL φf' φc st store' cd vs frame
        sp sretv ipv clp gs5 gs3 bodyLds m0 c)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0) := by
  intro c hstage
  obtain ⟨vm, hmi⟩ := hstage.minstret
  -- === leg 1: the staging seg + the jal (sailOutput-carrying bridge) ===
  obtain ⟨σ2, i2, hs1, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hout2, habi2⟩ :=
    bridgeOfSegOut callClosureValueNullCallSeg (callClosureValueNullCallL sp) []
      c.σ c.tick c.steps 0x80003324#64 0x800027ec#64 0x8000332c#64 vm c.σ.mem
      hstage.good hstage.pc hmi rfl ⟨hstage.spReg, trivial⟩
      (by show KeysOK [2]; decide) hstage.stagefacts hstage.tick
      (by show ChainOK 0x80003324#64 [2] callClosureValueNullCallSeg; decide)
      (by show WrChainAvoidAbi callClosureValueNullCallSeg; decide)
      (by show KeysOK [10, 2]; decide)
      (by show ∀ n ∈ ([10, 2] : List Nat), n ≠ 1; decide)
      hstage.jalSeam
  -- the staging seg is memory-pure
  have hmem2' : σ2.mem = c.σ.mem := by rw [hmem2]; rfl
  -- a0 = sp + 144 at the callee entry
  have hx10_2 : σ2.regs.get? Register.x10 = some (sp + 144#64) := by
    have h10 : gprGet σ2 10 = some (sp + sign_extend (m := 64) (0x090#12)) :=
      gholds_reg hregs2 (by rfl)
    rw [gprGet_x10] at h10
    rwa [(by decide : (sign_extend (m := 64) (0x090#12) : BitVec 64) = 144#64)] at h10
  have hloaded2 : Value_nullLoaded σ2.mem := by rw [hmem2']; exact hstage.loaded
  -- === leg 2: the REAL value_null contract (framed variant) ===
  obtain ⟨c3, hs2, hpost3⟩ :=
    value_null_spec_full (fun R => σ2.regs.get? R) (sp + 144#64) 0x8000332c#64
      N φc σ2.mem σ2.sailOutput
      ⟨σ2, i2, c.steps + evalBlocksFuel callClosureValueNullCallSeg + 1⟩
      ⟨hG2, hloaded2, rfl, hpc2, hx10_2, hra2, hmi2, hi2, hNR,
       (by decide), rfl, fun R _ => rfl⟩
  obtain ⟨hG3, hpc3, _hx10_3, _hx1_3, hmi3, hi3, _hVR3, hout3, hmemf3, hfr3⟩ := hpost3
  have hpc3' : c3.σ.regs.get? Register.PC = some (0x8000332c#64 : BitVec 64) := by
    rwa [(by decide : BitVec.update ((0x8000332c#64 : BitVec 64)
      + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x8000332c#64 : BitVec 64))] at hpc3
  -- the buffer window in ℕ terms
  have hbufN : ((sp + 144#64 : BitVec 64)).toNat = sp.toNat + 144 := by
    have hlt := sp.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  -- the whole-leg memory agreement outside the buffer
  have hagree : ∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = c3.σ.mem[k]? := by
    intro k hk
    have hnk : ¬ ((sp + 144#64 : BitVec 64).toNat ≤ k ∧
        k < (sp + 144#64 : BitVec 64).toNat + 24) := by
      rw [hbufN]; intro hc; exact hk ⟨hc.1, by omega⟩
    have h := hmemf3 k hnk
    exact hmem2' ▸ h
  -- === leg 3: the body-entry seg (bgtz TAKEN), enriched pins ===
  have hx2_3 : c3.σ.regs.get? Register.x2 = some sp :=
    (hfr3 _ (by decide)).trans ((habi2 _ (by decide)).trans hstage.spReg)
  have hx9_3 : c3.σ.regs.get? Register.x9 = some sretv :=
    (hfr3 _ (by decide)).trans ((habi2 _ (by decide)).trans hstage.sret)
  have hx18_3 : c3.σ.regs.get? Register.x18 = some ipv :=
    (hfr3 _ (by decide)).trans ((habi2 _ (by decide)).trans hstage.interp)
  have hx21_3 : c3.σ.regs.get? Register.x21 = some clp :=
    (hfr3 _ (by decide)).trans ((habi2 _ (by decide)).trans hstage.closReg)
  have hGH3 : GHolds c3.σ (valueNullBodyL sp sretv ipv clp) :=
    ⟨hx2_3, hx9_3, hx18_3, hx21_3, trivial⟩
  have hCF3 : ChainFacts c3.σ.mem c3.σ.mem (valueNullBodyL sp sretv ipv clp)
      bodyLds callClosureBodyEntrySeg :=
    hstage.bodyReads c3.σ.mem hagree
  obtain ⟨c4, hs3, hHand⟩ :=
    segToTripleOut callClosureBodyEntrySeg (valueNullBodyL sp sretv ipv clp)
      bodyLds 0x8000332c#64 c3.σ.mem c3.σ.sailOutput
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0)
      (by show ChainOK 0x8000332c#64 [2, 9, 18, 21] callClosureBodyEntrySeg; decide)
      (by -- === the BodyHandoff assembly ===
        intro σ4 i4 u4 hG4 hi4 hmem4 hout4 hpc4 hmi4 hregs4
        have hmem4' : σ4.mem = c3.σ.mem := by rw [hmem4]; rfl
        refine ⟨fun R => σ4.regs.get? R, φf', σ4.mem, hpe, ?_, ?_, ?_, ?_⟩
        · -- the stack/arena memory frame back to the dispatch-entry m0
          intro a hSL hA
          rw [hmem4']
          have h1 : c.σ.mem[a]? = c3.σ.mem[a]? := by
            refine hagree a (fun hc => hSL ⟨by omega, by omega⟩)
          rw [← h1]
          exact hstage.memFrame a hSL hA
        · -- BodyGhostTie g g' (g' := the actual registers)
          refine ⟨?_, ?_, ?_⟩
          · show σ4.regs.get? Register.x2 = g Register.x2
            rw [hgx2, ← gprGet_x2]
            exact gholds_reg hregs4 (by rfl)
          · show σ4.regs.get? Register.x9 = g Register.x9
            rw [hgx9, ← gprGet_x9]
            exact gholds_reg hregs4 (by rfl)
          · show σ4.regs.get? Register.x18 = g Register.x18
            rw [hgx18, ← gprGet_x18]
            exact gholds_reg hregs4 (by rfl)
        · -- CallerSpillSlots (the slot images survive: buffer-disjoint)
          intro spv hspv
          have hspv' : spv = sp := by
            rw [hgx2] at hspv; exact (Option.some.inj hspv).symm
          rw [hspv']
          refine ⟨?_, ?_, ?_⟩
          · intro w hw i hi
            have hw' : gs5 = w := by
              rw [hgs5] at hw; exact Option.some.inj hw
            rw [← hw', hmem4', ← hagree (sp.toNat + 1032 + i) (by omega)]
            exact hstage.slot5 i hi
          · intro w hw i hi
            have hw' : gs3 = w := by
              rw [hgs3] at hw; exact Option.some.inj hw
            rw [← hw', hmem4', ← hagree (sp.toNat + 1048 + i) (by omega)]
            exact hstage.slot3 i hi
          · intro i hi
            rw [hmem4', ← hagree (sp.toNat + 1016 + i) (by omega)]
            exact hstage.slot7 i hi
        · -- the body SegEntry at callBodyLoopPC (g' := actual regs, by rfl)
          refine { good := hG4, tick := hi4, pc := ?_, store := ?_, out := ?_,
                   mem := rfl, frame := fun R _ => rfl,
                   depth_budget := hdb, arena_budget := hab }
          · rw [hpc4]; rfl
          · show StoreRepr σ4.mem N A φf' φc
              (closureBoundSt st store' cd vs frame).store
            rw [hmem4']
            exact hstage.store_survives c3.σ.mem hagree
          · exact outRepr_transport (hout4.trans (hout3.trans hout2)) hstage.out)
      c3 ⟨⟨hG3, rfl, hpc3', hmi3, hGH3,
        (by show KeysOK [2, 9, 18, 21]; decide), hCF3, hi3⟩, rfl⟩
  exact ⟨c4, Steps.trans hs1 (Steps.trans hs2 hs3), hHand⟩

#print axioms valueNullHandoffSplice

/-! ## §5. The LAST-iteration env_define return (the amended `hFoldToHandoff`'s
machine head)

Per the wave-43 amendment (ledger `callparamfold-carrier-n-unreachable`) the
LAST fold iteration belongs to the handoff leg: after its `env_define` returns
(`0x80003314`) the back-edge `bne` FALLS THROUGH (`8·n = 8·n`) and the machine
restores `s6` and parks at the value_null staging `0x80003324`.  The pin
bundle mirrors `FoldDefineReturn` (CallCruxMarshal2 §3) but with the
EXIT-polarity seg (`callClosureFoldBackExitSeg`, two loads) and carrying the
`ValueNullStage` payload fields — everything §6 transports through the
memory-pure exit span. -/

/-- The exit-polarity pin list: sp, the pass-throughs (x9/x18/x21 —
`ValueNullStage`'s pins), and the fold bound (x22, the `bne` source; the exit
span then OVERWRITES x22 with the `1024(sp)` restore). -/
def foldExitL (sp sretv ipv clp s6v : BitVec 64) : GRegs :=
  [(2, sp), (9, sretv), (18, ipv), (21, clp), (22, s6v)]

/-- **`FoldDefineExitReturn`** — the pin bundle at the LAST `env_define`
return.  `spill` carries the exit-seg `ChainFacts` (the reloaded-index and
`s6`-restore readbacks `ib`/`s6b`, ∃-bound; its bne NOT-taken guard is the
supplier's `8·n = 8·(k+1)` — dual to the loop row's, cf.
`foldBackLoop_facts_last_false`).  The payload fields are stated at THIS
config; §6 transports them (the exit span is memory-pure and writes only
x15/x22). -/
structure FoldDefineExitReturn
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp sretv ipv clp gs5 gs3 : BitVec 64)
    (bodyLds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x80003314#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  spReg : c.σ.regs.get? Register.x2 = some sp
  sret : c.σ.regs.get? Register.x9 = some sretv
  interp : c.σ.regs.get? Register.x18 = some ipv
  closReg : c.σ.regs.get? Register.x21 = some clp
  /-- `s6` — the fold bound `8·n` (the `bne` source; restored right after). -/
  bound : c.σ.regs.get? Register.x22
    = some (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)
  /-- The exit-seg readbacks + facts (index reload `ib`, `s6` restore `s6b`). -/
  spill : ∃ (ib s6b : List (BitVec 8)),
    ChainFacts c.σ.mem c.σ.mem
      (foldExitL sp sretv ipv clp
        (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length))
      [ib, s6b] callClosureFoldBackExitSeg
  -- === the ValueNullStage payload (transported verbatim by §6) ===
  store_survives : ∀ m' : Mem,
    (∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf' φc (closureBoundStore store' cd vs frame)
  out : OutRepr c.σ st
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?
  slot5 : ∀ i : Nat, i < 8 →
    c.σ.mem[sp.toNat + 1032 + i]? = some (gs5.extractLsb' (8 * i) 8)
  slot3 : ∀ i : Nat, i < 8 →
    c.σ.mem[sp.toNat + 1048 + i]? = some (gs3.extractLsb' (8 * i) 8)
  slot7 : ∀ i : Nat, i < 8 →
    c.σ.mem[sp.toNat + 1016 + i]? = m0[sp.toNat + 1016 + i]?
  loaded : Value_nullLoaded c.σ.mem
  stagefacts : ChainFacts c.σ.mem c.σ.mem (callClosureValueNullCallL sp) []
    callClosureValueNullCallSeg
  jalSeam : ∀ (σ' : MState) (i' u' : Nat),
    GoodState σ' → i' < 2 →
    σ'.regs.get? Register.PC = some (evalBlocksPC 0x80003324#64
      (SegEvalState.init (callClosureValueNullCallL sp) [])
      callClosureValueNullCallSeg) →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    σ'.mem = writeLog c.σ.mem (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).log →
    GHolds σ' (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).regs →
    JalStepO 0x800027ec#64 0x8000332c#64 σ' i' u'
  bodyReads : ∀ m2 : Mem,
    (∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = m2[k]?) →
    ChainFacts m2 m2 (valueNullBodyL sp sretv ipv clp) bodyLds
      callClosureBodyEntrySeg

/-! ## §6. The exit-span run: `FoldDefineExitReturn → ValueNullStage` -/

/-- **`foldDefineExitReturn_step`** — run the exit back-edge (`ld a5,0(sp) ;
addi ▷ bne NOT taken ;; ld s6,1024(sp)`) and transport the payload to the
value_null staging carrier: pins via the exit `GHolds` pass-throughs, the
memory fields by the span's memory purity, `OutRepr` via `segToTripleOut`'s
sailOutput carry. -/
theorem foldDefineExitReturn_step
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp sretv ipv clp gs5 gs3 : BitVec 64)
    (bodyLds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (fun c => FoldDefineExitReturn N A SL φf' φc st store' cd vs frame
        sp sretv ipv clp gs5 gs3 bodyLds m0 c)
      (fun c => ValueNullStage N A SL φf' φc st store' cd vs frame
        sp sretv ipv clp gs5 gs3 bodyLds m0 c) := by
  intro c hp
  obtain ⟨ib, s6b, hfacts⟩ := hp.spill
  have hGH : GHolds c.σ (foldExitL sp sretv ipv clp
      (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) :=
    ⟨hp.spReg, hp.sret, hp.interp, hp.closReg, hp.bound, trivial⟩
  exact (segToTripleOut callClosureFoldBackExitSeg
      (foldExitL sp sretv ipv clp
        (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length))
      [ib, s6b] 0x80003314#64 c.σ.mem c.σ.sailOutput
      (fun c' => ValueNullStage N A SL φf' φc st store' cd vs frame
        sp sretv ipv clp gs5 gs3 bodyLds m0 c')
      (by show ChainOK 0x80003314#64 [2, 9, 18, 21, 22] callClosureFoldBackExitSeg
          decide)
      (by intro σ' i' u' hG' hi' hmem' hout' hpc' hmi' hregs'
          have hmm : σ'.mem = c.σ.mem := by rw [hmem']; rfl
          refine { good := hG', tick := hi', pc := ?_, minstret := hmi',
                   spReg := ?_, sret := ?_, interp := ?_, closReg := ?_,
                   store_survives := ?_, out := ?_, memFrame := ?_,
                   slot5 := ?_, slot3 := ?_, slot7 := ?_, loaded := ?_,
                   stagefacts := ?_, jalSeam := ?_, bodyReads := ?_ }
          · rw [hpc']; rfl
          · rw [← gprGet_x2]; exact gholds_reg hregs' (by rfl)
          · rw [← gprGet_x9]; exact gholds_reg hregs' (by rfl)
          · rw [← gprGet_x18]; exact gholds_reg hregs' (by rfl)
          · rw [← gprGet_x21]; exact gholds_reg hregs' (by rfl)
          · intro m' hag
            refine hp.store_survives m' ?_
            intro k hk
            exact hmm ▸ hag k hk
          · exact outRepr_transport hout' hp.out
          · intro a h1 h2
            rw [hmm]; exact hp.memFrame a h1 h2
          · intro i hi; rw [hmm]; exact hp.slot5 i hi
          · intro i hi; rw [hmm]; exact hp.slot3 i hi
          · intro i hi; rw [hmm]; exact hp.slot7 i hi
          · show Value_nullLoaded σ'.mem
            rw [hmm]; exact hp.loaded
          · show ChainFacts σ'.mem σ'.mem (callClosureValueNullCallL sp) []
              callClosureValueNullCallSeg
            rw [hmm]; exact hp.stagefacts
          · intro σ'' i'' u'' hG'' hi'' hpc'' hmi'' hmem'' hregs''
            refine hp.jalSeam σ'' i'' u'' hG'' hi'' hpc'' hmi'' ?_ hregs''
            rw [← hmm]; exact hmem''
          · intro m2 hagr
            refine hp.bodyReads m2 ?_
            intro k hk
            exact hmm ▸ hagr k hk)) c
    ⟨⟨hp.good, rfl, hp.pc, hp.minstret, hGH,
      (by show KeysOK [2, 9, 18, 21, 22]; decide), hfacts, hp.tick⟩, rfl⟩

#print axioms foldDefineExitReturn_step

/-! ## §7. The amended `hFoldToHandoff` composed -/

/-- **`foldToHandoff_of`** — the amended `hFoldToHandoff` leg from its three
named machine pieces: the LAST iteration's staging hop (`hStage`, the
`callClosureFoldStageBridge` marshalling into the env_define pre), the
env_define contract (`hDefine`), and the return-pin readback (`hPins`,
`FoldDefineExitReturn`-shaped) — then the landed exit span (§6) and value_null
handoff splice (§4).  Together with `callParamFoldSeamStep`
(CallCruxMarshal2 §5, the `k+1 < n` seams) this closes the machine content of
`callClosureEntrySplice`'s fold route to per-leg `(hStage, hDefine, hPins)`
suppliers. -/
theorem foldToHandoff_of
    (g : (R : Register) → Option (RegisterType R))
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φf' φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {d dLeft aLeft : Nat}
    {sp fp clp sretv ipv gs5 gs3 : BitVec 64}
    {bodyLds : List (List (BitVec 8))} {m0 : Mem} {k : Nat}
    (hspw : sp.toNat + 1088 < 2 ^ 64)
    (hNR : NullRegion (sp + 144#64))
    (hbufStack : SL.lo ≤ sp.toNat + 144 ∧ sp.toNat + 168 ≤ SL.hi)
    (hpe : PhiExtends φf φf' st.store.frames.size)
    (hgx2 : g Register.x2 = some sp)
    (hgx9 : g Register.x9 = some sretv)
    (hgx18 : g Register.x18 = some ipv)
    (hgs5 : g Register.x21 = some gs5)
    (hgs3 : g Register.x19 = some gs3)
    (hdb : d + 1 + (dLeft - 1) = maxCallDepth)
    (hab : A.lo + (aLeft - 1) ≤ A.hi)
    {PreDef PostDef : Config → Prop}
    (hStage : Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
      PreDef)
    (hDefine : Triple PreDef PostDef)
    (hPins : ∀ c, PostDef c →
      FoldDefineExitReturn N A SL φf' φc st store' cd vs frame
        sp sretv ipv clp gs5 gs3 bodyLds m0 c) :
    Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0) :=
  Triple.seq hStage (Triple.seq hDefine
    (Triple.seq
      (fun c hc =>
        foldDefineExitReturn_step N A SL φf' φc st store' cd vs frame
          sp sretv ipv clp gs5 gs3 bodyLds m0 c (hPins c hc))
      (valueNullHandoffSplice g N A SL φf φf' φc st store' cd vs frame
        d dLeft aLeft sp sretv ipv clp gs5 gs3 bodyLds m0
        hspw hNR hbufStack hpe hgx2 hgx9 hgx18 hgs5 hgs3 hdb hab)))

#print axioms foldToHandoff_of

end Vsa.Sim
