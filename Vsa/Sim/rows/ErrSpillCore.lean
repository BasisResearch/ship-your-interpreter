import Vsa.Sim.BridgeSegFramed

/-!
# `ErrSpillCore` — the seg-GENERIC spill-prefix→jal bridge (Family A)

`BridgeSegFramed.spillNeg_toJalErr` closed ONE error link (`hNegType`, jal
`0x800034e4`) over its hand-emitted 5-`sd` spill seg.  Eight of the 19 distinct
`jal runtime_error` sites share EXACTLY that shape — the jal is immediately
preceded by a contiguous run of `sd sN,off(sp)` callee-saved spills (the message
pointer is already staged in `a0..a2` before the run), so:

  * every prefix instruction is a `.sd` STORE — it writes MEMORY, not the
    registers `s3..s7`; `wrChain spillSeg = []`.  The seg frame preserves EVERY
    non-noise register for free (`x10 = inp` + the whole `NotWrittenJmp`
    `g`-frame carry from entry to the jal PC).
  * the ONLY real obligation is the memory side: the post-spill memory
    `writeLog m0 spillLog` still carries the `runtime_error`/`longjmp` images
    (`code ⊥ stack`) — the arm's named `Runtime_errorLoaded S.m0 ∧ LongjmpLoaded
    S.m0` datum.

This file factors `spillNeg_toJalErr` into ONE seg-parametric lemma
`spillSeg_toJalErr` over an arbitrary spill seg `bs` with `wrChain bs = []` (the
"pure stores" datum, one `decide` per site) and a NAMED-FIELD entry structure
`SpillArmPre` (per R7 — never an anonymous ∃/∧ tower).  Per-site files then emit
only the `#derive_case` for `bs` and a thin instantiation.  `negType_link_closed`
is recovered as `bs := spillNegSeg`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)
open Vsa.While
open Register

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-- **The seg-generic spill-prefix entry predicate.**  A config parked at a spill
block entry `pc0` with everything the seg + the `runtime_error` entry demand, for
an ARBITRARY pure-store spill seg `bs` ending at the jal PC `pcJal` (bytes
`b0..b3`).  Named-field (R7): the seg's `GoodState`/PC/minstret/`GHolds`/`KeysOK`/
`ChainFacts`/`ChainOK`, the entry memory `m0`, `tick < 2`, the `ErrorIn` pointer
in `x10` with its `WinRAM`, the `g` ghost frame over `NotWrittenJmp` (all at
ENTRY — pure stores preserve them), and the target facts over the POST-spill
memory `S.m0 = writeLog m0 spillLog`: the code images stay loaded (the named
geometric residual) and the jal byte pins.  The seg's computed end PC lands at the
jal. -/
structure SpillArmPre (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8))) (bs : List BBlock)
    (pc0 pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (c : Config) : Prop where
  hG : GoodState c.σ
  hmem : c.σ.mem = m0
  hpc : c.σ.regs.get? Register.PC = some pc0
  hmi : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  hL : GHolds c.σ L
  hkeys : KeysOK (keysG L)
  hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs
  hwf : ChainOK pc0 (keysG L) bs
  htick : c.tick < 2
  hx10 : c.σ.regs.get? Register.x10 = some S.inp
  hwin : WinRAM (S.inp + 16#64)
  hgframe : ∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = S.g R
  hm0eq : S.m0 = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log
  hRE : Runtime_errorLoaded S.m0
  hLJ : LongjmpLoaded S.m0
  hb0 : S.m0[pcJal.toNat]? = some b0
  hb1 : S.m0[pcJal.toNat + 1]? = some b1
  hb2 : S.m0[pcJal.toNat + 2]? = some b2
  hb3 : S.m0[pcJal.toNat + 3]? = some b3
  hpcEq : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pcJal

/-- **The seg-GENERIC spill-prefix bridge.**  Runs an arbitrary pure-store spill
seg `bs` (`hwrNil : wrChain bs = []`, one `decide` per site) via `segEval_sound`
(the RAW frame clause, not the pin-only `segToTriple`): because the body writes NO
register, the frame preserves EVERY non-noise register — so `x10 = inp` and the
whole `NotWrittenJmp` `g`-frame carry from entry to the jal PC for FREE, and the
memory side is `writeLog m0 spillLog = S.m0`.  This is exactly the `Triple
ArmBranchPre (JalErrPre …)` that `<premise>_hsite_of_armBranch` consumes.  NO
`bridgeOfSegFramed` — Family A never needed frame tracking.  `spillNeg_toJalErr`
is the `bs := spillNegSeg` instance. -/
theorem spillSeg_toJalErr (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8))) (bs : List BBlock)
    (pc0 pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hwrNil : wrChain bs = []) :
    Triple (SpillArmPre S m0 L lds bs pc0 pcJal b0 b1 b2 b3)
      (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3) := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, hwf, htick, hx10, hwin, hgframe,
    hm0eq, hRE, hLJ, hb0, hb1, hb2, hb3, hpcEq⟩ := hpre
  -- run the spill seg; keep the RAW frame clause `hframe`.
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', ⟨w, hmi'⟩, _hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds
      hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  -- `wrChain bs = []` (pure stores write no register), so the frame clause
  -- preserves every non-noise reg — the wrChain guard is vacuous.
  have hframe' : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      σ'.regs.get? R = c.σ.regs.get? R :=
    fun R hRn => hframe R hRn (fun n hn => by rw [hwrNil] at hn; exact absurd hn (by simp))
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  -- `NotWrittenJmp R` ⇒ R avoids every noise register (noise = jmp control set).
  have noiseAvoid : ∀ {R : Register}, NotWrittenJmp R → ∀ rr ∈ noiseRegs, (rr == R) = false := by
    intro R hR rr hrr
    simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hrr
    rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hR.mi
    · exact hR.pc
    · exact hR.npc
    · exact hR.mii
    · exact hR.mc
    · exact hR.mt
    · exact hR.mip
  -- assemble `JalErrPre`.
  refine ⟨hG', ?_, ?_, ?_, ?_, ?_, hwin, ⟨w, hmi'⟩, hi', ?_, ?_, ?_, ?_, ?_⟩
  · exact hm0eq ▸ hRE
  · exact hm0eq ▸ hLJ
  · show σ'.mem = S.m0; rw [hmem', ← hm0eq]
  · show σ'.regs.get? Register.PC = _; rw [hpc']; exact congrArg some hpcEq
  · show σ'.regs.get? Register.x10 = some S.inp
    rw [hframe' Register.x10 (by decide)]; exact hx10
  · intro R hR
    show σ'.regs.get? R = S.g R
    rw [hframe' R (noiseAvoid hR)]; exact hgframe R hR
  · show σ'.mem[pcJal.toNat]? = _; rw [hmem', ← hm0eq]; exact hb0
  · show σ'.mem[pcJal.toNat + 1]? = _; rw [hmem', ← hm0eq]; exact hb1
  · show σ'.mem[pcJal.toNat + 2]? = _; rw [hmem', ← hm0eq]; exact hb2
  · show σ'.mem[pcJal.toNat + 3]? = _; rw [hmem', ← hm0eq]; exact hb3

#print axioms spillSeg_toJalErr

end Vsa.Sim
