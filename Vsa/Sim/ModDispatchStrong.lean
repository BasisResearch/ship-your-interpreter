import Vsa.Sim.SegFrameFactsAuto
import Vsa.Sim.ModDispatchSeg

/-!
# `ModDispatchStrong` — the STRONG `mod` dispatch post + `_frame` row (div clone)

`ModDispatchSeg.lean` gives the WEAK `ModDispatchPost` (PC + `x10=Wl`/`x11=Wr` +
`x9`/`x2`).  Phase 4's value tail needs the SAME strong conjunct set the `.div`
post carries (`∃x12/x13`, `tick<2`, `sailOutput=out0`, callee-saved frame).  The
`mod` arm is byte-identical to `div` (see `ModDispatchSeg` header), so the strong
post `ModDispatchPostS`, the strong row `modDispatchRowS`, and the `_frame`
variant `modDispatchRow_frame` are verbatim clones of `DivDispatchPost`/
`divDispatchRow`/`divDispatchRow_frame` (`DivDispatchSeg`/`SegFrameFactsAuto`),
swapping the arm PCs (`0x800037dc→0x80003784`, `0x8000381c→0x800037c4`) and the
seg (`divDispatch→modDispatch`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The `mod` STRONG pin list — `modDispL` plus the op-token pin `(12, 15)` the
strong post's `∃x12` reads (div's `divDispL` carries `(12, 14)` the same way; the
entry linkage lands `x12 = 15` for mod). -/
def modDispLS (v2 sret Wr Wl : BitVec 64) : GRegs :=
  [(16, 2#64), (10, 2#64), (2, v2), (9, sret), (17, Wr), (19, Wl), (12, 15#64)]

/-- The `mod` STRONG dispatch outcome — the `div`-strength post for the `mod` arm:
parked at `0x800037c4` (ready for `jal __moddi3`), the five stack stores in memory,
`x10=Wl`/`x11=Wr` staged, plus `∃x12/x13`, `tick<2`, `sailOutput=out0`, and the
callee-saved frame.  Verbatim clone of `DivDispatchPost` with mod's PC/seg. -/
def ModDispatchPostS (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks modDispatch
    (SegEvalState.init (modDispLS v2 sret Wr Wl) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800037c4#64 ∧
  gprGet c.σ 10 = some Wl ∧
  gprGet c.σ 11 = some Wr ∧
  gprGet c.σ 9 = some sret ∧
  gprGet c.σ 2 = some v2 ∧
  (∃ w, gprGet c.σ 12 = some w) ∧
  (∃ w, gprGet c.σ 13 = some w) ∧
  c.tick < 2 ∧
  c.σ.sailOutput = out0 ∧
  (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
    c.σ.regs.get? R = gpre R)

/-- **The strong `mod` leaf.**  `0x80003784 → 0x800037c4` as a `Triple` to the
strong post.  Verbatim clone of `divDispatchRow`. -/
theorem modDispatchRowS (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) :
    Triple (fun c => SegPre modDispatch (modDispLS v2 sret Wr Wl) lds 0x80003784#64 m0 c ∧
        c.σ.sailOutput = out0 ∧ (∀ R : Register, c.σ.regs.get? R = gpre R))
      (ModDispatchPostS v2 sret Wr Wl lds m0 out0 gpre) := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩, hsailc, hgprec⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound modDispatch c.σ c.tick c.steps 0x80003784#64 vm
      (modDispLS v2 sret Wr Wl) lds hG hpc hmi hL hkeys hfacts
      (by show ChainOK 0x80003784#64 [16, 10, 2, 9, 17, 19, 12] modDispatch; decide) htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel modDispatch⟩, hs, ?_⟩
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi', ?_, ?_⟩
  · rw [hpc']
    show some (evalBlocksPC 0x80003784#64 (SegEvalState.init (modDispLS v2 sret Wr Wl) lds) modDispatch)
      = some 0x800037c4#64
    show some (chainEndPC 0x80003784#64 (modDispLS v2 sret Wr Wl) lds modDispatch)
      = some 0x800037c4#64
    rw [chainEndPC_eq_bt modDispatch 0x80003784#64 (modDispLS v2 sret Wr Wl) lds (by decide)]
    rfl
  · have e : (Wl + sign_extend (m := 64) (0#12) : BitVec 64) = Wl := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · have e : (Wr + sign_extend (m := 64) (0#12) : BitVec 64) = Wr := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sret) _ hregs (by rfl)
  · exact gholds_lookup (v := v2) _ hregs (by rfl)
  · exact ⟨_, gholds_lookup _ hregs (by rfl)⟩
  · exact ⟨_, gholds_lookup _ hregs (by rfl)⟩
  · rw [hout]; exact hsailc
  · intro R hR _he8
    have habi := hR.1
    rw [hframe R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 13, 14, 13, 15, 11, 10])]
    exact hgprec R

#print axioms modDispatchRowS

/-- The `mod` cross-block `ChainFacts` bundle from ONE `FrameBundle` + `Wr ≠ 0`.
Clone of `divDispatch_facts` (mod's arm is byte-identical). -/
theorem modDispatch_facts (σ : MState) (v2 sret Wr Wl : BitVec 64) (hWr : Wr ≠ 0)
    (fb : FrameBundle σ.mem v2) (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ∃ lds, ChainFacts σ.mem σ.mem (modDispLS v2 sret Wr Wl) lds modDispatch := by
  seg_frame_facts h with "Vsa.Sim.Code.eval_expr_at_" using fb
  show guardB bop.BEQ (srcVal 17 _) (srcVal 0 _) = false
  rw [show srcVal 17 _ = Wr from by srcval_peel]
  simp only [guardB]
  exact beq_eq_false_iff_ne.mpr hWr

#print axioms modDispatch_facts

/-- **The composed strong `mod` row.**  From `SegFramePre` + `Wr ≠ 0`, run to
`ModDispatchPostS`.  `mod` analogue of `divDispatchRow_frame`. -/
theorem modDispatchRow_frame (v2 sret Wr Wl : BitVec 64) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) (hWr : Wr ≠ 0)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => SegFramePre (modDispLS v2 sret Wr Wl) v2 0x80003784#64 m0 c ∧
        c.σ.sailOutput = out0 ∧ (∀ R : Register, c.σ.regs.get? R = gpre R))
      (fun c => ∃ lds, ModDispatchPostS v2 sret Wr Wl lds m0 out0 gpre c) := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, hmi, hL, hkeys, fb, hload, htick⟩, hsail, hgpre⟩ := hpre
  obtain ⟨lds, hfacts⟩ :=
    modDispatch_facts c.σ v2 sret Wr Wl hWr (hmem ▸ fb) (hmem ▸ hload)
  obtain ⟨c', hstep, hpost⟩ := modDispatchRowS v2 sret Wr Wl lds m0 out0 gpre c
    ⟨⟨hG, hmem, hpc, hmi, hL, hkeys, hfacts, htick⟩, hsail, hgpre⟩
  exact ⟨c', hstep, lds, hpost⟩

#print axioms modDispatchRow_frame

end Vsa.Sim
