import Vsa.Sim.SegFrameFactsAuto

/-!
# `EqNeDispatchStrong` — STRONG `eq`/`ne` dispatch posts + `_frame` rows

`EqNeDispatchSeg.lean` gives the WEAK `EqDispatchPost`/`NeDispatchPost` (PC +
`x10=bufa`/`x11=bufb` + `x2=sp`).  Phase 4's value tail needs the SAME strong
conjunct set the `.div` post carries (`tick<2`, `sailOutput=out0`, callee-saved
frame), plus `x2=sp` for the `value_equal` frame.  The `eq`/`ne` arms are
single-block (no kind ladder, no divisor guard), so the strong post/row are
SIMPLER than div's — no `∃x12/x13`, no `Wr≠0` residual — but carry the same
`tick`/`output`/frame.  `eqDispatch_facts` (`SegFrameFactsAuto`) already supplies
the `ChainFacts` for the single block; the `_frame` rows just thread the strong
post through it.  The `eq`/`ne` shape (`sp`/`bufa`/`bufb`) differs from div/mod
(`Wr`/`Wl`), so these are hand-instantiated against `eqDispatchRow`/`neDispatchRow`
following the `divDispatchRow_frame` recipe (as the brief permits).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The `eq` STRONG dispatch outcome: parked at `0x8000371c`, `x10=bufa`/`x11=bufb`
staged, `x2=sp`, plus `tick<2`, `sailOutput=out0`, callee-saved frame. -/
def EqDispatchPostS (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks eqDispatch
    (SegEvalState.init (eqDispL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000371c#64 ∧
  gprGet c.σ 10 = some (sp + 0x40#64) ∧
  gprGet c.σ 11 = some (sp + 0x20#64) ∧
  gprGet c.σ 2 = some sp ∧
  c.tick < 2 ∧
  c.σ.sailOutput = out0 ∧
  (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
    c.σ.regs.get? R = gpre R)

/-- The `ne` STRONG dispatch outcome: parked at `0x8000376c`, otherwise identical. -/
def NeDispatchPostS (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks neDispatch
    (SegEvalState.init (eqDispL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000376c#64 ∧
  gprGet c.σ 10 = some (sp + 0x40#64) ∧
  gprGet c.σ 11 = some (sp + 0x20#64) ∧
  gprGet c.σ 2 = some sp ∧
  c.tick < 2 ∧
  c.σ.sailOutput = out0 ∧
  (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
    c.σ.regs.get? R = gpre R)

/-- **The strong `eq` leaf.**  `0x800036e4 → 0x8000371c` to the strong post. -/
theorem eqDispatchRowS (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) :
    Triple (fun c => SegPre eqDispatch (eqDispL sp) lds 0x800036e4#64 m0 c ∧
        c.σ.sailOutput = out0 ∧ (∀ R : Register, c.σ.regs.get? R = gpre R))
      (EqDispatchPostS sp lds m0 out0 gpre) := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩, hsailc, hgprec⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound eqDispatch c.σ c.tick c.steps 0x800036e4#64 vm
      (eqDispL sp) lds hG hpc hmi hL hkeys hfacts
      (by show ChainOK 0x800036e4#64 [2] eqDispatch; decide) htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel eqDispatch⟩, hs, ?_⟩
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_, hi', ?_, ?_⟩
  · rw [hpc']
    show some (evalBlocksPC 0x800036e4#64 (SegEvalState.init (eqDispL sp) lds) eqDispatch)
      = some 0x8000371c#64
    show some (chainEndPC 0x800036e4#64 (eqDispL sp) lds eqDispatch) = some 0x8000371c#64
    rw [chainEndPC_eq_bt eqDispatch 0x800036e4#64 (eqDispL sp) lds (by decide)]
    rfl
  · have e : (sp + sign_extend (m := 64) (0x40#12) : BitVec 64) = sp + 0x40#64 := by
      rw [show (sign_extend (m := 64) (0x40#12) : BitVec 64) = 0x40#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · have e : (sp + sign_extend (m := 64) (0x20#12) : BitVec 64) = sp + 0x20#64 := by
      rw [show (sign_extend (m := 64) (0x20#12) : BitVec 64) = 0x20#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sp) _ hregs (by rfl)
  · rw [hout]; exact hsailc
  · intro R hR _he8
    have habi := hR.1
    rw [hframe R (abiNoise_noiseRegs hR) (by block_frame_wr [17, 16, 12, 13, 14, 15, 11, 10])]
    exact hgprec R

#print axioms eqDispatchRowS

/-- **The strong `ne` leaf.**  `0x80003734 → 0x8000376c` to the strong post. -/
theorem neDispatchRowS (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) :
    Triple (fun c => SegPre neDispatch (eqDispL sp) lds 0x80003734#64 m0 c ∧
        c.σ.sailOutput = out0 ∧ (∀ R : Register, c.σ.regs.get? R = gpre R))
      (NeDispatchPostS sp lds m0 out0 gpre) := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩, hsailc, hgprec⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound neDispatch c.σ c.tick c.steps 0x80003734#64 vm
      (eqDispL sp) lds hG hpc hmi hL hkeys hfacts
      (by show ChainOK 0x80003734#64 [2] neDispatch; decide) htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel neDispatch⟩, hs, ?_⟩
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_, hi', ?_, ?_⟩
  · rw [hpc']
    show some (evalBlocksPC 0x80003734#64 (SegEvalState.init (eqDispL sp) lds) neDispatch)
      = some 0x8000376c#64
    show some (chainEndPC 0x80003734#64 (eqDispL sp) lds neDispatch) = some 0x8000376c#64
    rw [chainEndPC_eq_bt neDispatch 0x80003734#64 (eqDispL sp) lds (by decide)]
    rfl
  · have e : (sp + sign_extend (m := 64) (0x40#12) : BitVec 64) = sp + 0x40#64 := by
      rw [show (sign_extend (m := 64) (0x40#12) : BitVec 64) = 0x40#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · have e : (sp + sign_extend (m := 64) (0x20#12) : BitVec 64) = sp + 0x20#64 := by
      rw [show (sign_extend (m := 64) (0x20#12) : BitVec 64) = 0x20#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sp) _ hregs (by rfl)
  · rw [hout]; exact hsailc
  · intro R hR _he8
    have habi := hR.1
    rw [hframe R (abiNoise_noiseRegs hR) (by block_frame_wr [17, 16, 12, 13, 14, 15, 11, 10])]
    exact hgprec R

#print axioms neDispatchRowS

/-- **The composed strong `eq` row.**  From `SegFramePre` (a `FrameBundle m0 sp` +
loaded image) run to `EqDispatchPostS`.  `ChainFacts` supplied by `eqDispatch_facts`. -/
theorem eqDispatchRow_frameS (sp : BitVec 64) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => SegFramePre (eqDispL sp) sp 0x800036e4#64 m0 c ∧
        c.σ.sailOutput = out0 ∧ (∀ R : Register, c.σ.regs.get? R = gpre R))
      (fun c => ∃ lds, EqDispatchPostS sp lds m0 out0 gpre c) := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, hmi, hL, hkeys, fb, hload, htick⟩, hsail, hgpre⟩ := hpre
  obtain ⟨lds, hfacts⟩ := eqDispatch_facts c.σ sp (hmem ▸ fb) (hmem ▸ hload)
  obtain ⟨c', hstep, hpost⟩ := eqDispatchRowS sp lds m0 out0 gpre c
    ⟨⟨hG, hmem, hpc, hmi, hL, hkeys, hfacts, htick⟩, hsail, hgpre⟩
  exact ⟨c', hstep, lds, hpost⟩

#print axioms eqDispatchRow_frameS

/-- The `ne` cross-block `ChainFacts` bundle from ONE `FrameBundle` (byte-identical
to `eqDispatch`; single block, no guard). -/
theorem neDispatch_facts (σ : MState) (sp : BitVec 64)
    (fb : FrameBundle σ.mem sp) (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ∃ lds, ChainFacts σ.mem σ.mem (eqDispL sp) lds neDispatch := by
  seg_frame_facts h with "Vsa.Sim.Code.eval_expr_at_" using fb

#print axioms neDispatch_facts

/-- **The composed strong `ne` row.**  From `SegFramePre` run to `NeDispatchPostS`. -/
theorem neDispatchRow_frameS (sp : BitVec 64) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => SegFramePre (eqDispL sp) sp 0x80003734#64 m0 c ∧
        c.σ.sailOutput = out0 ∧ (∀ R : Register, c.σ.regs.get? R = gpre R))
      (fun c => ∃ lds, NeDispatchPostS sp lds m0 out0 gpre c) := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, hmi, hL, hkeys, fb, hload, htick⟩, hsail, hgpre⟩ := hpre
  obtain ⟨lds, hfacts⟩ := neDispatch_facts c.σ sp (hmem ▸ fb) (hmem ▸ hload)
  obtain ⟨c', hstep, hpost⟩ := neDispatchRowS sp lds m0 out0 gpre c
    ⟨⟨hG, hmem, hpc, hmi, hL, hkeys, hfacts, htick⟩, hsail, hgpre⟩
  exact ⟨c', hstep, lds, hpost⟩

#print axioms neDispatchRow_frameS

end Vsa.Sim
