import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.SegReadback
import Vsa.Sim.TripleCat

namespace Vsa.Sim

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.Logic (Triple)

structure EffectStable (keep : Register → Prop)
    (left right : (R : Register) → Option (RegisterType R)) : Prop where
  eq : ∀ R, keep R → left R = right R

theorem EffectStable.trans
    (h₁ : EffectStable keep left middle)
    (h₂ : EffectStable keep middle right) :
    EffectStable keep left right := by
  exact ⟨fun R hR => (h₁.eq R hR).trans (h₂.eq R hR)⟩

structure FrameEffect where
  regs : Register → Prop
  mem : Nat → Prop
  output : Prop

structure EffectLe (weak strong : FrameEffect) : Prop where
  regs : ∀ R, weak.regs R → strong.regs R
  mem : ∀ a, weak.mem a → strong.mem a
  output : weak.output → strong.output

namespace EffectLe

theorem trans (h₁ : EffectLe first middle) (h₂ : EffectLe middle last) :
    EffectLe first last := by
  exact
    { regs := fun R hR => h₂.regs R (h₁.regs R hR)
      mem := fun a ha => h₂.mem a (h₁.mem a ha)
      output := fun ho => h₂.output (h₁.output ho) }

end EffectLe

universe u v w

abbrev GUpdate := Nat × BitVec 64

def GProjects (out : GRegs) : List GUpdate → Prop
  | [] => True
  | (n, v) :: rest => lookupG n out = some v ∧ GProjects out rest

theorem gholds_selected {sigma : Vsa.Machine.MState} {out selected : GRegs}
    (hproj : GProjects out selected) (hregs : GHolds sigma out) :
    GHolds sigma selected := by
  induction selected with
  | nil => trivial
  | cons update rest ih =>
    obtain ⟨n, v⟩ := update
    exact ⟨gholds_lookup out hregs hproj.1, ih hproj.2⟩

structure SelectedFramedSegResult
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c0 c1 : Config) : Prop where
  steps : Steps c0 c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = writeLog c0.σ.mem
    (evalBlocks bs (SegEvalState.init L lds)).log
  outside : ∀ k, ¬ foot k → c0.σ.mem[k]? = c1.σ.mem[k]?
  output : c1.σ.sailOutput = c0.σ.sailOutput
  pc : c1.σ.regs.get? Register.PC =
    some (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
  minstret : ∃ w, c1.σ.regs.get? Register.minstret = some w
  selected_regs : GHolds c1.σ selected
  reg_frame : ∀ R, keep R = true → c1.σ.regs.get? R = c0.σ.regs.get? R

structure CountedSelectedFramedSegResult
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c0 c1 : Config) : Prop extends
    SelectedFramedSegResult bs L lds pc0 foot keep selected c0 c1 where
  count : c1.steps = c0.steps + evalBlocksFuel bs

theorem segEval_selected_counted
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 vm : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some pc0)
    (hmi : c.σ.regs.get? Register.minstret = some vm)
    (hL : GHolds c.σ L) (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs) (hi : c.tick < 2)
    (hfoot : ∀ k, ¬ foot k → c.σ.mem[k]? =
      (writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log)[k]?)
    (hnoise : ∀ rr ∈ noiseRegs, keep rr = false)
    (havoid : WrChainAvoids keep bs)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init L lds)).regs selected) :
    ∃ c', CountedSelectedFramedSegResult bs L lds pc0 foot keep selected c c' := by
  obtain ⟨sigma', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hregs', hframe'⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds
      hG hpc hmi hL hkeys hfacts hwf hi
  let c' : Config := ⟨sigma', i', c.steps + evalBlocksFuel bs⟩
  refine ⟨c', ?_⟩
  refine
    { count := rfl
      steps := by simpa [c'] using hsteps
      good := by simpa [c'] using hG'
      tick := by simpa [c'] using hi'
      mem := by simpa [c'] using hmem'
      outside := ?_
      output := by simpa [c'] using hout'
      pc := by simpa [c'] using hpc'
      minstret := by simpa [c'] using hmi'
      selected_regs := by
        simpa [c'] using gholds_selected hproj hregs'
      reg_frame := ?_ }
  · intro k hk
    exact (hfoot k hk).trans (congrArg (fun m : Vsa.MemRepr.Mem => m[k]?) hmem').symm
  · intro R hR
    simpa [c'] using
      frame_of_wrChain_avoids (P := keep) hnoise havoid hframe' R hR

theorem segEval_selected_framed
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 vm : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some pc0)
    (hmi : c.σ.regs.get? Register.minstret = some vm)
    (hL : GHolds c.σ L) (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs) (hi : c.tick < 2)
    (hfoot : ∀ k, ¬ foot k → c.σ.mem[k]? =
      (writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log)[k]?)
    (hnoise : ∀ rr ∈ noiseRegs, keep rr = false)
    (havoid : WrChainAvoids keep bs)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init L lds)).regs selected) :
    ∃ c', SelectedFramedSegResult bs L lds pc0 foot keep selected c c' := by
  obtain ⟨after, result⟩ := segEval_selected_counted bs L lds pc0 vm foot keep selected
    c hG hpc hmi hL hkeys hfacts hwf hi hfoot hnoise havoid hproj
  exact ⟨after, result.toSelectedFramedSegResult⟩

end Vsa.Sim
