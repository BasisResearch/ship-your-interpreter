import Vsa.Compiler.Check
import Vsa.AbsInt.CostSound
import Vsa.While.Validation

namespace Vsa.Compiler

open Vsa.While Vsa.Sim Vsa.AbsInt LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Halts Diverges output)

def costBound (p : Program) : CB := progCost (A := Const × Itv) {} p

def budgetB (p : Program) : Bool :=
  match costBound p with
  | some n => decide (n ≤ heapUnits)
  | none => false

theorem budgetB_sound {p : Program} (h : budgetB p = true) :
    ∀ out, BigStep p out → BigStepBudget p out heapUnits := by
  unfold budgetB at h
  split at h
  · rename_i n hn
    intro out hb
    obtain ⟨st', m, hm, hout, hle⟩ := progCost_sound (A := Const × Itv) {} hn out hb
    exact ⟨st', m, hm, hout, Nat.le_trans hle (of_decide_eq_true h)⟩
  · cases h

def compileChecked (p : Program) : Option (List Ins) :=
  if supportedGB p && fitsB p && budgetB p then some (compileG p) else none

theorem compileChecked_spec {p : Program} {code : List Ins}
    (h : compileChecked p = some code) :
    code = compileG p ∧ supportedGB p = true ∧ fitsB p = true ∧ budgetB p = true := by
  unfold compileChecked at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨rfl, hc.1.1, hc.1.2, hc.2⟩
  · cases h

theorem compileChecked_correct (p : Program) (code : List Ins)
    (hc : compileChecked p = some code) (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (codeBytes code).length →
      c.σ.mem[0x80004800 + k]? = (codeBytes code)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) := by
  obtain ⟨rfl, hs, hf, hb⟩ := compileChecked_spec hc
  exact checked_correct p hs hf (budgetB_sound hb) c hgood htick hpc hpw hout hcode hlib

theorem whileWl_costBound : costBound Programs.whileWl = some 8272 := by decide +kernel

theorem whileWl_checked : compileChecked Programs.whileWl = some (compileG Programs.whileWl) := by
  have hs : supportedGB Programs.whileWl = true := by decide +kernel
  have hf : fitsB Programs.whileWl = true := by decide +kernel
  have hb : budgetB Programs.whileWl = true := by decide +kernel
  simp only [compileChecked, hs, hf, hb, Bool.and_self, ↓reduceIte]

theorem whileWl_checked_halts (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (codeBytes (compileG Programs.whileWl)).length →
      c.σ.mem[0x80004800 + k]? = (codeBytes (compileG Programs.whileWl))[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c "55\n2500\n36\n" 0 :=
  ((compileChecked_correct _ _ whileWl_checked c hgood htick hpc hpw hout hcode hlib).1 _).mp
    Validation.whileWl_valid

#print axioms compileChecked_correct
#print axioms whileWl_checked_halts

end Vsa.Compiler
