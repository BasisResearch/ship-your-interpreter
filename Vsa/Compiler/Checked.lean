import Vsa.Compiler.Check
import Vsa.AbsInt.CostSound
import Vsa.While.Validation

/-!
# The checked compiler

`compileChecked p` returns `compileG p` only when three decidable checks
pass: `supportedGB` (`SupportedG p`), `fitsB` (the code fits below
`tohost`), and the cost analysis (`progCost` over `Const × Itv`, default
`Cfg`) bounds the allocation cost of every run by at most `heapUnits`.
`progCost_sound` turns the last check into the heap-budget premise of
`compileG_correct`, so `compileChecked_correct` has no program premise
besides acceptance.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim Vsa.AbsInt LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Halts Diverges output)

/-- The allocation-cost bound the checked compiler uses. -/
def costBound (p : Program) : CB := progCost (A := Const × Itv) {} p

/-- The bound is known and within the heap budget. -/
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

/-- **The checked compiler**: the code of `compileG p` when `p` is
supported, its code fits, and its allocation cost is statically bounded
within the heap budget. -/
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

/-- **Correctness of the checked compiler.** For every program `p` it
accepts, and every machine configuration whose memory holds the bytes of the
returned code at `0x80004800` (plus libgcc's multiply and signed
divide/remainder routines at their addresses in the interpreter image), with
the PC at the code, in a good machine state with an idle HTIF mailbox and an
empty console: the machine halts with exit code `0` and output `out` exactly
when `out` is a big-step behaviour of `p`, and a diverging machine means `p`
has none. -/
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

/-! ## `whileWl` -/

/-- The analysis bounds every run of the embedded script by 8272 cost units
(its exact cost is 6992, `whileWl_normalCost`). -/
theorem whileWl_costBound : costBound Programs.whileWl = some 8272 := by decide +kernel

/-- The checked compiler accepts the embedded script. -/
theorem whileWl_checked : compileChecked Programs.whileWl = some (compileG Programs.whileWl) := by
  have hs : supportedGB Programs.whileWl = true := by decide +kernel
  have hf : fitsB Programs.whileWl = true := by decide +kernel
  have hb : budgetB Programs.whileWl = true := by decide +kernel
  simp only [compileChecked, hs, hf, hb, Bool.and_self, ↓reduceIte]

/-- **The checked-compiled `whileWl` prints `55 2500 36` and exits 0** on
every machine configuration that holds its code (and libgcc's routines) at
the entry. -/
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
