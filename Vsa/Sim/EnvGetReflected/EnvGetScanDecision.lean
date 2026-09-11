import Vsa.Sim.EnvGetReflected.EnvGetScanBranch

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The actual comparison register and its semantic equality test. -/
structure CompareValue (sa sb : String) (x : BitVec 64) (c : Config) : Prop where
  register : c.σ.regs.get? Register.x10 = some x
  zero_iff : x = 0#64 ↔ sa = sb

/-- Expose the legacy comparison witness once, through a named result. -/
theorem CompareResult.value
    {g : (R : Register) → Option (RegisterType R)}
    {pa name : BitVec 64} {sa sb : String} {before after : Config}
    (h : CompareResult g pa name sa sb before after) :
    ∃ x, CompareValue sa sb x after := by
  obtain ⟨csa, csb, x, hca, hcb, hsa, hsb, hx, hsign⟩ := h.post.comparison
  have hspec := string_eq_iff_strcmpSpecSign_zero before.σ.mem pa.toNat name.toNat
    sa sb csa csb hca hcb hsa hsb
  have hzero : strcmpSign x = 0 ↔ x = 0#64 := by
    unfold strcmpSign
    split
    · simp_all
    · split <;> simp_all
  refine ⟨x, { register := hx, zero_iff := ?_ }⟩
  constructor
  · intro hz
    exact hspec.mp (specSign_zero_of_x10_zero x csa csb hsign hz)
  · intro heq
    exact hzero.mp (hsign.trans (hspec.mpr heq))

/-- The executed comparison branch agrees with the semantic binding name. -/
structure ScanDecisionResult
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn sp : BitVec 64) (i : Nat) (taken : Bool)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem)
    (hi : i < f.vars.length) (before after : Config) : Prop extends
    ScanBranchResult g env name out count pn 0x80002c6c#64 sp i taken
      f nameStr N phiF phiC m0 before after where
  name_match : taken = false ↔ (f.vars[i]'hi).1 = nameStr

/-- Compose the actual slot load, comparison call, and generated branch.
All postconditions refer to that single execution's endpoint. -/
theorem scan_decision
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn ra sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g 0x80002c60#64 env name out count pn ra sp i
      f nameStr N phiF phiC m0 c) (hi : i < f.vars.length) :
    ∃ after taken, ScanDecisionResult g env name out count pn sp i taken
      f nameStr N phiF phiC m0 hi c after := by
  obtain ⟨compared, g', pa, hcmp⟩ := scan_compare_state g env name out count pn ra sp i
    f nameStr N phiF phiC m0 c hSt hi
  obtain ⟨x, hx⟩ := hcmp.toCompareResult.value
  let taken := x != 0#64
  obtain ⟨after, hbranch⟩ := scan_branch g env name out count pn 0x80002c6c#64 sp i taken
    f nameStr N phiF phiC m0 compared hcmp.scan x hx.register rfl
  refine ⟨after, taken,
    { steps := hcmp.steps.trans hbranch.steps
      scan := hbranch.scan
      output := hbranch.output.trans hcmp.post.out
      kept_frame := fun R hR =>
        (hbranch.kept_frame R hR).trans (hcmp.toCompareResult.kept_frame R hR)
      name_match := ?_ }⟩
  simpa only [taken, bne_eq_false_iff_eq] using hx.zero_iff

#print axioms CompareResult.value
#print axioms scan_decision

end Vsa.Sim.EnvGetReflected
