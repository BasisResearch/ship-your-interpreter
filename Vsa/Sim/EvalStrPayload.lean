import Vsa.Sim.rows.EntryGroundRows

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- The literal returns its original AST payload pointer. Its hereditary entry
bounds therefore cover the reached result's payload outside the whole stack. -/
theorem evalStrPayloadIH (st : Vsa.While.St) (d env : Nat) (s : String) :
    EvalPayloadIH st d env (.str s) st (.str s) where
  run := by
    intro g N A SL φf φc sp r sret aEnv aExpr m0 c hc
    obtain ⟨hssd, hsrd, hvsc, hvss, hvsl, hsl, htsd, hW⟩ :=
      Rows.field_hStr st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
    have hEntry := EvalStrEntry.of_entry hc hssd hsrd hvsc hvss hvsl hsl htsd
    obtain ⟨c', hs, hExit, hPin⟩ :=
      evalStrSimP_exact g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c hEntry
    have hD := evalExitD_of_pinnedExit ⟨hExit, hPin.memory⟩ hW (hc.mem ▸ hc.sret_words)
    refine ⟨c', hs, hD, ?_⟩
    change ∀ p, read64 c'.σ.mem (sret.toNat + 8) = some p →
      ∀ k, k ≤ s.length → ¬ (SL.lo ≤ p + k ∧ p + k < SL.hi)
    have hg : EvalGround m0 SL A sp sret aExpr.toNat (.str s) := hc.mem ▸ hc.ground
    obtain ⟨lo, hi, spec⟩ := hg.ast.region
    intro p hp k hk hstack
    have hp0 : read64 m0 (aExpr.toNat + 8) = some p := hPin.pointer.symm.trans hp
    obtain ⟨_, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
    rcases spec.stack_disjoint with hd | hd <;> omega

#print axioms evalStrPayloadIH
end Vsa.Sim
