import Vsa.CT.Machine

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Halted Halts RunT output)

theorem encAux_intE (Γ : NScope) (n : Int) : ∀ j, IntE Γ (encAux n j)
  | 0 => by
    have := chunk_small n 0
    simp only [encAux, IntE, InRange]; omega
  | j + 1 => by
    have := chunk_small n (j + 1)
    simp only [encAux, IntE, ArithOp, InRange]
    refine ⟨by simp, ⟨by simp, encAux_intE Γ n j, by decide⟩, by omega⟩

theorem sup_transfer (sec : String → Bool) (body : Program) : ∀ {ins1 ins2 : List (String × Int)},
    LowIns sec ins1 ins2 → ∀ (Γ : NScope) (loop : Bool),
    SupSeq Γ loop (prog sec ins1 body) → SupSeq Γ loop (prog sec ins2 body)
  | _, _, .nil, _, _, h => h
  | _, _, .cons (x := x) (a := a) (b := b) hab hr, Γ, loop, h => by
    have h' : SupSeq Γ loop (.varDecl x (some (inExpr sec x a)) :: prog sec _ body) := h
    show SupSeq Γ loop (.varDecl x (some (inExpr sec x b)) :: prog sec _ body)
    simp only [SupSeq] at h' ⊢
    obtain ⟨hn, he, hs⟩ := h'
    refine ⟨hn, ?_, sup_transfer sec body hr _ loop hs⟩
    by_cases hsx : sec x = true
    · simp only [inExpr, hsx, ite_true]; exact encAux_intE _ b 5
    · rw [← hab (by simpa using hsx)]; exact he

theorem len_transfer (sec : String → Bool) (body : Program) {ins1 ins2 : List (String × Int)}
    (h : LowIns sec ins1 ins2) :
    (compile (prog sec ins1 body)).length = (compile (prog sec ins2 body)).length := by
  obtain ⟨i1, i2, -, -⟩ := prefix_inv sec h ctx0 mainPos₀
  have e1 := prog_len sec body ins1 ctx0 mainPos₀
  have e2 := prog_len sec body ins2 ctx0 mainPos₀
  rw [compile_eq, compile_eq]
  simp only [List.length_append, Compiler.body]
  rw [i1, i2] at e1
  have hc : ctx0 = ⟨[[]], 0, 0, 0⟩ := rfl
  rw [hc] at e1 e2
  omega

theorem ct_machine' {sec : String → Bool} {body : Program} {ins1 ins2 : List (String × Int)}
    (hct : ctSeq sec body = true) (hnat : ∀ p ∈ ins1, isNat p.1 = false) (hlow : LowIns sec ins1 ins2)
    (hsup1 : Supported (prog sec ins1 body))
    (hfit1 : 0x80004800 + 4 * (compile (prog sec ins1 body)).length ≤ 0x8001ad00)
    {c1 c2 : Config} (hb1 : Boot (prog sec ins1 body) c1) (hb2 : Boot (prog sec ins2 body) c2)
    {o1 : String} (hh1 : Halts c1 o1 0) :
    ∃ o2 ℓ1 ℓ2, BigStepL (prog sec ins1 body) o1 ℓ1 ∧ BigStepL (prog sec ins2 body) o2 ℓ2 ∧
      Halts c2 o2 0 ∧ skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → o1 = o2 ∧ ∃ T : List (BitVec 64),
        (∃ c' σf, RunT c1 T c' ∧ Halted c' 0 σf ∧ output σf = o1) ∧
        (∃ c' σf, RunT c2 T c' ∧ Halted c' 0 σf ∧ output σf = o2)) :=
  ct_machine hct hnat hlow hsup1 (sup_transfer sec body hlow _ _ hsup1) hfit1
    (by rw [← len_transfer sec body hlow]; exact hfit1) hb1 hb2 hh1

end Vsa.Compiler
