import VsaIris.Vsa.Fprintf.Outer

/-!
# `fprintf(stdout, fmt, arg)` (lane N5)

`fprintf` (`0x800061c0`) spills its variadic registers (the argument at
`sp + 32`), loads the reent from `_impure_ptr` (the data view), calls
`_vfprintf_r(reent, stdout, fmt, sp + 32)` (the hook `hO`, `vfp_outer`), and
returns its count (`fprintf_wrap`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- The bytes `fprintf` changes: its frame, the outer `_vfprintf_r`'s and
below, `stdout`'s flags, `errno`. -/
def FpReg (sf : Nat) (a : Nat) : Prop :=
  (sf - 2880 ≤ a ∧ a < sf + 80) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

theorem fprintf_wrap (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sf : BitVec 64} {need N : Nat} {bytes : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sf.toNat) (hs2 : sf.toNat + 80 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sf.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = sf + 80#64) (himp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hDA : Cover (· ∈ DA) 0x8001b970 0x8001b978)
    (hO : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 2 = sf → R0 10 = 0x8001b538#64 → R0 11 = R 10 →
      R0 12 = R 11 → R0 13 = sf + 32#64 → R0 1 = 0x80006204#64 →
      Frame Mt0 Mt (fun a => sf.toNat ≤ a ∧ a < sf.toNat + 80) → ldv .ld Mt0 (sf + 32#64).toNat = R 12 →
      (∀ R' M', R' 10 = BitVec.ofNat 64 N → R' 2 = sf → R' 1 = 0x80006204#64 → (∀ x ∈ vfpSaved, R' x = R0 x) →
        Frame M' Mt0 (OuterReg (sf.toNat - 592)) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) 0x80006204#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R0 Mt0)
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 N) → Frame M' Mt (FpReg sf.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x800061c0#64 R Mt := by
  have e : sf + 80#64 + 18446744073709551536#64 = sf := by rw [BitVec.add_assoc]; simp
  have eo : ∀ k : Nat, k ≤ 100 → (sf + BitVec.ofNat 64 k).toNat = sf.toNat + k := fun k hk => sp_lit (by omega)
  nx_run hlive using [h2, e, himp, BitVec.add_assoc] at 2147526788
  refine hO _ _ (by rsimp) (by rsimp) (by rsimp) (by rsimp) (by rsimp) (by rsimp) ?_ (by nx_mem)
    fun R1 M1 e10 e2 e1 ek hfr1 => ?_
  · repeat (refine Frame.snoc ?_ ?_)
    all_goals first | exact Frame.refl _ _ |
      (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
       omega)
  have hn : ∀ j, j < widthOfM .ld → ¬ OuterReg (sf.toNat - 592) ((sf + 24#64).toNat + j) := by
    intro j hj h
    simp only [widthOfM] at hj
    rw [eo 24 (by omega)] at h
    unfold OuterReg at h
    omega
  have l24 : ldv .ld M1 (sf + 24#64).toNat = R 1 := by
    rw [hfr1.ldv .ld hn]
    nx_mem
  nx_run hlive using [e2, e10, l24, BitVec.add_assoc]
  refine hk _ _ (retOK_of (by rsimp; exact e10) fun x hx h32 h10 hc => ?_) ?_
  · simp only [iRegs, callClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hc
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; simp at hc; done)
      | (exfalso; simp at h32; done)
      | (exfalso; simp at h10; done)
      | (rsimp; done)
      | (rsimp; exact h2.symm)
      | (rsimp; rw [ek _ (by decide)]; rsimp)
  · refine (Frame.trans ?_ (hfr1.mono fun a h => ?_))
    · repeat (refine Frame.snoc ?_ ?_)
      all_goals first | exact Frame.refl _ _ |
        (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
         unfold FpReg; omega)
    · unfold FpReg; unfold OuterReg at h
      rcases h with ⟨h1, h2⟩ | h | h
      · exact .inl ⟨by rw [Nat.sub_sub] at h1; exact h1, by omega⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)

end VsaIris.Sym.Fp
