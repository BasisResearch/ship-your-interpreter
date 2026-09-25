import VsaIris.Vsa.Fprintf.SfvLoop

/-!
# `__sprint_r` on `__sbprintf`'s stack `FILE` (lane N5)

`_vfprintf_r` hands its collected pieces to `__sprint_r(reent, f, uio)`:
with a nonzero residual it runs `__sfvwrite_r` (`sfvwrite_chain`), then
clears the `uio`'s residual and piece count and returns `__sfvwrite_r`'s 0.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

/-- The bytes a `__sprint_r(reent, f, uio)` call changes, `sp` its entry
stack pointer. -/
def SprintReg (f sp U : Nat) (a : Nat) : Prop :=
  SfvCallReg f (sp - 32) U a ∨ (sp - 32 ≤ a ∧ a < sp) ∨ (U + 8 ≤ a ∧ a < U + 12)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem sprint_run (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f U : BitVec 64} {need A : Nat} {pend0 : List (BitVec 8)} {iovs : List (Nat × List (BitVec 8))}
    (hs1 : s.toNat - need + 384 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (hU1 : sp.toNat ≤ U.toNat) (hU2 : U.toNat + 24 ≤ s.toNat) (hUa : U.toNat % 8 = 0)
    (hfU : U.toNat + 24 ≤ f.toNat ∨ f.toNat + 1208 ≤ U.toNat)
    (hA : s.toNat - need ≤ A ∧ A + 16 * iovs.length ≤ s.toNat ∧ A % 8 = 0 ∧
      ∀ a, A ≤ a → a < A + 16 * iovs.length → ¬ SprintReg f.toNat sp.toNat U.toNat a)
    (h1ra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = sp) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h12 : R 12 = U)
    (hF : SbFile Mt f pend0) (hiovp : ldv .ld Mt U.toNat = BitVec.ofNat 64 A)
    (hres : ldv .ld Mt (U + 16#64).toNat = BitVec.ofNat 64 (piecesLen iovs))
    (htot : 0 < piecesLen iovs) (htot2 : piecesLen iovs < 2 ^ 31) (hiov : IovAt Mt A iovs)
    (hsrcs : ∀ p ∈ iovs, PieceReads Dt DA (outS s need) Mt p.1 p.2 ∧ 0x80000000 ≤ p.1 ∧
      p.1 + p.2.length ≤ 0x100000000 ∧ (p.1 + p.2.length ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ p.1) ∧
      ∀ i, i < p.2.length → ¬ SprintReg f.toNat sp.toNat U.toNat (p.1 + i))
    (hk : ∀ R' M' out pend', pend0 ++ piecesBytes iovs = out ++ pend' → RetOK R R' 0#64 → SbFile M' f pend' →
      Frame M' Mt (SprintReg f.toNat sp.toNat U.toNat) → ldv .ld M' (U + 16#64).toNat = 0#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000e8cc#64 R Mt := by
  have htotd : BitVec.ofNat 64 (piecesLen iovs) ≠ 0#64 := fun e => by
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  nx_run hlive using [h2, h12, hres, BitVec.add_assoc] at 2147540620
  have hsp : (sp + 18446744073709551584#64).toNat = sp.toNat - 32 := by
    rw [toNat_add_neg (by omega) (by omega)]
  -- `__sprint_r`'s two spills lie in `[sp - 32, sp)`
  have hFro : Frame (writeLog (writeLog Mt [((sp + 18446744073709551608#64).toNat, 8, R 1)])
      [((sp + 18446744073709551592#64).toNat, 8, U)]) Mt (fun a => sp.toNat - 32 ≤ a ∧ a < sp.toNat) := by
    frame_chain
  have hU16 : (U + 16#64).toNat = U.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine sfvwrite_chain (sp := sp + 18446744073709551584#64) (pend0 := pend0) (iovs := iovs) (A := A)
    hlive hlive' hsub ?_ ?_ hs3 hs4 ?_ ?_ hf2 hfa ?_ hU2 hUa hfU ?_ (by rsimp; decide) (by rsimp)
    (by rsimp; exact h10) (by rsimp; exact h11) (by rsimp; exact h12) ?_ ?_ ?_ htot htot2 ?_ ?_
    (fun R' M' out pend' hrel hret hF' hFr' => ?_)
  all_goals (try (rw [hsp]; omega))
  · exact ⟨hA.1, hA.2.1, hA.2.2.1, fun a h1 h2 hr => hA.2.2.2 a h1 h2 (.inl (by rw [hsp] at hr; exact hr))⟩
  · exact hF.frame_out hFro (by omega) fun b hb => by omega
  · rw [hFro.ldv .ld (fun j hj => by simp only [widthOfM] at hj; omega)]; exact hiovp
  · rw [hFro.ldv .ld (fun j hj => by simp only [widthOfM] at hj; rw [hU16]; omega)]; exact hres
  · intro j hj
    have hA2 := hA.2.1
    have hj16 : A + 16 * j + 16 ≤ A + 16 * iovs.length := by
      have : j + 1 ≤ iovs.length := hj
      omega
    have e1 : (BitVec.ofNat 64 (A + 16 * j)).toNat = A + 16 * j := by simp only [BitVec.toNat_ofNat]; omega
    have e2 : (BitVec.ofNat 64 (A + 16 * j + 8)).toNat = A + 16 * j + 8 := by
      simp only [BitVec.toNat_ofNat]; omega
    have hout : ∀ k, k < 16 → ¬ (sp.toNat - 32 ≤ A + 16 * j + k ∧ A + 16 * j + k < sp.toNat) := fun k hk h =>
      hA.2.2.2 _ (by omega) (by omega) (.inr (.inl h))
    obtain ⟨h1', h2'⟩ := hiov j hj
    exact ⟨by rw [hFro.ldv .ld (fun k hk => by simp only [widthOfM] at hk; rw [e1]; exact hout k (by omega))]; exact h1',
      by rw [hFro.ldv .ld (fun k hk => by simp only [widthOfM] at hk; rw [e2, Nat.add_assoc]; exact hout (8 + k) (by omega))]; exact h2'⟩
  · intro p hp
    obtain ⟨hr, h1, h2, h3, hok⟩ := hsrcs p hp
    refine ⟨hr.transport fun i hi => hFro _ (fun h => hok i hi (.inr (.inl h))),
      ⟨h1, h2, h3, fun i hi hr => hok i hi (.inl (.inl (by rw [hsp] at hr; exact hr)))⟩, ?_⟩
    intro i hi hr; exact hok i hi (.inl (.inr (by rw [hsp] at hr; exact hr)))
  · -- back from `__sfvwrite_r`
    nx_ret hret
    have e8 : (sp + 18446744073709551592#64).toNat = sp.toNat - 24 := by rw [toNat_add_neg (by omega) (by omega)]
    have e24 : (sp + 18446744073709551608#64).toNat = sp.toNat - 8 := by rw [toNat_add_neg (by omega) (by omega)]
    have hsl8 : ldv .ld M' (sp + 18446744073709551592#64).toNat = U := by
      rw [hFr'.ldv .ld (fun j hj hr => by
        simp only [widthOfM] at hj; rw [e8] at hr; rw [hsp] at hr; unfold SfvCallReg LoopReg SfvReg at hr; omega)]
      rw [ldv_store_hit]
    have hsl24 : ldv .ld M' (sp + 18446744073709551608#64).toNat = R 1 := by
      rw [hFr'.ldv .ld (fun j hj hr => by
        simp only [widthOfM] at hj; rw [e24] at hr; rw [hsp] at hr; unfold SfvCallReg LoopReg SfvReg at hr; omega)]
      rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    rsimp
    nx_run hlive using [rk1, rk2, rk10, hsl8, hsl24, BitVec.add_assoc]
    have hU8 : (U + 8#64).toNat = U.toNat + 8 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have hFs : Frame (writeLog (writeLog M' [((U + 16#64).toNat, 8, 0#64)]) [((U + 8#64).toNat, 4, 0#64)]) M'
        (fun a => (U.toNat + 8 ≤ a ∧ a < U.toNat + 12) ∨ (U.toNat + 16 ≤ a ∧ a < U.toNat + 24)) :=
      ((Frame.refl _ _).snoc fun b h1 h2 => by rw [hU16] at h1 h2; omega).snoc fun b h1 h2 => by
        rw [hU8] at h1 h2; omega
    refine hk _ _ out pend' hrel ?_ (hF'.frame_out hFs (by omega) fun b hb => by omega) ?_ ?_
    · refine retOK_of (by rsimp; exact rk10) ?_
      intro x hx h32 h10' hc
      simp only [iRegs, callClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hc
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (exfalso; simp at hc; done)
        | (exfalso; simp at h32; done)
        | (exfalso; simp at h10'; done)
        | (rsimp; done)
        | (rsimp; exact h2.symm)
        | (rsimp; simp only [rk8, rk9, rk18, rk19, rk20, rk21, rk22, rk23, rk24, rk25, rk26, rk27] <;> rsimp)
    · refine (hFro.mono fun a h => .inr (.inl h)).trans ((hFr'.mono fun a h => .inl (by rw [hsp] at h; exact h)).trans
        (hFs.mono fun a h => by
          unfold SprintReg SfvCallReg LoopReg; omega))
    · rw [ldv_ld_miss _ _ (by rw [hU8, hU16]; omega), ldv_store_hit]

end VsaIris.Sym.Fp
