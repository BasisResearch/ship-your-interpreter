import VsaIris.Vsa.Fprintf.ScanTo

/-!
# Printing a conversion's pieces (lane N5)

After a conversion `_vfprintf_r` hands the pending iovs to `__sprint_r`
(`0x8000b8c4`: `__sprint_r(reent, fp, sp + 224)`), then empties the array and
goes back to the loop head (`vfp_print`). Every conversion's emit ends here;
so does the final flush (`0x8000cf9c`, the same call).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- A pending piece `__sprint_r` can print: readable, in RAM, off `tohost`,
off the bytes the print changes. -/
def PieceOK (Dt : Mem) (DA : List Nat) (s : BitVec 64) (need : Nat) (Mt : Mem) (f sp : BitVec 64)
    (p : Nat × List (BitVec 8)) : Prop :=
  PieceReads Dt DA (outS s need) Mt p.1 p.2 ∧ 0x80000000 ≤ p.1 ∧
    p.1 + p.2.length ≤ 0x100000000 ∧ (p.1 + p.2.length ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ p.1) ∧
    ∀ i, i < p.2.length → ¬ SprintReg f.toNat sp.toNat (sp.toNat + 224) (p.1 + i)

/-- The bytes `vfp_print` changes. -/
def PrintReg (f sp : Nat) (a : Nat) : Prop :=
  SprintReg f sp (sp + 224) a ∨ (sp + 232 ≤ a ∧ a < sp + 236)

theorem vfp_print (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f P : BitVec 64} {need cnt : Nat} {pend0 : List (BitVec 8)}
    {iovs : List (Nat × List (BitVec 8))}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat + 592 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (hP : VfpPend R Mt sp 0x8001b538#64 f cnt iovs) (h24 : R 24 = P) (hn : iovs.length ≤ 7)
    (htot : 0 < piecesLen iovs) (htot2 : piecesLen iovs < 2 ^ 31)
    (hsrcs : ∀ p ∈ iovs, PieceOK Dt DA s need Mt f sp p)
    (hz32 : ldv .ld Mt (sp + 32#64).toNat = 0#64) (hF : SbFile Mt f pend0)
    (hk : ∀ R' M' out pend', pend0 ++ piecesBytes iovs = out ++ pend' →
      VfpLoop R' M' sp 0x8001b538#64 f P cnt → SbFile M' f pend' → Frame M' Mt (PrintReg f.toNat sp.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000a9b0#64 R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b8c4#64 R Mt := by
  have h2 := hP.spR
  have hre := hP.reent; have hfi := hP.file
  nx_run hlive using [h2, hre, hfi] at 2147543244
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    sp_lit (by omega)
  have hbase : ldv .ld Mt (sp + 224#64).toNat = BitVec.ofNat 64 (sp.toNat + 352) := by
    rw [hP.base]; apply BitVec.eq_of_toNat_eq; rw [eo 352 (by omega), BitVec.toNat_ofNat]; omega
  have hres : ldv .ld Mt (sp + 224#64 + 16#64).toNat = BitVec.ofNat 64 (piecesLen iovs) := by
    rw [BitVec.add_assoc]; exact hP.resid
  refine sprint_run (sp := sp) (U := sp + 224#64) (A := sp.toNat + 352) (iovs := iovs) hlive hlive' hsub
    (by omega) (by omega) hs3 hs4 hal (by omega) hf2 hfa (by rw [eo 224 (by omega)]; omega)
    (by rw [eo 224 (by omega)]; omega) (by rw [eo 224 (by omega)]; omega) (by rw [eo 224 (by omega)]; omega)
    ⟨by omega, by omega, by omega, fun a h1 h2 hr => by
      unfold SprintReg SfvCallReg LoopReg SfvReg at hr; rw [eo 224 (by omega)] at hr; omega⟩
    (by rsimp; decide) (by rsimp; exact h2) (by rsimp) (by rsimp) (by rsimp) hF hbase hres htot htot2
    (by simpa [Nat.add_comm] using hP.arr) (fun p hp => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hsrcs p hp
      exact ⟨h1, h2, h3, h4, fun i hi => by rw [eo 224 (by omega)]; exact h5 i hi⟩)
    fun R' M' out pend' hrel hret hF' hfr hres' => ?_
  nx_ret hret
  have hSR : ∀ a, (a < sp.toNat - 384 ∨ sp.toNat ≤ a) → a < sp.toNat + 232 ∨ sp.toNat + 236 ≤ a →
      a < sp.toNat + 240 ∨ sp.toNat + 248 ≤ a → a < f.toNat ∨ f.toNat + 1208 ≤ a →
      a < 0x8001ba08 ∨ 0x8001bb32 ≤ a → ¬ SprintReg f.toNat sp.toNat (sp.toNat + 224) a := fun a h1 h2 h3 h4 h5 hr => by
    unfold SprintReg SfvCallReg LoopReg SfvReg at hr; omega
  have l32 : ldv .ld M' (sp + 32#64).toNat = 0#64 := by
    rw [hfr.ldv .ld (fun j hj => by
      simp only [widthOfM] at hj; rw [eo 32 (by omega), eo 224 (by omega)]; exact hSR (sp.toNat + 32 + j) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact hz32
  have k2 : R' 2 = sp := by rw [rk2]; exact h2
  rsimp
  nx_run hlive using [k2, rk10, l32, BitVec.add_assoc] at 2147527088
  have hst : Frame (writeLog M' [((sp + 232#64).toNat, 4, 0#64)]) M'
      (fun a => sp.toNat + 232 ≤ a ∧ a < sp.toNat + 236) :=
    Frame.store M' _ fun b h1 h2 => by rw [eo 232 (by omega)] at h1 h2; exact ⟨h1, h2⟩
  have hfr2 : Frame (writeLog M' [((sp + 232#64).toNat, 4, 0#64)]) Mt (PrintReg f.toNat sp.toNat) :=
    (hfr.mono fun a h => by rw [eo 224 (by omega)] at h; exact .inl h).trans (hst.mono fun a h => .inr h)
  have hout : ∀ (kd : MKind) (k : Nat), k + widthOfM kd ≤ 232 →
      ldv kd (writeLog M' [((sp + 232#64).toNat, 4, 0#64)]) (sp.toNat + k) = ldv kd Mt (sp.toNat + k) :=
    fun kd k hk => hfr2.ldv kd fun j hj h => by
      unfold PrintReg at h
      rcases h with h | h
      · exact hSR (sp.toNat + k + j) (by omega) (by omega) (by omega) (by omega) (by omega) h
      · omega
  refine hk _ _ out pend' hrel ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ hfr2
  · rsimp; exact k2
  · rsimp; rw [rk9]; exact hP.s1
  · rsimp; rw [rk18]; exact hP.s2
  · rsimp; rw [rk19]; exact hP.s3
  · rsimp; rw [rk21]; exact hP.s5
  · rsimp; rw [rk21]; exact hP.s5
  · rsimp; rw [rk24]; exact h24
  · have := hout .ld 0 (by simp [widthOfM]); simp only [Nat.add_zero] at this; rw [this]; exact hP.reent
  · rw [eo 8 (by omega), hout .ld 8 (by simp [widthOfM]), ← eo 8 (by omega)]; exact hP.file
  · rw [eo 16 (by omega), hout .ld 16 (by simp [widthOfM]), ← eo 16 (by omega)]; exact hP.count
  · rw [eo 224 (by omega), hout .ld 224 (by simp [widthOfM]), ← eo 224 (by omega)]; exact hP.base
  · nx_mem; rfl
  · rw [ldv_ld_miss _ _ (by rw [eo 232 (by omega), eo 240 (by omega)]; omega)]
    rw [← hres', BitVec.add_assoc]; rfl
  · exact hF'.frame_out hst (by omega) fun b hb => by omega

end VsaIris.Sym.Fp
