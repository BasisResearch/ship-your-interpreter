import VsaIris.Vsa.Fprintf.Inner
import VsaIris.Vsa.Stderr.VfpEntry

/-!
# The inner `_vfprintf_r(reent, fake, "%lld", ap)` (lane N5)

`__sbprintf` calls `_vfprintf_r` on its stack `FILE`. For `"%lld"` the run
is the entry (N3's `vfpEntry_run`), the stack `FILE`'s prologue
(`vfp_fileSb`), the head (`vfp_headC`), the empty literal run before the
`%` (`vfp_toTerm`), the conversion (`vfp_lld`), the empty run before the NUL
(`vfp_toTerm`), and the end with nothing pending (`vfp_end0`). The bytes
reach the stack `FILE`'s buffer (`SbFile`); `lldBytes v` is what it prints.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem VfpSpills.frame {Mt M' : Mem} {sp : BitVec 64} {C : Nat → BitVec 64} {Reg : Nat → Prop}
    (h : VfpSpills Mt sp C) (hF : Frame M' Mt Reg) (hsp : sp.toNat + 600 < 2 ^ 64)
    (hR : ∀ a, Reg a → a < sp.toNat + 488 ∨ sp.toNat + 592 ≤ a) : VfpSpills M' sp C := by
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have l : ∀ k, 488 ≤ k → k + 8 ≤ 592 → ldv .ld M' (sp.toNat + k) = ldv .ld Mt (sp.toNat + k) :=
    fun k h1 h2 => hF.ldv .ld fun j hj hr => by simp only [widthOfM] at hj; have := hR _ hr; omega
  have l' : ∀ k, 488 ≤ k → k + 8 ≤ 592 → ldv .ld M' (sp + BitVec.ofNat 64 k).toNat =
      ldv .ld Mt (sp + BitVec.ofNat 64 k).toNat := fun k h1 h2 => by rw [eo k (by omega)]; exact l k h1 h2
  exact ⟨(l 584 (by omega) (by omega)).trans h.ra, (l 576 (by omega) (by omega)).trans h.s0,
    (l' 568 (by omega) (by omega)).trans h.s1, (l' 560 (by omega) (by omega)).trans h.s2,
    (l' 552 (by omega) (by omega)).trans h.s3, (l 544 (by omega) (by omega)).trans h.s4,
    (l' 536 (by omega) (by omega)).trans h.s5, (l 528 (by omega) (by omega)).trans h.s6,
    (l' 520 (by omega) (by omega)).trans h.s7, (l' 512 (by omega) (by omega)).trans h.s8,
    (l' 504 (by omega) (by omega)).trans h.s9, (l' 496 (by omega) (by omega)).trans h.s10,
    (l' 488 (by omega) (by omega)).trans h.s11⟩

/-- The caller's callee-saved registers in `_vfprintf_r`'s frame, from the
entry's spills (`VfpEntry`) and the head's (`VfpHeadPost`). -/
theorem vfpSpills_of {R R1 R2 R3 : Nat → BitVec 64} {Mt Mt1 Mt3 : Mem} {sp : BitVec 64}
    (E : VfpEntry R R1 Mt Mt1 sp) (H : VfpHeadPost R2 R3 Mt1 Mt3 sp)
    (hk : ∀ x ∈ [9, 18, 19, 21, 23, 24, 25, 26, 27], R2 x = R x) (hsp : sp.toNat + 600 < 2 ^ 64) :
    VfpSpills Mt3 sp R := by
  have l : ∀ k, (k = 584 ∨ k = 576 ∨ k = 544 ∨ k = 528) →
      ldv .ld Mt3 (sp.toNat + k) = ldv .ld Mt1 (sp.toNat + k) := fun k hk =>
    H.frame.ldv .ld fun j hj hr => by simp only [widthOfM] at hj; unfold HeadReg at hr; omega
  exact ⟨(l 584 (by omega)).trans E.ra, (l 576 (by omega)).trans E.s0v, H.s1.trans (hk 9 (by decide)),
    H.s2.trans (hk 18 (by decide)), H.s3.trans (hk 19 (by decide)), (l 544 (by omega)).trans E.s4v,
    H.s5.trans (hk 21 (by decide)), (l 528 (by omega)).trans E.s6v, H.s7.trans (hk 23 (by decide)),
    H.s8.trans (hk 24 (by decide)), H.s9.trans (hk 25 (by decide)), H.s10.trans (hk 26 (by decide)),
    H.s11.trans (hk 27 (by decide))⟩

/-- The bytes the inner `_vfprintf_r` changes: its frame and the callee
frames below it, the stack `FILE`, `stdout`'s flags, `errno`. -/
def InnerReg (f sp : Nat) (a : Nat) : Prop :=
  (sp - 384 ≤ a ∧ a < sp + 592) ∨ (f ≤ a ∧ a < f + 1208) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨
    (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

/-- **The start of `_vfprintf_r(reent, f, P, ap)` on the stack `FILE`**, at the
loop head: the loop state, the caller's callee-saved registers spilled, the
memory changed only in the frame, `ap` in its slot. -/
structure VfpBegin (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (sp f P : BitVec 64) : Prop where
  loop : VfpLoop R' Mt' sp 0x8001b538#64 f P 0
  spills : VfpSpills Mt' sp R
  frame : Frame Mt' Mt (fun a => sp.toNat ≤ a ∧ a < sp.toNat + 592)
  ap : ldv .ld Mt' (sp.toNat + 24) = R 13

theorem vfp_begin (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f P : BitVec 64} {need : Nat} {pend0 : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat + 592 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (h2 : R 2 = sp + 592#64) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h12 : R 12 = P)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8) (hF : SbFile Mt f pend0)
    (hk : ∀ R' Mt', VfpBegin R R' Mt Mt' sp f P →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b0#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R Mt := by
  have hsp : (sp + 592#64).toNat = sp.toNat + 592 := sp_lit (by omega)
  have hsp' : R 2 - 592#64 = sp := by rw [h2, BitVec.add_sub_cancel]
  refine vfpEntry_run hlive t Mt R s need (by rw [h2, hsp]; omega) (by rw [h2, hsp]; omega) hs3 hs4
    (by rw [h2, hsp]; omega) (R 1) _ _ _ _ rfl h10 h11 h12 rfl hdec hdA hdv fun R1 Mt1 E => ?_
  rw [hsp'] at E
  have hFrE : Frame Mt1 Mt (fun a => sp.toNat ≤ a ∧ a < sp.toNat + 592) := E.frame
  have hF1 : SbFile Mt1 f pend0 := hF.frame_out hFrE (by omega) fun b hb => by omega
  refine vfp_fileSb hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa E.sp_eq (E.s0.trans h10) (E.s4.trans h11) hF1
    fun R2 k2 => ?_
  refine vfp_headC hlive hs1 hs2 hs3 hs4 hal ((k2 2 (by decide)).trans E.sp_eq) fun R3 Mt3 H => ?_
  have e8 : R2 8 = 0x8001b538#64 := (k2 8 (by decide)).trans (E.s0.trans h10)
  have e20 : R2 20 = f := (k2 20 (by decide)).trans (E.s4.trans h11)
  have e22 : R2 22 = P := (k2 22 (by decide)).trans (E.s6.trans h12)
  have HL := H.loop; rw [e8, e20, e22] at HL
  refine hk R3 Mt3 ⟨HL, vfpSpills_of E H (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k2 _ (by decide)).trans (E.keep _ (by decide))) (by omega),
    hFrE.trans (H.frame.mono fun a h => by unfold HeadReg at h; omega),
    (H.frame.ldv .ld fun j hj h => by simp only [widthOfM] at hj; unfold HeadReg at h; omega).trans E.ap⟩

theorem vfpInnerLld (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f ap v : BitVec 64} {need : Nat} {pend0 : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat + 592 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (hap1 : sp.toNat + 592 ≤ ap.toNat) (hap2 : ap.toNat + 8 ≤ s.toNat) (hapa : ap.toNat % 8 = 0)
    (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = sp + 592#64) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h12 : R 12 = 0x800192c0#64)
    (h13 : R 13 = ap)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    (hF : SbFile Mt f pend0) (hL : LocMb Mt) (hv : ldv .ld Mt ap.toNat = v)
    (hFm : LldFmt Dt DA) (hP0 : FmtAt Dt DA 0x800192c0 [37#8]) (hP4 : FmtAt Dt DA 0x800192c4 [0#8])
    (hk : ∀ R' M' out pend', pend0 ++ lldBytes v = out ++ pend' → R' 2 = R 2 → R' 1 = R 1 →
      (∀ x ∈ vfpSaved, R' x = R x) → SbFile M' f pend' → LocMb M' → Frame M' Mt (InnerReg f.toNat sp.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R Mt := by
  refine vfp_begin hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa h2 h10 h11 h12 hdec hdA hdv hF fun R3 Mt3 B => ?_
  have hsp6 : sp.toNat + 600 < 2 ^ 64 := by omega
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have HL := B.loop
  have hFr3 := B.frame
  have hsv3 := B.spills
  have hloc3 : LocMb Mt3 := hL.frame hFr3 (fun a h1 h2 h => by omega) (fun h => by omega)
  have hF3 : SbFile Mt3 f pend0 := hF.frame_out hFr3 (by omega) fun b hb => by omega
  have hap3 : ldv .ld Mt3 (sp.toNat + 24) = ap := B.ap.trans h13
  have hv3 : ldv .ld Mt3 ap.toNat = v :=
    (hFr3.ldv .ld fun j hj h => by simp only [widthOfM] at hj; omega).trans hv
  have hP0' : FmtAt Dt DA (0x800192c0#64 : BitVec 64).toNat ([] ++ [37#8]) := hP0
  refine vfp_toTerm hlive (Or.inr rfl) hs1 hs2 hs3 hs4 hal HL hloc3 hP0' (by simp) (by simp) fun R4 Mt4 S4 f22 => ?_
  rw [show termPC 37#8 = 0x8000a9fc#64 by decide]
  have hP4' : VfpPend R4 Mt4 sp 0x8001b538#64 f 0 [] := by
    have := S4.pend; simpa [litIov] using this
  have h25 : R4 25 = 0x800192c0#64 := by have := S4.s9; simpa using this
  have hSc : ∀ a, ScanReg sp.toNat a → sp.toNat + 16 ≤ a ∧ a < sp.toNat + 368 ∧
      (a < sp.toNat + 24 ∨ sp.toNat + 32 ≤ a) := fun a h => by unfold ScanReg MbReg at h; omega
  have hap4 : ldv .ld Mt4 (sp + 24#64).toNat = ap := by
    rw [eo 24 (by omega), S4.frame.ldv .ld fun j hj h => by simp only [widthOfM] at hj; have := hSc _ h; omega]
    exact hap3
  have hv4 : ldv .ld Mt4 ap.toNat = v := by
    rw [S4.frame.ldv .ld fun j hj h => by simp only [widthOfM] at hj; have := hSc _ h; omega]; exact hv3
  have hF4 : SbFile Mt4 f pend0 := hF3.frame_out S4.frame (by omega) fun b hb => by have := hSc _ hb; omega
  refine vfp_lld hlive hlive' hsub hs1 hs2 hs3 hs4 hal hf1 hf2 hfa hap1 hap2 hapa (by omega) hP4' h25 hFm
    hap4 hv4 hF4 fun R5 M5 out pend' hrel HL5 hSb5 hfr5 => ?_
  have hLl : ∀ a, LldReg f.toNat sp.toNat a → (sp.toNat - 384 ≤ a ∧ a < sp.toNat + 384) ∨
      (f.toNat ≤ a ∧ a < f.toNat + 1208) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨
      (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) := fun a h => by
    unfold LldReg MagReg StageReg PrintReg SprintReg SfvCallReg LoopReg SfvReg at h; omega
  have hloc5 : LocMb M5 := (hloc3.frame S4.frame (fun a h1 h2 h => by have := hSc _ h; omega)
    (fun h => by have := hSc _ h; omega)).frame hfr5 (fun a h1 h2 h => by have := hLl _ h; omega)
    (fun h => by have := hLl _ h; omega)
  have hcl : lldCnt (lldSign v) (digBytes (lldMag v).toNat) ≤ 21 := by
    have := digBytes_len (lldMag v).toNat (lldMag v).isLt; unfold lldCnt; split <;> omega
  have hP4'' : FmtAt Dt DA (0x800192c4#64 : BitVec 64).toNat ([] ++ [0#8]) := hP4
  refine vfp_toTerm hlive (Or.inl rfl) hs1 hs2 hs3 hs4 hal HL5 hloc5 hP4'' (by simp) (by simp; omega)
    fun R6 M6 S6 f22' => ?_
  rw [show termPC 0#8 = 0x8000aca8#64 by decide]
  have hP6 : VfpPend R6 M6 sp 0x8001b538#64 f (0 + lldCnt (lldSign v) (digBytes (lldMag v).toNat)) [] := by
    have := S6.pend; simpa [litIov] using this
  have hSb6 : SbFile M6 f pend' := hSb5.frame_out S6.frame (by omega) fun b hb => by have := hSc _ hb; omega
  have hS6 : VfpSpills M6 sp R :=
    ((hsv3.frame S4.frame hsp6 fun a h => by have := hSc _ h; omega).frame hfr5 hsp6
      fun a h => by have := hLl _ h; omega).frame S6.frame hsp6 fun a h => by have := hSc _ h; omega
  have hst : Frame (writeLog M6 [((sp + 232#64).toNat, 4, 0#64)]) M6
      (fun a => sp.toNat + 232 ≤ a ∧ a < sp.toNat + 236) :=
    Frame.store M6 _ fun b h1 h2 => by rw [eo 232 (by omega)] at h1 h2; exact ⟨h1, h2⟩
  refine vfp_end0 hlive hs1 hs2 hs3 hs4 hal (by omega) (by omega) hfa (fun b h1 h2 => by unfold outS; omega)
    (.inr hf1) hP6 ⟨hSb6.flags, hSb6.flags2, by decide, by decide⟩ hS6 hra rfl fun R7 e10 e2 e1 ekeep => ?_
  refine hk R7 _ out pend' hrel (e2.trans h2.symm) e1 ekeep (hSb6.frame_out hst (by omega) fun b hb => by omega)
    ((hloc5.frame S6.frame (fun a h1 h2 h => by have := hSc _ h; omega) (fun h => by have := hSc _ h; omega)).frame
      hst (fun a h1 h2 h => by omega) (fun h => by omega)) ?_
  refine ((((hFr3.mono fun a h => ?_).trans (S4.frame.mono fun a h => ?_)).trans (hfr5.mono fun a h => ?_)).trans
    (S6.frame.mono fun a h => ?_)).trans (hst.mono fun a h => ?_)
  all_goals unfold InnerReg
  · omega
  · have := hSc _ h; omega
  · have := hLl _ h; omega
  · have := hSc _ h; omega
  · omega

end VsaIris.Sym.Fp
