import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.Fprintf.Loop
import VsaIris.Vsa.Fprintf.Sprint
import VsaIris.Interp.ITacTree
import VsaIris.Vsa.Carry

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout VsaIris.Sym.Win

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

structure VfpPend (R : Nat → BitVec 64) (Mt : Mem) (sp reent f : BitVec 64) (cnt : Nat)
    (iovs : List (Nat × List (BitVec 8))) : Prop where
  spR : R 2 = sp
  s1 : R 9 = 0x8001b798#64
  s2 : R 18 = 16#64
  s3 : R 19 = 37#64
  s5 : R 21 = sp + 352#64
  s7 : R 23 = sp + BitVec.ofNat 64 (352 + 16 * iovs.length)
  reent : ldv .ld Mt sp.toNat = reent
  file : ldv .ld Mt (sp + 8#64).toNat = f
  count : ldv .ld Mt (sp + 16#64).toNat = BitVec.ofNat 64 cnt
  base : ldv .ld Mt (sp + 224#64).toNat = sp + 352#64
  iovcnt : ldv .lw Mt (sp + 232#64).toNat = BitVec.ofNat 64 iovs.length
  resid : ldv .ld Mt (sp + 240#64).toNat = BitVec.ofNat 64 (piecesLen iovs)
  arr : IovAt Mt (sp.toNat + 352) iovs

def litIov (P : Nat) (bs : List (BitVec 8)) : List (Nat × List (BitVec 8)) :=
  if bs = [] then [] else [(P, bs)]

theorem addw_ofNat' {a b : Nat} (h : a + b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) =
      BitVec.ofNat 64 (a + b) := by
  have e : BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 b) =
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 (a + b)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [e]; exact sextw_ofNat h

def ScanReg (sp : Nat) (a : Nat) : Prop :=
  MbReg sp a ∨ (sp + 16 ≤ a ∧ a < sp + 24) ∨ (sp + 232 ≤ a ∧ a < sp + 248) ∨
    (sp + 352 ≤ a ∧ a < sp + 368)

structure ScanPost (R' : Nat → BitVec 64) (Mt Mt' : Mem) (sp reent f P : BitVec 64) (cnt : Nat)
    (bs : List (BitVec 8)) : Prop where
  pend : VfpPend R' Mt' sp reent f (cnt + bs.length) (litIov P.toNat bs)
  s9 : R' 25 = P + BitVec.ofNat 64 bs.length
  s8 : R' 24 = P
  loc : LocMb Mt'
  frame : Frame Mt' Mt (ScanReg sp.toNat)

def termPC (c : BitVec 8) : BitVec 64 := if c = 0#8 then 0x8000aca8#64 else 0x8000a9fc#64

def termFlag (c : BitVec 8) : BitVec 64 := if c = 0#8 then 0#64 else 1#64

set_option hygiene false in

local macro "scan_tail" : tactic => `(tactic| (
      rcases hbsn : bs with _ | ⟨b0, bs'⟩
      · subst hbsn
        simp only [List.length_nil, BitVec.add_zero] at r25
        nx_run hlive using [r2, r19, r24, r23, r25, e10, l240, l232, l16, l240', l232', lw_zext8, hce', BitVec.sub_self, BitVec.add_assoc] at 2147527164 2147527848
        have hfr2 : Frame (writeLog Mt1 [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 c)]) Mt (ScanReg sp.toNat) :=
          (hfr1.mono fun a h => .inl h).snoc fun b h1 h2 => by rw [eo 180 (by omega)] at h1 h2; unfold ScanReg MbReg; omega
        refine hk _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hfr2⟩ (by rsimp)
        all_goals simp (config := {failIfUnchanged := false}) only [litIov, if_pos, List.length_nil,
          Nat.add_zero, Nat.mul_zero, piecesLen, List.map_nil, List.sum_nil]
        all_goals try carry_close [r2, r19, r23, r24, r25, kk, hL.s1, hL.s2, hL.s5, hfr1.ldv, hL.reent, hL.file,
          hL.base, l16, l232, l240]
        all_goals first | (intro j hj; simp at hj) | exact hloc1.mb _ (by omega) (by omega)
      · have hn : bs.length = bs'.length + 1 := by rw [hbsn]; rfl
        have hsw := subw_add_ofNat (n := bs.length) (by omega) P
        have hz1 : (BitVec.ofNat 64 bs.length = 0#64) = False := eq_false fun h => by
          have := congrArg BitVec.toNat h; simp at this; omega
        have hz2 : (BitVec.ofNat 64 bs.length ≠ 0#64) = True := eq_true fun h => by
          have := congrArg BitVec.toNat h; simp at this; omega
        rw [← hbsn] at *
        nx_run hlive using [r2, r19, r24, r23, r25, e10, l240, l232, l16, l240', l232', lw_zext8, hce', hsw, hz1, hz2, l16', haw, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add] at 2147527164 2147527848
        have hbne : bs ≠ [] := fun h => by rw [h] at hn; simp at hn
        have hlit : litIov P.toNat bs = [(P.toNat, bs)] := by simp [litIov, hbne]
        have hfr2 : Frame (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt1
            [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 c)]) [((sp + 352#64).toNat, 8, P)])
            [((sp + 360#64).toNat, 8, BitVec.ofNat 64 bs.length)]) [((sp + 240#64).toNat, 8, BitVec.ofNat 64 bs.length)])
            [((sp + 232#64).toNat, 4, 1#64)]) [((sp + 16#64).toNat, 8, BitVec.ofNat 64 (cnt + bs.length))]) Mt
            (ScanReg sp.toNat) := by
          refine (hfr1.mono fun a h => .inl h).snoc ?_ |>.snoc ?_ |>.snoc ?_ |>.snoc ?_ |>.snoc ?_ |>.snoc ?_
          all_goals (intro b h1 h2; simp (disch := omega) only [toNat_add_lit] at h1 h2; unfold ScanReg MbReg; omega)
        refine hk _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hfr2⟩ (by rsimp)
        all_goals simp (config := {failIfUnchanged := false}) only [hlit, List.length_singleton, piecesLen,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        all_goals try carry_close [r2, r19, r23, r24, r25, kk, hL.s1, hL.s2, hL.s5, hfr1.ldv, hL.reent, hL.file,
          hL.base]
        · intro j hj
          obtain rfl : j = 0 := by simp at hj; omega
          constructor <;> carry_close [eo, Nat.mul_zero, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        · exact hloc.frame hfr2 (fun a h1 h2 h => by unfold ScanReg MbReg at h; omega) (fun h => by unfold ScanReg MbReg at h; omega)))

#ix_piece vfpToTerm_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp reent f P : BitVec 64} {need cnt : Nat} {bs : List (BitVec 8)} {c : BitVec 8} (hc : c = 0#8 ∨ c = 37#8)
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hL : VfpLoop R Mt sp reent f P cnt) (hloc : LocMb Mt)
    (hF : FmtAt Dt DA P.toNat (bs ++ [c])) (hbs : ∀ b ∈ bs, b ≠ 0#8 ∧ b ≠ 37#8)
    (hcnt : cnt + bs.length < 2 ^ 31)
    (hk : ∀ R' Mt', ScanPost R' Mt Mt' sp reent f P cnt bs → R' 22 = termFlag c →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t (termPC c) R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b0#64 R Mt by
  nx_win sp 1024 592; have h2 := hL.spR; have h24 := hL.fmt
  nx_run hlive using [h2, h24] at 2147527096
  have hFb : FmtAt Dt DA P.toNat bs := ⟨hF.lo, by have := hF.hi; simp at this; omega,
    fun i hi => hF.mem i (by simp; omega), fun i hi => by
      have := hF.byte i (by simp; omega); rwa [List.getElem_append_left hi] at this⟩
  refine vfp_scan hlive hs1 hs2 hs3 hs4 hal bs P _ Mt hFb hbs (by rsimp; exact h2) (by rsimp; exact hL.s1)
    (by rsimp; exact hL.s3) (by rsimp) hloc fun R1 Mt1 e25 hk1 hloc1 hfr1 => ?_
  have hP2 := hF.hi; simp only [List.length_append, List.length_singleton] at hP2
  have hP1 := hF.lo
  have ePn : (P + BitVec.ofNat 64 bs.length).toNat = P.toNat + bs.length := toNat_add_lit (by omega)
  have hcb := hF.byte bs.length (by simp)
  simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] at hcb
  have hcm := hF.mem bs.length (by simp)
  refine vfp_mb hlive hs1 hs2 hs3 hs4 hal (by carry_close [hk1, h2]) (by carry_close [hk1, hL.s1]) e25 (by rw [ePn]; omega) (by rw [ePn]; omega)
    (by rw [ePn]; exact hcm) (by rw [ePn]; exact hcb) hloc1 fun R2 h0 h10 hk2 => ?_
  have kk : ∀ x ∈ [2, 9, 18, 19, 21, 23, 24], R2 x = R x := by carry_close [hk2, hk1]
  have r2 : R2 2 = sp := (kk 2 (by decide)).trans h2
  have r19 : R2 19 = 37#64 := (kk 19 (by decide)).trans hL.s3
  have r24 : R2 24 = P := (kk 24 (by decide)).trans h24
  have r23 : R2 23 = sp + 352#64 := (kk 23 (by decide)).trans hL.s7
  have r25 : R2 25 = P + BitVec.ofNat 64 bs.length := by carry_close [hk2, e25]
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    sp_lit (by omega)
  have l240 : ldv .ld (writeLog Mt1 [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 c)]) (sp + 240#64).toNat = 0#64 := by
    carry_close [hfr1.ldv, hL.resid]
  have l232 : ldv .lw (writeLog Mt1 [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 c)]) (sp + 232#64).toNat = 0#64 := by
    carry_close [hfr1.ldv, hL.iovcnt]
  have l16 : ldv .ld (writeLog Mt1 [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 c)]) (sp + 16#64).toNat =
      BitVec.ofNat 64 cnt := by carry_close [hfr1.ldv, hL.count]
  have l16' : ldv .ld Mt1 (sp + 16#64).toNat = BitVec.ofNat 64 cnt := by carry_close [hfr1.ldv, hL.count]
  have haw := addw_ofNat' (a := cnt) (b := bs.length) hcnt
  have l240' : ldv .ld Mt1 (sp + 240#64).toNat = 0#64 := by carry_close [hfr1.ldv, hL.resid]
  have l232' : ldv .lw Mt1 (sp + 232#64).toNat = 0#64 := by carry_close [hfr1.ldv, hL.iovcnt]
  have hce : (BitVec.zeroExtend 64 c = 37#64) = (c = 37#8) := by
    apply propext; constructor
    · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; simp at this; have := c.isLt; simp; omega
    · intro h; subst h; decide
  rcases hc with hc0 | hc37

#ix_piece vfpToTerm_2 from vfpToTerm_1 at 1 by
  have e10 := h0 hc0
  have hce' : (BitVec.zeroExtend 64 c = 37#64) = False := by rw [hce, hc0]; exact eq_false (by decide)
  have hpc : termPC c = 0x8000aca8#64 := by simp [termPC, hc0]
  have hfl : termFlag c = 0#64 := by simp [termFlag, hc0]
  simp only [hpc, hfl] at hk
  scan_tail

#ix_piece vfpToTerm_3 from vfpToTerm_1 at 2 by
  have e10 := h10 (by rw [hc37]; decide)
  have hce' : (BitVec.zeroExtend 64 c = 37#64) = True := by rw [hce]; exact eq_true hc37
  have hpc : termPC c = 0x8000a9fc#64 := by simp [termPC, hc37]
  have hfl : termFlag c = 1#64 := by simp [termFlag, hc37]
  simp only [hpc, hfl] at hk
  scan_tail

#ix_tree vfp_toTerm := vfpToTerm_1 [vfpToTerm_2, vfpToTerm_3]

end VsaIris.Sym.Fp
