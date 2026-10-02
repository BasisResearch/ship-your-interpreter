import VsaIris.Vsa.Stderr.StrCodeStdio
import VsaIris.Vsa.Fprintf.Tac
import VsaIris.Vsa.Stderr.Mt
import VsaIris.Vsa.SymCompactTac
import VsaIris.Interp.SymFront
import VsaIris.Vsa.Carry

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout
open VsaIris.Interp.StrLeaf VsaIris.Inst.Strlen

theorem dot_lctx {live : Nat → Prop} (hcl : ∀ p ∈ strCode, live p.1) {bv : Nat → BitVec 8}
    (h0 : bv 0x80019770 = 0x2e#8) (h1 : bv 0x80019771 = 0#8) :
    LCtx live 0x80019770#64 0x8000a8bc#64 1 bv where
  regions := ⟨by decide, by decide, by decide, by unfold tohostAddr; decide⟩
  str := ⟨fun k hk => by
      obtain rfl : k = 0 := by omega
      rw [show (0x80019770#64).toNat + 0 = 0x80019770 from rfl, h0]; decide,
    by rw [show (0x80019770#64).toNat + 1 = 0x80019771 from rfl, h1]; rfl⟩
  retAlign := by decide
  code := hcl

theorem imgM_store1_eq (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    imgM (writeLog Mt [(b, 1, v)]) a = BitVec.ofNat 8 v.toNat := by
  subst h
  have := imgLE_store1_hit Mt a v
  simp only [imgLE, Nat.mul_zero, Nat.add_zero] at this
  apply BitVec.eq_of_toNat_eq
  rw [this, BitVec.toNat_ofNat]

structure VfpEntry (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (sp : BitVec 64) : Prop where
  sp_eq : R' 2 = sp
  s0 : R' 8 = R 10
  s4 : R' 20 = R 11
  s6 : R' 22 = R 12
  keep : ∀ x ∈ [9, 18, 19, 21, 23, 24, 25, 26, 27], R' x = R x
  frame : ∀ a, ¬ (sp.toNat ≤ a ∧ a < sp.toNat + 592) → imgM Mt' a = imgM Mt a
  ra : ldv .ld Mt' (sp.toNat + 584) = R 1
  s0v : ldv .ld Mt' (sp.toNat + 576) = R 8
  s4v : ldv .ld Mt' (sp.toNat + 544) = R 20
  s6v : ldv .ld Mt' (sp.toNat + 528) = R 22
  ap : ldv .ld Mt' (sp.toNat + 24) = R 13
  dec : ldv .ld Mt' (sp.toNat + 64) = 0x80019770#64
  decLen : ldv .ld Mt' (sp.toNat + 56) = 1#64
  mbs : ldv .ld Mt' (sp.toNat + 200) = 0#64

#ix_piece vfpEntry_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s : BitVec 64) (need : Nat)
    (hs1 : s.toNat - need + 592 ≤ (R 2).toNat) (hs2 : (R 2).toNat ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : (R 2).toNat % 16 = 0)
    (ra reent fp fmt ap : BitVec 64)
    (h1 : R 1 = ra) (h10 : R 10 = reent) (h11 : R 11 = fp) (h12 : R 12 = fmt)
    (h13 : R 13 = ap) (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64)
    (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    (hk : ∀ R' Mt', VfpEntry R R' Mt Mt' (R 2 - 592#64) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a8d0#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R Mt by
  xrun [30] hlive using [h1, h10, h11, h12, h13, hdec] at 0x80006cf0
  refine Fp.strlen_sw (dot_lctx (fun p hp => hlive _ (strCode_stdio p hp)) hdv.1 hdv.2)
    (fun p hp => ?_) (by nx_norm) (by nx_norm) (fun v => ?_)
  · rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ (strCode_stdio p h)
    · refine List.mem_append_right _ ?_
      unfold strText at h
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      have hk2 := List.mem_range.1 hk
      refine List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) ?_
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact hdA.1
      · exact hdA.2
  xrun [14] hlive using [h1, h10, h11, h12, h13, hdec, BitVec.reduceSub, BitVec.reduceHShiftLeft] at 0x8000a8d0

#ix_piece vfpEntry_02 from vfpEntry_01 by
  nx_runB hlive using [h1, h10, h11, h12, h13, hdec, BitVec.reduceSub, BitVec.reduceHShiftLeft] at 0x8000a8d0 #steps 1

#ix_piece vfpEntry_03 from vfpEntry_02 by
  nx_runB hlive using [h1, h10, h11, h12, h13, hdec, BitVec.reduceSub, BitVec.reduceHShiftLeft] at 0x8000a8d0 #steps 1

#ix_piece vfpEntry_04 from vfpEntry_03 by
  have e592 : R 2 + 18446744073709551024#64 = R 2 - 592#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  have hsp : (R 2 - 592#64).toNat = (R 2).toNat - 592 := toNat_sub_lit (by decide) (by omega)
  refine hk _ _ ⟨?gsp, ?gs0, ?gs4, ?gs6, ?gkeep, ?gframe, ?gra, ?gs0v, ?gs4v, ?gs6v, ?gap, ?gdec,
    ?gdecLen, ?gmbs⟩
  case gsp | gs0 | gs4 | gs6 | gkeep => carry_close [h10, h11, h12, e592]
  case gmbs =>
    rw [hsp]
    apply ldv_ld_of_imgLE
    simp only [imgLE, Nat.add_assoc, Nat.reduceAdd]
    simp (disch := nx_fdisch) only [imgM_store_miss, imgM_store1_eq]
    simp
  all_goals carry_close [hsp, hdec, h1, h13, toNat_add_neg, Nat.reducePow]

#ix_chain vfpEntry_run := [vfpEntry_01, vfpEntry_02, vfpEntry_03, vfpEntry_04]

end VsaIris.Sym
