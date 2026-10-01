import Vsa.Compiler.SimExit
import Vsa.Compiler.R6Keys

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem define_closures (s : Store) (c : Addr) (x : String) (v : Value) : (s.define c x v).closures = s.closures :=
  rfl

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem run_storeSlot {T : List String} {V : View} {st : St} {d : Nat} {env : Addr} {Γ : List (List String)}
    {sp fs pos : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A) (hA : A.pc = pcOf pos) {x : String}
    (hx : x ∈ Γ.headD []) (hseg : Seg code pos (storeSlot ((slotOf (Γ.headD []) x).getD 0))) {v : Value}
    {t p : BitVec 64} (h10 : Has A.regs a0 t) (h11 : Has A.regs a1 p) (hv : VRepr V.H A.mem V.h v t p) :
    Reaches code A (fun B => B.pc = pcOf (pos + 4) ∧
      MS code T V ⟨st.store.define env x v, st.out⟩ d env Γ sp fs B ∧ B.out = A.out ∧
      OutFrames A.mem B.mem V.hF ∧ Keep [t6] A.regs B.regs ∧
      SameShape st.store (st.store.define env x v)) := by
  obtain ⟨pc0, L, m, o⟩ := A
  simp only at hA h10 h11 hv; subst hA
  obtain ⟨hb, he, ht⟩ := frame_consts
  obtain ⟨f, hFa⟩ := hm.chn.head'
  obtain ⟨fr, hfr⟩ := hm.chn.frame
  obtain ⟨i, hsl⟩ : ∃ i, slotOf (Γ.headD []) x = some i := by
    cases h' : slotOf (Γ.headD []) x with
    | none => exact absurd hx (slotOf_none h')
    | some i => exact ⟨i, rfl⟩
  have hi := slotOf_lt hsl
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hm.rel.region env f _ hFa
  have htop := hm.rel.top
  unfold frSize at hf2
  have t1 : f + (8 + 16 * i) ≠ tohostAddr := by omega
  have t2 : f + (8 + 16 * i) + 8 ≠ tohostAddr := by omega
  have o1 : StOK (f + (8 + 16 * i)) := by unfold StOK; omega
  have o2 : StOK (f + (8 + 16 * i) + 8) := by unfold StOK; omega
  apply run_whole hR.fits hseg
  wp_simp [storeSlot, hsl, Option.getD_some, hm.keys.row.wp, View.fa_eq hFa, h10.wp, h11.wp, toNat_ofNat_lt,
    t1, t2, o1, o2]
  have ea : f + (8 + 16 * i) = f + 8 + 16 * i := by omega
  rw [ea]
  have hs1 := hm.rel.write_slot hfr hFa hsl hv (defFrame x v) binds_define
  rw [← define_eq] at hs1
  have hout : OutFrames m (applyW (applyW m (f + 8 + 16 * i, 8, t)) (f + 8 + 16 * i + 8, 8, p)) V.hF :=
    fun b hb' hb'' => by rw [rdW_two (by omega) hb', if_neg (by omega), if_neg (by omega)]
  have hobj := hout.obj (h := V.h) htop
  have hsh := define_shape st.store env x v
  refine reach_here ⟨by simp, ?_, rfl, hout, by reg_simp []; exact Keep.refl _ _, hsh⟩
  exact {
    rel := hs1
    img := hm.img.transport hobj (Nat.le_refl _) hm.img.ptr
    clo := hm.clo.shape hm.rel.clo hobj hsh (define_closures _ _ _ _)
    chn := hm.chn.transport hsh
    out := hm.out
    ho := by reg_simp []; exact hm.ho
    hf := by reg_simp []; exact hm.hf
    henv := by reg_simp []; exact hm.henv
    hsp := by reg_simp []; exact hm.hsp
    hdep := by reg_simp []; exact hm.hdep
    stk := hm.stk
    hfal := hm.hfal }

end

end Vsa.Compiler
