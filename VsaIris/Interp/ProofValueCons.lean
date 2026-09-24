import VsaIris.Interp.HelperRun
import VsaIris.Interp.SpecValue

/-!
# The value constructors (lane H2)

`value_null`, `value_bool`, `value_int` (lane G's `valueIntSpec`) and
`value_str`: each is one symbolic run of two or three stores and a `ret`
(`helper_leaf`), over the result slot.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **`value_null`**, for either WP. -/
theorem valueNull_spec (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    (N : NativeAddrs) (p : BitVec 64) : ⊢ valueNullSpec (vsaModel live) N Wp p := by
  unfold valueNullSpec
  refine helper_leaf Wp (InExt (p.toNat, 24)) iprop(emp) (fun rv _ => SlotGeom p ∧ rv 10 = p)
    (fun _ mv => imgLE mv p.toNat 4 = 0) (fun rv h10 => ?_) (fun rv Mt r h10 hP hal => ?_)
    (fun rv' mv hg => ?_)
  · iintro ⟨Hs, %hg⟩
    ihave ⟨%Mt, H⟩ := slot24_tracked _ $$ Hs
    iexists Mt
    iframe H
    ipureintro; exact ⟨trivial, hg, h10⟩
  · obtain ⟨hg, h10⟩ := hP
    have hg1 := hg.al; have hg2 := hg.lo; have hg3 := hg.hi
    unfold valueNullPC
    ix_run hlive using [h10]
    refine swp_helperEnd (by ix_reg) (fun x hx hc => by
      have : x ≠ 1 := fun e => by subst e; revert hx; decide
      ix_reg; simp [this]) (fun rv' mv _ hmv => ?_)
    rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)),
      imgLE_store_miss _ _ (by rw [BitVec.toNat_add]; simp; omega), imgLE_store4_hit]
    rfl
  · iintro ⟨-, HS⟩
    iapply valAt_of_img
    iframe HS
    unfold valImg valOf
    ipureintro
    rw [imgW_lo32]; exact hg

/-- The low word of a slot's first two words, through a later store of the
other word (`sw`/`sd` order of the constructors). -/
theorem imgW_lo32_of (mv : Nat → BitVec 8) (a k : Nat) (h : imgLE mv a 4 = k) :
    (imgW mv a).toNat % 2 ^ 32 = k := by rw [imgW_lo32, h]

/-- **`value_bool`**, for either WP. -/
theorem valueBool_spec (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    (N : NativeAddrs) (p b : BitVec 64) : ⊢ valueBoolSpec (vsaModel live) N Wp p b := by
  unfold valueBoolSpec
  refine helper_leaf Wp (InExt (p.toNat, 24)) iprop(emp) (fun rv _ => SlotGeom p ∧ rv 10 = p ∧ rv 11 = b)
    (fun _ mv => imgLE mv p.toNat 4 = 1 ∧ imgLE mv (p.toNat + 8) 4 = cond (b != 0#64) 1 0)
    (fun rv h => ?_) (fun rv Mt r h hP hal => ?_) (fun rv' mv hg => ?_)
  · iintro ⟨Hs, %hg⟩
    ihave ⟨%Mt, H⟩ := slot24_tracked _ $$ Hs
    iexists Mt
    iframe H
    ipureintro; exact ⟨trivial, hg, h⟩
  · obtain ⟨hg, h10, h11⟩ := hP
    have hg1 := hg.al; have hg2 := hg.lo; have hg3 := hg.hi
    unfold valueBoolPC
    ix_run hlive using [h10, h11]
    refine swp_helperEnd (by ix_reg) (fun x hx hc => by
      have : x ≠ 1 := fun e => by subst e; revert hx; decide
      have : x ≠ 15 := fun e => by subst e; exact hc (by decide)
      have : x ≠ 11 := fun e => by subst e; exact hc (by decide)
      ix_reg; simp [*]) (fun rv' mv _ hmv => ⟨?_, ?_⟩)
    · rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)), imgLE_store4_hit]
      rfl
    · rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)),
        imgLE_store_miss _ _ (by omega)]
      rw [show (p + 8#64).toNat = p.toNat + 8 by rw [BitVec.toNat_add]; simp; omega,
        imgLE_store4_hit, snez_reg]
      cases (b != 0#64) <;> decide
  · iintro ⟨-, HS⟩
    iapply valAt_of_img
    iframe HS
    unfold valImg valOf
    ipureintro
    refine ⟨imgW_lo32_of _ _ _ hg.1, ?_⟩
    rw [imgW_lo32_of _ _ _ hg.2]

/-- **`value_int`** (lane G's `valueIntSpec`), for either WP. -/
theorem valueInt_spec (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    (N : NativeAddrs) (p n : BitVec 64) : ⊢ valueIntSpec (vsaModel live) N Wp p n := by
  unfold valueIntSpec
  refine helper_leaf Wp (InExt (p.toNat, 24)) iprop(emp) (fun rv _ => SlotGeom p ∧ rv 10 = p ∧ rv 11 = n)
    (fun _ mv => imgLE mv p.toNat 4 = 2 ∧ imgLE mv (p.toNat + 8) 8 = n.toNat)
    (fun rv h => ?_) (fun rv Mt r h hP hal => ?_) (fun rv' mv hg => ?_)
  · iintro ⟨Hs, %hg⟩
    ihave ⟨%Mt, H⟩ := slot24_tracked _ $$ Hs
    iexists Mt
    iframe H
    ipureintro; exact ⟨trivial, hg, h⟩
  · obtain ⟨hg, h10, h11⟩ := hP
    have hg1 := hg.al; have hg2 := hg.lo; have hg3 := hg.hi
    ix_run hlive using [h10, h11]
    refine swp_helperEnd (by ix_reg) (fun x hx hc => by
      have : x ≠ 1 := fun e => by subst e; revert hx; decide
      have : x ≠ 15 := fun e => by subst e; exact hc (by decide)
      ix_reg; simp [*]) (fun rv' mv _ hmv => ⟨?_, ?_⟩)
    · rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)), imgLE_store4_hit]
      rfl
    · rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)),
        imgLE_store_miss _ _ (by omega)]
      rw [show (p + 8#64).toNat = p.toNat + 8 by rw [BitVec.toNat_add]; simp; omega,
        imgLE_imgM_store]
  · iintro ⟨-, HS⟩
    iapply valAt_of_img
    iframe HS
    unfold valImg valOf
    ipureintro
    refine ⟨imgW_lo32_of _ _ _ hg.1, ?_⟩
    have : imgW mv (p.toNat + 8) = n := by
      apply BitVec.eq_of_toNat_eq; rw [imgW_toNat, hg.2]
    rw [this]

/-- **`value_str`**, for either WP. -/
theorem valueStr_spec (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    (N : NativeAddrs) (p q : BitVec 64) (x : String) : ⊢ valueStrSpec (vsaModel live) N Wp p q x := by
  unfold valueStrSpec
  refine helper_leaf Wp (InExt (p.toNat, 24)) (strAt q.toNat x)
    (fun rv _ => SlotGeom p ∧ q.toNat ≠ 0 ∧ rv 10 = p ∧ rv 11 = q)
    (fun _ mv => imgLE mv p.toNat 4 = 3 ∧ imgLE mv (p.toNat + 8) 8 = q.toNat ∧ q.toNat ≠ 0)
    (fun rv h => ?_) (fun rv Mt r h hP hal => ?_) (fun rv' mv hg => ?_)
  · iintro ⟨Hs, %⟨hg, hq⟩, #Hx⟩
    ihave ⟨%Mt, H⟩ := slot24_tracked _ $$ Hs
    iexists Mt
    iframe H Hx
    ipureintro; exact ⟨hg, hq, h⟩
  · obtain ⟨hg, hq, h10, h11⟩ := hP
    have hg1 := hg.al; have hg2 := hg.lo; have hg3 := hg.hi
    unfold valueStrPC
    ix_run hlive using [h10, h11]
    refine swp_helperEnd (by ix_reg) (fun x hx hc => by
      have : x ≠ 1 := fun e => by subst e; revert hx; decide
      have : x ≠ 15 := fun e => by subst e; exact hc (by decide)
      ix_reg; simp [*]) (fun rv' mv _ hmv => ⟨?_, ?_, hq⟩)
    · rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)), imgLE_store4_hit]
      rfl
    · rw [imgLE_agree (g := imgM _) (fun i hi => hmv _ (by simp [InExt]; omega)),
        imgLE_store_miss _ _ (by omega)]
      rw [show (p + 8#64).toNat = p.toNat + 8 by rw [BitVec.toNat_add]; simp; omega,
        imgLE_imgM_store]
  · iintro ⟨#Hx, HS⟩
    iapply valAt_of_img
    iframe HS
    unfold valImg valOf
    have : imgW mv (p.toNat + 8) = q := by
      apply BitVec.eq_of_toNat_eq; rw [imgW_toNat, hg.2.1]
    rw [this]
    isplitr
    · ipureintro; exact ⟨imgW_lo32_of _ _ _ hg.1, hg.2.2⟩
    · iexact Hx

end

end VsaIris.Interp
