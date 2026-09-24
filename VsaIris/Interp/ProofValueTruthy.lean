import VsaIris.Interp.HelperRun
import VsaIris.Interp.SpecValue

/-!
# `value_truthy` (lane H2)

One symbolic run over the value's slot (read only): the kind word selects
`bool` (`lw` of the payload), `int` (`ld` and `snez`) or the rest (`snez` of
the kind).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The run of `value_truthy`, per kind. -/
theorem valueTruthy_run (hlive : ∀ p ∈ interpText, live p.1) (N : NativeAddrs) (p r : BitVec 64)
    (rv : Nat → BitVec 64) (Mt : Mem) (v : Value) (hg : SlotGeom p) (h10 : rv 10 = p)
    (hv : ValPure N v (imgW (imgM Mt) p.toNat) (imgW (imgM Mt) (p.toNat + 8)) (imgW (imgM Mt) (p.toNat + 16)))
    (hal : r.toNat % 4 = 0) :
    IW live ∅ [] (InExt (p.toNat, 24))
      (HelperEnd r rv [10, 14, 15] (fun rv' mv => (rv' 10 = if v.truthy then 1#64 else 0#64) ∧
        ∀ a, InExt (p.toNat, 24) a → mv a = imgM Mt a))
      valueTruthyPC (upd rv 1 r) Mt := by
  have hg1 := hg.al; have hg2 := hg.lo; have hg3 := hg.hi
  have h8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  unfold valueTruthyPC
  cases v with
  | null =>
    have hk := ldv_lw_kind (Mt := Mt) hv (by decide)
    ix_run1 hlive using [h10, hk]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; rw [snez_reg]; rfl
  | bool b =>
    have hk := ldv_lw_kind (Mt := Mt) hv.1 (by decide)
    have hb := ldv_lw_kind (Mt := Mt) (a := (p + 8#64).toNat) (k := cond b 1 0) (by rw [h8]; exact hv.2)
      (by cases b <;> decide)
    ix_run1 hlive using [h10, hk, hb]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; cases b <;> rfl
  | int n =>
    have hk := ldv_lw_kind (Mt := Mt) hv.1 (by decide)
    have hn := ldv_ld_imgW Mt (p + 8#64).toNat
    ix_run1 hlive using [h10, hk, hn]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; rw [snez_reg, h8]
    have e := hv.2
    by_cases h0 : imgW (imgM Mt) (p.toNat + 8) = 0#64
    · rw [h0] at e ⊢; subst e; rfl
    · have hn0 : n ≠ 0 := fun hn0 => h0 (by rw [hn0] at e; exact BitVec.eq_of_toInt_eq (by simpa using e))
      simp [Value.truthy, h0, hn0]
  | str x =>
    have hk := ldv_lw_kind (Mt := Mt) hv.1 (by decide)
    ix_run1 hlive using [h10, hk]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; rw [snez_reg]; rfl
  | closure a =>
    have hk := ldv_lw_kind (Mt := Mt) hv.1 (by decide)
    ix_run1 hlive using [h10, hk]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; rw [snez_reg]; rfl
  | native f =>
    have hk := ldv_lw_kind (Mt := Mt) hv.1 (by decide)
    ix_run1 hlive using [h10, hk]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; rw [snez_reg]; rfl

/-- **`value_truthy`**, for either WP. -/
theorem valueTruthy_spec (hlive : ∀ p ∈ interpText, live p.1)
    (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs) (p : BitVec 64) (v : Value) :
    ⊢ valueTruthySpec (vsaModel live) N Wp p v := by
  unfold valueTruthySpec
  refine helper_leaf Wp (InExt (p.toNat, 24)) (fun Mt => valImg N (imgM Mt) p.toNat v)
    (fun rv Mt => SlotGeom p ∧ rv 10 = p ∧
      ValPure N v (imgW (imgM Mt) p.toNat) (imgW (imgM Mt) (p.toNat + 8))
        (imgW (imgM Mt) (p.toNat + 16)))
    (fun Mt rv' mv => (rv' 10 = if v.truthy then 1#64 else 0#64) ∧
      ∀ a, InExt (p.toNat, 24) a → mv a = imgM Mt a)
    (fun rv h => ?_) (fun rv Mt r h hP hal => ?_) (fun Mt rv' mv hg => ?_)
  · iintro ⟨Hv, %hg⟩
    ihave ⟨%Mt, H, #Hw⟩ := valAt_tracked N _ v $$ Hv
    ihave %hpure := valOf_pure N v _ _ _ $$ Hw
    iexists Mt
    iframe H Hw
    ipureintro; exact ⟨hg, h, hpure⟩
  · exact valueTruthy_run hlive N p r rv Mt v hP.1 hP.2.1 hP.2.2 hal
  · iintro ⟨#Hw, HS⟩
    isplitl
    · iapply valAt_of_img
      iframe Hw
      iapply ownSet_congr (fun a ha => by rw [hg.2 a ha]) $$ HS
    · ipureintro; exact hg.1

end

end VsaIris.Interp
