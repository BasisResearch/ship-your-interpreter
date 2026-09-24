import VsaIris.Interp.HelperRun
import VsaIris.Interp.SpecErr
import VsaIris.Interp.BinArm

/-!
# `value_kind_name` (lane E2)

One symbolic run over the value's slot (read only): the kind word indexes
`CSWTCH.18` (`0x80019f28`), a `.rodata` table of name pointers. The model is
H2's `value_truthy` (`ProofValueTruthy.lean`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The run of `value_kind_name`, per kind. -/
theorem valueKindName_run (hlive : ∀ p ∈ interpText, live p.1) (p r : BitVec 64)
    (rv : Nat → BitVec 64) (Mt : Mem) (v : Value) (hg : SlotGeom p) (h10 : rv 10 = p)
    (hv : (imgW (imgM Mt) p.toNat).toNat % 2 ^ 32 = valTag v) (hal : r.toNat % 4 = 0) :
    IW live ∅ [] (InExt (p.toNat, 24))
      (HelperEnd r rv [10, 14, 15] (fun rv' mv => rv' 10 = kindNamePtr v ∧
        ∀ a, InExt (p.toNat, 24) a → mv a = imgM Mt a))
      valueKindNamePC (upd rv 1 r) Mt := by
  have hg1 := hg.al; have hg2 := hg.lo; have hg3 := hg.hi
  unfold valueKindNamePC
  cases v <;>
  · have hk := ldv_lw_kind (Mt := Mt) hv (by simp [valTag])
    simp only [valTag] at hk
    ix_run1 hlive using [h10, hk]
    refine swp_helperEnd (by ix_reg) (by helper_keep) (fun rv' mv hR hmv => ⟨?_, hmv⟩)
    rw [hR 10 (by decide)]; ix_reg; rfl

/-- **`value_kind_name`**, for either WP. -/
theorem valueKindName_spec (hlive : ∀ p ∈ interpText, live p.1)
    (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs) (p : BitVec 64) (Mt : Mem)
    (v : Value) : ⊢ valueKindNameSpec (vsaModel live) Wp p Mt v := by
  unfold valueKindNameSpec
  refine helper_leaf Wp (InExt (p.toNat, 24)) (fun _ => iprop(emp))
    (fun rv Mt' => Mt' = Mt ∧ SlotGeom p ∧ rv 10 = p ∧
      (imgW (imgM Mt) p.toNat).toNat % 2 ^ 32 = valTag v)
    (fun _ rv' mv => rv' 10 = kindNamePtr v ∧ ∀ a, InExt (p.toNat, 24) a → mv a = imgM Mt a)
    (fun rv h => ?_) (fun rv Mt' r h hP hal => ?_) (fun Mt' rv' mv hg => ?_)
  · iintro ⟨HS, %hg⟩
    iexists Mt
    iframe HS
    ipureintro; exact ⟨trivial, rfl, hg.1, h, hg.2⟩
  · obtain ⟨rfl, hg, h10, hv⟩ := hP
    exact valueKindName_run hlive p r rv Mt' v hg h10 hv hal
  · iintro ⟨-, HS⟩
    isplitl
    · iapply ownSet_congr (fun a ha => by rw [hg.2 a ha]) $$ HS
    · ipureintro; exact hg.1

end

end VsaIris.Interp
