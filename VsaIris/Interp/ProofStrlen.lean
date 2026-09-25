import VsaIris.Interp.StrlenRun
import VsaIris.Interp.StrIris

/-!
# `strlen` in the Iris logic (lane A)

`strlen_spec_env`: newlib's `strlen` meets `strlenSpec` (`SpecEnv.lean`) for
every `live` holding the binary's code. The string is `strAt`: persistent
bytes up to the NUL and the RAM geometry `StrWin` of its eight-byte
over-read window. The run is `StrlenRun.strlenRunL`: the word loop's loads
of the bytes past the NUL are `sr_havoc` loads, which need neither ownership
nor liveness of those bytes.
-/

namespace VsaIris.Interp.StrLeaf

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen VsaIris.Newlib
open Vsa.Sim Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`strlen` meets `strlenSpec`**, for either WP. -/
theorem strlen_spec_env (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) :
    binImg (GF := GF) ⊢ strlenSpec Wp := by
  iintro #Himg
  ihave #Hcode := strCode_of_binImg $$ Himg
  unfold strlenSpec
  imodintro
  iintro %p %x
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Ha0, Hcl, Hs⟩ Hk
  unfold VsaIris.Interp.strAt
  icases Hs with ⟨%img, %⟨hstr, hwin⟩, #Hro⟩
  ihave #Hdat := roImg_strText p.toNat x.toList.length img $$ Hro
  ihave ⟨Ht, Hrest⟩ := (clobbered_split retClob_perm).1 $$ Hcl
  ihave ⟨%f, Ht⟩ := clobbered_fn leafTemps (by decide) $$ Ht
  have c : LCtx live p r x.toList.length img :=
    ⟨regions_of_win hwin, strBytes_of_img hstr, hal, strCode_live hcl⟩
  have hrun := strlenRunL (S := fun _ => False) (Mt := ∅) c
    (R := entryRv strlenPC r p (f 11) f) rfl rfl
  ihave Hpc := (pc_reg _).1 $$ Hpc
  ihave Hra := (ra_reg _).1 $$ Hra
  simp only [leafTemps, sepL_cons, sepL_nil]
  icases Ht with ⟨H11, H12, H13, H14, H15, H16, -⟩
  ihave Hregs := sRegs_in strlenPC r p (f 11) f $$ [Hpc Hra Ha0 H11 H12 H13 H14 H15 H16]
  · simp only [sepL_cons, sepL_nil]
    iframe Hpc Hra Ha0 H11 H12 H13 H14 H15 H16
  ihave Hnone := ownSet_none (GF := GF) (fun a => iprop(a ↦ₘ imgM ∅ a))
  iapply wp_sw Wp hrun _ rfl (fun _ _ _ => rfl)
  isplitr [Hregs Hnone Hk Hrest]
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    iapply (sepL_append _ _ _).2
    iframe Hcode Hdat
  iframe Hregs Hnone
  unfold runKontW
  iintro %rv' %mv' %⟨h32, h1, h10⟩ Hregs -
  ihave ⟨Hpc, Hra, Ha0, Ht⟩ := sRegs_out rv' $$ Hregs
  ihave Ht := clobbered_of_fn leafTemps rv' $$ Ht
  ihave Hcl := (clobbered_split retClob_perm).2 $$ [Ht Hrest]
  · iframe Ht Hrest
  ihave Hpc := reg_eq h32 $$ Hpc
  ihave Hra := reg_eq h1 $$ Hra
  ihave Ha0 := reg_eq (b := BitVec.ofNat 64 x.length) (h10.trans rfl) $$ Ha0
  ihave Hpc := (pc_reg _).2 $$ Hpc
  ihave Hra := (ra_reg _).2 $$ Hra
  iapply Hk $$ Hpc Hra
  iframe Ha0 Hcl

end

end VsaIris.Interp.StrLeaf
