import VsaIris.Interp.StrcpyRun
import VsaIris.Interp.StrIris
import VsaIris.Interp.HelperRun
import VsaIris.Interp.SpecStringify

/-!
# `strcpy` in the Iris logic (lane A)

`strcpy_spec`: newlib's `strcpy` (`0x80006dc4`) meets `strcpySpec`
(`SpecStringify.lean`) for every `live` holding the binary's code. The run is
`StrcpyRun.strcpyRun`; the source's over-read bytes are loaded unowned
(`sr_havoc`).

**Named premise `hgap`.** VSA's store facts (`BlockMem.MemFacts`, `.sb`/`.sd`)
require the stored address at or above `tohostAddr + 16`; `strcpySpec`'s
`RamWin dst n` also admits a buffer below the HTIF words. Below `0x8001acf0`
the binary's `.text`/`.rodata` are read-only in `binImg`, so an owned buffer
there is contradictory (`ro_off`); the 16 bytes `[0x8001acf0, 0x8001ad00)`
between `.rodata` and `tohost` are in no resource `binImg` names. `hgap`
states they are read-only too (`gapRO`). Supplier: the boundary, which owns
them read-only (`World.CodeByte`, `roOn CodeByte`); `binImg` would need its
`.rodata` window widened to `0x8001ad00`.
-/

namespace VsaIris.Interp.StrLeaf

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen VsaIris.Newlib
open Vsa.Sim Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The 16 bytes between `.rodata` and `tohost` are read-only. -/
def gapRO : IProp GF :=
  iprop(□ ∀ a : Nat, ⌜0x8001acf0 ≤ a ∧ a < 0x8001ad00⌝ → ∃ v : BitVec 8, a ↦ₘ□ v)

instance : Persistent (gapRO (GF := GF)) := by unfold gapRO; infer_instance

/-- Every byte below the HTIF words is read-only. -/
theorem low_ro (hgap : binImg (GF := GF) ⊢ gapRO) :
    binImg (GF := GF) ⊢ □ ∀ a : Nat, ⌜0x80000000 ≤ a ∧ a < 0x8001ad00⌝ → ∃ v : BitVec 8, a ↦ₘ□ v := by
  iintro #H
  ihave #Hg := hgap $$ H
  unfold binImg
  icases H with ⟨#Ht, #Hr⟩
  imodintro
  iintro %a %ha
  by_cases h1 : a < 0x80018be0
  · iexists textByte a
    unfold VsaIris.Interp.roImg
    iapply Ht $$ %a %⟨ha.1, h1⟩
  · by_cases h2 : a < 0x8001acf0
    · iexists rodataByte a
      unfold VsaIris.Interp.roImg
      iapply Hr $$ %a %⟨by omega, h2⟩
    · unfold gapRO
      iapply Hg $$ %a %⟨by omega, ha.2⟩

/-- A read-only byte is in no owned set. -/
theorem ro_off (a : Nat) (w : BitVec 8) (S : Nat → Prop) :
    (a ↦ₘ□ w) ⊢@{IProp GF} ownSet S byteAny -∗ ⌜¬ S a⌝ := by
  unfold ownSet
  iintro #Ha ⟨%l, %⟨_, hmem⟩, Hl⟩
  suffices h : ∀ l : List Nat, (a ↦ₘ□ w) ⊢@{IProp GF} sepL l byteAny -∗ ⌜a ∉ l⌝ by
    ihave %hn := h l $$ Ha Hl
    ipureintro
    exact fun hs => hn ((hmem a).2 hs)
  intro l
  induction l with
  | nil => iintro _ _; ipureintro; exact List.not_mem_nil
  | cons x xs ih =>
    rw [sepL_cons]
    iintro #Ha ⟨⟨%b, Hx⟩, Hxs⟩
    ihave %hx := VsaIris.Interp.memRO_excl_ne a x w b $$ [Ha Hx]
    · iframe Ha Hx
    ihave %hxs := ih $$ Ha Hxs
    ipureintro
    simp [List.mem_cons, hx, hxs]

theorem argClob_perm' : (12 :: VsaIris.Interp.argClob).Perm ([12, 13, 14, 15, 16] ++ retRest) := by
  decide

/-- **`strcpy` meets `strcpySpec`**, for either WP (`hgap`: the module doc). -/
theorem strcpy_spec (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (hgap : binImg (GF := GF) ⊢ gapRO) :
    binImg (GF := GF) ⊢ VsaIris.Interp.strcpySpec (vsaModel live) Wp := by
  iintro #Himg
  ihave #Hcode := strCode_of_binImg $$ Himg
  ihave #Hlow := low_ro hgap $$ Himg
  unfold VsaIris.Interp.strcpySpec
  imodintro
  iintro %dst %src %x %n
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hal, hram, hn⟩, Ha0, Ha1, Hcl, Hb, Hs⟩ Hk
  unfold blockOwn
  by_cases hd : tohostAddr + 16 ≤ dst.toNat
  rotate_left
  · -- a buffer below the HTIF words would overlap read-only bytes
    have hlo := hram.lo; have hh := hram.htif
    have e3 : tohostAddr = VsaIris.Interp.htifLo := rfl
    have hlt : dst.toNat < 0x8001ad00 := by
      unfold VsaIris.Interp.htifLo at *; rcases hh with hh | hh <;> omega
    ihave ⟨%w, #Hw⟩ := Hlow $$ %dst.toNat %⟨hlo, hlt⟩
    ihave %hno := ro_off dst.toNat w (InExt (dst.toNat, n)) $$ Hw Hb
    exact absurd ⟨Nat.le_refl _, by simp; omega⟩ hno
  unfold VsaIris.Interp.strAt
  icases Hs with ⟨%img, %⟨hstr, hwin⟩, #Hro⟩
  ihave #Hdat := roImg_strText src.toNat x.toList.length img $$ Hro
  ihave ⟨Ht, Hrest⟩ := (clobbered_split argClob_perm').1 $$ Hcl
  ihave ⟨%f, Ht⟩ := clobbered_fn [12, 13, 14, 15, 16] (by decide) $$ Ht
  ihave ⟨%g, Hb⟩ := ownSet_fn (InExt (dst.toNat, n)) $$ Hb
  ihave ⟨%Mt, Hb, %_⟩ := VsaIris.Interp.ownSet_trackedAt _ g $$ Hb
  have c : CCtx live dst src r x.toList.length img n :=
    ⟨⟨regions_of_win hwin, strBytes_of_img hstr, hal, strCode_live hcl⟩, hd, hram.hi, hn⟩
  have hrun := strcpyRun (Mt := Mt) c (R := entryRv VsaIris.Interp.strcpyPC r dst src f) rfl rfl rfl
  ihave Hpc := (pc_reg _).1 $$ Hpc
  ihave Hra := (ra_reg _).1 $$ Hra
  ihave Hregs := sRegs_in VsaIris.Interp.strcpyPC r dst src f $$ [Hpc Hra Ha0 Ha1 Ht]
  · iframe Hpc Hra Ha0 Ha1 Ht
  iapply wp_sw Wp hrun _ rfl (fun _ _ _ => rfl)
  isplitr [Hregs Hb Hk Hrest]
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    iapply (sepL_append _ _ _).2
    iframe Hcode Hdat
  iframe Hregs Hb
  unfold runKontW
  iintro %rv' %mv' %⟨h32, h1, h10, hcp⟩ Hregs HB
  ihave ⟨Hpc, Hra, Ha0, Ht⟩ := sRegs_out rv' $$ Hregs
  ihave Ht := clobbered_of_fn leafTemps rv' $$ Ht
  ihave Hcl := (clobbered_split retClob_perm).2 $$ [Ht Hrest]
  · iframe Ht Hrest
  ihave Hpc := reg_eq h32 $$ Hpc
  ihave Hra := reg_eq h1 $$ Hra
  ihave Ha0 := reg_eq h10 $$ Ha0
  ihave Hpc := (pc_reg _).2 $$ Hpc
  ihave Hra := (ra_reg _).2 $$ Hra
  iapply Hk $$ Hpc Hra
  simp only []
  iframe Ha0 Hcl
  iexists mv'
  iframe HB
  ipureintro
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hcp i (by omega)]; exact hstr.1 i hi
  · rw [hcp _ (Nat.le_refl _)]; exact hstr.2

end

end VsaIris.Interp.StrLeaf
