import VsaIris.Interp.ProofStrHeap

/-!
# `strcpy` with the destination above the HTIF words (lane A)

`strcpySpecH`/`strcpyHeapSpecH` are `strcpySpec`/`strcpyHeapSpec` with one
added conjunct in the pure precondition: the destination starts at or above
`htifLo + 16` (VSA's store facts need it, as for `memcpy`). With it the
proofs need no `gapRO` premise.
-/

namespace VsaIris.Interp.StrLeaf

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen VsaIris.Newlib
open VsaIris.VsaHeap VsaIris.Interp
open Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel)

omit I in
/-- `strcpySpec` with `htifLo + 16 ≤ dst`. -/
def strcpySpecH (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (x : String) (n : Nat), fnSpecW Wp strcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ x.toList.length + 1 ≤ n ∧
        htifLo + 16 ≤ dst.toNat⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ clobbered (12 :: argClob) ∗ blockOwn dst.toNat n ∗
      strAt src.toNat x))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      (∃ img, ownImg (InExt (dst.toNat, n)) img ∗ ⌜CStrImg img dst.toNat x⌝))))

/-- `strcpyHeapSpec` with `htifLo + 16 ≤ d`. -/
def strcpyHeapSpecH (Wp : MachWP (GF := GF) M) (d q : BitVec 64) (y : String) (ρ : Regime)
    (H : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp strcpyPC callerSaved (fun rv => rv 10 = d ∧ rv 11 = q)
    iprop(⌜HeapStr H q y ∧ RamWin d.toNat (y.toList.length + 1) ∧ htifLo + 16 ≤ d.toNat⌝ ∗
      blockOwn d.toNat (y.toList.length + 1) ∗ strOwn q.toNat y ∗
      heapRes vsaLayoutP vsaRoomB ρ H)
    (fun _ => iprop((∃ img, ownImg (InExt (d.toNat, y.toList.length + 1)) img ∗
        ⌜CStrImg img d.toNat y⌝) ∗ strOwn q.toNat y ∗ heapRes vsaLayoutP vsaRoomB ρ H))

end Specs

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`strcpy` meets `strcpySpecH`**, for either WP. -/
theorem strcpy_specH (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) :
    binImg (GF := GF) ⊢ strcpySpecH (vsaModel live) Wp := by
  iintro #Himg
  ihave #Hcode := strCode_of_binImg $$ Himg
  unfold strcpySpecH
  imodintro
  iintro %dst %src %x %n
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hal, hram, hn, hdh⟩, Ha0, Ha1, Hcl, Hb, Hs⟩ Hk
  unfold blockOwn
  have hd : tohostAddr + 16 ≤ dst.toNat := by
    have : tohostAddr = htifLo := rfl
    omega
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


variable [I : InterpGS GF]

/-- **`strcpy` of an owned heap string meets `strcpyHeapSpecH`**, for either WP. -/
theorem strcpy_heap_specH (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live))
    (d q : BitVec 64) (y : String) (ρ : Regime) (H : List (Nat × Nat)) :
    binImg (GF := GF) ⊢ strcpyHeapSpecH (vsaModel live) Wp d q y ρ H := by
  iintro #Himg
  ihave #Hcode := strCode_of_binImg $$ Himg
  unfold strcpyHeapSpecH helperSpec
  iintro %rv
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h11⟩, -, %⟨hhs, hram, hdh⟩, Hb, Hs, Hh⟩ Hk
  unfold blockOwn
  have hd : tohostAddr + 16 ≤ d.toNat := by
    have : tohostAddr = htifLo := rfl
    omega
  ihave ⟨Hh, %⟨img0, hshape⟩⟩ := heapRes_shape ρ H $$ Hh
  unfold strOwn
  icases Hs with ⟨%img, Hs, %hstr⟩
  ihave ⟨%g, Hb⟩ := ownSet_fn (InExt (d.toNat, y.toList.length + 1)) $$ Hb
  ihave ⟨%Mt, Hb, %_⟩ := VsaIris.Interp.ownSet_trackedAt _ g $$ Hb
  ihave %hdisj := ownSet_disj (InExt (q.toNat, y.toList.length + 1))
    (InExt (d.toNat, y.toList.length + 1)) img (imgM Mt) $$ [Hs Hb]
  · iframe Hs Hb
  have c : CCtx live d q r y.toList.length img (y.toList.length + 1) :=
    ⟨⟨regions_of_heap hshape hhs, strBytes_of_img hstr, hal, strCode_live hcl⟩, hd, hram.hi,
      Nat.le_refl _⟩
  let mv : Nat → BitVec 8 := fun a =>
    if q.toNat ≤ a ∧ a < q.toNat + (y.toList.length + 1) then img a else imgM Mt a
  have hmvS : ∀ a, InExt (d.toNat, y.toList.length + 1) a → mv a = imgM Mt a := fun a ha => by
    simp only [mv]; rw [if_neg (show ¬ (q.toNat ≤ a ∧ a < q.toNat + (y.toList.length + 1)) from fun h => hdisj a h ha)]
  have hmvT : ∀ a, InExt (q.toNat, y.toList.length + 1) a → mv a = img a := fun a ha => by
    simp only [mv]; rw [if_pos (show q.toNat ≤ a ∧ a < q.toNat + (y.toList.length + 1) from ha)]
  obtain ⟨n, hn⟩ := strcpyRun (Mt := Mt) c (R := entryRv VsaIris.Interp.strcpyPC r (rv 10) (rv 11) rv)
    rfl h10 h11
  have hrun := LocalRun.promote (fun p hp hS => hdisj p.1 (by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (show p ∈ strText q.toNat y.toList.length img from hp)
      have := List.mem_range.mp hk
      exact ⟨by simp, by simp; omega⟩) hS) n _ mv
    (hn _ mv ⟨rfl, fun _ _ _ => rfl, hmvS⟩) (fun p hp => by
      rw [hmvT _ ((strText_iff _ _ img _).1 (.inr ⟨p, hp, rfl⟩)), strText_mem_img p hp])
  ihave ⟨Hl, Ho⟩ := (regFile_split rv).1 $$ Hregs
  ihave ⟨H10, H11, H1216⟩ := fLeaf_split rv $$ Hl
  ihave Hpc := (pc_reg _).1 $$ Hpc
  ihave Hra := (ra_reg _).1 $$ Hra
  ihave Hsr := sRegs_in VsaIris.Interp.strcpyPC r (rv 10) (rv 11) rv $$ [Hpc Hra H10 H11 H1216]
  · iframe Hpc Hra H10 H11 H1216
  ihave Hb := Strlen.ownSet_congr (g := fun a => iprop(a ↦ₘ mv a)) (fun a ha => by
    rw [hmvS a ha]) $$ Hb
  ihave Hs := Strlen.ownSet_congr (g := fun a => iprop(a ↦ₘ mv a)) (fun a ha => by
    rw [hmvT a ha]) $$ Hs
  ihave Hall := ownSet_join _ _ _ (fun a h1 h2 => hdisj a h2 h1) $$ [Hb Hs]
  · iframe Hb Hs
  ihave Hall := ownSet_iff _ (S := fun a => InExt (d.toNat, y.toList.length + 1) a ∨
      InExt (q.toNat, y.toList.length + 1) a)
    (T := fun a => InExt (d.toNat, y.toList.length + 1) a ∨
      ∃ p ∈ strText q.toNat y.toList.length img, p.1 = a)
    (fun a => or_congr_right (Iff.trans (strText_iff q.toNat y.toList.length img a).symm
      ⟨fun h => h.resolve_left id, Or.inr⟩)) $$ Hall
  iapply wp_localRunW Wp n _ mv hrun
  isplitr [Hsr Hall Hk Ho Hh]
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    iexact Hcode
  iframe Hsr Hall
  unfold runKontW
  iintro %rv' %mv' %⟨⟨h32, h1, h10', hcp⟩, hT⟩ Hsr HS
  ihave ⟨Hpc, Hra, Ha0, Ht⟩ := sRegs_out rv' $$ Hsr
  ihave Hf := regFile_after rv rv' $$ [Ha0 Ht Ho]
  · iframe Ha0 Ht Ho
  ihave Hpc := reg_eq h32 $$ Hpc
  ihave Hra := reg_eq h1 $$ Hra
  ihave Hpc := (pc_reg _).2 $$ Hpc
  ihave Hra := (ra_reg _).2 $$ Hra
  ihave ⟨HD, HQ⟩ := ownSet_split _ (InExt (d.toNat, y.toList.length + 1)) _ $$ HS
  ihave HD := ownSet_iff _ (T := InExt (d.toNat, y.toList.length + 1))
    (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ HD
  ihave HQ := ownSet_iff _ (T := InExt (q.toNat, y.toList.length + 1))
    (fun a => ⟨fun h => by
      rcases h.1 with h1 | h1
      · exact absurd h1 h.2
      · exact (strText_iff _ _ img a).1 (.inr h1),
      fun h => ⟨.inr (((strText_iff _ _ img a).2 h).resolve_left id), fun h' => hdisj a h h'⟩⟩) $$ HQ
  ihave HQ := Strlen.ownSet_congr (g := fun a => iprop(a ↦ₘ img a)) (fun a ha => by
    rw [hT _ (strText_of_ext ha)]) $$ HQ
  iapply Hk $$ Hpc Hra
  iexists leafRv rv rv'
  iframe Hf
  isplitr
  · ipureintro; exact leafRv_keep rv rv'
  simp only []
  iframe Hh
  isplitl [HD]
  · iexists mv'
    iframe HD
    ipureintro
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hcp i (by omega)]; exact hstr.1 i hi
    · rw [hcp _ (Nat.le_refl _)]; exact hstr.2
  iexists img
  iframe HQ
  ipureintro; exact hstr


end

end VsaIris.Interp.StrLeaf

#print axioms VsaIris.Interp.StrLeaf.strcpy_specH
#print axioms VsaIris.Interp.StrLeaf.strcpy_heap_specH
