import VsaIris.Interp.ProofStrlen
import VsaIris.Interp.ProofStrcpy
import VsaIris.Interp.SpecConcat

/-!
# `strlen` and `strcpy` of a string the caller owns in a live heap block (lane A)

`strlenHeapSpec`/`strcpyHeapSpec` (`SpecConcat.lean`): the string lies in a
live heap block `(q, len + 1)` the caller owns (`strOwn`), and the caller
lends `heapRes`. The word loops read up to seven bytes past the NUL, in the
allocator's footprint (the chunk's tail or the next chunk's header).

Those bytes are NOT lent out of `heapRes`: the runs load them with
`sr_havoc` (`StrRun.lean`), which needs no ownership of them, only their RAM
geometry. `heapRes` is used for exactly that geometry, read off its pure
shape (`live_window`: `HeapAt.live` puts a live extent inside an in-use
chunk's usable payload, the chunk walk ends at `top`, and `top + 16 ≤ brk ≤
heapEnd`), and is handed back untouched. The string's owned bytes enter the
run as its data view and are promoted back to owned bytes
(`LocalRun.promote`, `StrlenOwned.lean`).
-/

namespace VsaIris.Interp.StrLeaf

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen VsaIris.Newlib
open VsaIris.VsaHeap
open Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr

/-! ## The window of a live block -/

/-- **A live block's eight-byte over-read window is in the arena.** A live
extent lies in an in-use chunk's usable payload, which ends at most eight
bytes into the next chunk; the walk ends at `top`, whose header takes 16
bytes below the break. -/
theorem live_window {img : Nat → BitVec 8} {H : List (Nat × Nat)} {q n : Nat}
    (hs : pShape img H) (hm : (q, n) ∈ H) : heapStart + 16 ≤ q ∧ q + n + 8 ≤ heapEnd := by
  obtain ⟨_, m, top, brkv, chunks, bins, _, hp⟩ := hs
  have hh := hp.heap.heap
  obtain ⟨c, hc, _, hlo, hhi⟩ := hh.live (q, n) hm
  obtain ⟨hc1, hc2, _⟩ := hh.walk.chunk_bounds c hc
  have := hp.heap.top_room
  have := hh.brk_le
  simp only at hlo hhi
  exact ⟨by omega, by omega⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
/-- The heap resource's pure shape, the resource kept. -/
theorem heapRes_shape (ρ : Regime) (H : List (Nat × Nat)) :
    heapRes (GF := GF) vsaLayoutP vsaRoomB ρ H ⊢
      heapRes vsaLayoutP vsaRoomB ρ H ∗ ⌜∃ img, pShape img H⌝ := by
  cases ρ with
  | counted k =>
    unfold heapRes isHeapRoom
    iintro ⟨%img, %⟨hs, hr⟩, HF⟩
    isplitl [HF]
    · iexists img; iframe HF; ipureintro; exact ⟨hs, hr⟩
    · ipureintro; exact ⟨img, hs⟩
  | uncounted =>
    unfold heapRes isHeap
    iintro ⟨%img, %hs, HF⟩
    isplitl [HF]
    · iexists img; iframe HF; ipureintro; exact hs
    · ipureintro; exact ⟨img, hs⟩

/-- A heap string's read geometry. -/
theorem regions_of_heap {img : Nat → BitVec 8} {H : List (Nat × Nat)} {q : BitVec 64} {x : String}
    (hs : pShape img H) (hh : HeapStr H q x) : ReadRegions q x.toList.length := by
  obtain ⟨h1, h2⟩ := live_window hs hh.live
  have e1 : heapStart = 0x8001c170 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  have e3 : tohostAddr = 0x8001ad00 := rfl
  exact ⟨by omega, by omega, by omega, by right; omega⟩

theorem strText_iff (p n : Nat) (img : Nat → BitVec 8) (a : Nat) :
    (False ∨ ∃ q ∈ strText p n img, q.1 = a) ↔ InExt (p, n + 1) a := by
  unfold strText InExt
  constructor
  · rintro (h | ⟨q, hq, rfl⟩)
    · exact h.elim
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
      have := List.mem_range.mp hk
      simp only; omega
  · intro h
    refine .inr ⟨(a, img a), List.mem_map.mpr ⟨a - p, List.mem_range.mpr (by simp at h; omega), ?_⟩, rfl⟩
    simp only at h
    rw [show p + (a - p) = a by omega]

/-! ## Registers of a helper spec -/

abbrev fLeaf : List Nat := [10, 11, 12, 13, 14, 15, 16]
abbrev fOther : List Nat :=
  [2, 5, 6, 7, 8, 9, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

theorem fRegs_perm : fRegs.Perm (fLeaf ++ fOther) := by decide

omit I in
theorem regFile_split (rv : Nat → BitVec 64) :
    regFile (GF := GF) rv ⊣⊢ sepL fLeaf (fun k => k ↦ᵣ rv k) ∗ sepL fOther (fun k => k ↦ᵣ rv k) := by
  unfold regFile
  exact (sepL_perm _ fRegs_perm).trans (sepL_append _ _ _)

/-- The body's registers after a leaf run: the leaf's from the run, the
others kept. -/
def leafRv (rv rv' : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k ∈ fLeaf then rv' k else rv k

omit I in
theorem regFile_after (rv rv' : Nat → BitVec 64) :
    (10 : Nat) ↦ᵣ rv' 10 ∗ sepL leafTemps (fun k => k ↦ᵣ rv' k) ∗
      sepL fOther (fun k => k ↦ᵣ rv k) ⊢@{IProp GF} regFile (leafRv rv rv') := by
  refine .trans ?_ (regFile_split _).2
  simp only [sepL_cons, sepL_nil, leafRv, leafTemps, fOther, fLeaf, List.mem_cons,
    List.not_mem_nil, or_false, ↓reduceIte, Nat.reduceEqDiff, or_self, or_true]
  iintro ⟨H10, ⟨H11, H12, H13, H14, H15, H16, -⟩, ⟨H2, H5, H6, H7, H8, H9, H17, H18, H19, H20, H21,
    H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, -⟩⟩
  iframe H10 H11 H12 H13 H14 H15 H16 H2 H5 H6 H7 H8 H9 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26
    H27 H28 H29 H30 H31

omit I in
theorem fLeaf_split (rv : Nat → BitVec 64) :
    sepL fLeaf (fun k => k ↦ᵣ rv k) ⊢@{IProp GF}
      (10 : Nat) ↦ᵣ rv 10 ∗ (11 : Nat) ↦ᵣ rv 11 ∗ sepL [12, 13, 14, 15, 16] (fun k => k ↦ᵣ rv k) := by
  simp only [fLeaf, sepL_cons]
  iintro ⟨H10, H11, H⟩
  iframe H10 H11 H

theorem leafRv_keep (rv rv' : Nat → BitVec 64) :
    ∀ x ∈ fRegs, x ∉ callerSaved → leafRv rv rv' x = rv x := by
  intro x _ hx
  unfold leafRv
  rw [ite_eq_right_iff.2 (fun h => absurd h ?_)]
  intro hm
  exact hx (by revert hm; revert x; decide)

theorem strText_mem_img {p n : Nat} {img : Nat → BitVec 8} :
    ∀ q ∈ strText p n img, img q.1 = q.2 := by
  intro q hq
  unfold strText at hq
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
  rfl

theorem strText_of_ext {p n : Nat} {img : Nat → BitVec 8} {a : Nat} (h : InExt (p, n + 1) a) :
    (a, img a) ∈ strText p n img := by
  obtain ⟨q, hq, e⟩ := ((strText_iff p n img a).2 h).resolve_left id
  have := strText_mem_img q hq
  have hq' : (q.1, q.2) ∈ strText p n img := hq
  rw [← this] at hq'
  rw [← e]
  exact hq'

/-! ## `strlen` of an owned heap string -/

/-- **`strlen` of a string the caller owns in a live heap block**, for
either WP. The over-read bytes are loaded unowned (`sr_havoc`); `heapRes`
supplies their geometry and is handed back untouched. -/
theorem strlen_heap_spec (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (q : BitVec 64) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) :
    binImg (GF := GF) ⊢ strlenHeapSpec (vsaModel live) Wp q x ρ H := by
  iintro #Himg
  ihave #Hcode := strCode_of_binImg $$ Himg
  unfold strlenHeapSpec helperSpec
  iintro %rv
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Hregs, %h10, -, %hhs, Hs, Hh⟩ Hk
  ihave ⟨Hh, %⟨img0, hshape⟩⟩ := heapRes_shape ρ H $$ Hh
  unfold strOwn
  icases Hs with ⟨%img, Hb, %hstr⟩
  have c : LCtx live q r x.toList.length img :=
    ⟨regions_of_heap hshape hhs, strBytes_of_img hstr, hal, strCode_live hcl⟩
  obtain ⟨n, hn⟩ := strlenRunL (S := fun _ => False) (Mt := ∅) c
    (R := entryRv strlenPC r (rv 10) (rv 11) rv) rfl h10
  have hrun := LocalRun.promote (fun _ _ h => h) n _ img
    (hn _ img ⟨rfl, fun _ _ _ => rfl, fun _ h => h.elim⟩) strText_mem_img
  ihave ⟨Hl, Ho⟩ := (regFile_split rv).1 $$ Hregs
  ihave ⟨H10, H11, H1216⟩ := fLeaf_split rv $$ Hl
  ihave Hpc := (pc_reg _).1 $$ Hpc
  ihave Hra := (ra_reg _).1 $$ Hra
  ihave Hsr := sRegs_in strlenPC r (rv 10) (rv 11) rv $$ [Hpc Hra H10 H11 H1216]
  · iframe Hpc Hra H10 H11 H1216
  ihave Hb := ownSet_iff _ (fun a => (strText_iff q.toNat x.toList.length img a).symm) $$ Hb
  iapply wp_localRunW Wp n _ img hrun
  isplitr [Hsr Hb Hk Ho Hh]
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    iexact Hcode
  iframe Hsr Hb
  unfold runKontW
  iintro %rv' %mv' %⟨⟨h32, h1, h10'⟩, hT⟩ Hsr HS
  ihave ⟨Hpc, Hra, Ha0, Ht⟩ := sRegs_out rv' $$ Hsr
  ihave Hf := regFile_after rv rv' $$ [Ha0 Ht Ho]
  · iframe Ha0 Ht Ho
  ihave Hpc := reg_eq h32 $$ Hpc
  ihave Hra := reg_eq h1 $$ Hra
  ihave Hpc := (pc_reg _).2 $$ Hpc
  ihave Hra := (ra_reg _).2 $$ Hra
  ihave HS := ownSet_iff _ (fun a => strText_iff q.toNat x.toList.length img a) $$ HS
  ihave HS := Strlen.ownSet_congr (g := fun a => iprop(a ↦ₘ img a)) (fun a ha => by
    rw [hT _ (strText_of_ext ha)]) $$ HS
  iapply Hk $$ Hpc Hra
  iexists leafRv rv rv'
  iframe Hf
  isplitr
  · ipureintro; exact leafRv_keep rv rv'
  isplitr
  · ipureintro
    show (if 10 ∈ fLeaf then rv' 10 else rv 10) = _
    rw [ite_eq_left_iff.2 (fun h => absurd (by decide) h), h10']; rfl
  iframe Hh
  iexists img
  iframe HS
  ipureintro; exact hstr

/-! ## `strcpy` of an owned heap string -/

/-- **`strcpy` of a string the caller owns in a live heap block** into an
owned buffer, for either WP (`hgap`: `ProofStrcpy.lean`). -/
theorem strcpy_heap_spec (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (hgap : binImg (GF := GF) ⊢ gapRO)
    (d q : BitVec 64) (y : String) (ρ : Regime) (H : List (Nat × Nat)) :
    binImg (GF := GF) ⊢ strcpyHeapSpec (vsaModel live) Wp d q y ρ H := by
  iintro #Himg
  ihave #Hcode := strCode_of_binImg $$ Himg
  ihave #Hlow := low_ro hgap $$ Himg
  unfold strcpyHeapSpec helperSpec
  iintro %rv
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h11⟩, -, %⟨hhs, hram⟩, Hb, Hs, Hh⟩ Hk
  unfold blockOwn
  by_cases hd : tohostAddr + 16 ≤ d.toNat
  rotate_left
  · have hlo := hram.lo; have hh := hram.htif
    have e3 : tohostAddr = VsaIris.Interp.htifLo := rfl
    have hlt : d.toNat < 0x8001ad00 := by
      unfold VsaIris.Interp.htifLo at *; rcases hh with hh | hh <;> omega
    ihave ⟨%w, #Hw⟩ := Hlow $$ %d.toNat %⟨hlo, hlt⟩
    ihave %hno := ro_off d.toNat w (InExt (d.toNat, y.toList.length + 1)) $$ Hw Hb
    exact absurd ⟨Nat.le_refl _, by simp⟩ hno
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

end VsaIris.Interp.StrLeaf

#print axioms VsaIris.Interp.StrLeaf.strlen_spec_env
#print axioms VsaIris.Interp.StrLeaf.strcpy_spec
#print axioms VsaIris.Interp.StrLeaf.strlen_heap_spec
#print axioms VsaIris.Interp.StrLeaf.strcpy_heap_spec
