import VsaIris.Vsa.StrcmpRun
import VsaIris.Interp.SpecEnv
import VsaIris.Interp.SpecErr
import VsaIris.Interp.CallRegs

/-!
# `strcmp` in Iris, for either WP

INTERP_DESIGN.md §9 (H3's `strcmp`). The whole function is one bounded run
(`Strcmp.strcmpRun`, `VsaIris/Vsa/StrcmpRun.lean`), so the Iris layer is ONE
`wp_localRunW` application (xv6iris `ProofMemset.v:1-9`, "bounded loop, not
iLöb"), stated for an abstract `Wp : MachWP` and so serving both WPs.

Ownership: the code, the `.rodata` mask and the two strings' bytes (the
characters and the NUL, `strAt`) are persistent; the run owns only the ten
registers it touches. The at most seven bytes past each NUL that the aligned
word loop loads are NOT owned: `strAt`'s window (`StrWin`) makes them RAM off
the HTIF words, and the run reads them at whatever the machine holds
(`Strcmp.cmpStep`). Their values change no result: branch outcomes that depend
on them are case splits of the run.

* `strcmp_core`: the run in continuation form, from a register valuation.
* `strcmp_spec_env`: `strcmpSpec` (`SpecEnv.lean`, `fnSpecW`, `a0 = 0 ↔ x = y`).
* `strcmp_spec_ord`: `strcmpOrdSpec` (`SpecErr.lean`, the sign class `StrcmpSign`).
* `strcmp_spec_v`: `strcmpSpecV` (`SpecValue.lean`), from `strcmp_spec_ord`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.Sim
open VsaIris.Inst.Strcmp
open VsaIris.Inst.Strlen (codeText instrAt_text sepL_mono_mem)

/-! ## The sign class from the byte-lexicographic sign -/

theorem allNonzero_of_cstr {img : Nat → BitVec 8} {a : Nat} {s : String}
    (h : CStrImg img a s) : AllNonzero s.toList := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  exact (h.1 i hi).2.1

/-- **`strcmp`'s sign class** from the byte-lexicographic sign of two strings
without interior NULs. -/
theorem strcmpSign_class {res : BitVec 64} {x y : String} (hx : AllNonzero x.toList)
    (hy : AllNonzero y.toList) (h : strcmpSign res = strcmpSpecSign x.toList y.toList) :
    StrcmpSign res x y := by
  have hr := strcmpSpecSign_range x.toList y.toList
  have hneg : strcmpSpecSign x.toList y.toList < 0 ↔ x < y :=
    strcmpSpecSign_neg_iff_lex _ _ hx hy
  have hpos : 0 < strcmpSpecSign x.toList y.toList ↔ y < x :=
    strcmpSpecSign_pos_iff_lex _ _ hx hy
  have hxy : x = y ↔ strcmpSpecSign x.toList y.toList = 0 := by
    constructor
    · intro e; subst e; exact strcmpSpecSign_self_zero _ hx
    · intro e; exact String.toList_inj.mp (eq_of_strcmpSpecSign_zero_ascii _ _ hx hy e)
  have hti : res.toInt = 0 ↔ res = 0 := by
    constructor
    · intro e; exact BitVec.eq_of_toInt_eq (by rw [e]; rfl)
    · intro e; rw [e]; rfl
  unfold strcmpSign at h
  by_cases h0 : res = 0
  · rw [ite_eq_left h0] at h
    have := hti.2 h0
    refine ⟨?_, ?_, ?_⟩
    · rw [hxy]; exact ⟨fun _ => h.symm, fun _ => h0⟩
    · rw [← hneg]; omega
    · rw [← hpos]; omega
  · rw [ite_eq_right h0] at h
    have hne := mt hti.1 h0
    by_cases h1 : res.toInt < 0
    · rw [ite_eq_left h1] at h
      refine ⟨?_, ?_, ?_⟩
      · rw [hxy]; exact ⟨fun e => absurd e h0, fun e => by omega⟩
      · rw [← hneg]; omega
      · rw [← hpos]; omega
    · rw [ite_eq_right h1] at h
      refine ⟨?_, ?_, ?_⟩
      · rw [hxy]; exact ⟨fun e => absurd e h0, fun e => by omega⟩
      · rw [← hneg]; omega
      · rw [← hpos]; omega

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-! ## The read cells -/

/-- `strcmp`'s code is the image's. -/
theorem strcmpCode_text : TextAt cmpBase strcmpCode := by decide +kernel

theorem maskText_rodata : ∀ t ∈ maskText, rodataDom t.1 ∧ rodataByte t.1 = t.2 := by decide

omit I in
/-- Read-only bytes of a view as a list of persistent cells. -/
theorem roImg_strList (S : Nat → Prop) (img : Nat → BitVec 8) :
    ∀ l : List (Nat × BitVec 8), (∀ t ∈ l, S t.1 ∧ img t.1 = t.2) →
      roImg (GF := GF) S img ⊢ sepL l (fun t => t.1 ↦ₘ□ t.2)
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | t :: l, h => by
    simp only [sepL_cons]
    iintro #H
    isplitl
    · obtain ⟨hs, he⟩ := h t List.mem_cons_self
      unfold roImg
      rw [← he]
      iapply H $$ %t.1 %hs
    · iapply roImg_strList S img l (fun u hu => h u (List.mem_cons_of_mem _ hu)) $$ H

omit I in
theorem roImg_strT (p len : Nat) (img : Nat → BitVec 8) :
    roImg (GF := GF) (InExt (p, len + 1)) img ⊢ sepL (strT p len img) (fun t => t.1 ↦ₘ□ t.2) :=
  roImg_strList _ _ _ fun t ht => by
    unfold strT at ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    have := List.mem_range.mp hk
    exact ⟨⟨by simp, by simp; omega⟩, rfl⟩

/-- The side conditions of a run, from the two strings' facts. -/
theorem strcmpCtx {live : Nat → Prop} (hcl : CodeLive live) {p q r : BitVec 64} {x y : String}
    {ix iy : Nat → BitVec 8} (hx : CStrImg ix p.toNat x ∧ StrWin p.toNat x.toList.length)
    (hy : CStrImg iy q.toNat y ∧ StrWin q.toNat y.toList.length) (hal : r.toNat % 4 = 0) :
    Ctx live p q r x.toList y.toList ix iy := by
  have sb : ∀ {img : Nat → BitVec 8} {a : Nat} {s : String}, CStrImg img a s →
      SBytes img a s.toList := fun {img a s} h => by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rcases Nat.lt_or_ge k s.toList.length with h1 | h1
      · obtain ⟨e, _, hlt⟩ := h.1 k h1
        rw [e]
        unfold byteVal
        rw [List.getElem?_eq_getElem h1]
        simp only [BitVec.toNat_ofNat]
        omega
      · have : k = s.toList.length := by omega
        subst this
        rw [h.2]
        unfold byteVal; simp
    · obtain ⟨_, h0, hlt⟩ := h.1 k hk
      unfold byteVal
      rw [List.getElem?_eq_getElem hk]
      exact ⟨h0, hlt⟩
  have sw : ∀ {a len : Nat}, StrWin a len → SWin a len := fun {a len} h =>
    ⟨h.lo, h.hi, by
      rcases h.htif with h1 | h1
      · exact .inl h1
      · exact .inr (by unfold htifLo at h1; rw [show tohostAddr = 0x8001ad00 from rfl]; omega)⟩
  refine ⟨fun t ht => ?_, sb hx.1, sb hy.1, sw hx.2, sw hy.2, hal⟩
  unfold codeText at ht
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ht
  exact hcl _ (strcmpCode_text z hz).1

/-! ## The run in Iris -/

/-- The nine GPRs besides `ra` the run touches. -/
abbrev cregs : List Nat := [5, 6, 7, 10, 11, 12, 13, 14, 15]

omit I in
/-- **`strcmp` in continuation style, for either WP.** Entered at `0x80006ea0`
with the return address `r`, `a0 = p`, `a1 = q` and the strings `x`, `y`: the
continuation receives the PC at `r`, `ra` restored, and the nine registers at
values whose `a0` has `strcmp`'s sign class. -/
theorem strcmp_core (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {p q r : BitVec 64} {x y : String} (hal : r.toNat % 4 = 0) (rv0 : Nat → BitVec 64)
    (hp : rv0 10 = p) (hq : rv0 11 = q) :
    binImg ∗ strAt p.toNat x ∗ strAt q.toNat y ∗ VsaIris.PC ↦ᵣ 0x80006ea0#64 ∗
      VsaIris.ra ↦ᵣ r ∗ sepL cregs (fun k => k ↦ᵣ rv0 k) ∗
      (∀ rv' : Nat → BitVec 64, ⌜StrcmpSign (rv' 10) x y⌝ -∗ VsaIris.PC ↦ᵣ r -∗
        VsaIris.ra ↦ᵣ r -∗ sepL cregs (fun k => k ↦ᵣ rv' k) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold strAt
  iintro ⟨#Himg, ⟨%ix, %hx, #Hx⟩, ⟨%iy, %hy, #Hy⟩, Hpc, Hra, Hregs, Hk⟩
  have ctx := strcmpCtx hcl hx hy hal
  let rvE : Nat → BitVec 64 := fun k =>
    if k = VsaIris.PC then 0x80006ea0#64 else if k = 1 then r else rv0 k
  have hrun := strcmpRun ctx (rv := rvE) rfl rfl hp hq (fun _ => 0)
  ihave #Hcode := instrAt_of_binImg strcmpCode_text $$ Himg
  ihave #Hrod := binImg_rodata $$ Himg
  ihave #Hmask := roImg_strList (GF := GF) rodataDom rodataByte maskText maskText_rodata $$ Hrod
  ihave #Hsx := roImg_strT (GF := GF) p.toNat x.toList.length ix $$ Hx
  ihave #Hsy := roImg_strT (GF := GF) q.toNat y.toList.length iy $$ Hy
  iapply wp_localRunW Wp _ _ _ hrun
  isplitr
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    unfold TT cmpText
    iapply (sepL_append _ _ _).2
    isplitl
    · iapply (sepL_append _ _ _).2
      isplitl
      · iapply (sepL_append _ _ _).2
        isplitl
        · rw [← instrAt_text]; iexact Hcode
        · iexact Hmask
      · iexact Hsx
    · iexact Hsy
  have hsplit : ∀ f : Nat → BitVec 64, sepL (GF := GF) cmpRs (fun k => k ↦ᵣ f k) =
      iprop(VsaIris.PC ↦ᵣ f VsaIris.PC ∗ VsaIris.ra ↦ᵣ f 1 ∗ sepL cregs (fun k => k ↦ᵣ f k)) :=
    fun f => rfl
  have hE : sepL (GF := GF) cregs (fun k => k ↦ᵣ rvE k) = sepL cregs (fun k => k ↦ᵣ rv0 k) :=
    sepL_congr fun k hk => by
      have h32 : k ≠ VsaIris.PC := fun e => by subst e; revert hk; decide
      have h1 : k ≠ 1 := fun e => by subst e; revert hk; decide
      simp only [rvE, h32, h1, ite_false]
  isplitl [Hpc Hra Hregs]
  · have e1 : rvE VsaIris.PC = 0x80006ea0#64 := by simp [rvE]
    have e2 : rvE 1 = r := by simp [rvE, VsaIris.PC]
    rw [hsplit, hE, e1, e2]
    iframe Hpc Hra Hregs
  isplitr
  · unfold ownSet
    iexists []
    simp only [sepL_nil]
    isplitr
    · ipureintro; exact ⟨List.nodup_nil, fun a => by simp⟩
    · iempintro
  iintro %rv' %mv' %⟨hpc', hra', hsg⟩ Hregs' -
  rw [hsplit]
  icases Hregs' with ⟨Hpc, Hra, Hregs⟩
  rw [hpc', hra']
  iapply Hk $$ %rv' %(strcmpSign_class (allNonzero_of_cstr hx.1) (allNonzero_of_cstr hy.1) hsg)
    Hpc Hra Hregs

/-! ## The three specifications -/

/-- The registers of a body other than `strcmp`'s. -/
abbrev cOther : List Nat :=
  [2, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

theorem fRegs_perm_c : fRegs.Perm (cregs ++ cOther) := by decide

omit I in
/-- **`strcmp` with its sign class** (`strcmpOrdSpec`, `SpecErr.lean`), for
either WP. -/
theorem strcmp_spec_ord (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) :
    ⊢ strcmpOrdSpec (GF := GF) (vsaModel live) Wp := by
  unfold strcmpOrdSpec helperSpec fnSpecW
  imodintro
  iintro %p %q %x %y %rv
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨hp, hq⟩, -, #Himg, #Hx, #Hy⟩ Hk
  ihave ⟨Hc, Ho⟩ := (regFile_cut fRegs_perm_c rv).1 $$ Hregs
  iapply strcmp_core live hcl Wp hal rv hp hq
  iframe Himg Hx Hy Hpc Hra Hc
  iintro %rv' %hs Hpc Hra Hc
  iapply Hk $$ Hpc Hra
  iexists (fun k => if k ∈ cregs then rv' k else rv k)
  isplitl [Hc Ho]
  · iapply regFile_uncut fRegs_perm_c rv rv' $$ [Hc Ho]
    iframe Hc Ho
  isplitr
  · ipureintro
    intro k _ hc
    have hsub : ∀ k ∈ cregs, k ∈ callerSaved := by decide
    have : k ∉ cregs := fun h => hc (hsub k h)
    simp [this]
  · ipureintro
    simpa using hs

/-- **`strcmp`'s equality** (`strcmpSpecV`, `SpecValue.lean`), for either WP:
the sign class's first field. -/
theorem strcmp_spec_v (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) :
    ⊢ strcmpSpecV (GF := GF) (vsaModel live) Wp := by
  ihave #H := strcmp_spec_ord live hcl Wp
  unfold strcmpSpecV
  imodintro
  iintro %p %q %x %y
  ihave #H1 := strcmpOrdSpec_at (vsaModel live) p q x y $$ H
  unfold helperSpec fnSpecW
  iintro %rv
  imodintro
  iintro %r %Φ Hpc Hra HP Hk
  ihave #H2 := H1 $$ %rv
  iapply H2 $$ %r %Φ Hpc Hra HP
  iintro Hpc Hra ⟨%rv', Hregs, %hkeep, %hs⟩
  iapply Hk $$ Hpc Hra
  iexists rv'
  iframe Hregs
  ipureintro
  exact ⟨hkeep, hs.eq⟩

/-- The registers `strcmpSpec` hands over, besides `a0`/`a1`. -/
abbrev cClob : List Nat := [12, 5, 6, 7, 13, 14, 15]
abbrev cRest : List Nat := [16, 17, 28, 29, 30, 31]

theorem clob_perm : (12 :: argClob).Perm (cClob ++ cRest) := by decide
theorem cregs_perm : cregs.Perm ([10, 11] ++ cClob) := by decide
theorem retClob_perm : retClob.Perm ((11 :: cClob) ++ cRest) := by decide
theorem cregs_perm' : cregs.Perm ([10] ++ (11 :: cClob)) := by decide

omit I in
/-- **`strcmp`'s environment spec** (`strcmpSpec`, `SpecEnv.lean`), for
either WP. -/
theorem strcmp_spec_env (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) :
    binImg (GF := GF) ⊢ strcmpSpec Wp := by
  iintro #Himg
  unfold strcmpSpec fnSpecW
  imodintro
  iintro %p %q %x %y
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Ha0, Ha1, Hcl, #Hx, #Hy⟩ Hk
  rw [show strcmpPC = 0x80006ea0#64 from rfl]
  ihave ⟨%f, Hcl⟩ := clobbered_fn (12 :: argClob) (by decide) $$ Hcl
  ihave ⟨Hc, Hr⟩ := ((sepL_perm _ clob_perm).trans (sepL_append _ _ _)).1 $$ Hcl
  let rv0 : Nat → BitVec 64 := fun k => if k = 10 then p else if k = 11 then q else f k
  have e0 : sepL (GF := GF) cClob (fun k => k ↦ᵣ rv0 k) = sepL cClob (fun k => k ↦ᵣ f k) :=
    sepL_congr fun k hk => by
      have h10 : k ≠ 10 := fun e => by subst e; revert hk; decide
      have h11 : k ≠ 11 := fun e => by subst e; revert hk; decide
      simp only [rv0, h10, h11, ite_false]
  iapply strcmp_core live hcl Wp (p := p) (q := q) hal rv0 (by simp [rv0]) (by simp [rv0])
  iframe Himg Hx Hy Hpc Hra
  isplitl [Ha0 Ha1 Hc]
  · iapply ((sepL_perm _ cregs_perm).trans (sepL_append _ _ _)).2
    rw [e0]
    iframe Hc
    have r10 : rv0 10 = p := by simp [rv0]
    have r11 : rv0 11 = q := by simp [rv0]
    simp only [sepL_cons, sepL_nil]
    rw [r10, r11]
    iframe Ha0 Ha1
  iintro %rv' %hs Hpc Hra Hc
  ihave ⟨H10, Hc⟩ := ((sepL_perm _ cregs_perm').trans (sepL_append _ _ _)).1 $$ Hc
  iapply Hk $$ Hpc Hra
  iexists rv' 10
  ihave H10 := (show sepL (GF := GF) [10] (fun k => k ↦ᵣ rv' k) ⊢ (10 : Nat) ↦ᵣ rv' 10 from by
    simp only [sepL_cons, sepL_nil]; iintro ⟨H, -⟩; iexact H) $$ H10
  iframe H10
  isplitr
  · ipureintro; exact hs.eq
  unfold clobbered
  iapply ((sepL_perm _ retClob_perm).trans (sepL_append _ _ _)).2
  isplitl [Hc]
  · ihave H := clobbered_of_fn (GF := GF) (11 :: cClob) rv' $$ Hc
    unfold clobbered; iexact H
  · ihave H := clobbered_of_fn (GF := GF) cRest f $$ Hr
    unfold clobbered; iexact H

end Spec

#print axioms strcmp_spec_env
#print axioms strcmp_spec_ord
#print axioms strcmp_spec_v

end VsaIris.Interp
