import VsaIris.Interp.CallKs
import VsaIris.Interp.HeapRealloc
import VsaIris.Interp.EnvCalls

/-!
# `env_define`'s calls from its spans

`strlen`, `memcpy` and `realloc` (both regimes, live block or NULL), each an
instance of `wp_call_ks`: the callee's registers are `ra :: Ks`, everything
else of the span's file comes back unchanged.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym

section Calls

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

omit I in
/-- A register and a file over the rest make up the file with it updated. -/
theorem regsOf_cons_fun (k : Nat) (v : BitVec 64) (rest : List Nat) (hk : k ∉ rest)
    (f : Nat → BitVec 64) :
    k ↦ᵣ v ∗ regsOf (GF := GF) rest f ⊢ regsOf (k :: rest) (fun j => if j = k then v else f j) := by
  classical
  rw [regsOf_cons, regsOf_congr (R := fun j => if j = k then v else f j) (R' := f) (rs := rest)
    fun j hj => by
    have : j ≠ k := fun h => hk (h ▸ hj)
    simp [this]]
  simp only [ite_true]
  iintro H; iexact H

omit I in
theorem regsOf_eq_of {rs : List Nat} {R R' : Nat → BitVec 64} (h : ∀ r ∈ rs, R r = R' r) :
    regsOf (GF := GF) rs R ⊢ regsOf rs R' := by
  rw [regsOf_congr h]

omit I in
theorem regsOf_append_intro (a b : List Nat) (R : Nat → BitVec 64) :
    regsOf (GF := GF) a R ∗ regsOf b R ⊢ regsOf (a ++ b) R := by
  unfold regsOf; exact (sepL_append _ _ _).2

/-- The registers a `strlen`/`memcpy` call takes besides `ra`. -/
abbrev strKs : List Nat := 10 :: retClob

omit I in
/-- **`jal strlen` from a span**: `a0` gets the length. -/
theorem wp_call_strlen (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code strlenPC)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) {R : Nat → BitVec 64} {x : String} :
    instrAt i code ∗ strlenSpec Wp ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗ regsOf gprs R ∗
      strAt (R 10).toNat x ∗
      (∀ R' : Nat → BitVec 64, ⌜R' 10 = BitVec.ofNat 64 x.length ∧
          R' 1 = BitVec.ofNat 64 (i + 4) ∧ ∀ k, k ∉ VsaIris.ra :: strKs → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hs, Hpc, HR, #Hx, Hk⟩
  unfold strlenSpec
  ihave Hsp := Hs $$ %(R 10) %x
  iapply wp_call_ks Wp hexec strKs (by decide) (by decide) (R := R)
    (A := strAt (R 10).toNat x) (B := fun Rc => iprop(⌜Rc 10 = BitVec.ofNat 64 x.length⌝))
    (P := fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ R 10 ∗ clobbered retClob ∗
      strAt (R 10).toNat x))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 x.length ∗ clobbered retClob))
  · iintro ⟨HR, #Hx⟩
    rw [regsOf_cons]
    icases HR with ⟨Ha0, Hcl⟩
    ihave Hcl := clobbered_of_regsOf _ R $$ Hcl
    iframe Ha0 Hcl Hx
    ipureintro; exact hi4
  · iintro ⟨Ha0, Hcl⟩
    ihave ⟨%f, Hcl⟩ := regsOf_of_clobbered retClob (by decide) $$ Hcl
    ihave HR := regsOf_cons_fun 10 _ retClob (by decide) f $$ [Ha0 Hcl]
    · iframe Ha0 Hcl
    iexists (fun j => if j = 10 then BitVec.ofNat 64 x.length else f j)
    iframe HR
    ipureintro; simp
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hsp
  iframe Hpc HR Hx
  iintro %Rc %R' %⟨h1, hks, hkeep⟩ Hpc HR %h10
  iapply Hk $$ %R' %⟨(hks 10 (by decide)).trans h10, h1, hkeep⟩ Hpc HR

omit I in
/-- **`jal memcpy` from a span**: `n` bytes from a read-only source into an
owned block. -/
theorem wp_call_memcpy (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code memcpyPC)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) {R : Nat → BitVec 64} {n : Nat}
    {img : Nat → BitVec 8} (h12 : R 12 = BitVec.ofNat 64 n) (hd : RamWin (R 10).toNat n)
    (hs : RamWin (R 11).toNat n) :
    instrAt i code ∗ memcpySpec Wp ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗ regsOf gprs R ∗
      blockOwn (R 10).toNat n ∗ roImg (InExt ((R 11).toNat, n)) img ∗
      (∀ R' : Nat → BitVec 64, ⌜R' 10 = R 10 ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ VsaIris.ra :: strKs → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗
        ownImg (InExt ((R 10).toNat, n)) (fun a => img (a - (R 10).toNat + (R 11).toNat)) -∗
        Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hs, Hpc, HR, Hb, #Hsrc, Hk⟩
  unfold memcpySpec
  ihave Hsp := Hs $$ %(R 10) %(R 11) %n %img
  iapply wp_call_ks Wp hexec strKs (by decide) (by decide) (R := R)
    (A := iprop(blockOwn (R 10).toNat n ∗ roImg (InExt ((R 11).toNat, n)) img))
    (B := fun Rc => iprop(⌜Rc 10 = R 10⌝ ∗
      ownImg (InExt ((R 10).toNat, n)) (fun a => img (a - (R 10).toNat + (R 11).toNat))))
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin (R 10).toNat n ∧ RamWin (R 11).toNat n⌝ ∗
      (10 : Nat) ↦ᵣ R 10 ∗ (11 : Nat) ↦ᵣ R 11 ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗
      clobbered argClob ∗ blockOwn (R 10).toNat n ∗ roImg (InExt ((R 11).toNat, n)) img))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ R 10 ∗ clobbered retClob ∗
      ownImg (InExt ((R 10).toNat, n)) (fun a => img (a - (R 10).toNat + (R 11).toNat))))
  · iintro ⟨HR, Hb, #Hsrc⟩
    rw [show strKs = 10 :: 11 :: 12 :: argClob from rfl, regsOf_cons, regsOf_cons, regsOf_cons, h12]
    icases HR with ⟨Ha0, Ha1, Ha2, Hcl⟩
    ihave Hcl := clobbered_of_regsOf _ R $$ Hcl
    iframe Ha0 Ha1 Ha2 Hcl Hb Hsrc
    ipureintro; exact ⟨hi4, hd, hs⟩
  · iintro ⟨Ha0, Hcl, Hout⟩
    ihave ⟨%f, Hcl⟩ := regsOf_of_clobbered retClob (by decide) $$ Hcl
    ihave HR := regsOf_cons_fun 10 _ retClob (by decide) f $$ [Ha0 Hcl]
    · iframe Ha0 Hcl
    iexists (fun j => if j = 10 then R 10 else f j)
    iframe HR Hout
    ipureintro; simp
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hsp
  iframe Hpc HR Hb Hsrc
  iintro %Rc %R' %⟨h1, hks, hkeep⟩ Hpc HR ⟨%h10, Hout⟩
  iapply Hk $$ %R' %⟨(hks 10 (by decide)).trans h10, h1, hkeep⟩ Hpc HR Hout

/-- The registers an allocator call takes besides `ra`. -/
abbrev allocKs : List Nat := 10 :: VsaIris.sp :: (vsaClob ++ vsaSaved)

/-- The callee-saved words an allocator call hands over and gets back. -/
abbrev savedOf (R : Nat → BitVec 64) : List (Nat × BitVec 64) := vsaSaved.map fun k => (k, R k)

theorem savedOf_fst (R : Nat → BitVec 64) : (savedOf R).map Prod.fst = vsaSaved := by
  simp [savedOf, vsaSaved]

omit I in
theorem savedOwn_savedOf (R : Nat → BitVec 64) :
    savedOwn (GF := GF) (savedOf R) = regsOf vsaSaved R := by
  unfold savedOwn savedOf regsOf
  rw [sepL_map]

omit I in
/-- **An allocator `jal` from a span**: `a0`, `sp`, the clobbered and the
spilled registers go to the callee (spec `P`/`Q`); the continuation gets the
result in `a0`, `sp` and `s0-s3` back, `ra` at the return address. -/
theorem wp_call_allocKs (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64} {P Q : BitVec 64 → IProp GF}
    (hexec : JalExec (vsaModel live) i code entry) {R : Nat → BitVec 64} {X : IProp GF}
    {Y : BitVec 64 → IProp GF}
    (hpre : VsaIris.a0 ↦ᵣ R 10 ∗ VsaIris.sp ↦ᵣ R 2 ∗ regsOf vsaClob R ∗ savedOwn (savedOf R) ∗ X ⊢
      P (BitVec.ofNat 64 (i + 4)))
    (hpost : Q (BitVec.ofNat 64 (i + 4)) ⊢ ∃ p', VsaIris.a0 ↦ᵣ p' ∗ VsaIris.sp ↦ᵣ R 2 ∗
      clobbered vsaClob ∗ savedOwn (savedOf R) ∗ Y p') :
    instrAt i code ∗ fnSpecW Wp entry P Q ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗ regsOf gprs R ∗ X ∗
      (∀ (R' : Nat → BitVec 64) (p' : BitVec 64), ⌜R' 10 = p' ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ VsaIris.ra :: 10 :: vsaClob → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗ Y p' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hs, Hpc, HR, HX, Hk⟩
  classical
  iapply wp_call_ks Wp hexec allocKs (by decide) (by decide) (R := R) (A := X) (P := P) (Q := Q)
    (B := fun Rc => iprop(∃ p', ⌜Rc 10 = p' ∧ Rc 2 = R 2 ∧ ∀ k ∈ vsaSaved, Rc k = R k⌝ ∗ Y p'))
  · iintro ⟨HR, HX⟩
    rw [show allocKs = 10 :: VsaIris.sp :: (vsaClob ++ vsaSaved) from rfl, regsOf_cons,
      regsOf_cons]
    icases HR with ⟨Ha0, Hsp, Hcs⟩
    unfold regsOf
    ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
    iapply hpre
    isplitl [Ha0]
    · iapply regPt_congr (x := 10) (y := VsaIris.a0) rfl rfl $$ Ha0
    isplitl [Hsp]
    · iapply regPt_congr (x := VsaIris.sp) (y := VsaIris.sp) (v := R VsaIris.sp) (w := R 2) rfl rfl
        $$ Hsp
    rw [savedOwn_savedOf]
    unfold regsOf
    iframe Hcl HX Hsv
  · iintro HQ
    ihave ⟨%p', Ha0, Hsp, Hcl, Hsv, HY⟩ := hpost $$ HQ
    ihave ⟨%f, Hcl⟩ := regsOf_of_clobbered vsaClob (by decide) $$ Hcl
    iexists (fun k => if k = 10 then p' else if k = 2 then R 2 else if k ∈ vsaClob then f k else R k)
    isplitl [Ha0 Hsp Hcl Hsv]
    · rw [show allocKs = 10 :: VsaIris.sp :: (vsaClob ++ vsaSaved) from rfl, regsOf_cons,
        regsOf_cons]
      isplitl [Ha0]
      · simp only [ite_true]; iapply regPt_congr (x := VsaIris.a0) (y := 10) rfl rfl $$ Ha0
      isplitl [Hsp]
      · simp only [VsaIris.sp, show (2 : Nat) ≠ 10 by decide, ite_true, ite_false]
        iexact Hsp
      iapply regsOf_append_intro
      isplitl [Hcl]
      · iapply regsOf_eq_of (rs := vsaClob) (R := f) (fun k hk => by
          have h10 : k ≠ 10 := by simp [vsaClob] at hk; omega
          have h2 : k ≠ 2 := by simp [vsaClob] at hk; omega
          simp [h10, h2, hk]) $$ Hcl
      · rw [savedOwn_savedOf]
        iapply regsOf_eq_of (rs := vsaSaved) (R := R) (fun k hk => by
          have h10 : k ≠ 10 := by simp [vsaSaved] at hk; omega
          have h2 : k ≠ 2 := by simp [vsaSaved] at hk; omega
          have hc : k ∉ vsaClob := by simp [vsaSaved, vsaClob] at hk ⊢; omega
          simp [h10, h2, hc]) $$ Hsv
    iexists p'
    iframe HY
    ipureintro
    refine ⟨by simp, by simp, fun k hk => ?_⟩
    have h10 : k ≠ 10 := by simp [vsaSaved] at hk; omega
    have h2 : k ≠ 2 := by simp [vsaSaved] at hk; omega
    have hc : k ∉ vsaClob := by simp [vsaSaved, vsaClob] at hk ⊢; omega
    simp [h10, h2, hc]
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hs
  iframe Hpc HR HX
  iintro %Rc %R' %⟨h1, hks, hkeep⟩ Hpc HR ⟨%p', %⟨h10, h2, hsv⟩, HY⟩
  iapply Hk $$ %R' %p' %⟨(hks 10 (by decide)).trans h10, h1, fun k hk => ?_⟩ Hpc HR HY
  by_cases hK : k ∈ VsaIris.ra :: allocKs
  · have hk' : k ∈ allocKs := by
      rcases List.mem_cons.1 hK with h | h
      · exact absurd (List.mem_cons_self) (h ▸ hk)
      · exact h
    rw [hks k hk']
    simp only [allocKs, List.mem_cons, List.mem_append] at hk' hk
    rcases hk' with h | h | h | h
    · exact absurd (.inr (.inl h)) hk
    · subst h; exact h2
    · exact absurd (.inr (.inr h)) hk
    · exact hsv k h
  · exact hkeep k hK

omit I in
/-- **`jal realloc` of a live block from a span**, regime `ρ`, charged `c`
credits for the new size `nNew` in `a1`. -/
theorem wp_call_realloc (AH : AllocHoles) (hlive : AllocLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code reallocEntryBV)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat))
    (nOld nNew : Nat) (old : Nat → BitVec 8) (c : Nat) (hc : vsaChg nNew c)
    {R : Nat → BitVec 64} (h11 : R 11 = BitVec.ofNat 64 nNew) (hsp : SpOKA (R 2))
    (hlt : nOld < nNew) :
    instrAt i code ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗
      regsOf gprs R ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) (((R 10).toNat, nOld) :: H) ∗
      blockOwnAt (R 10).toNat nOld old ∗
      (∀ (R' : Nat → BitVec 64) (p' : BitVec 64), ⌜R' 10 = p' ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ VsaIris.ra :: 10 :: vsaClob → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗
        stackScratch (R 2) allocHeadroom -∗ reallocRes ρ H (R 10) nOld nNew old p' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hat, #Hgp, Hpc, HR, Hstk, Hh, Hb, Hk⟩
  ihave #Hs := reallocRho_spec AH hlive Wp ρ H (R 10) nOld nNew (R 2) old c hc (savedOf R)
    (savedOf_fst R) $$ Hat
  iapply wp_call_allocKs Wp hexec (R := R)
    (X := iprop(gp ↦ᵣ□ gpV ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) (((R 10).toNat, nOld) :: H) ∗
      blockOwnAt (R 10).toNat nOld old))
    (Y := fun p' => iprop(stackScratch (R 2) allocHeadroom ∗ reallocRes ρ H (R 10) nOld nNew old p'))
    (P := fun r => iprop(⌜SpOKA (R 2) ∧ r.toNat % 4 = 0 ∧ nOld < nNew⌝ ∗ VsaIris.a0 ↦ᵣ R 10 ∗
        clobberedArg vsaClob a1 (BitVec.ofNat 64 nNew) ∗ VsaIris.sp ↦ᵣ R 2 ∗ gp ↦ᵣ□ gpV ∗
        savedOwn (savedOf R) ∗ stackScratch (R 2) allocHeadroom ∗
        heapRes vsaLayoutP vsaRoomB (ρ.plus c) (((R 10).toNat, nOld) :: H) ∗
        blockOwnAt (R 10).toNat nOld old))
    (Q := fun _ => iprop(∃ p', VsaIris.a0 ↦ᵣ p' ∗ VsaIris.sp ↦ᵣ R 2 ∗ clobbered vsaClob ∗
        savedOwn (savedOf R) ∗ stackScratch (R 2) allocHeadroom ∗
        reallocRes ρ H (R 10) nOld nNew old p'))
  · iintro ⟨Ha0, Hsp, Hcl, Hsv, #Hgp, Hstk, Hh, Hb⟩
    iframe Ha0 Hsp Hgp Hsv Hstk Hh Hb
    isplitr
    · ipureintro; exact ⟨hsp, hi4, hlt⟩
    unfold clobberedArg
    iexists R
    unfold regsOf
    iframe Hcl
    ipureintro; exact h11
  · iintro ⟨%p', Ha0, Hsp, Hcl, Hsv, Hstk, Hres⟩
    iexists p'
    iframe Ha0 Hsp Hcl Hsv Hstk Hres
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hs
  iframe Hpc HR
  isplitl [Hstk Hh Hb]
  · iframe Hgp Hstk Hh Hb
  iintro %R' %p' %hR' Hpc HR ⟨Hstk, Hres⟩
  iapply Hk $$ %R' %p' %hR' Hpc HR Hstk Hres

omit I in
/-- **`jal realloc` from NULL**, regime `ρ`, charged `c` credits for the
size in `a1`. -/
theorem wp_call_reallocNull (NH : ReallocNullHoles) (hlive : AllocLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code reallocEntryBV)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat))
    (c : Nat) {R : Nat → BitVec 64} (hc : vsaChg (R 11).toNat c) (h10 : R 10 = 0#64)
    (hsp : SpOKA (R 2)) :
    instrAt i code ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗
      regsOf gprs R ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗
      (∀ (R' : Nat → BitVec 64) (p' : BitVec 64), ⌜R' 10 = p' ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ VsaIris.ra :: 10 :: vsaClob → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗
        stackScratch (R 2) allocHeadroom -∗ mallocRes ρ H (R 11).toNat p' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hat, #Hgp, Hpc, HR, Hstk, Hh, Hk⟩
  ihave #Hs := reallocNullRho_spec NH hlive Wp ρ H (R 11) (R 2) c hc (savedOf R)
    (savedOf_fst R) $$ Hat
  iapply wp_call_allocKs Wp hexec (R := R)
    (X := iprop(gp ↦ᵣ□ gpV ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) H))
    (Y := fun p' => iprop(stackScratch (R 2) allocHeadroom ∗ mallocRes ρ H (R 11).toNat p'))
    (P := fun r => iprop(⌜SpOKA (R 2) ∧ r.toNat % 4 = 0⌝ ∗ VsaIris.a0 ↦ᵣ 0#64 ∗
        clobberedArg vsaClob a1 (R 11) ∗ VsaIris.sp ↦ᵣ R 2 ∗ gp ↦ᵣ□ gpV ∗
        savedOwn (savedOf R) ∗ stackScratch (R 2) allocHeadroom ∗
        heapRes vsaLayoutP vsaRoomB (ρ.plus c) H))
    (Q := fun _ => iprop(∃ p', VsaIris.a0 ↦ᵣ p' ∗ VsaIris.sp ↦ᵣ R 2 ∗ clobbered vsaClob ∗
        savedOwn (savedOf R) ∗ stackScratch (R 2) allocHeadroom ∗ mallocRes ρ H (R 11).toNat p'))
  · iintro ⟨Ha0, Hsp, Hcl, Hsv, #Hgp, Hstk, Hh⟩
    rw [h10]
    iframe Ha0 Hsp Hgp Hsv Hstk Hh
    isplitr
    · ipureintro; exact ⟨hsp, hi4⟩
    unfold clobberedArg
    iexists R
    unfold regsOf
    iframe Hcl
    ipureintro; rfl
  · iintro ⟨%p', Ha0, Hsp, Hcl, Hsv, Hstk, Hres⟩
    iexists p'
    iframe Ha0 Hsp Hcl Hsv Hstk Hres
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hs
  iframe Hpc HR
  isplitl [Hstk Hh]
  · iframe Hgp Hstk Hh
  iintro %R' %p' %hR' Hpc HR ⟨Hstk, Hres⟩
  iapply Hk $$ %R' %p' %hR' Hpc HR Hstk Hres

/-- A `realloc`'s old block: none (`realloc(NULL, _)`) or a live extent. -/
def obPtr : Option (Nat × Nat) → Nat
  | none => 0
  | some b => b.1

def obLen : Option (Nat × Nat) → Nat
  | none => 0
  | some b => b.2

/-- The old block's bytes. -/
def obOwn : Option (Nat × Nat) → (Nat → BitVec 8) → IProp GF
  | none, _ => iprop(emp)
  | some b, old => blockOwnAt b.1 b.2 old

/-- `realloc`'s outcome from an optional old block, in regime `ρ`. -/
def reallocOptRes (ρ : Regime) (H : List (Nat × Nat)) (ob : Option (Nat × Nat)) (nNew : Nat)
    (old : Nat → BitVec 8) (p' : BitVec 64) : IProp GF :=
  iprop((⌜p' = 0#64 ∧ ρ = .uncounted⌝ ∗ heapRes vsaLayoutP vsaRoomB ρ (ob.toList ++ H) ∗
      obOwn ob old) ∨
    (⌜FreshBlock vsaLayoutP H p'.toNat nNew ∧ p'.toNat % 16 = 0⌝ ∗
      heapRes vsaLayoutP vsaRoomB ρ ((p'.toNat, nNew) :: H) ∗
      ∃ v : Nat → BitVec 8, ⌜Copies old v (obPtr ob) p'.toNat (obLen ob)⌝ ∗
        blockOwnAt p'.toNat nNew v))

omit I in
/-- **`jal realloc` from an optional old block** (`wp_call_reallocNull` or
`wp_call_realloc`). -/
theorem wp_call_reallocOpt (AH : AllocHoles) (NH : ReallocNullHoles) (hlive : AllocLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code reallocEntryBV)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat))
    (ob : Option (Nat × Nat)) (nNew : Nat) (old : Nat → BitVec 8) (c : Nat) (hc : vsaChg nNew c)
    (hn : nNew < 2 ^ 32) {R : Nat → BitVec 64} (h10 : (R 10).toNat = obPtr ob)
    (h11 : R 11 = BitVec.ofNat 64 nNew) (hsp : SpOKA (R 2)) (hlt : obLen ob < nNew) :
    instrAt i code ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗
      regsOf gprs R ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) (ob.toList ++ H) ∗ obOwn ob old ∗
      (∀ (R' : Nat → BitVec 64) (p' : BitVec 64), ⌜R' 10 = p' ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ VsaIris.ra :: 10 :: vsaClob → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗
        stackScratch (R 2) allocHeadroom -∗ reallocOptRes ρ H ob nNew old p' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hat, #Hgp, Hpc, HR, Hstk, Hh, Hob, Hk⟩
  have h11n : (R 11).toNat = nNew := by rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases ob with
  | none =>
    have h0 : R 10 = 0#64 := BitVec.eq_of_toNat_eq (by rw [h10]; rfl)
    iapply wp_call_reallocNull NH hlive Wp hexec hi4 ρ H c (R := R) (by rw [h11n]; exact hc) h0 hsp
    simp only [Option.toList_none, List.nil_append]
    iframe Hi Hat Hgp Hpc HR Hstk Hh
    iintro %R' %p' %hR' Hpc HR Hstk Hres
    iapply Hk $$ %R' %p' %hR' Hpc HR Hstk
    unfold mallocRes reallocOptRes
    rw [h11n]
    simp only [Option.toList_none, List.nil_append]
    icases Hres with (⟨%h, Hh⟩ | ⟨%hf, Hh, Hb⟩)
    · ileft
      iframe Hh
      isplitl []
      · ipureintro; exact h
      unfold obOwn; iempintro
    · iright
      iframe Hh
      isplitl []
      · ipureintro; exact hf
      unfold blockOwn
      ihave ⟨%v, Hb⟩ := ownSet_fn _ $$ Hb
      iexists v
      unfold blockOwnAt
      iframe Hb
      ipureintro
      intro k hk; simp [obLen] at hk
  | some b =>
    obtain ⟨bp, bn⟩ := b
    simp only [obPtr, obLen] at h10 hlt
    have hb : ((R 10).toNat, bn) = (bp, bn) := by rw [h10]
    iapply wp_call_realloc AH hlive Wp hexec hi4 ρ H bn nNew old c hc (R := R) h11 hsp hlt
    iframe Hi Hat Hgp Hpc HR Hstk
    rw [hb]
    simp only [Option.toList_some, List.singleton_append]
    isplitl [Hh]
    · iexact Hh
    isplitl [Hob]
    · unfold obOwn; rw [h10]; iexact Hob
    iintro %R' %p' %hR' Hpc HR Hstk Hres
    iapply Hk $$ %R' %p' %hR' Hpc HR Hstk
    unfold reallocRes reallocOptRes
    rw [h10]
    simp only [Option.toList_some, List.singleton_append, obOwn, obPtr, obLen]
    iexact Hres

end Calls

end VsaIris.Interp
