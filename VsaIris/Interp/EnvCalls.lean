import VsaIris.Interp.EnvScan
import VsaIris.Interp.HeapCall

/-!
# Allocator calls from an `env_*` span

`wp_call_malloc`: a `jal malloc` from a span's register file, in either regime
(`mallocRho_spec`). The call takes `ra`, `a0` and the caller-saved registers;
`sp` and `s0-s3` come back at their values, `s4-s6` are not touched.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym

section Calls

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

omit I in
/-- A register points-to up to the register's and the value's equalities. -/
theorem regPt_congr {x y : Nat} {v w : BitVec 64} (hx : x = y) (hv : v = w) :
    (x ↦ᵣ v) ⊢@{IProp GF} (y ↦ᵣ w) := by
  subst hx; subst hv; exact .rfl

/-- The registers a `malloc` call hands over. -/
abbrev mallocKs : List Nat := VsaIris.ra :: 10 :: VsaIris.sp :: (vsaClob ++ vsaSaved)

theorem mallocKs_nodup : mallocKs.Nodup := by decide
theorem mallocKs_sub : ∀ k ∈ mallocKs, k ∈ gprs := by decide

theorem mallocKs_saved (k : Nat) (h1 : k ∈ mallocKs) (h2 : k ∉ VsaIris.ra :: 10 :: vsaClob)
    (h3 : k ≠ VsaIris.sp) : k ∈ vsaSaved := by
  simp only [mallocKs, vsaClob, vsaSaved, VsaIris.ra, VsaIris.sp, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at h1 h2 h3 ⊢
  omega

/-- **`jal malloc` from a span**, in regime `ρ`, charged `c` credits for the
request in `a0`. The continuation gets the result in `a0`, `ra` at the return
address, `sp` and `s0-s6` unchanged, and `malloc`'s outcome. -/
theorem wp_call_malloc (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code mallocEntryBV)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat))
    (c : Nat) {R : Nat → BitVec 64} (hc : vsaChg (R 10).toNat c) (hsp : SpOKA (R 2)) :
    instrAt i code ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗
      regsOf gprs R ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗
      (∀ (R' : Nat → BitVec 64) (p : BitVec 64), ⌜R' 10 = p ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ VsaIris.ra :: 10 :: vsaClob → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗
        stackScratch (R 2) allocHeadroom -∗ mallocRes ρ H (R 10).toNat p -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hat, #Hgp, Hpc, HR, Hstk, Hh, Hk⟩
  ihave ⟨Hks, Hrest⟩ := regsOf_extract gprs mallocKs gprs_nodup mallocKs_nodup mallocKs_sub R $$ HR
  rw [show mallocKs = VsaIris.ra :: 10 :: VsaIris.sp :: (vsaClob ++ vsaSaved) from rfl]
  rw [regsOf_cons, regsOf_cons, regsOf_cons]
  icases Hks with ⟨Hra, Ha0, Hsp, Hcs⟩
  unfold regsOf
  ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
  ihave Hcl := clobbered_of_fn vsaClob R $$ Hcl
  have hsv : (vsaSaved.map fun k => (k, R k)).map Prod.fst = vsaSaved := by
    simp [vsaSaved]
  ihave #Hs := mallocRho_spec A Wp ρ H (R 10) (R 2) c hc (vsaSaved.map fun k => (k, R k)) hsv $$ Hat
  iapply wp_callW Wp hexec
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hs
  isplitl [Hpc]
  · iexact Hpc
  isplitl [Hra]
  · iexact Hra
  isplitl [Ha0 Hsp Hcl Hsv Hstk Hh]
  · isplitr
    · ipureintro; exact ⟨hsp, hi4⟩
    isplitl [Ha0]
    · iapply regPt_congr (x := 10) (y := VsaIris.a0) rfl rfl $$ Ha0
    isplitl [Hsp]
    · iapply regPt_congr (x := VsaIris.sp) (y := VsaIris.sp) (v := R VsaIris.sp) (w := R 2) rfl rfl
        $$ Hsp
    iframe Hgp Hcl Hstk Hh
    unfold savedOwn
    rw [sepL_map]
    iexact Hsv
  iintro Hpc Hra ⟨%p, Ha0, Hsp, Hcl, Hsv, Hstk, Hres⟩
  ihave ⟨%f, Hcl⟩ := regsOf_of_clobbered vsaClob (by decide) $$ Hcl
  classical
  obtain ⟨R'', hR''⟩ : ∃ R'' : Nat → BitVec 64, R'' = fun k =>
      if k = VsaIris.ra then BitVec.ofNat 64 (i + 4) else if k = 10 then p
      else if k ∈ vsaClob then f k else R k := ⟨_, rfl⟩
  have e1 : R'' VsaIris.ra = BitVec.ofNat 64 (i + 4) := by simp [hR'']
  have e2 : R'' 10 = p := by simp [hR'', VsaIris.ra]
  have e3 : R'' VsaIris.sp = R VsaIris.sp := by simp [hR'', VsaIris.ra, VsaIris.sp, vsaClob]
  have e4 : ∀ k ∈ vsaClob, R'' k = f k := fun k hk => by
    have h1 : k ≠ VsaIris.ra := by simp [vsaClob, VsaIris.ra] at hk ⊢; omega
    have h10 : k ≠ 10 := by simp [vsaClob] at hk; omega
    simp [hR'', h1, h10, hk]
  have e5 : ∀ k ∈ vsaSaved, R'' k = R k := fun k hk => by
    have h1 : k ≠ VsaIris.ra := by simp [vsaSaved, VsaIris.ra] at hk ⊢; omega
    have h10 : k ≠ 10 := by simp [vsaSaved] at hk; omega
    have hc' : k ∉ vsaClob := by simp [vsaSaved, vsaClob] at hk ⊢; omega
    simp [hR'', h1, h10, hc']
  ihave HR := Hrest $$ %R'' [Hra Ha0 Hsp Hcl Hsv]
  · rw [sepL_cons, sepL_cons, sepL_cons, e1, e2, e3]
    isplitl [Hra]
    · iexact Hra
    isplitl [Ha0]
    · iapply regPt_congr (x := VsaIris.a0) (y := 10) rfl rfl $$ Ha0
    isplitl [Hsp]
    · iapply regPt_congr (x := VsaIris.sp) (y := VsaIris.sp) (v := R 2) (w := R VsaIris.sp) rfl rfl
        $$ Hsp
    iapply (sepL_append _ _ _).2
    rw [sepL_congr (l := vsaClob) (Ψ := fun k => k ↦ᵣ f k) (fun k hk => by rw [e4 k hk]),
      sepL_congr (l := vsaSaved) (Ψ := fun k => k ↦ᵣ R k) (fun k hk => by rw [e5 k hk])]
    unfold regsOf
    iframe Hcl
    unfold savedOwn
    rw [sepL_map]
    iexact Hsv
  have hpure : (fun k => if k ∈ mallocKs then R'' k else R k) 10 = p ∧
      (fun k => if k ∈ mallocKs then R'' k else R k) 1 = BitVec.ofNat 64 (i + 4) ∧
      ∀ k, k ∉ VsaIris.ra :: 10 :: vsaClob →
        (fun k => if k ∈ mallocKs then R'' k else R k) k = R k := by
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · dsimp only; rw [ite_eq_left_iff.2 (fun h => absurd (by decide) h), e2]
    · dsimp only
      rw [ite_eq_left_iff.2 (fun h => absurd (by decide) h), show (1 : Nat) = VsaIris.ra from rfl, e1]
    · dsimp only
      split
      · by_cases hsp' : k = VsaIris.sp
        · subst hsp'; exact e3
        · exact e5 k (mallocKs_saved k ‹_› hk hsp')
      · rfl
  iapply Hk $$ %_ %p %hpure Hpc HR Hstk Hres

end Calls

end VsaIris.Interp
