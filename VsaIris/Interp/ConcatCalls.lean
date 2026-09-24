import VsaIris.Interp.SpecConcat
import VsaIris.Interp.CallFree
import VsaIris.Interp.BinEq

/-!
# The concatenation arm's calls from a run (lane E2)

* `ms_callHelperA`: `ms_callHelper` for a helper that may abort
  (`helperSpecA`); both continuations come from one context (`∧`), the abort
  one receives the run's owned bytes.
* `abortAt_of_evalCallee`: a callee's abort below an `eval_expr` arm's `sp`
  becomes the arm's `abortAt Core s n` (the callee's stack, the slack below it
  and the frame bytes rejoin the stack below `s`; `CoreOK` absorbs the core).
  `ms_rtErrEval` is its first user.
* `ms_callMemcpyOwned`: `memcpy` from an owned source (`memcpySpecOwned`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.VsaHeap
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

omit I in
/-- **A helper that may abort, from a run** (`jal entry` at `i`). -/
theorem ms_callHelperA (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre A : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} :
    ⌜pins R⌝ ∗ helperSpecA (vsaModel live) Wp entry clob pins Pre Post A ∗ codeRes ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ Pre ∗
      ((∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ clob → R' x = R x⌝ -∗ Post R' -∗
          ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ) ∧
        (A -∗ ownSet S (fun a => a ↦ₘ imgM Mt a) -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  unfold ms helperSpecA
  iintro ⟨%hpins, Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HPre, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %R
  iapply wp_callAbort Wp hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs HPre]
  · iframe Hregs HPre Hcode
    ipureintro; exact ⟨hal, hpins⟩
  isplit
  · iintro Hpc Hra Hpost
    ihave Hk := and_elim_l $$ Hk
    icases Hpost with ⟨%R', Hregs, %hkeep, HPost⟩
    iapply Hk $$ %R' %hkeep HPost
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro HA
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ HA HS

/-- **A callee's abort below an `eval_expr` arm** (`sp = s - 1088`, the callee
entered with `need` bytes below `sp`): the arm's own `abortAt Core s n`. -/
theorem abortAt_of_evalCallee {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} (hC : CoreOK N L Room inp Core) {s : BitVec 64} {n need : Nat}
    (hsg : StackGeom s n) (hn : 1088 + need ≤ n) :
    abortRes N L Room inp (evalSP s) need ∗ blockOwn (s.toNat - n) (n - 1088 - need) ∗
      ownSet (InExt (s.toNat - 1088, 1088)) byteAny ⊢ abortAt Core s n := by
  have hs1 := hsg.lo; have hs2 := hsg.hi; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs1 hs2
  simp only at hs1 hs2
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  iintro ⟨HA, Hslack, HS⟩
  unfold abortRes abortAt
  icases HA with ⟨Hcore, Hst⟩
  ihave Hcore := hC (evalSP s) need (by rw [hsf]; omega) (by rw [hsf]; omega) (by rw [hsf]; omega)
    $$ Hcore
  ihave Hst := stackScratch_widen (s := evalSP s) (n := n - 1088) (m := need)
    (by rw [hsf]; omega) (by omega) $$ [Hslack Hst]
  · rw [hsf, show s.toNat - 1088 - (n - 1088) = s.toNat - n by omega]; iframe Hslack Hst
  ihave Hst := evalFrame_join hs4 (by omega) $$ [Hst HS]
  · iframe Hst HS
  iframe Hcore Hst

/-- **`memcpy(R 10, R 11, n)` from an owned source**, from a run: the
destination holds the source's bytes, the source is handed back. -/
theorem ms_callMemcpyOwnedR (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code memcpyPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {n : Nat} {img : Nat → BitVec 8}
    (h12 : R 12 = BitVec.ofNat 64 n) (hd : RamWin (R 10).toNat n) (hs : RamWin (R 11).toNat n) :
    codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ blockOwn (R 10).toNat n ∗
      ownImg (InExt ((R 11).toNat, n)) img ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗ ⌜R' 10 = R 10⌝ -∗
        ownImg (InExt ((R 10).toNat, n)) (fun a => img (a - (R 10).toNat + (R 11).toNat)) -∗
        ownImg (InExt ((R 11).toNat, n)) img -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, Hms, Hblk, Hsrc, Hk⟩
  ihave #Hmc0 := hmc
  unfold memcpySpecOwned
  ihave #Hmcs := Hmc0 $$ %(R 10) %(R 11) %n %img
  iapply (ms_callRegs Wp hexec hcode
    (L := [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31])
    (K := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin (R 10).toNat n ∧ RamWin (R 11).toNat n⌝ ∗
      (10 : Nat) ↦ᵣ R 10 ∗ (11 : Nat) ↦ᵣ R 11 ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗
      clobbered argClob ∗ blockOwn (R 10).toNat n ∗ ownImg (InExt ((R 11).toNat, n)) img))
    (Q := fun _ => iprop((10 : Nat) ↦ᵣ R 10 ∗ clobbered retClob ∗
      ownImg (InExt ((R 10).toNat, n)) (fun a => img (a - (R 10).toNat + (R 11).toNat)) ∗
      ownImg (InExt ((R 11).toNat, n)) img))
    (X := iprop(blockOwn (R 10).toNat n ∗ ownImg (InExt ((R 11).toNat, n)) img))
    (Y := fun g => iprop(⌜g 10 = R 10⌝ ∗
      ownImg (InExt ((R 10).toNat, n)) (fun a => img (a - (R 10).toNat + (R 11).toNat)) ∗
      ownImg (InExt ((R 11).toNat, n)) img))
    (R := R) (S := S) (Mt := Mt) ?hP ?hQ)
  case hP =>
    simp only [sepL_cons, sepL_nil]
    iintro ⟨⟨H10, H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩, Hbk, HB⟩
    iframe H10 H11 Hbk HB
    isplitl []
    · ipureintro; exact ⟨hal, hd, hs⟩
    isplitl [H12]
    · rw [h12]; iexact H12
    iapply clobbered_of_fn argClob _
    unfold argClob
    simp only [sepL_cons, sepL_nil]
    iframe H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31
  case hQ =>
    iintro ⟨H10, Hcl, Hd, HB⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then R 10 else g y)
    unfold retClob argClob
    simp only [sepL_cons, sepL_nil]
    icases Hcl with ⟨H11, H12, H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩
    simp only [ite_true]
    simp (config := { decide := true }) only [ite_false]
    iframe H10 H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31 Hd HB
  iframe Hmcs Hcode Hms Hblk Hsrc
  iintro %g ⟨%hg10, Hd, HB⟩ Hms
  have hkeep : ∀ x ∈ fRegs, x ∉ callerSaved →
      (fun x => if x ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] then g x
        else R x) x = R x := by
    intro x _ hc
    have hsub : ∀ y ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31], y ∈ callerSaved := by
      decide
    have : x ∉ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] := fun h => hc (hsub x h)
    simp only [this, ite_false]
  have h10 : (fun x => if x ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] then g x
      else R x) 10 = R 10 := by
    simp only [show (10 : Nat) ∈ [10, 11, 12, 5, 6, 7, 13, 14, 15, 16, 17, 28, 29, 30, 31] by decide,
      ite_true]; exact hg10
  iapply Hk $$ %_ %hkeep %h10 Hd HB Hms


/-- `ms_callMemcpyOwnedR` at named arguments, the register facts a pure premise. -/
theorem ms_callMemcpyOwned (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hmc : ⊢ memcpySpecOwned (vsaModel live) Wp)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code memcpyPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {dst src : BitVec 64} {n : Nat}
    {img : Nat → BitVec 8} (hd : RamWin dst.toNat n) (hs : RamWin src.toNat n) :
    ⌜R 10 = dst ∧ R 11 = src ∧ R 12 = BitVec.ofNat 64 n⌝ ∗
      codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ blockOwn dst.toNat n ∗
      ownImg (InExt (src.toNat, n)) img ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗ ⌜R' 10 = dst⌝ -∗
        ownImg (InExt (dst.toNat, n)) (fun a => img (a - dst.toNat + src.toNat)) -∗
        ownImg (InExt (src.toNat, n)) img -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%⟨h10, h11, h12⟩, H⟩
  subst h10 h11
  iapply ms_callMemcpyOwnedR Wp hmc hexec hcode hal h12 hd hs $$ H

/-- `ms_callMalloc` at a named request, the register facts a pure premise. -/
theorem ms_callMallocN (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code mallocEntryBV)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat)) (n c : Nat)
    (hc : vsaChg n c) {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {sp : BitVec 64} :
    ⌜(R 10).toNat = n ∧ R 2 = sp ∧ SpOKA sp⌝ ∗
      textOwn allocText ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      stackScratch sp allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗
        stackScratch sp allocHeadroom -∗ mallocRes ρ H n (R' 10) -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%⟨hn, h2, hsp⟩, H⟩
  subst hn h2
  iapply ms_callMalloc A Wp hexec hcode hi4 ρ H c hc hsp $$ H

/-- `ms_callFree` at a named block, the register facts a pure premise. -/
theorem ms_callFreeN (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code freeEntryBV)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat))
    (q : BitVec 64) (n : Nat) {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {sp : BitVec 64} :
    ⌜R 10 = q ∧ R 2 = sp ∧ SpOKA sp⌝ ∗
      textOwn allocText ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      stackScratch sp allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, n) :: H) ∗ blockOwn q.toNat n ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗
        stackScratch sp allocHeadroom -∗ heapRes vsaLayoutP vsaRoomB ρ H -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%⟨hq, h2, hsp⟩, H⟩
  subst hq h2
  iapply ms_callFree A Wp hexec hcode hi4 ρ H n hsp $$ H

end

end VsaIris.Interp
