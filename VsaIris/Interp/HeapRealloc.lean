import VsaIris.Interp.HeapCall
import VsaIris.Interp.ReallocNullRun

/-!
# `realloc` in either regime

`env_define` grows a frame's two arrays with `realloc`: from `NULL` on the
first growth (`reallocNullRho_spec`, from `reallocNullChgRun_proved`/`reallocNullLocalRun_proved`) and
from a live block afterwards (`reallocRho_spec`, from H4's
`reallocChgRun_proved` and `AllocSpecs.reallocUncounted`). As for
`malloc` (`mallocRho_spec`), one spec covers both regimes; NULL is possible
only uncounted.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym

/-! ## The heap depends on its live list only up to permutation -/

section Congr

open Vsa.Sim.DlHeap in
theorem heapAt_congr {m : Vsa.MemRepr.Mem} {exts exts' : List (Nat × Nat)}
    {re re' : Nat × Nat → Prop} {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hx : ∀ e, e ∈ exts ↔ e ∈ exts') (hr : ∀ e, re e ↔ re' e)
    (h : HeapAt m exts re top brkv chunks bins) : HeapAt m exts' re' top brkv chunks bins :=
  { h with
    live := fun e he => h.live e ((hx e).2 he)
    exact := fun e he hre => h.exact e ((hx e).2 he) ((hr e).2 hre) }

theorem vsaFoot_congr {H H' : List (Nat × Nat)} (hx : ∀ e, e ∈ H ↔ e ∈ H') :
    vsaFoot H = vsaFoot H' := by
  funext a
  unfold vsaFoot
  apply propext
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact .inl h
    · exact .inr ⟨h1, h2, fun e he => h3 e ((hx e).2 he)⟩
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact .inl h
    · exact .inr ⟨h1, h2, fun e he => h3 e ((hx e).1 he)⟩

theorem pHeapAt_congr {m : Vsa.MemRepr.Mem} {H H' : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Vsa.Sim.DlHeap.Chunk} {bins : Nat → List Nat} (hx : ∀ e, e ∈ H ↔ e ∈ H')
    (h : PHeapAt m H top brkv chunks bins) : PHeapAt m H' top brkv chunks bins :=
  { h with heap := { h.heap with heap := heapAt_congr hx hx h.heap.heap } }

theorem pShape_congr {img : Nat → BitVec 8} {H H' : List (Nat × Nat)} (hp : H.Perm H')
    (h : pShape img H) : pShape img H' := by
  obtain ⟨hst, m, top, brkv, chunks, bins, hm, hs⟩ := h
  exact ⟨(hp.map Prod.fst).nodup_iff.1 hst, m, top, brkv, chunks, bins,
    vsaFoot_congr (fun _ => hp.mem_iff) ▸ hm, pHeapAt_congr (fun _ => hp.mem_iff) hs⟩

theorem vsaRoomB_congr {img : Nat → BitVec 8} {H H' : List (Nat × Nat)} {k : Nat}
    (hp : H.Perm H') (h : vsaRoomB img H k) : vsaRoomB img H' k := by
  obtain ⟨hst, m, top, brkv, chunks, bins, hm, hs, hk⟩ := h
  exact ⟨(hp.map Prod.fst).nodup_iff.1 hst, m, top, brkv, chunks, bins,
    vsaFoot_congr (fun _ => hp.mem_iff) ▸ hm, pHeapAt_congr (fun _ => hp.mem_iff) hs, hk⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The heap resource up to a permutation of its live list** (e.g. bringing
a block to the front for `realloc`). A permutation, not only membership: the
shape keeps the live starts distinct (`Starts`). -/
theorem heapRes_congr {ρ : Regime} {H H' : List (Nat × Nat)} (hx : H.Perm H') :
    heapRes (GF := GF) vsaLayoutP vsaRoomB ρ H ⊢ heapRes vsaLayoutP vsaRoomB ρ H' := by
  have hf : heapFoot vsaLayoutP H = heapFoot vsaLayoutP H' := by
    rw [heapFoot_vsaLayoutP, heapFoot_vsaLayoutP]; exact vsaFoot_congr fun _ => hx.mem_iff
  cases ρ with
  | counted k =>
    simp only [heapRes]
    unfold isHeapRoom
    iintro ⟨%img, %⟨hs, hrm⟩, HF⟩
    iexists img
    rw [hf]
    iframe HF
    ipureintro; exact ⟨pShape_congr hx hs, vsaRoomB_congr hx hrm⟩
  | uncounted =>
    simp only [heapRes]
    unfold isHeap
    iintro ⟨%img, %hs, HF⟩
    iexists img
    rw [hf]
    iframe HF
    ipureintro; exact pShape_congr hx hs

end Congr

section Heap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

omit I in
theorem vsaRegsDistinct {saved : List (Nat × BitVec 64)} (hsv : saved.map Prod.fst = vsaSaved) :
    RegsDistinct vsaClob (saved.map Prod.fst) := by
  rw [hsv]; exact RegsDistinct.of_nodup vsaAllocRegs_nodup

omit I in
/-- **`realloc(NULL, n)` in regime `ρ`** (= `malloc(n)`), charged `c` credits when counted. -/
theorem reallocNullRho_spec (hlive : AllocLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (ρ : Regime) (H : List (Nat × Nat)) (n s : BitVec 64)
    (c : Nat) (hc : vsaChg n.toNat c) (saved : List (Nat × BitVec 64))
    (hsv : saved.map Prod.fst = vsaSaved) :
    textOwn (GF := GF) allocText ⊢ fnSpecW Wp reallocEntryBV
      (fun r => iprop(⌜SpOKA s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ 0#64 ∗ clobberedArg vsaClob a1 n ∗
        sp ↦ᵣ s ∗ gp ↦ᵣ□ gpV ∗ savedOwn saved ∗ stackScratch s allocHeadroom ∗
        heapRes vsaLayoutP vsaRoomB (ρ.plus c) H))
      (fun _ => iprop(∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered vsaClob ∗ savedOwn saved ∗
        stackScratch s allocHeadroom ∗ mallocRes ρ H n.toNat p)) := by
  have hd := vsaRegsDistinct hsv
  have hloc := shapeLocal_vsaLayoutP
  unfold fnSpecW clobberedArg
  iintro #Ht
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hsp, hr⟩, Ha0, Hcl, Hsp, #Hgp, Hsv, Hstk, Hh⟩ Hk
  cases ρ with
  | counted k =>
    simp only [Regime.plus_counted, heapRes]
    unfold isHeapRoom
    have hrun : ∀ rv mv, EntryRegs rv reallocEntryBV r 0#64 s saved → rv a1 = n →
        vsaLayoutP.Shape mv H ∧ vsaRoomB mv H (k + c) →
        (∀ a, stackWin s allocHeadroom a → ¬ heapFoot vsaLayoutP H a) →
        ∃ fuel, LocalRun (vsaModel live) [(gp, gpV)] allocText
          (allocRegs vsaClob (saved.map Prod.fst))
          (fun a => stackWin s allocHeadroom a ∨ heapFoot vsaLayoutP H a)
          (fun rv' mv' => RetFrame rv' r s saved ∧
            (FreshBlock vsaLayoutP H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
              vsaLayoutP.Shape mv' (((rv' a0).toNat, n.toNat) :: H) ∧
              vsaRoomB mv' (((rv' a0).toNat, n.toNat) :: H) k)) fuel rv mv := by
      intro rv mv he hargs hs hdj
      rw [hsv]
      exact (reallocNullChgRun_proved live hlive H n s r saved rv mv k c hsv hc hsp hr ⟨he, hargs⟩ hs.1 hs.2
        hdj).imp fun _ h => LocalRun.mono (fun _ _ (he : MallocRoomEnd _ _ _ _ _ _ _ _ _ _) =>
          ⟨he.frame, he.fresh, he.align, he.shape, he.room⟩) _ _ _ h
    iapply allocCallArgs_of_localRun Wp hd (heapFoot vsaLayoutP H)
      (fun img => vsaLayoutP.Shape img H ∧ vsaRoomB img H (k + c))
      (fun img img' h hs => ⟨hloc H img img' h hs.1, roomLocal_vsaRoomB H img img' _ h hs.2⟩)
      (fun cv => cv a1 = n) (fun f g h hf => (h a1 (by decide)).symm.trans hf)
      (fun rv' mv' => FreshBlock vsaLayoutP H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
        vsaLayoutP.Shape mv' (((rv' a0).toNat, n.toNat) :: H) ∧
        vsaRoomB mv' (((rv' a0).toNat, n.toNat) :: H) k)
      (fun p => mallocRes (.counted k) H n.toNat p) ?_
      hrun
    · intro rv' mv' ⟨hf, hal, hsh, hrm⟩
      unfold mallocRes blockOwn
      simp only [heapRes]
      iintro HF
      ihave ⟨HF, Hblk⟩ := heapFoot_carve_gen vsaLayoutP H _ _ hf _ $$ HF
      ihave Hblk := ownSet_forget _ mv' $$ Hblk
      iright
      isplitr
      · ipureintro; exact ⟨hf, hal⟩
      iframe Hblk
      unfold isHeapRoom
      iexists mv'
      iframe HF
      ipureintro; exact ⟨hsh, hrm⟩
    · iframe Ht Hpc Hra Ha0 Hsp Hgp Hcl Hsv Hstk Hh
      iintro Hpc Hra HQ
      iapply Hk $$ Hpc Hra HQ
  | uncounted =>
    simp only [Regime.plus_uncounted, heapRes]
    ihave Hh := isHeap_unfold vsaLayoutP H $$ Hh
    have hrun : ∀ rv mv, EntryRegs rv reallocEntryBV r 0#64 s saved → rv a1 = n →
        vsaLayoutP.Shape mv H →
        (∀ a, stackWin s allocHeadroom a → ¬ heapFoot vsaLayoutP H a) →
        ∃ fuel, LocalRun (vsaModel live) [(gp, gpV)] allocText
          (allocRegs vsaClob (saved.map Prod.fst))
          (fun a => stackWin s allocHeadroom a ∨ heapFoot vsaLayoutP H a)
          (fun rv' mv' => RetFrame rv' r s saved ∧
            ((rv' a0 = 0 ∧ vsaLayoutP.Shape mv' H) ∨
              (FreshBlock vsaLayoutP H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
                vsaLayoutP.Shape mv' (((rv' a0).toNat, n.toNat) :: H)))) fuel rv mv := by
      intro rv mv he hargs hs hdj
      rw [hsv]
      exact (reallocNullLocalRun_proved live hlive H n s r saved rv mv hsv hsp hr ⟨he, hargs⟩ hs hdj).imp
        fun _ h => LocalRun.mono (fun _ _ (he : MallocEnd _ _ _ _ _ _ _ _) =>
          ⟨he.frame, he.result⟩) _ _ _ h
    iapply allocCallArgs_of_localRun Wp hd (heapFoot vsaLayoutP H)
      (fun img => vsaLayoutP.Shape img H) (hloc H)
      (fun cv => cv a1 = n) (fun f g h hf => (h a1 (by decide)).symm.trans hf)
      (fun rv' mv' => (rv' a0 = 0 ∧ vsaLayoutP.Shape mv' H) ∨
        (FreshBlock vsaLayoutP H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
          vsaLayoutP.Shape mv' (((rv' a0).toNat, n.toNat) :: H)))
      (fun p => mallocRes .uncounted H n.toNat p) ?_
      hrun
    · intro rv' mv' hE
      unfold mallocRes blockOwn
      simp only [heapRes]
      rcases hE with ⟨h0, hsh⟩ | ⟨hf, hal, hsh⟩
      · iintro HF
        ileft
        isplitr
        · ipureintro; exact ⟨h0, trivial⟩
        iapply isHeap_fold
        iexists mv'
        iframe HF
        ipureintro; exact hsh
      · iintro HF
        ihave ⟨HF, Hblk⟩ := heapFoot_carve_gen vsaLayoutP H _ _ hf _ $$ HF
        ihave Hblk := ownSet_forget _ mv' $$ Hblk
        iright
        isplitr
        · ipureintro; exact ⟨hf, hal⟩
        iframe Hblk
        iapply isHeap_fold
        iexists mv'
        iframe HF
        ipureintro; exact hsh
    · iframe Ht Hpc Hra Ha0 Hsp Hgp Hcl Hsv Hstk Hh
      iintro Hpc Hra HQ
      iapply Hk $$ Hpc Hra HQ

/-- `realloc(p, nNew)`'s outcome in regime `ρ`: NULL with the old block and
heap unchanged (only uncounted), or a fresh block holding the old contents. -/
def reallocRes (ρ : Regime) (H : List (Nat × Nat)) (p : BitVec 64) (nOld nNew : Nat)
    (old : Nat → BitVec 8) (p' : BitVec 64) : IProp GF :=
  iprop((⌜p' = 0#64 ∧ ρ = .uncounted⌝ ∗ heapRes vsaLayoutP vsaRoomB ρ ((p.toNat, nOld) :: H) ∗
      blockOwnAt p.toNat nOld old) ∨
    (⌜FreshBlock vsaLayoutP H p'.toNat nNew ∧ p'.toNat % 16 = 0⌝ ∗
      heapRes vsaLayoutP vsaRoomB ρ ((p'.toNat, nNew) :: H) ∗
      ∃ v : Nat → BitVec 8, ⌜Copies old v p.toNat p'.toNat nOld⌝ ∗ blockOwnAt p'.toNat nNew v))

omit I in
/-- **`realloc` of a live block in regime `ρ`**, charged `c` credits for the
new size when counted. -/
theorem reallocRho_spec (hlive : AllocLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (ρ : Regime) (H : List (Nat × Nat)) (p : BitVec 64)
    (nOld nNew : Nat) (s : BitVec 64) (old : Nat → BitVec 8) (c : Nat) (hc : vsaChg nNew c)
    (hn : nNew < 2 ^ 64) (saved : List (Nat × BitVec 64)) (hsv : saved.map Prod.fst = vsaSaved) :
    textOwn (GF := GF) allocText ⊢ fnSpecW Wp reallocEntryBV
      (fun r => iprop(⌜SpOKA s ∧ r.toNat % 4 = 0 ∧ nOld < nNew⌝ ∗ a0 ↦ᵣ p ∗
        clobberedArg vsaClob a1 (BitVec.ofNat 64 nNew) ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpV ∗ savedOwn saved ∗
        stackScratch s allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB (ρ.plus c) ((p.toNat, nOld) :: H) ∗
        blockOwnAt p.toNat nOld old))
      (fun _ => iprop(∃ p', a0 ↦ᵣ p' ∗ sp ↦ᵣ s ∗ clobbered vsaClob ∗ savedOwn saved ∗
        stackScratch s allocHeadroom ∗ reallocRes ρ H p nOld nNew old p')) := by
  cases ρ with
  | counted k =>
    iintro #Ht
    ihave #Hs := reallocChgSpec_of_run Wp (reallocChgRun_proved live hlive) shapeLocal_vsaLayoutP
      roomLocal_vsaRoomB vsaAllocRegs_nodup (by decide) H p nOld nNew s old k c saved hsv $$ Ht
    unfold reallocChgSpec fnSpecW
    imodintro
    iintro %r %Φ Hpc Hra ⟨%⟨hsp, hr, hlt⟩, Ha0, Hcl, Hsp, #Hgp, Hsv, Hstk, Hh, Hb⟩ Hk
    simp only [Regime.plus_counted, heapRes]
    iapply Hs $$ %r %Φ Hpc Hra [Ha0 Hcl Hsp Hsv Hstk Hh Hb]
    · isplitr
      · ipureintro; exact ⟨hsp, hr, hlt, hc⟩
      iframe Ha0 Hcl Hsp Hgp Hsv Hstk Hh Hb
    iintro Hpc Hra ⟨%p', Ha0, Hsp, Hcl, Hsv, Hstk, Hpost⟩
    iapply Hk $$ Hpc Hra
    iexists p'
    iframe Ha0 Hsp Hcl Hsv Hstk
    unfold reallocRes reallocChgPost
    simp only [heapRes]
    iright
    iexact Hpost
  | uncounted =>
    iintro #Ht
    ihave #Hs := (allocSpecs live hlive).reallocUncounted.realloc Wp H p nOld nNew s old saved hsv
      $$ Ht
    unfold reallocSpec fnSpecW
    imodintro
    iintro %r %Φ Hpc Hra ⟨%⟨hsp, hr, hlt⟩, Ha0, Hcl, Hsp, #Hgp, Hsv, Hstk, Hh, Hb⟩ Hk
    simp only [Regime.plus_uncounted, heapRes]
    iapply Hs $$ %r %Φ Hpc Hra [Ha0 Hcl Hsp Hsv Hstk Hh Hb]
    · isplitr
      · ipureintro; exact ⟨hsp, hr, hlt, hn⟩
      iframe Ha0 Hcl Hsp Hgp Hsv Hstk Hh Hb
    iintro Hpc Hra ⟨%p', Ha0, Hsp, Hcl, Hsv, Hstk, Hpost⟩
    iapply Hk $$ Hpc Hra
    iexists p'
    iframe Ha0 Hsp Hcl Hsv Hstk
    unfold reallocRes reallocPost
    simp only [heapRes]
    icases Hpost with (⟨%h0, Hh, Hb⟩ | ⟨%hf, Hh, Hb⟩)
    · ileft
      iframe Hh Hb
      ipureintro; exact ⟨h0, trivial⟩
    · iright
      iframe Hh Hb
      ipureintro; exact hf

end Heap

end VsaIris.Interp
