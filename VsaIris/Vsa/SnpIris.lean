import VsaIris.Vsa.SnpView
import VsaIris.Vsa.Stdout.OutSpec
import VsaIris.Vsa.NewlibOut
import VsaIris.Interp.NewlibCall
import VsaIris.Interp.HelperRun
import VsaIris.Vsa.StrlenOwned

/-!
# From a `snprintf` run to its Iris specification (lane N2)

A `snprintf` hole is a `fnSpecW` in H5's calling convention: argument
registers (`argsAt`), the destination block (`blockOwn`), newlib's data
(`stdioOwn`), the call frame (`callFrame`: `sp`, 1024 bytes of stack, the
callee-saved registers, the temporaries, `gp`, the image), and read-only
inputs. `snpSpec_of_run` turns a run over `SnpW` from the entry into that
specification: the registers become one register file (`call_regs`), the
owned bytes one set `snpS` (`snpBytes`, every disjointness from ownership),
the read-only cells the run's code and data view (`roOwn_snp`), and the end
state gives the bytes back (`snpBytes_back`) with the destination's image.

The register and read-only-disjointness lemmas are lane N1's
(`Vsa/Stdout/OutSpec.lean`: `call_regs`, `ownSet_ro_off`).
-/

namespace VsaIris.Sym

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open VsaIris.Inst


/-! ## The owned bytes -/

/-- The owned byte sets of a `snprintf` call, pairwise disjoint (from their
ownership). -/
structure SnpDisj (s dst n : Nat) : Prop where
  stdio_stack : ∀ a, stdioExcl a → ¬ InExt (s - 1024, 1024) a
  stdio_dst : ∀ a, stdioExcl a → ¬ InExt (dst, n) a
  stack_dst : ∀ a, InExt (s - 1024, 1024) a → ¬ InExt (dst, n) a

theorem snpS_iff {s dst n : Nat} (hs : 1024 ≤ s) (a : Nat) :
    snpS s dst n a ↔ stdioExcl a ∨ InExt (s - 1024, 1024) a ∨ InExt (dst, n) a := by
  unfold snpS stdioExcl impureW InExt snpNeed
  constructor
  · rintro (h | ⟨h1, h2⟩ | h)
    · exact .inl h
    · exact .inr (.inl ⟨h1, by simp only; omega⟩)
    · exact .inr (.inr h)
  · rintro (h | ⟨h1, h2⟩ | h)
    · exact .inl h
    · exact .inr (.inl ⟨h1, by simp only at h2; omega⟩)
    · exact .inr (.inr h)

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The owned bytes of a `snprintf` call**, at one tracking memory:
newlib's exclusive data at its image, the stack and the destination at any
values. -/
theorem snpBytes (img : Nat → BitVec 8) (s dst n : Nat) (hs : 1024 ≤ s) :
    iprop(ownSet (GF := GF) stdioExcl (fun a => a ↦ₘ img a) ∗ blockOwn (s - 1024) 1024 ∗
      blockOwn dst n) ⊢
      ∃ Mt : Mem, ownSet (snpS s dst n) (fun a => a ↦ₘ imgM Mt a) ∗
        ⌜(∀ a, stdioExcl a → imgM Mt a = img a) ∧ SnpDisj s dst n⌝ := by
  classical
  iintro ⟨Hx, Hst, Hd⟩
  unfold blockOwn
  ihave ⟨%fs, Hst⟩ := ownSet_fn _ $$ Hst
  ihave ⟨%fd, Hd⟩ := ownSet_fn _ $$ Hd
  ihave %d1 := ownSet_disj _ _ _ _ $$ [Hx Hst]
  · iframe Hx Hst
  ihave %d2 := ownSet_disj _ _ _ _ $$ [Hx Hd]
  · iframe Hx Hd
  ihave %d3 := ownSet_disj _ _ _ _ $$ [Hst Hd]
  · iframe Hst Hd
  let f : Nat → BitVec 8 := fun a =>
    if stdioExcl a then img a else if InExt (s - 1024, 1024) a then fs a else fd a
  ihave Hx := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a)) (fun a ha => by simp [f, ha]) $$ Hx
  ihave Hst := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a))
    (fun a ha => by simp [f, ha, show ¬ stdioExcl a from fun h => d1 a h ha]) $$ Hst
  ihave Hd := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a))
    (fun a ha => by simp [f, show ¬ stdioExcl a from fun h => d2 a h ha,
      show ¬ InExt (s - 1024, 1024) a from fun h => d3 a h ha]) $$ Hd
  ihave H := ownSet_join _ _ _ (fun a h1 h2 => d3 a h1 h2) $$ [Hst Hd]
  · iframe Hst Hd
  ihave H := ownSet_join stdioExcl (fun a => InExt (s - 1024, 1024) a ∨ InExt (dst, n) a) _
    (fun a (h1 : stdioExcl a) (h2 : InExt (s - 1024, 1024) a ∨ InExt (dst, n) a) => by
      rcases h2 with h2 | h2
      · exact d1 a h1 h2
      · exact d2 a h1 h2) $$ [Hx H]
  · iframe Hx H
  ihave H := ownSet_iff (T := snpS s dst n) _ (fun a => (snpS_iff hs a).symm) $$ H
  ihave ⟨%M, H, %hM⟩ := ownSet_trackedAt _ f $$ H
  iexists M
  iframe H
  ipureintro
  refine ⟨fun a ha => ?_, ⟨d1, d2, d3⟩⟩
  rw [hM a ((snpS_iff hs a).2 (.inl ha))]
  simp [f, ha]

/-- **The owned bytes back**: newlib's data, the stack, the destination. -/
theorem snpBytes_back (mv : Nat → BitVec 8) (s dst n : Nat) (hs : 1024 ≤ s)
    (D : SnpDisj s dst n) :
    ownSet (GF := GF) (snpS s dst n) (fun a => a ↦ₘ mv a) ⊢
      ownSet stdioExcl (fun a => a ↦ₘ mv a) ∗ blockOwn (s - 1024) 1024 ∗
        ownImg (InExt (dst, n)) mv := by
  iintro H
  ihave ⟨Hx, H⟩ := ownSet_split _ stdioExcl _ $$ H
  ihave ⟨Hd, Hs⟩ := ownSet_split _ (InExt (dst, n)) _ $$ H
  isplitl [Hx]
  · iapply ownSet_iff _ (fun a => ⟨fun h => h.2, fun h => ⟨(snpS_iff hs a).2 (.inl h), h⟩⟩) $$ Hx
  isplitl [Hs]
  · unfold blockOwn
    ihave Hs := ownSet_forget _ mv $$ Hs
    iapply ownSet_iff _ (fun a => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => by
      rcases (snpS_iff hs a).1 h1 with h | h | h
      · exact absurd h h2
      · exact h
      · exact absurd h h3,
      fun h => ⟨⟨(snpS_iff hs a).2 (.inr (.inl h)), fun h' => D.stdio_stack a h' h⟩,
        D.stack_dst a h⟩⟩) $$ Hs
  · iapply ownSet_iff _ (fun a => ⟨fun h => h.2, fun h => ⟨⟨(snpS_iff hs a).2 (.inr (.inr h)),
      fun h' => D.stdio_dst a h' h⟩, h⟩⟩) $$ Hd

end Own

/-! ## The specification from a run -/

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- What a `snprintf` run's end state keeps: `ra`, `sp` and the
callee-saved registers, and every byte outside its stack and the
destination. -/
structure SnpRet (R : Nat → BitVec 64) (Mt : Mem) (s dst n : Nat) (R' : Nat → BitVec 64)
    (Mt' : Mem) : Prop where
  ra : R' 1 = R 1
  sp : R' 2 = R 2
  saved : ∀ x ∈ Newlib.calleeSaved, R' x = R x
  frame : ∀ a, ¬ (s - 1024 ≤ a ∧ a < s) → ¬ (dst ≤ a ∧ a < dst + n) → imgM Mt' a = imgM Mt a

/-- **A `snprintf` call from its run.** The run, from the call's registers
and owned bytes (newlib's data at a `StdioOK` image, the locale words as
loads), reads the data view the read-only input `Rr` supplies and ends in
`SnpRet` with the destination's image satisfying `Post`. -/
theorem snpSpec_of_run {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live))
    {Pre Post' : BitVec 64 → IProp GF} {args : List (BitVec 64)} {Rr : IProp GF}
    {s : BitVec 64} {dst n : Nat} {cs : Nat → BitVec 64} {X : Type} {f : X → Nat → BitVec 8}
    {DA : X → List Nat} {Pf : X → Prop} {Post : (Nat → BitVec 8) → Prop}
    (hlen : args.length ≤ 8) (hs : 1024 ≤ s.toNat)
    (hP : ∀ r, Pre r ⊢ iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt args ∗ blockOwn dst n ∗ Rr ∗ stdioOwn ∗
      callFrame s snprintfNeed Newlib.calleeSaved cs))
    (hQ : ∀ r, iprop(clobbered argRegs ∗ (∃ img, ownImg (InExt (dst, n)) img ∗ ⌜Post img⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed Newlib.calleeSaved cs) ⊢ Post' r)
    (hdata : iprop(Rr ∗ binImg ∗ impureRO) ⊢
      ∃ x, sepL (dataOf (viewMem (f x) (DA x)) (DA x)) (fun p => p.1 ↦ₘ□ p.2) ∗ ⌜Pf x⌝)
    (hrun : ∀ (x : X) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (R : Nat → BitVec 64)
      (Mt : Mem), Pf x → (R 1).toNat % 4 = 0 → R 2 = s →
      (∀ i (h : i < args.length), R (10 + i) = args[i]) → LocaleMt Mt →
      (∀ a ∈ DA x, ¬ snpS s.toNat dst n a) → SnpDisj s.toNat dst n →
      (∀ R' Mt', SnpRet R Mt s.toNat dst n R' Mt' → Post (imgM Mt') →
        SnpW live (viewMem (f x) (DA x)) (DA x) (snpS s.toNat dst n) Q (R 1) R' Mt') →
      SnpW live (viewMem (f x) (DA x)) (DA x) (snpS s.toNat dst n) Q 0x80005c44#64 R Mt) :
    ⊢ fnSpecW Wp snprintfEntry Pre Post' := by
  classical
  unfold fnSpecW
  unfold snprintfEntry
  iintro !> %r %Φ Hpc Hra HP Hk
  ihave ⟨%hal, Hargs, Hbuf, HR, Hstd, Hcf⟩ := hP r $$ HP
  unfold callFrame
  icases Hcf with ⟨Hsp, Hst, Hcs, Ht, #Hgp, #Himg⟩
  ihave ⟨%R, Hregs, %⟨h32, h1, h2, hargs, hcs⟩⟩ := call_regs 0x80005c44#64 r s args cs hlen $$
    [Hpc Hra Hargs Hsp Hcs Ht]
  · iframe Hpc Hra Hargs Hsp Hcs Ht
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs R).1 $$ Hregs
  rw [h32]
  unfold stdioOwn stdioAt
  icases Hstd with ⟨%img, %⟨hok, himp⟩, Hx, #Himp⟩
  ihave ⟨%x, #Hd, %hPf⟩ := hdata $$ [HR]
  · iframe HR Himg Himp
  unfold stackScratch snprintfNeed
  ihave ⟨%Mt, HS, %⟨hMt, D⟩⟩ := snpBytes img s.toNat dst n hs $$ [Hx Hst Hbuf]
  · iframe Hx Hst Hbuf
  ihave ⟨⟨HS, -⟩, %hoff⟩ := keep_pure (ownSet_ro_off (snpS s.toNat dst n) (imgM Mt)
    (dataOf (viewMem (f x) (DA x)) (DA x))) $$ [HS]
  · iframe HS Hd
  have hoff' : ∀ a ∈ DA x, ¬ snpS s.toNat dst n a := fun a ha =>
    hoff (a, _) (List.mem_map_of_mem (f := fun a => (a, imgM (viewMem (f x) (DA x)) a)) ha)
  let F : IProp GF := iprop((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Post' r -∗ Wp.W Φ) ∗ gp ↦ᵣ□ Newlib.gpV ∗
    binImg ∗ impureRO)
  have hrun' := hrun x (RunK Wp Φ F (snpS s.toNat dst n)) R Mt hPf (by rw [h1]; exact hal) h2 hargs
    (localeMt_of hok fun a h1 h2 => hMt a ⟨h1, h2⟩) hoff' D fun R' Mt' K hpost => ?_
  · iapply wp_swpF Wp (F := F) hrun'
    isplitl []
    · iapply roOwn_snp _ (viewMem (f x) (DA x)) (DA x) .rfl $$ [Hd]
      iframe Hgp Himg Hd
    unfold ms
    dsimp only [F]
    iframe Hpc Hra Hregs HS Hk Hgp Himg Himp
  -- the end of the run
  refine swp_closeF Wp ?_
  unfold ms
  dsimp only [F]
  iintro ⟨⟨Hk, #Hgp, #Himg, #Himp⟩, Hpc, Hra, Hregs, HS⟩
  ihave ⟨Hsp, Hcs, Ht, Ha⟩ := (regFile_newlib R').1 $$ Hregs
  ihave ⟨Hx, Hst, Hd⟩ := snpBytes_back (imgM Mt') s.toNat dst n hs D $$ HS
  rw [h1, K.ra, h1]
  iapply Hk $$ Hpc Hra
  iapply hQ r
  isplitl [Ha]
  · iapply clobbered_of_fn _ R' $$ Ha
  isplitl [Hd]
  · iexists imgM Mt'
    iframe Hd
    ipureintro; exact hpost
  isplitl [Hx]
  · unfold stdioOwn stdioAt
    iexists img
    isplitr
    · ipureintro; exact ⟨hok, himp⟩
    iframe Himp
    iapply ownSet_congr (fun a (ha : stdioExcl a) => by
      rw [K.frame a (fun h => D.stdio_stack a ha ⟨h.1, by simp only; omega⟩)
        (fun h => D.stdio_dst a ha h), hMt a ha]) $$ Hx
  · unfold callFrame stackScratch snprintfNeed
    rw [K.sp, h2]
    iframe Hsp Hst Hgp Himg
    isplitl [Hcs]
    · rw [sepL_congr (Φ := fun x => iprop(x ↦ᵣ R' x)) (Ψ := fun x => iprop(x ↦ᵣ cs x))
        (l := Newlib.calleeSaved) (fun z hz => by rw [K.saved z hz, hcs z hz])]
      iexact Hcs
    · iapply clobbered_of_fn _ R' $$ Ht


/-- **A `snprintf` call whose run reads owned bytes.** Like `snpSpec_of_run`,
but the read-only input `Rr` opens to a data view whose addresses `DAro` are
read-only and `DAown` owned (`O`): the run is proved with both in the view,
then `LocalRun.promote` makes the owned ones part of the run's owned set, and
hands them back unchanged. The end state is a pure predicate. -/
theorem snpSpec_of_runO {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live))
    {Pre Post' : BitVec 64 → IProp GF} {args : List (BitVec 64)} {Rr : IProp GF}
    {s : BitVec 64} {dst n : Nat} {cs : Nat → BitVec 64} {X : Type} {f : X → Nat → BitVec 8}
    {DAro DAown : X → List Nat} {O : X → Nat → Prop} {Pf : X → Prop}
    {Post : (Nat → BitVec 8) → Prop}
    (hloc : ∀ g g', (∀ a, InExt (dst, n) a → g a = g' a) → Post g → Post g')
    (hlen : args.length ≤ 8) (hs : 1024 ≤ s.toNat)
    (hP : ∀ r, Pre r ⊢ iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt args ∗ blockOwn dst n ∗ Rr ∗ stdioOwn ∗
      callFrame s snprintfNeed Newlib.calleeSaved cs))
    (hQ : ∀ r, iprop(clobbered argRegs ∗ (∃ img, ownImg (InExt (dst, n)) img ∗ ⌜Post img⌝) ∗ Rr ∗
      stdioOwn ∗ callFrame s snprintfNeed Newlib.calleeSaved cs) ⊢ Post' r)
    (hdata : iprop(Rr ∗ binImg ∗ impureRO) ⊢
      ∃ x, sepL (dataOf (viewMem (f x) (DAro x ++ DAown x)) (DAro x)) (fun p => p.1 ↦ₘ□ p.2) ∗
        ownSet (O x) (fun a => a ↦ₘ f x a) ∗ ⌜Pf x ∧ ∀ a, O x a ↔ a ∈ DAown x⌝ ∗
        (ownSet (O x) (fun a => a ↦ₘ f x a) -∗ Rr))
    (hrun : ∀ (x : X) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (R : Nat → BitVec 64)
      (Mt : Mem), Pf x → (R 1).toNat % 4 = 0 → R 2 = s →
      (∀ i (h : i < args.length), R (10 + i) = args[i]) → LocaleMt Mt →
      (∀ a ∈ DAro x ++ DAown x, ¬ snpS s.toNat dst n a) → SnpDisj s.toNat dst n →
      (∀ R' Mt', SnpRet R Mt s.toNat dst n R' Mt' → Post (imgM Mt') →
        SnpW live (viewMem (f x) (DAro x ++ DAown x)) (DAro x ++ DAown x) (snpS s.toNat dst n) Q
          (R 1) R' Mt') →
      SnpW live (viewMem (f x) (DAro x ++ DAown x)) (DAro x ++ DAown x) (snpS s.toNat dst n) Q
        0x80005c44#64 R Mt) :
    ⊢ fnSpecW Wp snprintfEntry Pre Post' := by
  classical
  unfold fnSpecW snprintfEntry
  iintro !> %r %Φ Hpc Hra HP Hk
  ihave ⟨%hal, Hargs, Hbuf, HR, Hstd, Hcf⟩ := hP r $$ HP
  unfold callFrame
  icases Hcf with ⟨Hsp, Hst, Hcs, Ht, #Hgp, #Himg⟩
  ihave ⟨%R, Hregs, %⟨h32, h1, h2, hargs, hcs⟩⟩ := call_regs 0x80005c44#64 r s args cs hlen $$
    [Hpc Hra Hargs Hsp Hcs Ht]
  · iframe Hpc Hra Hargs Hsp Hcs Ht
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs R).1 $$ Hregs
  rw [h32]
  unfold stdioOwn stdioAt
  icases Hstd with ⟨%img, %⟨hok, himp⟩, Hx, #Himp⟩
  ihave ⟨%x, #Hd, HO, %⟨hPf, hO⟩, Hback⟩ := hdata $$ [HR]
  · iframe HR Himg Himp
  unfold stackScratch snprintfNeed
  ihave ⟨%Mt, HS, %⟨hMt, D⟩⟩ := snpBytes img s.toNat dst n hs $$ [Hx Hst Hbuf]
  · iframe Hx Hst Hbuf
  ihave ⟨⟨HS, -⟩, %hoff1⟩ := keep_pure (ownSet_ro_off (snpS s.toNat dst n) (imgM Mt)
    (dataOf (viewMem (f x) (DAro x ++ DAown x)) (DAro x))) $$ [HS]
  · iframe HS Hd
  ihave %hoff2 := ownSet_disj _ _ _ _ $$ [HO HS]
  · iframe HO HS
  -- the run's data view
  let Dt := viewMem (f x) (DAro x ++ DAown x)
  have hoff : ∀ a ∈ DAro x ++ DAown x, ¬ snpS s.toNat dst n a := fun a ha => by
    rcases List.mem_append.mp ha with h | h
    · exact hoff1 (a, _) (List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) h)
    · exact fun hs' => hoff2 a ((hO a).2 h) hs'
  -- the end state, as a pure predicate
  let Qe : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop := fun rv mv =>
    rv 32 = r ∧ rv 1 = r ∧ rv 2 = s ∧ (∀ z ∈ Newlib.calleeSaved, rv z = cs z) ∧
      (∀ a, stdioExcl a → mv a = img a) ∧ Post mv
  have hsw : SnpW live Dt (DAro x ++ DAown x) (snpS s.toNat dst n) Qe 0x80005c44#64 R Mt :=
    hrun x Qe R Mt hPf (by rw [h1]; exact hal) h2 hargs (localeMt_of hok fun a h1 h2 => hMt a ⟨h1, h2⟩) hoff D
      fun R' Mt' K hpost => swp_done fun rv mv hm => by
        have hk : ∀ z, z ∈ nRegs → z ≠ 32 → rv z = R' z := fun z hz hne => hm.regs z hz hne
        refine ⟨hm.pc.trans h1, ?_, ?_, fun z hz => ?_, fun a ha => ?_, ?_⟩
        · rw [hk 1 (by decide) (by decide), K.ra, h1]
        · rw [hk 2 (by decide) (by decide), K.sp, h2]
        · have hz' : z ∈ nRegs ∧ z ≠ 32 := by
            simp only [Newlib.calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [hk z hz'.1 hz'.2, K.saved z hz, hcs z hz]
        · rw [hm.img a ((snpS_iff hs a).2 (.inl ha)),
            K.frame a (fun h => D.stdio_stack a ha ⟨h.1, by simp only; omega⟩)
              (fun h => D.stdio_dst a ha h), hMt a ha]
        · exact hloc _ _ (fun a ha => (hm.img a ((snpS_iff hs a).2 (.inr (.inr ha)))).symm) hpost
  obtain ⟨N, hN⟩ := hsw
  let rv : Nat → BitVec 64 := fun z => if z = 32 then 0x80005c44#64 else R z
  let mv : Nat → BitVec 8 := fun a => if a ∈ DAown x then f x a else imgM Mt a
  have hsnp : ∀ a, snpS s.toNat dst n a → a ∉ DAown x := fun a h1 h2 => hoff a (List.mem_append_right _ h2) h1
  have hrun1 := hN rv mv ⟨by simp [rv, VsaIris.PC],
    fun z _ hne => by simp only [rv, show z ≠ 32 from by simpa [VsaIris.PC] using hne, ite_false],
    fun a ha => by simp only [mv, if_neg (hsnp a ha)]⟩
  have et : snpText ++ dataOf Dt (DAro x ++ DAown x) =
      (snpText ++ dataOf Dt (DAro x)) ++ dataOf Dt (DAown x) := by
    simp only [dataOf, List.map_append, List.append_assoc]
  rw [et] at hrun1
  have hrun2 := LocalRun.promote (t1 := snpText ++ dataOf Dt (DAro x)) (t2 := dataOf Dt (DAown x))
    (fun p hp => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact fun h => hsnp a h ha) N rv mv hrun1 (fun p hp => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      simp only [mv, if_pos ha]
      exact (imgM_viewMem (List.mem_append_right _ ha)).symm)
  have hS' : ∀ a, (snpS s.toNat dst n a ∨ ∃ p ∈ dataOf Dt (DAown x), p.1 = a) ↔
      (snpS s.toNat dst n a ∨ O x a) := fun a => by
    rw [hO a]
    constructor
    · rintro (h | ⟨p, hp, rfl⟩)
      · exact .inl h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp; exact .inr hb
    · rintro (h | h)
      · exact .inl h
      · exact .inr ⟨(a, imgM Dt a), List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) h, rfl⟩
  iapply wp_localRunW Wp N rv mv hrun2
  isplitl []
  · iapply roOwn_snp _ Dt (DAro x) .rfl $$ [Hd]
    iframe Hgp Himg Hd
  isplitl [Hpc Hra Hregs]
  · iapply (sepL_iRegs rv).2
    have e1 : rv 32 = 0x80005c44#64 := by simp [rv]
    have e2 : rv 1 = R 1 := by simp [rv]
    have e3 : regFile (GF := GF) rv = regFile R := by
      unfold regFile
      exact sepL_congr fun z hz => by
        have : z ≠ 32 := fun e => by subst e; revert hz; decide
        simp only [rv, this, ite_false]
    rw [e1, e2, e3]
    iframe Hpc Hra Hregs
  isplitl [HS HO]
  · ihave HS := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ mv a))
      (fun a ha => by simp only [mv, if_neg (hsnp a ha)]) $$ HS
    ihave HO := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ mv a))
      (fun a ha => by simp only [mv, if_pos ((hO a).1 ha)]) $$ HO
    ihave H := ownSet_join _ _ _ (fun a h1 h2 => hoff2 a h2 h1) $$ [HS HO]
    · iframe HS HO
    iapply ownSet_iff _ (fun a => (hS' a).symm) $$ H
  -- the end of the run
  iintro %rv' %mv' %⟨⟨e32, e1, e2, ecs, estd, hpost⟩, hback⟩ Hregs HS
  ihave HS := ownSet_iff _ hS' $$ HS
  ihave ⟨HS, HO⟩ := ownSet_split _ (snpS s.toNat dst n) _ $$ HS
  ihave HS := ownSet_iff (T := snpS s.toNat dst n) _ (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ HS
  ihave HO := ownSet_iff (T := O x) _ (fun a => ⟨fun h => h.1.resolve_left h.2,
    fun h => ⟨.inr h, fun h' => hoff2 a h h'⟩⟩) $$ HO
  ihave HO := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f x a)) (fun a ha => by
    have := hback (a, imgM Dt a) (List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) ((hO a).1 ha))
    simp only at this
    rw [this, imgM_viewMem (List.mem_append_right _ ((hO a).1 ha))]) $$ HO
  ihave HR := Hback $$ HO
  ihave ⟨Hx, Hst, Hd⟩ := snpBytes_back mv' s.toNat dst n hs D $$ HS
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs rv').1 $$ Hregs
  ihave ⟨Hsp, Hcs, Ht, Ha⟩ := (regFile_newlib rv').1 $$ Hregs
  rw [e32, e1]
  iapply Hk $$ Hpc Hra
  iapply hQ r
  isplitl [Ha]
  · iapply clobbered_of_fn _ rv' $$ Ha
  isplitl [Hd]
  · iexists mv'
    iframe Hd
    ipureintro; exact hpost
  iframe HR
  isplitl [Hx]
  · unfold stdioOwn stdioAt
    iexists img
    isplitr
    · ipureintro; exact ⟨hok, himp⟩
    iframe Himp
    iapply ownSet_congr (fun a (ha : stdioExcl a) => by rw [estd a ha]) $$ Hx
  · unfold callFrame stackScratch snprintfNeed
    rw [e2]
    iframe Hsp Hst Hgp Himg
    isplitl [Hcs]
    · rw [sepL_congr (Φ := fun z => iprop(z ↦ᵣ rv' z)) (Ψ := fun z => iprop(z ↦ᵣ cs z))
        (l := Newlib.calleeSaved) (fun z hz => by rw [ecs z hz])]
      iexact Hcs
    · iapply clobbered_of_fn _ rv' $$ Ht

end Spec

end VsaIris.Sym
