import VsaIris.Vsa.Landing
import VsaIris.Vsa.ErrnoOwn

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Stdio VsaIris.Newlib VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr VsaIris.Newlib.Landing

section Agree

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem memRO_agree (a : Nat) (b b' : BitVec 8) :
    (a ↦ₘ□ b) ∗ (a ↦ₘ□ b') ⊢@{IProp GF} ⌜b = b'⌝ := by
  unfold memPointsTo; exact ghost_map_elem_agree _ _ _ _ _ _

theorem roImg_agree {S : Nat → Prop} {f g : Nat → BitVec 8} :
    roImg (GF := GF) S f ∗ roImg S g ⊢ ⌜∀ k, S k → f k = g k⌝ := by
  unfold roImg
  iintro ⟨#Hf, #Hg⟩
  iintro %k %hk
  ihave Hfk := Hf $$ %k %hk
  ihave Hgk := Hg $$ %k %hk
  ihave %h := memRO_agree k (f k) (g k) $$ [$]
  ipureintro
  exact h

theorem ownImg_cast {a a' n n' : Nat} {img : Nat → BitVec 8} (h : a = a') (hn : n = n') :
    ownImg (GF := GF) (InExt (a, n)) img ⊢ ownImg (InExt (a', n')) img := by
  subst h; subst hn; exact .rfl

omit G in
theorem jmpRO_agree [MachGS hlc GF] [InterpGS GF] (inp : Nat) (jb jb' : Nat → BitVec 8) :
    jmpRO (GF := GF) inp jb ∗ jmpRO inp jb' ⊢
      ⌜∀ k, InExt (inp + interpJmpOff, interpJmpLen) k → jb k = jb' k⌝ := by
  unfold jmpRO; exact roImg_agree

end Agree

def jbWord (inp : Nat) (jb : Nat → BitVec 8) (i : Nat) : BitVec 64 :=
  imgW jb (inp + interpJmpOff + 8 * i)

def jbSaved : List (Nat × Nat) :=
  [(8, 1), (9, 2), (18, 3), (19, 4), (20, 5), (21, 6), (22, 7), (23, 8), (24, 9), (25, 10),
    (26, 11), (27, 12)]

theorem jbWord_congr {inp : Nat} {jb jb' : Nat → BitVec 8}
    (h : ∀ k, InExt (inp + interpJmpOff, interpJmpLen) k → jb k = jb' k) {i : Nat} (hi : i ≤ 13) :
    jbWord inp jb i = jbWord inp jb' i := by
  unfold jbWord imgW
  rw [imgLE_congr (fun j hj => h _ ⟨by omega, by unfold interpJmpOff interpJmpLen; omega⟩)]

structure OomSp (s : BitVec 64) (n : Nat) (s' : BitVec 64) : Prop where
  need : n ≤ s.toNat
  lo : Vsa.Sim.tohostAddr + 16 ≤ s.toNat - n
  fits : s.toNat - n + exitNeed ≤ s'.toNat
  below : s'.toNat ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s'.toNat % 16 = 0

theorem OomSp.mono {sc sp : BitVec 64} {nc np : Nat} {s' : BitVec 64} (h : OomSp sc nc s')
    (hnp : np ≤ sp.toNat) (hlo : Vsa.Sim.tohostAddr + 16 ≤ sp.toNat - np)
    (hle : sp.toNat - np ≤ sc.toNat - nc) (hsc : sc.toNat ≤ sp.toNat) (hhi : sp.toNat ≤ 0x88000000) :
    OomSp sp np s' :=
  ⟨hnp, hlo, by have := h.fits; omega, by have := h.below; omega, hhi, h.align⟩

section Core

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (N : Vsa.RuntimeRepr.NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

def landingRegs (jb : Nat → BitVec 8) : IProp GF :=
  iprop(PC ↦ᵣ jbWord inp jb 0 ∗ ra ↦ᵣ jbWord inp jb 0 ∗ sp ↦ᵣ jbWord inp jb 13 ∗
    (10 : Nat) ↦ᵣ 1#64 ∗ sepL jbSaved (fun p => p.1 ↦ᵣ jbWord inp jb p.2) ∗
    clobbered (argRegs.drop 1) ∗ clobbered tmpRegs)

def landingCore : IProp GF :=
  iprop(∃ (ρ : Regime) (st : Vsa.While.St) (d : Nat) (jb : Nat → BitVec 8),
    worldE (errStr inp) N L Room inp ρ st d ∗ jmpRO inp jb ∗ landingRegs inp jb)

def oomCore (s : BitVec 64) (n : Nat) : IProp GF :=
  iprop(∃ (s' r v0 : BitVec 64) (o : String), ⌜OomSp s n s'⌝ ∗ PC ↦ᵣ exitEntry ∗
    (10 : Nat) ↦ᵣ 1#64 ∗ ra ↦ᵣ r ∗ (8 : Nat) ↦ᵣ v0 ∗ sp ↦ᵣ s' ∗ clobbered (argRegs.drop 1) ∗
    clobbered tmpRegs ∗ sepL (calleeSaved.drop 1) (fun r => iprop(∃ w, r ↦ᵣ w)) ∗
    stdioAt (fun img => StdioOK img ∨ stdioErr img) ∗ errnoOwn ∗ consoleOwn o)

def abortCore (s : BitVec 64) (n : Nat) : IProp GF :=
  iprop(landingCore N L Room inp ∨ oomCore s n)

def abortRes (s : BitVec 64) (n : Nat) : IProp GF :=
  abortAt (abortCore N L Room inp s n) s n

theorem abortCore_mono {sc sp : BitVec 64} {nc np : Nat} (hnp : np ≤ sp.toNat)
    (hlo : Vsa.Sim.tohostAddr + 16 ≤ sp.toNat - np) (hle : sp.toNat - np ≤ sc.toNat - nc)
    (hsc : sc.toNat ≤ sp.toNat) (hhi : sp.toNat ≤ 0x88000000) :
    abortCore N L Room inp sc nc ⊢ abortCore (GF := GF) N L Room inp sp np := by
  unfold abortCore oomCore
  iintro (Hl | ⟨%s', %r, %v0, %o, %hs, H⟩)
  · ileft; iexact Hl
  · iright
    iexists s', r, v0, o
    iframe H
    ipureintro
    exact hs.mono hnp hlo hle hsc hhi

omit I in

theorem wp_abortOom (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hΦ : ∀ o, ⊢ Φ (1, o)) (s : BitVec 64) (n : Nat) :
    oomCore s n ∗ stackScratch s n ∗ gp ↦ᵣ□ gpV ∗ binImg ⊢ Wp.W Φ := by
  unfold oomCore
  iintro ⟨⟨%s', %r, %v0, %o, %hs, Hpc, Ha0, Hra, Hs0, Hsp, Hargs, Htmp, Hsaved, Hstd, Hno, Hcon⟩,
    Hscr, #Hgp, #Himg⟩
  have h1 := hs.need; have h2 := hs.lo; have h3 := hs.fits; have h4 := hs.below
  have h5 := hs.hi; have h6 := hs.align
  unfold exitNeed exitHandlersNeed at h3
  ihave ⟨%cs, Hsaved⟩ := sepL_exists_fn (fun (r : Nat) (w : BitVec 64) => iprop(r ↦ᵣ w))
    (calleeSaved.drop 1) (by decide) $$ Hsaved

  unfold stackScratch
  ihave ⟨-, Hscr⟩ := blockOwn_split (s.toNat - n) n (s'.toNat - 272 - (s.toNat - n))
    (s'.toNat - 272) (n - (s'.toNat - 272 - (s.toNat - n))) (by omega) (by omega) rfl $$ Hscr
  ihave ⟨Hscr, -⟩ := blockOwn_split (s'.toNat - 272) (n - (s'.toNat - 272 - (s.toNat - n))) 272
    s'.toNat (n - (s'.toNat - 272 - (s.toNat - n)) - 272) (by omega) (by omega) rfl $$ Hscr
  have hsp' : SpIn s' exitNeed := by
    unfold Vsa.Sim.tohostAddr at h2
    exact ⟨by unfold exitNeed exitHandlersNeed Vsa.Sim.tohostAddr; omega, by omega, h6⟩
  have he : (1#64 : BitVec 64).toNat < 2 ^ 31 := by decide
  have HA := H.at
  iapply wp_exitCall HA live hlive Wp s' r 1#64 v0 cs o false he hsp'
  unfold argsAt callFrame stackScratch exitNeed exitHandlersNeed
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero,
    List.length_singleton]
  iframe Hpc Hra Hs0 Ha0 Hargs Hsp Hscr Hsaved Htmp Hgp Himg Hcon Hno
  isplitl [Hstd]
  · iapply stdioAt_mono (fun img h => by
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨by simp, h⟩) $$ Hstd
  iintro %o' -
  rw [show (1#64 : BitVec 64).toNat = 1 from rfl]
  iapply hΦ

structure TopLanding (inp : Nat) (sM : BitVec 64) (jb0 imgI imgT : Nat → BitVec 8) : Prop where
  main : MainSp sM
  inp_eq : inp = sM.toNat + 272
  ra : jbWord inp jb0 0 = 0x80004428#64
  sp : jbWord inp jb0 13 = sM - 176#64
  inI : imgW imgI (sM - 176#64).toNat = sM + 272#64
  raI : imgW imgI ((sM - 176#64).toNat + 168) = 0x800045ec#64
  s0I : imgW imgI ((sM - 176#64).toNat + 160) = 0x8001b970#64
  raT : imgW imgT (sM.toNat + 760) = 0x80000038#64

theorem wp_abortLanding (H : NewlibHoles) (hEL : ErrnoOwn.ErrnoLend (GF := GF) L Room)
    (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hΦ : ∀ o, ⊢ Φ (70, o)) (sM : BitVec 64) (jb0 imgI imgT : Nat → BitVec 8)
    (hT : TopLanding inp sM jb0 imgI imgT) :
    landingCore N L Room inp ∗ stackScratch (sM - 176#64) (fprintfNeed - 176) ∗ jmpRO inp jb0 ∗
      ownImg (InExt ((sM - 176#64).toNat, 176)) imgI ∗ ownImg (InExt (sM.toNat + 752, 16)) imgT ∗
      gp ↦ᵣ□ gpV ∗ binImg
    ⊢ Wp.W Φ := by
  have hinp := hT.inp_eq
  unfold landingCore worldE interpCtxE interpCoreE errStr landingRegs wordAt
  iintro ⟨⟨%ρ, %st, %d, %jb, ⟨%Hh, %B, Hheap, -, Hcon, Hstd,
    ⟨⟨%g, -, -, ⟨%dimg, Hd, -⟩, -, -, ⟨%eimg, Herr, %hnul⟩⟩, -⟩, -, -⟩, #Hjb,
    ⟨Hpc, Hra, Hsp, Ha0, Hsaved, Hargs, Htmp⟩⟩, Hscr, #Hjb0, HI, HT, #Hgp, #Himg⟩

  ihave ⟨Herrno, -⟩ := hEL _ _ $$ Hheap
  ihave %hag := jmpRO_agree inp jb jb0 $$ [$]
  have hw : ∀ i, i ≤ 13 → jbWord inp jb i = jbWord inp jb0 i := fun i hi => jbWord_congr hag hi
  rw [hw 0 (by omega), hT.ra, hw 13 (by omega), hT.sp]
  unfold jbSaved
  simp only [sepL_cons, sepL_nil]
  icases Hsaved with ⟨H8, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, -⟩
  ihave Hd := ownImg_cast (a := inp + interpDepthOff) (n := 4) (a' := sM.toNat + 280) (n' := 4)
    (by unfold interpDepthOff; omega) rfl $$ Hd
  ihave Hd := blockOwn_of_ownImg _ _ _ $$ Hd
  ihave Herr := ownImg_cast (a := inp + interpErrOff) (n := interpErrLen) (a' := sM.toNat + 496)
    (n' := 256) (by unfold interpErrOff; omega) rfl $$ Herr
  have herr : ∃ k, k < 256 ∧ eimg (sM.toNat + 496 + k) = 0 := by
    obtain ⟨k, hk, h0⟩ := hnul
    refine ⟨k, hk, ?_⟩
    rw [show sM.toNat + 496 + k = inp + interpErrOff + k by unfold interpErrOff; omega]
    exact h0
  iapply wp_landing H live hlive Wp sM 1#64 0x80004428#64 (fun r => jbWord inp jb (r - 15))
    st.out imgI imgT eimg hT.main (by decide) hT.inI hT.raI hT.s0I hT.raT herr
  simp only [sepL_cons, sepL_nil, Nat.reduceSub]
  iframe Hpc Ha0 Hra Hsp Hargs Htmp Hgp Himg HI Hd Hscr HT Herr Hstd Herrno Hcon
  isplitl [H8 H9 H18 H19 H20 H21 H22]
  · isplitl [H8]
    · iexists _; iexact H8
    isplitl [H9]
    · iexists _; iexact H9
    isplitl [H18]
    · iexists _; iexact H18
    isplitl [H19]
    · iexists _; iexact H19
    isplitl [H20]
    · iexists _; iexact H20
    isplitl [H21]
    · iexists _; iexact H21
    isplitl [H22]
    · iexists _; iexact H22
    iempintro
  iframe H23 H24 H25 H26 H27
  iintro %o'
  iapply hΦ

theorem wp_abort (H : NewlibHoles) (hEL : ErrnoOwn.ErrnoLend (GF := GF) L Room)
    (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hΦ : ∀ e o, e ≠ 0 → ⊢ Φ (e, o)) (sM : BitVec 64) (n : Nat)
    (hn : fprintfNeed - 176 ≤ n) (hns : n ≤ (sM - 176#64).toNat)
    (jb0 imgI imgT : Nat → BitVec 8) (hT : TopLanding inp sM jb0 imgI imgT) :
    abortRes N L Room inp (sM - 176#64) n ∗ jmpRO inp jb0 ∗
      ownImg (InExt ((sM - 176#64).toNat, 176)) imgI ∗ ownImg (InExt (sM.toNat + 752, 16)) imgT ∗
      gp ↦ᵣ□ gpV ∗ binImg
    ⊢ Wp.W Φ := by
  unfold abortRes
  iintro ⟨HA, #Hjb0, HI, HT, #Hgp, #Himg⟩
  ihave ⟨HC, Hscr⟩ := abortAt_elim _ _ _ $$ HA
  unfold abortCore
  icases HC with (Hl | Ho)
  · ihave ⟨-, Hscr⟩ := stackScratch_narrow hns hn $$ Hscr
    iapply wp_abortLanding N L Room inp H hEL live hlive Wp (fun o => hΦ 70 o (by decide)) sM jb0
      imgI imgT hT
    iframe Hl Hscr Hjb0 HI HT Hgp Himg
  · iapply wp_abortOom H live hlive Wp (fun o => hΦ 1 o (by decide)) (sM - 176#64) n
    iframe Ho Hscr Hgp Himg

end Core

end VsaIris.Interp
