import VsaIris.Vsa.Landing

/-!
# The abort resource and its continuation (INTERP_DESIGN.md §4.2, H5)

`abortRes s n = abortAt (abortCore s n) s n` is what the abort branch of
`evalSpecP_body`/`execSpecP_body` (`fnSpecAbort`) hands the continuation. An
abort is one of two machine states:

* **the `longjmp` landing** (`landingCore`): `runtime_error` has written a C
  string to `err_msg` and `longjmp(in->on_error, 1)` restored `ra`, `s0`–`s11`
  and `sp` from the `jmp_buf` (`landingRegs`), with `a0 = 1` and the PC at the
  restored `ra`; the world is intact with `err_msg` a C string (`errStr`);
* **`exit(1)`'s entry after an out-of-memory `fwrite`** (`oomCore s n`): `a0 = 1`,
  newlib's data after a `stderr` write, and a stack pointer `s'` with room for
  `exit` inside the site's region `[s - n, s)` (`OomSp`).

The second depends on the site's region, and is monotone in it
(`abortCore_mono`): a callee's `abortRes` widens to its caller's
(`abortRes_widen`), so F3's `wp_callArmAbort` applies at `Core := abortCore s n`
of the caller through `fnSpecAbort_mono`.

**The continuation** (`wp_abort`): at `interp_run`'s `jal exec_stmt`
(`sp = sM - 176`, `main`'s frame at `sM`), the abort resource and what
`interp_run`'s own proof owns (its frame, `main`'s saved pair, the `jmp_buf` it
wrote) finish the run with exit code 70 (landing) or 1 (out of memory), for
either WP. With `Φ := fun v => ⌜v.1 ≠ 0⌝` and F1's `Inst.vsa_adequacyP_nonzero`
this is `Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Stdio VsaIris.Newlib VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr VsaIris.Newlib.Landing

/-! ## The landing registers -/

section Agree

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem memRO_agree (a : Nat) (b b' : BitVec 8) :
    (a ↦ₘ□ b) ∗ (a ↦ₘ□ b') ⊢@{IProp GF} ⌜b = b'⌝ := by
  unfold memPointsTo; exact ghost_map_elem_agree _ _ _ _ _ _

/-- Two read-only views of the same bytes agree. -/
theorem roImg_agree {S : Nat → Prop} {f g : Nat → BitVec 8} :
    roImg (GF := GF) S f ∗ roImg S g ⊢ ⌜∀ k, S k → f k = g k⌝ := by
  unfold roImg
  iintro ⟨#Hf, #Hg⟩
  iintro %k %hk
  ihave Hfk := Hf $$ %k %hk
  ihave Hgk := Hg $$ %k %hk
  ihave %h := memRO_agree k (f k) (g k) $$ [Hfk Hgk]
  · iframe Hfk Hgk
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

/-- Word `i` of the `jmp_buf` image: `ra` (0), `s0`–`s11` (1–12), `sp` (13)
(`setjmp` @`0x80006ffc`). -/
def jbWord (inp : Nat) (jb : Nat → BitVec 8) (i : Nat) : BitVec 64 :=
  imgW jb (inp + interpJmpOff + 8 * i)

/-- `s0`–`s11` and their `jmp_buf` slots. -/
def jbSaved : List (Nat × Nat) :=
  [(8, 1), (9, 2), (18, 3), (19, 4), (20, 5), (21, 6), (22, 7), (23, 8), (24, 9), (25, 10),
    (26, 11), (27, 12)]

/-- The stack pointer of an out-of-memory `exit(1)`: `exit` fits inside the
site's region `[s - n, s)`. -/
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

/-- The registers after `longjmp(in->on_error, 1)`: `ra`, `s0`–`s11`, `sp`
restored from the `jmp_buf` image `jb`, `a0 = 1`, the PC at the restored `ra`
(`longjmp` ends in `ret`), the other argument and temporary registers at any
value. -/
def landingRegs (jb : Nat → BitVec 8) : IProp GF :=
  iprop(PC ↦ᵣ jbWord inp jb 0 ∗ ra ↦ᵣ jbWord inp jb 0 ∗ sp ↦ᵣ jbWord inp jb 13 ∗
    (10 : Nat) ↦ᵣ 1#64 ∗ sepL jbSaved (fun p => p.1 ↦ᵣ jbWord inp jb p.2) ∗
    clobbered (argRegs.drop 1) ∗ clobbered tmpRegs)

/-- **The `longjmp` landing**: some world with `err_msg` a C string, the
`jmp_buf` read-only at `jb`, and the landing registers read off `jb`. -/
def landingCore : IProp GF :=
  iprop(∃ (ρ : Regime) (st : Vsa.While.St) (d : Nat) (jb : Nat → BitVec 8),
    worldE (errStr inp) N L Room inp ρ st d ∗ jmpRO inp jb ∗ landingRegs inp jb)

/-- **`exit(1)`'s entry after an out-of-memory `fwrite`**, with room for
`exit` inside the site's region. -/
def oomCore (s : BitVec 64) (n : Nat) : IProp GF :=
  iprop(∃ (s' r v0 : BitVec 64) (o : String), ⌜OomSp s n s'⌝ ∗ PC ↦ᵣ exitEntry ∗
    (10 : Nat) ↦ᵣ 1#64 ∗ ra ↦ᵣ r ∗ (8 : Nat) ↦ᵣ v0 ∗ sp ↦ᵣ s' ∗ clobbered (argRegs.drop 1) ∗
    clobbered tmpRegs ∗ sepL (calleeSaved.drop 1) (fun r => iprop(∃ w, r ↦ᵣ w)) ∗
    stdioAt (fun img => StdioOK img ∨ stdioErr img) ∗ consoleOwn o)

/-- What an abort hands the continuation, besides the stack. -/
def abortCore (s : BitVec 64) (n : Nat) : IProp GF :=
  iprop(landingCore N L Room inp ∨ oomCore s n)

/-- **The abort resource** at a site with `sp = s` owning `n` bytes below. -/
def abortRes (s : BitVec 64) (n : Nat) : IProp GF :=
  abortAt (abortCore N L Room inp s n) s n

/-- The abort core of a callee is its caller's. -/
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

/-- **A callee's abort resource widens to its caller's core**: what
`fnSpecAbort_mono` needs to call a child whose spec carries `abortRes` with
F3's `wp_callArmAbort` at the caller's `Core := abortCore s n`. -/
theorem abortRes_widen {sc sp : BitVec 64} {nc np : Nat} (hnp : np ≤ sp.toNat)
    (hlo : Vsa.Sim.tohostAddr + 16 ≤ sp.toNat - np) (hle : sp.toNat - np ≤ sc.toNat - nc)
    (hsc : sc.toNat ≤ sp.toNat) (hhi : sp.toNat ≤ 0x88000000) :
    abortRes N L Room inp sc nc ⊢ abortAt (GF := GF) (abortCore N L Room inp sp np) sc nc := by
  unfold abortRes
  iintro H
  ihave ⟨HC, Hs⟩ := abortAt_elim _ _ _ $$ H
  ihave HC := abortCore_mono N L Room inp hnp hlo hle hsc hhi $$ HC
  iapply abortAt_intro
  iframe HC Hs

/-! ## The continuation -/

omit I in
/-- **Out of memory**: `exit(1)` from the site's region. -/
theorem wp_abortOom (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hΦ : ∀ o, ⊢ Φ (1, o)) (s : BitVec 64) (n : Nat) :
    oomCore s n ∗ stackScratch s n ∗ gp ↦ᵣ□ gpV ∗ binImg ⊢ Wp.W Φ := by
  unfold oomCore
  iintro ⟨⟨%s', %r, %v0, %o, %hs, Hpc, Ha0, Hra, Hs0, Hsp, Hargs, Htmp, Hsaved, Hstd, Hcon⟩,
    Hscr, #Hgp, #Himg⟩
  have h1 := hs.need; have h2 := hs.lo; have h3 := hs.fits; have h4 := hs.below
  have h5 := hs.hi; have h6 := hs.align
  unfold exitNeed exitHandlersNeed at h3
  ihave ⟨%cs, Hsaved⟩ := sepL_exists_fn (fun (r : Nat) (w : BitVec 64) => iprop(r ↦ᵣ w))
    (calleeSaved.drop 1) (by decide) $$ Hsaved
  -- `exit`'s stack inside the site's region
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
  iapply wp_exitCall HA live hlive Wp s' r 1#64 v0 cs o he hsp'
  unfold argsAt callFrame stackScratch exitNeed exitHandlersNeed
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero,
    List.length_singleton]
  iframe Hpc Hra Hs0 Ha0 Hargs Hsp Hscr Hsaved Htmp Hgp Himg Hstd Hcon
  iintro %o'
  rw [show (1#64 : BitVec 64).toNat = 1 from rfl]
  iapply hΦ

/-- What `interp_run`'s own proof knows at its `jal exec_stmt`: `main`'s frame
at `sM`, `in = sM + 272`, the `jmp_buf` it wrote with `setjmp` (`ra` its
`setjmp` return, `sp` its frame), its frame's spills (`in`, `main`'s link,
`main`'s `s0`) and `main`'s saved `ra` (`crt0`'s link). -/
structure TopLanding (inp : Nat) (sM : BitVec 64) (jb0 imgI imgT : Nat → BitVec 8) : Prop where
  main : MainSp sM
  inp_eq : inp = sM.toNat + 272
  ra : jbWord inp jb0 0 = 0x80004428#64
  sp : jbWord inp jb0 13 = sM - 176#64
  inI : imgW imgI (sM - 176#64).toNat = sM + 272#64
  raI : imgW imgI ((sM - 176#64).toNat + 168) = 0x800045ec#64
  s0I : imgW imgI ((sM - 176#64).toNat + 160) = 0x8001b970#64
  raT : imgW imgT (sM.toNat + 760) = 0x80000038#64

/-- **The landing**: `interp_run` returns 1, `main` prints `err_msg` and exits
70. -/
theorem wp_abortLanding (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hΦ : ∀ o, ⊢ Φ (70, o)) (sM : BitVec 64) (jb0 imgI imgT : Nat → BitVec 8)
    (hT : TopLanding inp sM jb0 imgI imgT) :
    landingCore N L Room inp ∗ stackScratch (sM - 176#64) (fprintfNeed - 176) ∗ jmpRO inp jb0 ∗
      ownImg (InExt ((sM - 176#64).toNat, 176)) imgI ∗ ownImg (InExt (sM.toNat + 752, 16)) imgT ∗
      gp ↦ᵣ□ gpV ∗ binImg
    ⊢ Wp.W Φ := by
  have hinp := hT.inp_eq
  unfold landingCore worldE interpCtxE interpCoreE errStr landingRegs wordAt
  iintro ⟨⟨%ρ, %st, %d, %jb, ⟨%Hh, %B, -, -, Hcon, Hstd,
    ⟨⟨%g, -, -, ⟨%dimg, Hd, -⟩, -, -, ⟨%eimg, Herr, %hnul⟩⟩, -⟩, -, -⟩, #Hjb,
    ⟨Hpc, Hra, Hsp, Ha0, Hsaved, Hargs, Htmp⟩⟩, Hscr, #Hjb0, HI, HT, #Hgp, #Himg⟩
  ihave %hag := jmpRO_agree inp jb jb0 $$ [Hjb Hjb0]
  · iframe Hjb Hjb0
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
  iapply wp_landing H.at live hlive Wp sM 1#64 0x80004428#64 (fun r => jbWord inp jb (r - 15))
    st.out imgI imgT eimg hT.main (by decide) hT.inI hT.raI hT.s0I hT.raT herr
  simp only [sepL_cons, sepL_nil, Nat.reduceSub]
  iframe Hpc Ha0 Hra Hsp Hargs Htmp Hgp Himg HI Hd Hscr HT Herr Hstd Hcon
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

/-- **The abort continuation at `interp_run`'s `jal exec_stmt`**, for either
WP: `interp_run` calls `exec_stmt` with `sp = sM - 176` (its frame below
`main`'s at `sM`) lending `n` bytes; whatever abort comes back — the
`longjmp` landing or the out-of-memory `exit(1)` — together with what
`interp_run`'s own proof keeps (the `jmp_buf` it wrote, its frame, `main`'s
saved pair) ends the run with a nonzero exit code. With
`Φ := fun v => ⌜v.1 ≠ 0⌝` and `Inst.vsa_adequacyP_nonzero` this is
`Halts c out e ∧ e ≠ 0` for every run that aborts. -/
theorem wp_abort (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
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
    iapply wp_abortLanding N L Room inp H live hlive Wp (fun o => hΦ 70 o (by decide)) sM jb0
      imgI imgT hT
    iframe Hl Hscr Hjb0 HI HT Hgp Himg
  · iapply wp_abortOom H live hlive Wp (fun o => hΦ 1 o (by decide)) (sM - 176#64) n
    iframe Ho Hscr Hgp Himg

end Core

end VsaIris.Interp
