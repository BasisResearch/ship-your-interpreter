import VsaIris.Vsa.ExitH.RunIdle
import VsaIris.Vsa.ExitH.RunWritten
import VsaIris.Vsa.ExitH.RunIdleU
import VsaIris.Vsa.ExitH.RunWrittenU
import VsaIris.Vsa.Newlib

/-!
# `exit`'s newlib interior in the Iris logic (lane N4)

`exitHandlers_spec` proves `Newlib.exitHandlersSpec` (formerly the hole
`IrisHoles.newlib.exitHandlers`) for every post-write state `Ierr` from which
the close path runs (`CloseReady`), both WPs. The run is `exitIdle_chain` or
`exitWritten_chain` (`RunIdle`/`RunWritten`, generated), by `wp_localRunW`:

* registers: the entry values (`exitRv`) over `iRegs`, split as `exit`'s
  call frame (`iRegs_exit`);
* bytes: `exitS s`, newlib's exclusive data, `errno` and the 256 bytes of
  scratch, glued into one owned set at one image (`exitImg`). The scratch is
  off newlib's data by ownership (`ownSet_disj`), which places it below
  `__sglue` or above `__bss_end` (`place_of_disj`);
* facts: `CloseReady`'s canonical memory gives `CloseMt` and `stderr`'s
  state (`Loads.lean`).

The run prints nothing, in either `stderr` state.
-/

namespace VsaIris.Newlib.ExitH

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Sym VsaIris.MallocFast

/-! ## Pure facts -/

theorem stdioText_img :
    stdioText.all (fun p => decide (textDom p.1) && textByte p.1 == p.2) = true := by
  decide +kernel

theorem stdioText_mem : ∀ p ∈ stdioText, textDom p.1 ∧ textByte p.1 = p.2 := by
  intro p hp
  have h := List.all_eq_true.1 stdioText_img p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem stdioText_live {live : Nat → Prop} (h : CodeLive live) : ∀ p ∈ stdioText, live p.1 :=
  fun p hp => h _ (stdioText_mem p hp).1

/-- The scratch window off newlib's exclusive data and `errno` lies below
`__sglue` or above `__bss_end`: every gap of their union is shorter than 256
bytes, so a window meeting the range meets a byte of the union (one of the
chunk ends, or its own top byte). -/
theorem place_of_disj {s : Nat}
    (hd : ∀ a, s - 256 ≤ a ∧ a < s → ¬ ((stdioFoot a ∧ ¬ impureW a) ∨ errnoFoot a)) :
    s ≤ 0x8001b520 ∨ 0x8001c168 + 256 ≤ s := by
  have c := fun a => hd a
  have h0 := c (s - 1)
  have h1 := c 0x8001b520
  have h2 := c 0x8001b537
  have h3 := c 0x8001b53c
  have h4 := c 0x8001b95f
  have h5 := c 0x8001b978
  have h6 := c 0x8001b98f
  have h7 := c 0x8001b9b0
  have h8 := c 0x8001ba17
  have h9 := c 0x8001ba68
  have h10 := c 0x8001c167
  simp only [stdioFoot, InRange, impureW, errnoFoot, not_or, not_and, Decidable.not_not,
    Decidable.imp_iff_not_or] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  omega

/-- The saved registers `exit`'s interior keeps (`s1`–`s11`). -/
abbrev savedX : List Nat := [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem savedX_eq : savedX = calleeSaved.drop 1 := rfl

/-- The end of the run, for the Iris continuation: at `mv a0,s0` with `sp`,
`s0` and `s1`–`s11` as at the entry. -/
def ExitQ (s e : BitVec 64) (cs : Nat → BitVec 64) (rv : Nat → BitVec 64) (_ : Nat → BitVec 8) :
    Prop :=
  rv 32 = 0x80004788#64 ∧ rv 2 = s ∧ rv 8 = e ∧ ∀ x ∈ savedX, rv x = cs x

/-- **`exit`'s interior as one symbolic run**, from either `stderr` state. -/
theorem exit_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {R : Nat → BitVec 64}
    {Mt : Mem} {s e : BitVec 64} {cs : Nat → BitVec 64} {o : Bool} (hs : ExitSp s) (h2 : R 2 = s)
    (h8 : R 8 = e) (h11 : R 11 = 0#64) (hsv : ∀ x ∈ savedX, R x = cs x)
    (hC : CloseMt (consoleFlagsV o) Mt)
    (hE : ErrIdleMt Mt ∨ ErrWrittenMt Mt) :
    NW live ∅ [] (exitS s) (ExitQ s e cs) 0x80004778#64 R Mt := by
  have hin : ∀ x ∈ savedX, x ∈ iRegs ∧ x ≠ VsaIris.PC := by decide
  have hk : ∀ R' Mt', ExitEnd R s e R' →
      NW live ∅ [] (exitS s) (ExitQ s e cs) 0x80004788#64 R' Mt' :=
    fun R' Mt' hend => swp_done fun rv mv hm =>
      ⟨hm.pc, (hm.regs 2 (by decide) (by decide)).trans hend.sp,
        (hm.regs 8 (by decide) (by decide)).trans hend.s0,
        fun x hx => (hm.regs x (hin x hx).1 (hin x hx).2).trans ((hend.saved x hx).trans (hsv x hx))⟩
  cases o <;> rcases hE with hE | hE
  · exact exitIdleU_chain hlive hs h2 h8 h11 hC hE hk
  · exact exitWrittenU_chain hlive hs h2 h8 h11 hC hE hk
  · exact exitIdle_chain hlive hs h2 h8 h11 hC hE hk
  · exact exitWritten_chain hlive hs h2 h8 h11 hC hE hk

/-! ## The owned bytes at one image -/

open Classical in
/-- newlib's data at `img`, `errno` at `fe`, the scratch at `fs`. -/
noncomputable def exitImg (img fe fs : Nat → BitVec 8) (a : Nat) : BitVec 8 :=
  if stdioFoot a then img a else if errnoFoot a then fe a else fs a

/-- The addresses of `exitS s`. -/
def exitList (s : BitVec 64) : List Nat :=
  dataList ++ List.range' 0x8001ba08 4 ++ List.range' (s.toNat - 256) 256

/-- A tracking memory holding the glued image on `exitList s`. -/
noncomputable def exitMt (img fe fs : Nat → BitVec 8) (s : BitVec 64) : Mem :=
  fillMem (exitImg img fe fs) (exitList s)

theorem imgM_exitMt {img fe fs : Nat → BitVec 8} {s : BitVec 64} {a : Nat} (h : a ∈ exitList s) :
    imgM (exitMt img fe fs s) a = exitImg img fe fs a := by
  unfold imgM exitMt; rw [fillMem_get _ h]; rfl

theorem mem_exitList {s : BitVec 64} {a : Nat} (h : exitS s a) : a ∈ exitList s := by
  unfold exitList
  simp only [List.mem_append, List.mem_range']
  rcases h with ⟨h, _⟩ | h | h
  · exact .inl (.inl (mem_dataList h))
  · exact .inl (.inr ⟨a - 0x8001ba08, by omega, by omega⟩)
  · exact .inr ⟨a - (s.toNat - 256), by omega, by omega⟩

theorem exitMt_stdio {img fe fs : Nat → BitVec 8} {s : BitVec 64} :
    ∀ a, stdioFoot a → imgM (exitMt img fe fs s) a = img a := by
  intro a ha
  rw [imgM_exitMt (by unfold exitList; simp only [List.mem_append]; exact .inl (.inl (mem_dataList ha)))]
  unfold exitImg; rw [if_pos ha]

/-! ## Registers -/

/-- The register values at the entry: `a0 = s0 = e`, `a1 = 0`, the other
arguments at `fa`, the temporaries at `ft`, `s1`–`s11` at `cs`. -/
def exitRv (r s e : BitVec 64) (ft fa cs : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k = 32 then 0x80004778#64 else if k = 1 then r else if k = 2 then s else if k = 8 then e
  else if k = 10 then e else if k = 11 then 0#64 else if k ∈ tmpRegs then ft k
  else if k ∈ argRegs.drop 2 then fa k else cs k

theorem iRegs_perm :
    iRegs.Perm (32 :: 1 :: 2 :: 8 :: 10 :: 11 :: (tmpRegs ++ (argRegs.drop 2 ++ savedX))) := by
  decide

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem regEq {k : Nat} {a b : BitVec 64} (h : a = b) : k ↦ᵣ a ⊢@{IProp GF} k ↦ᵣ b := by
  rw [h]

theorem clobbered_args2 :
    clobbered (GF := GF) argRegs ⊣⊢
      iprop((∃ v, (10 : Nat) ↦ᵣ v) ∗ (∃ v, (11 : Nat) ↦ᵣ v) ∗ clobbered (argRegs.drop 2)) := by
  unfold clobbered argRegs; simp only [sepL_cons, List.drop]; exact .rfl

/-- `iRegs` in `exit`'s call-frame groups. -/
theorem iRegs_exit (rv : Nat → BitVec 64) :
    sepL (GF := GF) iRegs (fun k => k ↦ᵣ rv k) ⊣⊢
      iprop(VsaIris.PC ↦ᵣ rv 32 ∗ VsaIris.ra ↦ᵣ rv 1 ∗ VsaIris.sp ↦ᵣ rv 2 ∗ (8 : Nat) ↦ᵣ rv 8 ∗
        (10 : Nat) ↦ᵣ rv 10 ∗ (11 : Nat) ↦ᵣ rv 11 ∗ sepL tmpRegs (fun k => k ↦ᵣ rv k) ∗
        sepL (argRegs.drop 2) (fun k => k ↦ᵣ rv k) ∗ sepL savedX (fun k => k ↦ᵣ rv k)) := by
  refine (sepL_perm _ iRegs_perm).trans ?_
  simp only [sepL_cons]
  refine sep_congr_right (sep_congr_right (sep_congr_right (sep_congr_right (sep_congr_right
    (sep_congr_right ?_)))))
  exact (sepL_append _ _ _).trans (sep_congr_right (sepL_append _ _ _))

/-- **`exit`'s newlib interior** (`Newlib.exitHandlersSpec`), for either WP,
from any post-write state the close path runs from. -/
theorem exitHandlers_spec {Ierr : (Nat → BitVec 8) → Prop}
    (hI : ∀ img, Ierr img → CloseReady img) (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF) (quiet : Bool)
    (hcl : CodeLive live) (hs : SpIn s exitHandlersNeed) :
    ⊢ exitHandlersSpec Ierr live Wp s e r cs o Φ quiet := by
  have hlo := hs.lo; have hhi := hs.hi; have hal := hs.align
  unfold exitHandlersNeed tohostAddr at hlo
  unfold exitHandlersSpec callFrame argsAt stackScratch exitHandlersNeed exitHandlersPC
    exitHandlersEnd
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero, Nat.reduceAdd,
    List.length_cons, List.length_nil]
  iintro ⟨Hpc, Hra, Hs0, ⟨⟨Ha0, Ha1, -⟩, Hargs⟩, Hstd, Herr, Hcon,
    ⟨Hsp, Hscr, Hsaved, Htmp, #Hgp, #Himg⟩, Hk⟩
  unfold stdioAt errnoOwn blockOwn
  icases Hstd with ⟨%img, %⟨hP, himp⟩, Hx, #Hro⟩
  ihave ⟨%fe, Herr⟩ := ownSet_fn errnoFoot $$ Herr
  ihave ⟨%fs, Hscr⟩ := ownSet_fn _ $$ Hscr
  -- the scratch is off newlib's data and `errno`
  ihave ⟨⟨Hx, Hscr⟩, %hd1⟩ := keep_pure (ownSet_disj _ _ _ _) $$ [Hx Hscr]
  · iframe Hx Hscr
  ihave ⟨⟨Herr, Hscr⟩, %hd2⟩ := keep_pure (ownSet_disj _ _ _ _) $$ [Herr Hscr]
  · iframe Herr Hscr
  have hplace : s.toNat ≤ 0x8001b520 ∨ 0x8001c168 + 256 ≤ s.toNat :=
    place_of_disj fun a ha hu => by
      have hw : InExt (s.toNat - 256, 256) a := by unfold InExt; simp only; omega
      rcases hu with hu | hu
      · exact hd1 a hu hw
      · exact hd2 a hu hw
  have hsp : ExitSp s := ⟨by omega, hhi, hal, hplace⟩
  -- one owned set at one image, on a tracking memory
  let Mt := exitMt img fe fs s
  have hwin : ∀ a, InExt (s.toNat - 256, 256) a → ¬ stdioFoot a ∧ ¬ errnoFoot a := by
    intro a ha; unfold InExt at ha; simp only at ha
    unfold stdioFoot errnoFoot InRange; omega
  have hSx : ∀ a, stdioExcl a → imgM Mt a = img a := fun a ha => exitMt_stdio a ha.1
  have hSe : ∀ a, errnoFoot a → imgM Mt a = fe a := fun a ha => by
    have hn : ¬ stdioFoot a := by unfold errnoFoot InRange at ha; unfold stdioFoot InRange; omega
    rw [imgM_exitMt (mem_exitList (.inr (.inl (by unfold errnoFoot InRange at ha; omega))))]
    unfold exitImg; rw [if_neg hn, if_pos ha]
  have hSs : ∀ a, InExt (s.toNat - 256, 256) a → imgM Mt a = fs a := fun a ha => by
    have hw := hwin a ha
    rw [imgM_exitMt (mem_exitList (.inr (.inr (by unfold InExt at ha; simp only at ha; omega))))]
    unfold exitImg; rw [if_neg hw.1, if_neg hw.2]
  ihave Hx := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ imgM Mt a))
    (fun a ha => by rw [hSx a ha]) $$ Hx
  ihave Herr := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ imgM Mt a))
    (fun a ha => by rw [hSe a ha]) $$ Herr
  ihave Hscr := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ imgM Mt a))
    (fun a ha => by rw [hSs a ha]) $$ Hscr
  ihave HS := ownSet_join _ _ _ (fun a (h1 : stdioExcl a) (h2 : errnoFoot a) => by
    unfold errnoFoot InRange at h2; unfold stdioExcl stdioFoot InRange at h1; omega) $$ [Hx Herr]
  · iframe Hx Herr
  ihave HS := ownSet_join _ _ _ (fun a (h1 : stdioExcl a ∨ errnoFoot a) h2 => by
    rcases h1 with h1 | h1
    · exact (hwin a h2).1 h1.1
    · exact (hwin a h2).2 h1) $$ [HS Hscr]
  · iframe HS Hscr
  ihave HS := ownSet_iff (T := exitS s) _ (fun a => by
    unfold exitS stdioExcl impureW errnoFoot InRange InExt stdioFoot InRange; simp only
    constructor <;> intro h <;> omega) $$ HS
  -- the fields the run reads
  have hcr : CloseReady img := hP.elim StdioOK.closeReady (fun h => hI _ h.2)
  obtain ⟨_, hcr⟩ := hcr
  obtain ⟨hcc, hst⟩ := hcr (fillMem img dataList)
    (fun _ ha => fillMem_get (l := dataList) img (mem_dataList ha))
  have hC := closeMt_of hcc exitMt_stdio (Mt := Mt)
  have hE : ErrIdleMt Mt ∨ ErrWrittenMt Mt :=
    hst.imp (fun h => errIdleMt_of h exitMt_stdio) (fun h => errWrittenMt_of h exitMt_stdio)
  -- the registers
  ihave ⟨%ft, Htmp⟩ := clobbered_fn tmpRegs (by decide) $$ Htmp
  ihave ⟨%fa, Hargs⟩ := clobbered_fn (argRegs.drop 2) (by decide) $$ Hargs
  let rv := exitRv r s e ft fa cs
  have hrun := exit_run (stdioText_live hcl) hsp (R := rv) (Mt := Mt) (e := e) (cs := cs) rfl rfl rfl
    (fun x hx => by simp only [savedX, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
                    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    hC hE
  obtain ⟨n, hn⟩ := hrun
  have hL := hn rv (imgM Mt) ⟨rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
  iapply wp_localRunW Wp n rv (imgM Mt) hL
  isplitl []
  · unfold roOwn
    simp only [roR, sepL_cons, sepL_nil, dataOf, List.map_nil, List.append_nil]
    isplitl []
    · isplitl []
      · rw [show (MallocFast.gpV : BitVec 64) = Newlib.gpV from rfl]; iexact Hgp
      · iempintro
    · iapply binImg_sepL stdioText (fun p hp => .inl (stdioText_mem p hp)) $$ Himg
  isplitl [Hpc Hra Hsp Hs0 Ha0 Ha1 Htmp Hargs Hsaved]
  · iapply (iRegs_exit rv).2
    rw [show rv 32 = 0x80004778#64 from rfl, show rv 1 = r from rfl, show rv 2 = s from rfl,
      show rv 8 = e from rfl, show rv 10 = e from rfl, show rv 11 = 0#64 from rfl]
    iframe Hpc Hra Hsp Hs0 Ha0 Ha1
    have htmp : sepL (GF := GF) tmpRegs (fun k => iprop(k ↦ᵣ rv k)) =
        sepL tmpRegs (fun k => iprop(k ↦ᵣ ft k)) := sepL_congr fun k hk => by
      simp only [tmpRegs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hargs : sepL (GF := GF) (argRegs.drop 2) (fun k => iprop(k ↦ᵣ rv k)) =
        sepL (argRegs.drop 2) (fun k => iprop(k ↦ᵣ fa k)) := sepL_congr fun k hk => by
      simp only [argRegs, List.drop, List.mem_cons, List.not_mem_nil, _root_.or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hsv : sepL (GF := GF) savedX (fun k => iprop(k ↦ᵣ rv k)) =
        sepL savedX (fun k => iprop(k ↦ᵣ cs k)) := sepL_congr fun k hk => by
      simp only [savedX, List.mem_cons, List.not_mem_nil, _root_.or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [htmp, hargs, hsv, ← savedX_eq] at *
    iframe Htmp Hargs Hsaved
  iframe HS
  -- the end: `mv a0,s0`
  unfold runKontW
  iintro %rv' %mv' %⟨h32, h2', h8', hsv'⟩ Hregs HS
  ihave ⟨Hpc, Hra, Hsp, Hs0, Ha0, Ha1, Htmp, Hargs, Hsaved⟩ := (iRegs_exit rv').1 $$ Hregs
  ihave Hpc' := regEq h32 $$ Hpc
  ihave Hsp' := regEq h2' $$ Hsp
  ihave Hs0' := regEq h8' $$ Hs0
  have hsvE : sepL (GF := GF) savedX (fun k => iprop(k ↦ᵣ rv' k)) =
      sepL savedX (fun k => iprop(k ↦ᵣ cs k)) := sepL_congr fun k hk => by rw [hsv' k hk]
  rw [hsvE] at *
  -- the owned bytes, back in three parts
  ihave HS := ownSet_iff (T := fun a => (stdioExcl a ∨ errnoFoot a) ∨ InExt (s.toNat - 256, 256) a)
    _ (fun a => by
      unfold exitS stdioExcl impureW errnoFoot InRange InExt stdioFoot InRange; simp only
      constructor <;> intro h <;> omega) $$ HS
  ihave ⟨HS, Hw⟩ := ownSet_unglue _ _ _ (fun a (h1 : stdioExcl a ∨ errnoFoot a) h2 => by
    rcases h1 with h1 | h1
    · exact (hwin a h2).1 h1.1
    · exact (hwin a h2).2 h1) $$ HS
  ihave ⟨Hx, He⟩ := ownSet_unglue _ _ _ (fun a (h1 : stdioExcl a) (h2 : errnoFoot a) => by
    unfold errnoFoot InRange at h2; unfold stdioExcl stdioFoot InRange at h1; omega) $$ HS
  ihave He := ownSet_forget errnoFoot mv' $$ He
  ihave Hw := ownSet_forget _ mv' $$ Hw
  iapply Hk $$ Hpc' [Hra] Hs0' [Ha0 Ha1 Hargs] [Hx] He [Hcon] [Hsp' Hw Hsaved Htmp]
  · iexists rv' 1; iexact Hra
  · iapply clobbered_args2.2
    ihave Hargs := clobbered_of_fn (argRegs.drop 2) rv' $$ Hargs
    iframe Hargs
    isplitl [Ha0]
    · iexists rv' 10; iexact Ha0
    · iexists rv' 11; iexact Ha1
  · open Classical in
    iexists fun a => if impureW a then img a else mv' a
    iframe Hro
    isplitr
    · ipureintro
      exact ⟨trivial, fun a ha => by simp only [ha, ite_true]; exact himp a ha⟩
    iapply ownSet_congr (fun a (ha : stdioExcl a) => by simp only [ha.2, ite_false]) $$ Hx
  · iexists ""
    rw [String.append_empty]
    iframe Hcon
    · ipureintro; exact fun _ => rfl
  · rw [← savedX_eq]
    iframe Hsp' Hw Hsaved Hgp Himg
    iapply clobbered_of_fn tmpRegs rv' $$ Htmp

end Wp

end VsaIris.Newlib.ExitH

namespace VsaIris.Newlib

/-- **The newlib statements from the assumed ones**: `exit`'s interior is
proved (`ExitH.exitHandlers_spec`) at `StdioErrOK`, a state the close path
runs from (`StdioErrOK.closeReady`); `fprintf`'s proof (`fprintf_ok`, above
this file) and `snprintf`'s (`Sym.snprintf_ok`) are passed in. -/
theorem NewlibCore.full (h : NewlibCore) (hf : FprintfProved) (hs : SnprintfProved) : NewlibHoles :=
  { toNewlibCoreAt := h
    snprintf := hs
    fprintf := hf
    exitHandlers := fun live Wp s e r cs o Φ quiet hcl hs =>
      ExitH.exitHandlers_spec (fun _ h => Stdio.StdioErrOK.closeReady h) live Wp s e r cs o Φ quiet hcl hs }

end VsaIris.Newlib
