import VsaIris.Interp.NewlibCall
import VsaIris.Vsa.NewlibOut

/-!
# `value_print` (lane H2)

The kind table at `0x80019f10` selects the arm; every arm tail-calls newlib
(`fwrite`, `fputs`, `fprintf` on `stdout`, `IrisHoles.out`), so the run ends
at the newlib entry and the callee returns to `value_print`'s caller
(`ms_tailNewlib`). The console grows by `Value.display`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The frame of `value_print`'s run: the value's meaning and display
resources, the image, newlib's data, the console, the stack, the code, and
the return continuation. -/
def Fvp (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (p s r : BitVec 64) (v : Value) (st : Store) (o : String) (rv : Nat → BitVec 64) (Ma : Mem) :
    IProp GF :=
  iprop(valImg N (imgM Ma) p.toNat v ∗ dispRes st v ∗ binImg ∗ stdioOwn ∗ consoleOwn o ∗
    stackScratch s printNeed ∗ codeRes ∗
    (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
      (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
        (valAt N p.toNat v ∗ stdioOwn ∗ consoleOwn (o ++ v.display st) ∗ stackAt s printNeed)) -∗
      Wp.W Φ))

/-- **Closing a `value_print` run at a newlib tail call.** -/
theorem vp_swp_close (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {v : Value} {st : Store} {o : String}
    {rv R : Nat → BitVec 64} {M Ma : Mem} {entry : BitVec 64} {P Q : BitVec 64 → IProp GF}
    {vs : List (BitVec 64)} {Xr : IProp GF} [Persistent Xr] {frag : String} {need : Nat}
    (hspec : ⊢ fnSpecW Wp entry P Q)
    (hlen : vs.length ≤ 8) (hvs : ∀ i (h : i < vs.length), R (10 + i) = vs[i]) (hs : R 2 = s)
    (h1 : R 1 = r) (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → R x = rv x)
    (hsg : StackGeom s printNeed) (hneed : need ≤ printNeed)
    (hP : ∀ r, iprop(argsAt vs ∗ (Xr ∗ stdioOwn ∗ consoleOwn o) ∗
      callFrame s need Newlib.calleeSaved R) ⊢ P r)
    (hQ : ∀ r, Q r ⊢ iprop(clobbered argRegs ∗ (stdioOwn ∗ consoleOwn (o ++ frag)) ∗
      callFrame s need Newlib.calleeSaved R))
    (hX : valImg N (imgM Ma) p.toNat v ∗ dispRes st v ∗ binImg ⊢ Xr)
    (hfrag : frag = v.display st)
    (hMa : ∀ x, InExt (p.toNat, 24) x → imgM M x = imgM Ma x) :
    IW live ∅ [] (InExt (p.toNat, 24)) (RunK Wp Φ (Fvp Wp Φ N p s r v st o rv Ma) (InExt (p.toNat, 24)))
      entry R M := by
  apply swp_closeF
  unfold Fvp codeRes roOwn
  simp only [sepL_cons, sepL_nil]
  iintro ⟨⟨#Hv, #Hd, #Himg, Hstd, Hcon, Hst, ⟨⟨#Hgp, -⟩, -⟩, Hk⟩, Hms⟩
  ihave #Hsp := hspec
  ihave #HX := hX $$ [Hv Hd Himg]
  · iframe Hv Hd Himg
  iapply ms_tailNewlib Wp hlen hvs hs hsg.le hneed hP hQ
  iframe Hsp Hms Hst Himg
  isplitl [Hstd Hcon]
  · iframe HX Hstd Hcon
  isplitr
  · rw [show Newlib.gpV = MallocFast.gpV from rfl]; iexact Hgp
  iintro Hpc Hra Hregs ⟨Hstd, Hcon⟩ HS Hst
  rw [h1]
  iapply Hk $$ Hpc Hra
  icases Hregs with ⟨%rv', Hregs, %hk'⟩
  iexists rv'
  iframe Hregs
  isplitr
  · ipureintro; exact fun x hx hc => (hk' x hx hc).trans (hkeep x hx hc)
  rw [← hfrag]
  iframe Hstd Hcon
  isplitl [HS]
  · iapply valAt_of_img
    iframe Hv
    iapply ownSet_congr (fun x hx => by rw [hMa x hx]) $$ HS
  · unfold stackAt
    iframe Hst
    ipureintro; exact hsg

/-- The pure context of a `value_print` run. -/
structure VpCtx (live : Nat → Prop) (p s r : BitVec 64) (rv : Nat → BitVec 64) (M Ma : Mem) : Prop where
  hlive : ∀ q ∈ interpText, live q.1
  hcl : CodeLive live
  hal : r.toNat % 4 = 0
  h10 : rv 10 = p
  h11 : rv 11 = stdoutFile
  h2 : rv 2 = s
  hg : SlotGeom p
  hsg : StackGeom s printNeed
  hMa : ∀ x, InExt (p.toNat, 24) x → imgM M x = imgM Ma x

/-- The goal of a `value_print` run. -/
abbrev VpGoal (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (p s r : BitVec 64) (v : Value) (st : Store) (o : String) (rv : Nat → BitVec 64) (M Ma : Mem) :
    Prop :=
  IW live ∅ [] (InExt (p.toNat, 24)) (RunK Wp Φ (Fvp Wp Φ N p s r v st o rv Ma) (InExt (p.toNat, 24)))
    valuePrintPC (upd rv 1 r) M

omit I in
/-- An `outSpec` precondition from H5's calling convention. -/
theorem outSpec_P {vs : List (BitVec 64)} {Xr : IProp GF} {o : String} {s : BitVec 64} {need : Nat}
    {cs : Nat → BitVec 64} (r : BitVec 64) :
    iprop(argsAt vs ∗ (Xr ∗ stdioOwn ∗ consoleOwn o) ∗ callFrame s need Newlib.calleeSaved cs) ⊢
      (fun (_ : BitVec 64) => iprop(argsAt vs ∗ Xr ∗ stdioOwn ∗ consoleOwn o ∗
        callFrame s need Newlib.calleeSaved cs)) r := by
  dsimp only
  iintro ⟨Ha, ⟨Hx, Hs, Hc⟩, Hf⟩
  iframe Ha Hx Hs Hc Hf

omit I in
theorem outSpec_Q {o frag : String} {s : BitVec 64} {need : Nat} {cs : Nat → BitVec 64} (r : BitVec 64) :
    (fun (_ : BitVec 64) => iprop(clobbered argRegs ∗ stdioOwn ∗ consoleOwn (o ++ frag) ∗
        callFrame s need Newlib.calleeSaved cs)) r ⊢
      iprop(clobbered (GF := GF) argRegs ∗ (stdioOwn ∗ consoleOwn (o ++ frag)) ∗
        callFrame s need Newlib.calleeSaved cs) := by
  dsimp only
  iintro ⟨Ha, Hs, Hc, Hf⟩
  iframe Ha Hs Hc Hf

theorem str_null : "null".toList = ['n', 'u', 'l', 'l'] := by decide

/-- `null`: `fwrite("null", 1, 4, stdout)`. -/
theorem vp_null (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma)
    (hk : ldv .lw M p.toNat = 0#64) (hku : ldv .lwu M p.toNat = 0#64) :
    VpGoal Wp Φ N p s r .null st o rv M Ma := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  unfold VpGoal valuePrintPC
  ix_run c.hlive using [h10, h11, h2, hk, hku]
  refine vp_swp_close Wp (Xr := strAt 0x80019018 "null") (frag := "null")
    (H.fwrite live Wp 0x80019018#64 s _ "null" o c.hcl (spIn_of_stackGeom c.hsg (by decide)))
    (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
    outSpec_Q ?hX rfl c.hMa
  case hvs =>
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | _ | _ | i
    · ix_reg; rfl
    · ix_reg; rfl
    · ix_reg; rw [str_null]; rfl
    · simp [upd, h11]
    · omega
  case hX =>
    iintro ⟨-, -, #Hi⟩
    iapply strAt_rodata (by rw [str_null]; decide) (by unfold CStrImg; rw [str_null]; decide) $$ Hi

end

end VsaIris.Interp
