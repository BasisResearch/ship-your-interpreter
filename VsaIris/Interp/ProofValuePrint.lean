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
    (p s r : BitVec 64) (v : Value) (st : Store) (o : String) (rv : Nat → BitVec 64) (Ma : Mem)
    (E : IProp GF) : IProp GF :=
  iprop(valImg N (imgM Ma) p.toNat v ∗ dispRes st v ∗ E ∗ binImg ∗ stdioOwn ∗ consoleOwn o ∗
    stackScratch s printNeed ∗ codeRes ∗
    (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
      (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
        (valAt N p.toNat v ∗ stdioOwn ∗ consoleOwn (o ++ v.display st) ∗ stackAt s printNeed)) -∗
      Wp.W Φ))

/-- **Closing a `value_print` run at a newlib tail call.** -/
theorem vp_swp_close (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {v : Value} {st : Store} {o : String}
    {rv R : Nat → BitVec 64} {M Ma Dt : Mem} {DA : List Nat} {entry : BitVec 64}
    {P Q : BitVec 64 → IProp GF}
    {vs : List (BitVec 64)} {Xr E : IProp GF} [Persistent Xr] [Persistent E] {frag : String}
    {need : Nat}
    (hspec : ⊢ fnSpecW Wp entry P Q)
    (hlen : vs.length ≤ 8) (hvs : ∀ i (h : i < vs.length), R (10 + i) = vs[i]) (hs : R 2 = s)
    (h1 : R 1 = r) (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → R x = rv x)
    (hsg : StackGeom s printNeed) (hneed : need ≤ printNeed)
    (hP : ∀ r, iprop(argsAt vs ∗ (Xr ∗ stdioOwn ∗ consoleOwn o) ∗
      callFrame s need Newlib.calleeSaved R) ⊢ P r)
    (hQ : ∀ r, Q r ⊢ iprop(clobbered argRegs ∗ (stdioOwn ∗ consoleOwn (o ++ frag)) ∗
      callFrame s need Newlib.calleeSaved R))
    (hX : valImg N (imgM Ma) p.toNat v ∗ dispRes st v ∗ E ∗ binImg ⊢ Xr)
    (hfrag : frag = v.display st)
    (hMa : ∀ x, InExt (p.toNat, 24) x → imgM M x = imgM Ma x) :
    IW live Dt DA (InExt (p.toNat, 24))
      (RunK Wp Φ (Fvp Wp Φ N p s r v st o rv Ma E) (InExt (p.toNat, 24))) entry R M := by
  apply swp_closeF
  unfold Fvp codeRes roOwn
  simp only [sepL_cons, sepL_nil]
  iintro ⟨⟨#Hv, #Hd, #HE, #Himg, Hstd, Hcon, Hst, ⟨⟨#Hgp, -⟩, -⟩, Hk⟩, Hms⟩
  ihave #Hsp := hspec
  ihave #HX := hX $$ [Hv Hd HE Himg]
  · iframe Hv Hd HE Himg
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
  IW live ∅ [] (InExt (p.toNat, 24))
    (RunK Wp Φ (Fvp Wp Φ N p s r v st o rv Ma iprop(emp)) (InExt (p.toNat, 24))) valuePrintPC (upd rv 1 r) M

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
  ix_run1 c.hlive using [h10, h11, h2, hk, hku]
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
    · simp [upd]
    · omega
  case hX =>
    iintro ⟨-, -, -, #Hi⟩
    iapply strAt_rodata (by rw [str_null]; decide) (by unfold CStrImg; rw [str_null]; decide) $$ Hi

theorem str_true : "true".toList = ['t', 'r', 'u', 'e'] := by decide
theorem str_false : "false".toList = ['f', 'a', 'l', 's', 'e'] := by decide

/-- A payload word of the value, read through the run's memory. -/
theorem VpCtx.word {p s r : BitVec 64} {rv : Nat → BitVec 64} {M Ma : Mem}
    (c : VpCtx live p s r rv M Ma) (o : Nat) (ho : o ≤ 16) :
    imgW (imgM M) (p + BitVec.ofNat 64 o).toNat = imgW (imgM Ma) (p.toNat + o) := by
  have := c.hg.hi
  rw [show (p + BitVec.ofNat 64 o).toNat = p.toNat + o by rw [BitVec.toNat_add]; simp; omega]
  exact imgW_agree (fun i hi => c.hMa _ (by simp [InExt]; omega))

/-- `bool`: `fputs(b ? "true" : "false", stdout)`. -/
theorem vp_bool (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma) {b : Bool}
    (hk : ldv .lw M p.toNat = 1#64) (hku : ldv .lwu M p.toNat = 1#64)
    (hb : ldv .lw M (p + 8#64).toNat = BitVec.ofNat 64 (cond b 1 0)) :
    VpGoal Wp Φ N p s r (.bool b) st o rv M Ma := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  unfold VpGoal valuePrintPC
  cases b
  · simp only [Bool.cond_false] at hb
    ix_run1 c.hlive using [h10, h11, h2, hk, hku, hb]
    refine vp_swp_close Wp (Xr := strAt 0x80019010 "false") (frag := "false")
      (H.fputs live Wp 0x80019010#64 s _ "false" o c.hcl (spIn_of_stackGeom c.hsg (by decide)))
      (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
      outSpec_Q ?hX rfl c.hMa
    case hvs =>
      intro i h
      simp only [List.length_cons, List.length_nil] at h
      rcases i with _ | _ | i
      · ix_reg; rfl
      · simp [upd, h11]
      · omega
    case hX =>
      iintro ⟨-, -, -, #Hi⟩
      iapply strAt_rodata (by rw [str_false]; decide) (by unfold CStrImg; rw [str_false]; decide) $$ Hi
  · simp only [Bool.cond_true] at hb
    ix_run1 c.hlive using [h10, h11, h2, hk, hku, hb]
    refine vp_swp_close Wp (Xr := strAt 0x80019008 "true") (frag := "true")
      (H.fputs live Wp 0x80019008#64 s _ "true" o c.hcl (spIn_of_stackGeom c.hsg (by decide)))
      (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
      outSpec_Q ?hX rfl c.hMa
    case hvs =>
      intro i h
      simp only [List.length_cons, List.length_nil] at h
      rcases i with _ | _ | i
      · ix_reg; rfl
      · simp [upd, h11]
      · omega
    case hX =>
      iintro ⟨-, -, -, #Hi⟩
      iapply strAt_rodata (by rw [str_true]; decide) (by unfold CStrImg; rw [str_true]; decide) $$ Hi

/-- `int`: `fprintf(stdout, "%lld", n)`. -/
theorem vp_int (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma) {n : Int}
    (hk : ldv .lw M p.toNat = 2#64) (hku : ldv .lwu M p.toNat = 2#64)
    (hn : (imgW (imgM Ma) (p.toNat + 8)).toInt = n) :
    VpGoal Wp Φ N p s r (.int n) st o rv M Ma := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  have hw := (ldv_ld_imgW M (p + BitVec.ofNat 64 8).toNat).trans (c.word 8 (by omega))
  generalize imgW (imgM Ma) (p.toNat + 8) = w at hw hn
  unfold VpGoal valuePrintPC
  ix_run1 c.hlive using [h10, h11, h2, hk, hku, hw]
  refine vp_swp_close Wp (Xr := fprintfOut 0x800192c0#64 w (intToString w.toInt))
    (frag := intToString w.toInt)
    (H.fprintf live Wp 0x800192c0#64 w s _ (intToString w.toInt) o c.hcl
      (spIn_of_stackGeom c.hsg (by decide)))
    (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
    outSpec_Q ?hX (by rw [← hn]; rfl) c.hMa
  case hvs =>
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | _ | i
    · simp [upd]
    · ix_reg; rfl
    · ix_reg; rfl
    · omega
  case hX =>
    iintro -
    unfold fprintfOut
    ileft; ipureintro; exact ⟨rfl, rfl⟩

/-- `str`: `fputs(s, stdout)`. -/
theorem vp_str (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma) {x : String}
    (hk : ldv .lw M p.toNat = 3#64) (hku : ldv .lwu M p.toNat = 3#64) :
    VpGoal Wp Φ N p s r (.str x) st o rv M Ma := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  have hw := (ldv_ld_imgW M (p + BitVec.ofNat 64 8).toNat).trans (c.word 8 (by omega))
  unfold VpGoal valuePrintPC
  ix_run1 c.hlive using [h10, h11, h2, hk, hku, hw]
  refine vp_swp_close Wp (Xr := strAt (imgW (imgM Ma) (p.toNat + 8)).toNat x) (frag := x)
    (H.fputs live Wp (imgW (imgM Ma) (p.toNat + 8)) s _ x o c.hcl
      (spIn_of_stackGeom c.hsg (by decide)))
    (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
    outSpec_Q ?hX rfl c.hMa
  case hvs =>
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | i
    · ix_reg; rfl
    · simp [upd, h11]
    · omega
  case hX =>
    iintro ⟨#Hv, -, -, -⟩
    iapply valImg_str $$ Hv

/-- `native`: `fprintf(stdout, "<native fn %s>", name)`. -/
theorem vp_native (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma) {f : NativeFn}
    (hk : ldv .lw M p.toNat = 5#64) (hku : ldv .lwu M p.toNat = 5#64) :
    VpGoal Wp Φ N p s r (.native f) st o rv M Ma := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  have hw := (ldv_ld_imgW M (p + BitVec.ofNat 64 8).toNat).trans (c.word 8 (by omega))
  unfold VpGoal valuePrintPC
  ix_run1 c.hlive using [h10, h11, h2, hk, hku, hw]
  refine vp_swp_close Wp
    (Xr := fprintfOut 0x800192d8#64 (imgW (imgM Ma) (p.toNat + 8)) ("<native fn " ++ nativeName f ++ ">"))
    (frag := "<native fn " ++ nativeName f ++ ">")
    (H.fprintf live Wp 0x800192d8#64 (imgW (imgM Ma) (p.toNat + 8)) s _
      ("<native fn " ++ nativeName f ++ ">") o c.hcl (spIn_of_stackGeom c.hsg (by decide)))
    (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
    outSpec_Q ?hX (by cases f <;> rfl) c.hMa
  case hvs =>
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | _ | i
    · simp [upd]
    · ix_reg; rfl
    · ix_reg; rfl
    · omega
  case hX =>
    iintro ⟨#Hv, -, -, -⟩
    unfold fprintfOut
    iright; iright
    iexists nativeName f
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold valImg valOf
    icases Hv with ⟨-, #H⟩
    iexact H

theorem str_fn : "<fn>".toList = ['<', 'f', 'n', '>'] := by decide

/-- The closure arm's data view: the closure object's first word, the
`EX_FN` node's name field. -/
abbrev clodA (cp q : Nat) : List Nat := accAddrs cp 8 ++ accAddrs (q + 8) 8

/-- The closure arm's shared facts. -/
structure CloFacts (M Ma Dt : Mem) (p : BitVec 64) (cp q nm : Nat) : Prop where
  hk : ldv .lw M p.toNat = 4#64
  hku : ldv .lwu M p.toNat = 4#64
  hw : imgW (imgM Ma) (p.toNat + 8) = BitVec.ofNat 64 cp
  hc0 : ReadOK cp
  hc7 : ReadOK (cp + 7)
  hq : ldv .ld Dt cp = BitVec.ofNat 64 q
  hq0 : ReadOK (q + 8)
  hq7 : ReadOK (q + 15)
  hnm : ldv .ld Dt (q + 8) = BitVec.ofNat 64 nm

/-- An anonymous closure: `fwrite("<fn>", 1, 4, stdout)`. -/
theorem vp_clo_anon (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma) {ca : Nat} {Dt : Mem} {cp q : Nat}
    {E : IProp GF} [Persistent E] (f : CloFacts M Ma Dt p cp q 0)
    (hdisp : Value.display st (.closure ca) = "<fn>") :
    IW live Dt (clodA cp q) (InExt (p.toNat, 24))
      (RunK Wp Φ (Fvp Wp Φ N p s r (.closure ca) st o rv Ma E) (InExt (p.toNat, 24)))
      valuePrintPC (upd rv 1 r) M := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  have hk := f.hk; have hku := f.hku; have hq := f.hq; have hnm := f.hnm
  have hw8 := (ldv_ld_imgW M (p + BitVec.ofNat 64 8).toNat).trans ((c.word 8 (by omega)).trans f.hw)
  have c1 := f.hc0.lo; have c2 := f.hc0.hi; have c3 := f.hc0.off
  have c4 := f.hc7.lo; have c5 := f.hc7.hi; have c6 := f.hc7.off
  have q1 := f.hq0.lo; have q2 := f.hq0.hi; have q3 := f.hq0.off
  have q4 := f.hq7.lo; have q5 := f.hq7.hi; have q6 := f.hq7.off
  have ecp : (BitVec.ofNat 64 cp).toNat = cp := by simp; omega
  have eq8 : (BitVec.ofNat 64 q + 8#64).toNat = q + 8 := by rw [BitVec.toNat_add]; simp; omega
  unfold valuePrintPC
  ix_run1 c.hlive using [h10, h11, h2, hk, hku, hw8, ecp, hq, eq8, hnm]
  refine vp_swp_close Wp (Xr := strAt 0x800192d0 "<fn>") (frag := "<fn>")
    (H.fwrite live Wp 0x800192d0#64 s _ "<fn>" o c.hcl (spIn_of_stackGeom c.hsg (by decide)))
    (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
    outSpec_Q ?hX hdisp.symm c.hMa
  case hvs =>
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | _ | _ | i
    · ix_reg; rfl
    · ix_reg; rfl
    · ix_reg; rw [str_fn]; rfl
    · simp [upd]
    · omega
  case hX =>
    iintro ⟨-, -, -, #Hi⟩
    iapply strAt_rodata (by rw [str_fn]; decide) (by unfold CStrImg; rw [str_fn]; decide) $$ Hi

/-- A named closure: `fprintf(stdout, "<fn %s>", name)`. -/
theorem vp_clo_named (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {st : Store} {o : String} {rv : Nat → BitVec 64} {M Ma : Mem}
    (H : OutHoles) (c : VpCtx live p s r rv M Ma) {ca : Nat} {Dt : Mem} {cp q nm : Nat}
    {E : IProp GF} [Persistent E] {x : String} (f : CloFacts M Ma Dt p cp q nm)
    (hnz : nm ≠ 0) (hnlt : nm < 2 ^ 64) (hE : E ⊢ strAt nm x)
    (hdisp : Value.display st (.closure ca) = "<fn " ++ x ++ ">") :
    IW live Dt (clodA cp q) (InExt (p.toNat, 24))
      (RunK Wp Φ (Fvp Wp Φ N p s r (.closure ca) st o rv Ma E) (InExt (p.toNat, 24)))
      valuePrintPC (upd rv 1 r) M := by
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have hg1 := c.hg.al; have hg2 := c.hg.lo; have hg3 := c.hg.hi
  have hk := f.hk; have hku := f.hku; have hq := f.hq; have hnm := f.hnm
  have hw8 := (ldv_ld_imgW M (p + BitVec.ofNat 64 8).toNat).trans ((c.word 8 (by omega)).trans f.hw)
  have c1 := f.hc0.lo; have c2 := f.hc0.hi; have c3 := f.hc0.off
  have c4 := f.hc7.lo; have c5 := f.hc7.hi; have c6 := f.hc7.off
  have q1 := f.hq0.lo; have q2 := f.hq0.hi; have q3 := f.hq0.off
  have q4 := f.hq7.lo; have q5 := f.hq7.hi; have q6 := f.hq7.off
  have ecp : (BitVec.ofNat 64 cp).toNat = cp := by simp; omega
  have eq8 : (BitVec.ofNat 64 q + 8#64).toNat = q + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hnz' : BitVec.ofNat 64 nm ≠ 0#64 := fun h => hnz (by
    have := congrArg BitVec.toNat h; simp at this; omega)
  unfold valuePrintPC
  ix_run1 c.hlive using [h10, h11, h2, hk, hku, hw8, ecp, hq, eq8, hnm, hnz']
  refine vp_swp_close Wp (Xr := fprintfOut 0x800192c8#64 (BitVec.ofNat 64 nm) ("<fn " ++ x ++ ">"))
    (frag := "<fn " ++ x ++ ">")
    (H.fprintf live Wp 0x800192c8#64 (BitVec.ofNat 64 nm) s _ ("<fn " ++ x ++ ">") o c.hcl
      (spIn_of_stackGeom c.hsg (by decide)))
    (by simp) ?hvs (by ix_reg; exact h2) (by ix_reg) (by helper_keep) c.hsg (by decide) outSpec_P
    outSpec_Q ?hX hdisp.symm c.hMa
  case hvs =>
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | _ | i
    · simp [upd]
    · ix_reg; rfl
    · ix_reg; rfl
    · omega
  case hX =>
    iintro ⟨-, -, #HE, -⟩
    unfold fprintfOut
    iright; ileft
    iexists x
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    rw [show (BitVec.ofNat 64 nm).toNat = nm by simp; omega]
    iapply hE $$ HE

omit I in
/-- A read-only image and a read-only view agree where both own a byte. -/
theorem roImg_roOn_agree {S P : Nat → Prop} {img : Nat → BitVec 8} {m : Mem} :
    roImg (GF := GF) S img ∗ roOn P m ⊢ ⌜∀ a b, S a → P a → m[a]? = some b → img a = b⌝ := by
  iintro ⟨#H1, #H2⟩
  iintro %a %b %hs %hp %hm
  unfold roImg roOn
  ihave #Ha := H1 $$ %a %hs
  ihave #Hb := H2 $$ %a %b %hp %hm
  iapply memRO_agree a (img a) b $$ [Ha Hb]
  iframe Ha Hb

omit I in
/-- **The closure arm's data view** from the closure object and the `EX_FN`
node's view: a memory `Dt` agreeing with each on its bytes. -/
theorem roOwn_clod {img : Nat → BitVec 8} {P : Nat → Prop} {m : Mem} {cp q : Nat}
    (hP : ∀ k, q + 8 ≤ k → k < q + 16 → P k ∧ (m[k]?).isSome) :
    codeRes (GF := GF) ∗ roImg (InExt (cp, 16)) img ∗ roOn P m ⊢
      ∃ Dt : Mem, roOwn roR (interpText ++ dataOf Dt (clodA cp q)) ∗
        ⌜(∀ k, cp ≤ k → k < cp + 8 → imgM Dt k = img k) ∧
          ∀ k, q + 8 ≤ k → k < q + 16 → m[k]? = some (imgM Dt k)⌝ := by
  classical
  iintro ⟨#Hc, #H1, #H2⟩
  ihave %hag := roImg_roOn_agree $$ [H1 H2]
  · iframe H1 H2
  let f : Nat → BitVec 8 := fun k => if cp ≤ k ∧ k < cp + 16 then img k else (m[k]?).getD 0
  obtain ⟨Dt, hDt⟩ := exists_mem_img f (clodA cp q)
  have hc : ∀ k, cp ≤ k → k < cp + 8 → imgM Dt k = img k := fun k h1 h2 => by
    rw [hDt k (List.mem_append_left _ (mem_accAddrs_iff.2 ⟨h1, h2⟩))]
    simp [f, h1, show k < cp + 16 by omega]
  have hn : ∀ k, q + 8 ≤ k → k < q + 16 → m[k]? = some (imgM Dt k) := fun k h1 h2 => by
    rw [hDt k (List.mem_append_right _ (mem_accAddrs_iff.2 ⟨h1, h2⟩))]
    obtain ⟨hPk, hsome⟩ := hP k h1 h2
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    by_cases hin : cp ≤ k ∧ k < cp + 16
    · simp only [f, hin]; rw [hb, hag k b (by simp [InExt]; omega) hPk hb]; simp
    · simp only [f, hin, ite_false]; rw [hb]; rfl
  iexists Dt
  isplitl
  · unfold codeRes roOwn at *
    icases Hc with ⟨#Hgp, #Htx⟩
    iframe Hgp
    iapply (sepL_append _ _ _).2
    iframe Htx
    unfold dataOf
    rw [sepL_map]
    iapply (sepL_append _ _ _).2
    isplitl
    · iapply sepL_of_persistent (roImg (InExt (cp, 16)) img) _ _ (fun k hk => by
        obtain ⟨h1, h2⟩ := mem_accAddrs_iff.1 hk
        rw [hc k h1 h2]
        unfold roImg
        iintro #H
        iapply H $$ %k %(show InExt (cp, 16) k by simp [InExt]; omega)) $$ H1
    · iapply sepL_of_persistent (roOn P m) _ _ (fun k hk => by
        obtain ⟨h1, h2⟩ := mem_accAddrs_iff.1 hk
        unfold roOn
        iintro #H
        iapply H $$ %k %(imgM Dt k) %(hP k h1 h2).1 %(hn k h1 h2)) $$ H2
  · ipureintro; exact ⟨hc, hn⟩

/-- An unsigned word load of a slot's kind. -/
theorem ldv_lwu_kind {Mt : Mem} {a k : Nat} (h : (imgW (imgM Mt) a).toNat % 2 ^ 32 = k) :
    ldv .lwu Mt a = BitVec.ofNat 64 k :=
  ldvf_lwu_imgLE (by rw [← imgW_lo32]; exact h)

/-- **The run of `value_print`** for every value but a closure. -/
theorem vp_run (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {v : Value} {st : Store} {o : String}
    {rv : Nat → BitVec 64} {Ma : Mem} (H : OutHoles) (c : VpCtx live p s r rv Ma Ma)
    (hp : ValPure N v (imgW (imgM Ma) p.toNat) (imgW (imgM Ma) (p.toNat + 8))
      (imgW (imgM Ma) (p.toNat + 16)))
    (hnc : ∀ ca, v ≠ .closure ca) : VpGoal Wp Φ N p s r v st o rv Ma Ma := by
  have hk := ldv_lw_kind (Mt := Ma) hp.kind (by cases v <;> simp [kindTag])
  have hku := ldv_lwu_kind (Mt := Ma) hp.kind
  have hg3 := c.hg.hi
  cases v with
  | null => exact vp_null Wp H c hk hku
  | bool b =>
    refine vp_bool Wp H c hk hku ?_
    have e8 : (p + 8#64).toNat = p.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    refine ldv_lw_kind (k := cond b 1 0) ?_ (by cases b <;> decide)
    rw [e8]; exact hp.2
  | int n => exact vp_int Wp H c hk hku hp.2
  | str x => exact vp_str Wp H c hk hku
  | closure ca => exact absurd rfl (hnc ca)
  | native f => exact vp_native Wp H c hk hku

/-- The name field of an `EX_FN` node. -/
theorem fnName_facts {m : Mem} {P : Nat → Prop} {q : Nat} {name : Option String} {ps : List String}
    {ss : List Stmt} (h : ExprReprWithin m P q (.fn name ps ss)) :
    ∃ w, read64 m (q + 8) = some w ∧ Covers P (q + 8) 8 ∧
      ((name = none ∧ w = 0) ∨ ∃ x, name = some x ∧ w ≠ 0 ∧ CStringWithin m P w x) := by
  cases h with
  | fnNamed _ _ hr hc hne hs => exact ⟨_, hr, hc, .inr ⟨_, rfl, hne, hs⟩⟩
  | fnAnon _ _ hr hc => exact ⟨_, hr, hc, .inl ⟨rfl, rfl⟩⟩

/-- `read64`'s value is a 64-bit word. -/
theorem read64_lt {m : Mem} {a w : Nat} (h : read64 m a = some w) : w < 2 ^ 64 := by
  have := readLE_memImg h
  have := imgLE_lt (memImg m) a 8
  omega

/-- A closure value's payload is its closure's address. -/
theorem valImg_clos {N : NativeAddrs} {f : Nat → BitVec 8} {a ca : Nat} :
    valImg (GF := GF) N f a (.closure ca) ⊢ closAt ca (imgW f (a + 8)).toNat := by
  unfold valImg valOf
  iintro ⟨-, #H⟩
  iexact H

/-- A closure's display resources, opened. -/
theorem dispRes_clos {st : Store} {ca : Nat} :
    dispRes (GF := GF) st (.closure ca) ⊢ ∃ (cd : ClosureData) (p q : Nat) (img : Nat → BitVec 8)
      (P : Nat → Prop) (m : Mem), ⌜st.closures[ca]? = some cd ∧ imgLE img p 8 = q ∧
        (∀ k, InExt (p, 16) k → ReadOK k) ∧ ExprReprWithin m P q (.fn cd.name cd.params cd.body) ∧
        (∀ k, P k → ReadOK k)⌝ ∗
      closAt ca p ∗ roImg (InExt (p, 16)) img ∗ roOn P m := by
  unfold dispRes; exact .rfl

/-- The continuation `value_print`'s frame hands its caller. -/
abbrev VpK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (p s r : BitVec 64) (v : Value) (st : Store) (o : String) (rv : Nat → BitVec 64) : IProp GF :=
  iprop(PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
    (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
      (valAt N p.toNat v ∗ stdioOwn ∗ consoleOwn (o ++ v.display st) ∗ stackAt s printNeed)) -∗
    Wp.W Φ)

/-- **`value_print` on a closure**: the data view from `dispRes`, then the
named or anonymous arm. -/
theorem vp_closure (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {p s r : BitVec 64} {ca : Nat} {st : Store} {o : String}
    {rv : Nat → BitVec 64} {Ma : Mem} (H : OutHoles) (c : VpCtx live p s r rv Ma Ma)
    (hp : ValPure N (.closure ca) (imgW (imgM Ma) p.toNat) (imgW (imgM Ma) (p.toNat + 8))
      (imgW (imgM Ma) (p.toNat + 16))) :
    codeRes ∗ valImg N (imgM Ma) p.toNat (.closure ca) ∗ dispRes st (.closure ca) ∗ binImg ∗
      stdioOwn ∗ consoleOwn o ∗ stackScratch s printNeed ∗ VpK Wp Φ N p s r (.closure ca) st o rv ∗
      ms valuePrintPC (upd rv 1 r) (InExt (p.toNat, 24)) Ma
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, #Hw, #Hd, #Himg, Hstd, Hcon, Hst, Hk, Hms⟩
  ihave #Hd2 := dispRes_clos $$ Hd
  icases Hd2 with ⟨%cd, %cp, %q, %img, %P, %m, %⟨hcd, hqimg, hcR, hrep, hPR⟩, #Hca, #Hro, #Hon⟩
  ihave #Hca' := valImg_clos $$ Hw
  ihave %hcp := closAt_agree ca cp (imgW (imgM Ma) (p.toNat + 8)).toNat $$ [Hca Hca']
  · iframe Hca Hca'
  obtain ⟨w, hrw, hcov, hname⟩ := fnName_facts hrep
  have hP : ∀ k, q + 8 ≤ k → k < q + 16 → P k ∧ (m[k]?).isSome := fun k h1 h2 => by
    refine ⟨by have := hcov (k - (q + 8)) (by omega); rwa [show q + 8 + (k - (q + 8)) = k by omega] at this, ?_⟩
    have := read64_bytes_present hrw (k - (q + 8)) (by omega)
    rw [show q + 8 + (k - (q + 8)) = k by omega] at this
    rw [this]; rfl
  ihave ⟨%Dt, #Hview, %⟨hc, hn⟩⟩ := roOwn_clod hP $$ [Hcode Hro Hon]
  · iframe Hcode Hro Hon
  have f : CloFacts Ma Ma Dt p cp q w := {
    hk := ldv_lw_kind hp.kind (by decide)
    hku := ldv_lwu_kind hp.kind
    hw := by rw [hcp]; simp
    hc0 := hcR cp (by simp [InExt])
    hc7 := hcR (cp + 7) (by simp [InExt])
    hq := by
      rw [ldv_ld_imgW]; unfold imgW
      rw [imgLE_congr (img' := img) (fun i hi => hc (cp + i) (by omega) (by omega)), hqimg]
    hq0 := hPR (q + 8) (by have := hcov 0 (by omega); simpa using this)
    hq7 := hPR (q + 15) (by have := hcov 7 (by omega); simpa using this)
    hnm := by
      rw [ldv_ld_imgW]; unfold imgW
      have h8 : readLE m (q + 8) 8 = some (imgLE (imgM Dt) (q + 8) 8) :=
        readLE_of_img (fun i hi => hn (q + 8 + i) (by omega) (by omega))
      have : read64 m (q + 8) = readLE m (q + 8) 8 := rfl
      rw [this, h8] at hrw
      cases hrw; rfl }
  have hdisp : Value.display st (.closure ca) =
      match cd.name with | some x => "<fn " ++ x ++ ">" | none => "<fn>" := by
    simp only [Value.display, hcd]
    cases cd.name <;> rfl
  rcases hname with ⟨hn0, rfl⟩ | ⟨x, hnx, hnz, hcs⟩
  · iapply wp_swpF Wp (text := interpText ++ dataOf Dt (clodA cp q)) (S := InExt (p.toNat, 24))
      (R := upd rv 1 r) (Mt := Ma) (pc := valuePrintPC)
      (F := Fvp Wp Φ N p s r (.closure ca) st o rv Ma iprop(emp))
    rotate_left
    · unfold Fvp
      iframe Hview Hw Hd Himg Hstd Hcon Hst Hcode Hk Hms
    intro F'
    exact vp_clo_anon Wp H c f (by rw [hdisp, hn0])
  · ihave #Hx := strAt_of_cstringWithin hcs $$ Hon
    iapply wp_swpF Wp (text := interpText ++ dataOf Dt (clodA cp q)) (S := InExt (p.toNat, 24))
      (R := upd rv 1 r) (Mt := Ma) (pc := valuePrintPC)
      (F := Fvp Wp Φ N p s r (.closure ca) st o rv Ma (strAt w x))
    rotate_left
    · unfold Fvp
      iframe Hview Hw Hd Hx Himg Hstd Hcon Hst Hcode Hk Hms
    intro F'
    exact vp_clo_named Wp H c f hnz (read64_lt hrw) .rfl (by rw [hdisp, hnx])

/-- **`value_print`**, for either WP, given newlib's stdout calls. -/
theorem valuePrint_spec (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live) (H : OutHoles)
    (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs) (p s : BitVec 64) (v : Value)
    (st : Store) (o : String) : ⊢ valuePrintSpec (vsaModel live) N Wp p s v st o := by
  unfold valuePrintSpec helperSpec fnSpecW
  iintro %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h11, h2⟩, #Hcode, Hv, %hg, #Hd, #Himg, Hstd, Hcon,
    ⟨Hst, %hsg⟩⟩ Hk
  ihave ⟨%Ma, HA, #Hw⟩ := valAt_tracked N _ v $$ Hv
  ihave %hpv := valOf_pure N v _ _ _ $$ Hw
  have c : VpCtx live p s r rv Ma Ma := ⟨hlive, hcl, hal, h10, h11, h2, hg, hsg, fun _ _ => rfl⟩
  have hms : ms (GF := GF) valuePrintPC (upd rv 1 r) (InExt (p.toNat, 24)) Ma =
      iprop(PC ↦ᵣ valuePrintPC ∗ ra ↦ᵣ r ∗ regFile rv ∗
        ownSet (InExt (p.toNat, 24)) (fun a => a ↦ₘ imgM Ma a)) := by
    unfold ms; rw [regFile_upd_ra]; simp only [upd_same]
  by_cases hclo : ∃ ca, v = .closure ca
  · obtain ⟨ca, rfl⟩ := hclo
    iapply vp_closure Wp H c hpv
    rw [hms]
    iframe Hcode Hw Hd Himg Hstd Hcon Hst Hk Hpc Hra Hregs HA
  · iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (S := InExt (p.toNat, 24))
      (R := upd rv 1 r) (Mt := Ma) (pc := valuePrintPC)
      (F := Fvp Wp Φ N p s r v st o rv Ma iprop(emp))
    rotate_left
    · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
        unfold codeRes; simp [dataOf]
      rw [hro, hms]
      unfold Fvp
      iframe Hcode Hw Hd Himg Hstd Hcon Hst Hk Hpc Hra Hregs HA
    intro F'
    exact vp_run Wp H c hpv (fun ca h => hclo ⟨ca, h⟩)

end

end VsaIris.Interp
