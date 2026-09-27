import Vsa.Compiler.SetupRun
import Vsa.Compiler.AbsLift

/-!
# Correctness of the full compiler

`compileG_correct`: for every supported WHILE program `p` whose big-step
executions stay within the heap budget, and every machine configuration whose
memory holds the bytes of `compileG p` at `codeBase` (plus libgcc's
multiply/divide routines, as in the interpreter image), with the PC at
`codeBase`, in a good machine state with an empty console, the machine halts
with exit code `0` and output `out` exactly when `out` is a big-step behaviour of
`p`, and a diverging machine means `p` has no behaviour.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Halts Diverges output)

/-- The programs the full compiler supports: well-formed against the program's
string table and global frame, with a small static image. -/
structure SupportedG (p : Program) : Prop where
  wf : WfSeq (strTab p) [globalNames p] p
  setup : SetupOK p

/-- The heap budget in cost units: the frame region above the global frame
holds `64 * heapUnits` bytes. -/
def heapUnits : Nat := 0x3F8000

/-- The context of the top-level statements. -/
def ctxG (p : Program) : GCtx := ⟨[globalNames p], 0, none, none, none⟩

/-- The compiled top-level statements. -/
def bodyG (p : Program) : List Ins := gseq (strTab p) (ctxG p) (mainPos + (setupCode p).length) p

/-- The machine code bytes of `compileG p`. -/
def compileGBytes (p : Program) : List (BitVec 8) := codeBytes (compileG p)

theorem compileG_eq (p : Program) :
    compileG p = [J 0 mainPos] ++ (errCode ++ rtCode) ++ setupCode p ++ bodyG p ++ exitCode 0 := by
  simp only [compileG, bodyG, ctxG, List.append_assoc]

/-- The pieces of `compileG p` in place. -/
structure GSegs (p : Program) : Prop where
  entry : Seg (compileG p) 0 [J 0 mainPos]
  rt : Seg (compileG p) errPos (errCode ++ rtCode)
  setup : Seg (compileG p) mainPos (setupCode p)
  body : Seg (compileG p) (mainPos + (setupCode p).length) (bodyG p)
  exit : Seg (compileG p) (mainPos + (setupCode p).length + (bodyG p).length) (exitCode 0)

/-- The lengths of the runtime's pieces. -/
theorem rt_lengths : errCode.length = 13 ∧ (psCode psPos).length = 32 ∧ (itCode itPos).length = 52 ∧
    (cpCode cpPos).length = 8 ∧ (scCode scPos).length = 22 ∧ (trCode trPos).length = 10 ∧
    (nfCode nfPos).length = 27 ∧ (dpCode dpPos).length = 126 ∧ (csCode csPos).length = 83 ∧
    (ccCode ccPos).length = 32 ∧ (addCode addPos).length = 23 ∧ (subCode subPos).length = 5 ∧
    (mulCode mulPos).length = 13 ∧ (divCode divPos).length = 14 ∧ (modCode modPos).length = 14 ∧
    (cmpCode cmpPos).length = 35 ∧ (eqCode eqPos).length = 13 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rtCode_length : rtCode.length = 509 := by
  obtain ⟨-, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17⟩ := rt_lengths
  simp only [rtCode, List.length_append, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17]

theorem gsegs (p : Program) : GSegs p := by
  have h := Seg.self (compileG p)
  rw [compileG_eq] at h
  obtain ⟨h1234, h5⟩ := h.append
  obtain ⟨h123, h4⟩ := h1234.append
  obtain ⟨h12, h3⟩ := h123.append
  obtain ⟨h1, h2⟩ := h12.append
  have hm : mainPos = 523 := rfl
  simp only [List.length_append, List.length_singleton, rt_lengths.1, rtCode_length] at h3 h4 h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [compileG_eq]
  · exact h1
  · exact h2
  · exact h3.cast (by omega)
  · exact h4.cast (by omega)
  · exact h5.cast (by omega)

theorem RTLoaded.of {code : List Ins} (hfit : Fits code) (h : Seg code errPos (errCode ++ rtCode)) :
    RTLoaded code := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17⟩ := rt_lengths
  obtain ⟨he, h⟩ := h.append
  simp only [rtCode, List.append_assoc] at h
  obtain ⟨h1, h⟩ := h.append
  obtain ⟨h2, h⟩ := h.append
  obtain ⟨h3, h⟩ := h.append
  obtain ⟨h4, h⟩ := h.append
  obtain ⟨h5, h⟩ := h.append
  obtain ⟨h6, h⟩ := h.append
  obtain ⟨h7, h⟩ := h.append
  obtain ⟨h8, h⟩ := h.append
  obtain ⟨h9, h⟩ := h.append
  obtain ⟨h10, h⟩ := h.append
  obtain ⟨h11, h⟩ := h.append
  obtain ⟨h12, h⟩ := h.append
  obtain ⟨h13, h⟩ := h.append
  obtain ⟨h14, h⟩ := h.append
  obtain ⟨h15, h16⟩ := h.append
  simp only [l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17] at *
  exact ⟨hfit, he, h1.cast rfl, h2.cast rfl, h3.cast rfl, h4.cast rfl, h5.cast rfl, h6.cast rfl, h7.cast rfl,
    h8.cast rfl, h9.cast rfl, h10.cast rfl, h11.cast rfl, h12.cast rfl, h13.cast rfl, h14.cast rfl, h15.cast rfl,
    h16.cast rfl⟩

theorem ctxG_ok (p : Program) : CtxOK (ctxG p) where
  blk := by simp [ctxG]
  brk _ _ e := by cases e
  cont _ _ e := by cases e
  ret _ _ e := by cases e

section
variable {p : Program} (hsup : SupportedG p) (hfit : Fits (compileG p))
include hsup hfit

/-- The abstract machine reaches the first statement with the invariant. -/
theorem reach_body (m : Mem) (o : Array String) (ho : String.join o.toList = "") :
    Reaches (compileG p) (A0 m o) fun B => B.pc = pcOf (mainPos + (setupCode p).length) ∧
      MS (compileG p) (strTab p) (view0 p) initSt 0 0 [globalNames p] (stackHi - frameSize p) (frameSize p) B := by
  have hs := gsegs p
  have hR := RTLoaded.of hfit hs.rt
  have hP := seg_end_posOK hfit hs.exit (by simp [exitCode])
  have hbl : (bodyG p).length = (gseq (strTab p) (ctxG p) (mainPos + (setupCode p).length) p).length := rfl
  have hstep := step_jump hfit hs.entry.head (A := A0 m o) rfl (by unfold PosOK Fits at *; decide)
    (posOK_le hP (by omega))
  obtain ⟨B, r, hB⟩ := run_setup hR p hsup.setup hs.setup (posOK_le hP (by omega)) (L := []) (m := m) (o := o) ho
  exact ⟨B, Star.step hstep r, hB⟩

/-- A big-step behaviour is reached, and the code then exits with `0`. -/
theorem absG_term (hcap : ∀ out, BigStep p out → BigStepBudget p out heapUnits) (m : Mem) (o : Array String)
    (ho : String.join o.toList = "") {out : String} (hb : BigStep p out) :
    Reaches (compileG p) (A0 m o) fun B => astep (compileG p) B = some (.halt 0) ∧
      String.join B.out.toList = out := by
  obtain ⟨st', n, C, rfl, hle⟩ := hcap out hb
  have hs := gsegs p
  have hR := RTLoaded.of hfit hs.rt
  have hP := seg_end_posOK hfit hs.exit (by simp [exitCode])
  have hbl : (bodyG p).length = (gseq (strTab p) (ctxG p) (mainPos + (setupCode p).length) p).length := rfl
  have hn : 64 * n ≤ 0xFE00000 := by unfold heapUnits at hle; omega
  have hroom : Room (view0 p) n := by
    have := hsup.setup.glob; have := hsup.setup.tab
    have hfb : frameBase = 0x80100000 := rfl; have hfe : frameEnd = 0x90000000 := rfl
    have hob : objBase = 0x90000000 := rfl; have hoe : objEnd = 0xE0000000 := rfl
    exact ⟨by simp only [view0]; omega, by simp only [view0]; omega⟩
  obtain ⟨B1, r1, hpc1, hm1⟩ := reach_body hsup hfit m o ho
  obtain ⟨B2, r2, hB2⟩ := (sim_all (T := strTab p) hR).q C (view0 p) (ctxG p) _ _ _ B1 hm1 hpc1 hsup.wf (ctxG_ok p)
    hs.body (posOK_le hP (by omega)) (by simp [frameSize])
  rcases hB2 with ⟨-, hno⟩ | ⟨V', hp⟩
  · exact absurd hroom hno
  obtain ⟨hpc2, hm2⟩ := hp.out
  obtain ⟨B3, r3, -, hBo, hh⟩ := run_exit hfit (by decide : (0 : Nat) = 0 ∨ 0 = 70) hs.exit hpc2
  exact ⟨B3, r1.trans (r2.trans r3), hh, by rw [hBo]; exact hm2.out⟩

/-- Without a big-step behaviour the code reaches the error exit or runs forever. -/
theorem absG_stuck (m : Mem) (o : Array String) (ho : String.join o.toList = "")
    (hnb : ¬ ∃ out, BigStep p out) :
    Reaches (compileG p) (A0 m o) (fun B => astep (compileG p) B = some (.halt 70)) ∨
      ∀ n, Runs (compileG p) n (A0 m o) := by
  have hs := gsegs p
  have hR := RTLoaded.of hfit hs.rt
  have hP := seg_end_posOK hfit hs.exit (by simp [exitCode])
  have hbl : (bodyG p).length = (gseq (strTab p) (ctxG p) (mainPos + (setupCode p).length) p).length := rfl
  obtain ⟨B1, r1, hpc1, hm1⟩ := reach_body hsup hfit m o ho
  have hf : ∀ n, Fail (compileG p) n B1 := by
    intro n
    by_cases hq : HasQ initSt 0 0 p
    · obtain ⟨st', t, D⟩ := hq
      have ht : t ≠ .normal := fun h => hnb ⟨st'.out, st', by rw [← h]; exact D, rfl⟩
      obtain ⟨nq, C⟩ := ExecSeqCost.exists D
      refine Fail.of_err_or hR (P := fun _ => True) ?_
      refine reaches_mono ((sim_all (T := strTab p) hR).q C (view0 p) (ctxG p) _ _ _ B1 hm1 hpc1 hsup.wf
        (ctxG_ok p) hs.body (posOK_le hP (by omega)) (by simp [frameSize])) ?_
      rintro B (⟨h1, -⟩ | ⟨V', hp⟩)
      · exact .inl ⟨h1, trivial⟩
      · have hout := hp.out
        cases t with
        | normal => exact absurd rfl ht
        | brk => exact .inl ⟨hout, trivial⟩
        | cont => exact .inl ⟨hout, trivial⟩
        | ret v => exact .inl ⟨hout.1, trivial⟩
    · exact (stuck_all (T := strTab p) hR n).q initSt 0 0 p (view0 p) (ctxG p) _ _ _ B1 hm1 hpc1 hsup.wf
        (ctxG_ok p) hs.body (posOK_le hP (by omega)) (by simp [frameSize]) hq
  by_cases hh : Reaches (compileG p) (A0 m o) (fun B => astep (compileG p) B = some (.halt 70))
  · exact .inl hh
  · exact .inr fun n => (Fail.of_star r1 (hf n)).resolve_left hh

end

/-- **Correctness of the full compiler.** For every supported WHILE program
`p` whose big-step behaviours have allocation cost at most `heapUnits`
(`BigStepBudget`; the machine uses at most 64 heap bytes per unit), and every
machine configuration whose memory holds the bytes of `compileG p` at
`0x80004800` (below `tohost`), libgcc's multiply and signed divide/remainder
routines at their addresses in the interpreter image, with the PC at the code,
in a good machine state with an idle HTIF mailbox and an empty console: the
machine halts with exit code `0` and output `out` exactly when `out` is a
big-step behaviour of `p`, and a diverging machine means `p` has none. -/
theorem compileG_correct (p : Program) (hsup : SupportedG p)
    (hfit : 0x80004800 + 4 * (compileG p).length ≤ 0x8001ad00)
    (hcap : ∀ out, BigStep p out → BigStepBudget p out heapUnits) (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes p).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes p)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) := by
  have hfit' : Fits (compileG p) := hfit
  have hlib' : LibLoaded (A0 c.σ.mem c.σ.sailOutput).mem :=
    let ⟨h1, h2, h3, h4, h5⟩ := hlib; ⟨h1, h2, h3, h4, h5⟩
  have hc : Corr c (A0 c.σ.mem c.σ.sailOutput) :=
    ⟨hgood, htick, by rw [hpc]; rfl, trivial, (fun _ h => by cases h), rfl, rfl, hpw⟩
  have hca : CodeAt (A0 c.σ.mem c.σ.sailOutput).mem (compileG p) := codeAt_of_codeBytes hcode
  have ho : String.join c.σ.sailOutput.toList = "" := hout
  have term : ∀ out, BigStep p out → Halts c out 0 := by
    intro out hb
    obtain ⟨B, r, hh, hBo⟩ := absG_term hsup hfit' hcap c.σ.mem c.σ.sailOutput ho hb
    have := halts_of_abstract hfit' hc hca hlib' r hh
    rwa [hBo] at this
  refine ⟨fun out => ⟨term out, fun hH => ?_⟩, fun hd ⟨out, hb⟩ => hd.not_halts (term out hb)⟩
  by_cases hnb' : BigStep p out
  · exact hnb'
  have hnb : ¬ BigStep p out := hnb'
  exfalso
  by_cases hex : ∃ out', BigStep p out'
  · obtain ⟨out', hb'⟩ := hex
    obtain ⟨rfl, -⟩ := hH.deterministic (term out' hb')
    exact hnb hb'
  · rcases absG_stuck hsup hfit' c.σ.mem c.σ.sailOutput ho hex with ⟨B, r, hh⟩ | hdiv
    · have := halts_of_abstract hfit' hc hca hlib' r hh
      exact absurd (hH.deterministic this).2 (by decide)
    · exact (diverges_of_abstract hfit' hc hca hlib' hdiv).not_halts hH

end Vsa.Compiler
