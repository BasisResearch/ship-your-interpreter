import Vsa.Sim.DivCorrClose

/-!
# `DivLoopProgress` reduced to the two `interp_run` loop-head simulation seams

`Vsa/Sim/DivCorrClose.lean` reseated the whole divergence arm on TWO named
residuals — `DivEntryDrive` (the shared `interp_run` prologue drive, now supplied
by `Vsa/Sim/DriveToLoopHeadSpans.lean`'s `driveToLoopHead_interpRunLayout` via
`divEntryDrive_of_driveToLoopHead`) and `DivLoopProgress` (the still-running
per-statement forward simulation AT the top-level `interp_run` dispatch loop
head).  This file discharges the STRUCTURAL PLUMBING of the second one and names
the genuine machine content that remains.

## What `DivLoopProgress` is, and why arm 2 is a genuine second residual

`DivLoopProgress` (`DivCorrClose.lean:123`) is the `interp_run` main-loop
forward simulation, two arms mirroring `DivergeSim.DivStep`:

* **arm 1** — a head statement `s` that runs *normally*
  (`ExecS st d env s st' .normal`) at the loop head executing `s :: ss` drives
  ≥ 1 non-halting machine step to the loop head executing the tail `ss` for the
  post-state `st'` (one dispatch → `exec_stmt` → back-edge iteration);
* **arm 2** — a head statement that is INTERNALLY still-running for `n` fuel
  (`SApprox n st d env s`, the within-statement divergence family — a diverging
  inner `while`/`for` or a non-terminating closure body) drives ≥ n+1 machine
  steps from the loop head.

The two arms are NOT reducible to one another.  Arm 2 does not conclude an exit
`divCorr` (a still-running statement never returns to the loop head), only a step
count.  One might hope to derive arm 2 from arm 1 by `Approx.head` +
`DivergeSim.divStep_run`, but `divStep_run` consumes a *full* `DivStep` — both
arms — so that route is circular.  Discharging arm 2 directly is a structural
induction over the whole mutual `SApprox`/`EApprox`/`ArgsApprox`/`CApprox`/
`FlApprox` family (`Vsa/While/ErrorSem.lean:345-523`), and EACH constructor that
recurses through `EvalE`/`ExecS`/`EvalArgs`/`ForCond`/`ExecInit`/`ExecStep`
demands the corresponding machine forward-simulation step.  That is the
still-running twin of the ENTIRE M4 sim layer — it does not exist as a Triple,
and it is emphatically not a forgetful bridge.  So arm 2 stays a NAMED machine
residual (`InterpLoopApprox` below), phrased at the `interp_run` loop head.

## What THIS file discharges

The `divCorr`-repackaging plumbing of arm 1 (the SAME move as
`divEntryDrive_of_driveToLoopHead`, `Vsa/Sim/EntryDrive.lean:128`): the genuine
machine seam concludes a RAW loop-head landing — `∃ m c₁ ghosts, 1 ≤ m ∧
StepsN m cH c₁ ∧ SegEntry@loopHead executing ss for st' ∧ Reflect c₁ env ss` —
and this file threads the `k = 0` reindex that turns it into the `divCorr` post
`DivLoopProgress` arm 1 demands.  Arm 2 is threaded verbatim.

`divLoopProgress_of_seams` reduces `DivLoopProgress Reflect` to the named-field
`InterpRunLoopSeams Reflect`; `divFamily_of_seams` then composes it with the
supplied `DivEntryDrive` to close `DivFamily L` modulo the three seams.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS SApprox Stmt Addr)
open Vsa.Sim.Scaffold (SegEntry)

namespace Vsa.Sim.DivLoopProgressClose

local notation "SpecSt" => Vsa.While.St

variable (Reflect : Config → Addr → List Stmt → Prop)

/-! ## §1. The two `interp_run` loop-head simulation seams

`InterpRunLoopSeams` bundles the genuine machine content `DivLoopProgress` rests
on, as a named-field `structure … : Prop where` (the CLAUDE.md-mandated shape for
a NEW post/entry predicate — model `FoundSt`/`GeomFacts`/`FrameCalc`).  Both
fields are phrased AT the `interp_run` dispatch-loop head (`interpLoopHeadPC =
0x8000448c`), where the divergence correspondence lives; each field's doc comment
names the machine seam that supplies it. -/

/-- **The two loop-head forward-simulation seams of `interp_run`.** -/
structure InterpRunLoopSeams : Prop where
  /-- **`iter` — one normal-step loop iteration.**  From the loop head executing
  `s :: ss` for `(st, d, env)`, when the head statement `s` runs normally to
  `st'` (`ExecS st d env s st' .normal`), the machine takes ≥ 1 non-halting step
  to the loop head executing the TAIL `ss` for `st'` (fresh `∃`-packed layout
  ghosts, the loop-head config reflecting `(env, ss)` via `Reflect`).  This is
  the `interp_run` back-edge iteration — dispatch on the current statement node,
  `jal exec_stmt`, advance the statement cursor, `bne`/`j` back to the loop head.
  SUPPLIER: the progress-only ("took ≥ 1 step, still corresponds", forgetting
  output and final value) skeleton of the M4 `exec_stmt` case Triples — the same
  `hterm`-side machine content, re-landed at the loop back-edge (the M4 rows'
  `SegEntry`→`SegExit` spans over `exec_stmt`, wrapped by the interp-loop
  dispatch prefix + advance/back-edge suffix).  It concludes a RAW loop-head
  landing; the `divCorr` `k = 0` repackaging is done by
  `divLoopProgress_of_seams` here. -/
  iter :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
      ExecS st d env s st' .normal →
      ∀ (cH : Config)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
        Reflect cH env (s :: ss) →
        ∃ (m : Nat) (c₁ cH' : Config)
          (g' : (R : Register) → Option (RegisterType R))
          (N' : NativeAddrs) (A' : Arena) (SL' : StackLayout) (φf' φc' : Addr → Nat)
          (dLeft' aLeft' : Nat) (m0' : Mem),
          1 ≤ m ∧ StepsN m cH c₁ ∧
          StepsN 0 c₁ cH' ∧
          SegEntry g' N' A' SL' φf' φc' st' d dLeft' aLeft' interpLoopHeadPC m0' cH' ∧
          Reflect cH' env ss
  /-- **`approx` — within-statement divergence.**  From the loop head executing
  `s :: ss`, when the head statement is internally still-running for `n` fuel
  (`SApprox n st d env s`), the machine takes ≥ n+1 steps (no exit
  correspondence: a diverging head never returns to the loop head).  SUPPLIER:
  the still-running per-relation progress simulation over the mutual
  `SApprox`/`EApprox`/`ArgsApprox`/`CApprox`/`FlApprox` family — the divergence
  twin of the M4 `eval_expr`/`exec_stmt` sim layer, phrased from the `interp_run`
  loop-head dispatch into `s`.  This is genuine machine content orthogonal to
  `iter` (it counts the head's OWN internal rule steps); it is NOT derivable from
  `iter` (see the file header). -/
  approx :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (n : Nat),
      SApprox n st d env s →
      ∀ (cH : Config)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
        Reflect cH env (s :: ss) →
        ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁

/-! ## §2. `DivLoopProgress` from the two seams

Arm 1 threads the `iter` seam's RAW loop-head landing into a `divCorr` with `k = 0`
(the `StepsN 0 c₁ cH'` witness makes the exit config `cH'` reachable-in-0 from
`c₁`, so the reached config is `c₁` and its `divCorr` carries `cH'` as the
loop-head landing — exactly the `k = 0` reindex `divEntryDrive_of_driveToLoopHead`
uses).  Arm 2 is `approx` verbatim. -/

/-- **`DivLoopProgress` reduced to `InterpRunLoopSeams`.**  The two `interp_run`
loop-head seams discharge the divergence-arm loop-body progress residual: arm 1
repackages `iter`'s raw landing into the `divCorr` exit correspondence (`k = 0`),
arm 2 is `approx`.  All the reachability/`divCorr`-packaging plumbing is proved
here; the two `InterpRunLoopSeams` fields are the honest machine residuals. -/
theorem divLoopProgress_of_seams (h : InterpRunLoopSeams Reflect) :
    DivCorrClose.DivLoopProgress Reflect := by
  refine ⟨?_, ?_⟩
  · -- Arm 1: normal head step → ≥ 1 step to a `divCorr` for the tail.
    intro st d env s ss st' hExec cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
    obtain ⟨m, c₁, cH', g', N', A', SL', φf', φc', dLeft', aLeft', m0',
      hm, hsteps, hsteps0, hSeg', hRefl'⟩ :=
      h.iter st d env s ss st' hExec cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
    -- `c₁` is the reached config; its `divCorr` uses the `k = 0` landing `cH'`.
    exact ⟨m, c₁, hm, hsteps,
      cH', 0, g', N', A', SL', φf', φc', dLeft', aLeft', m0',
      hsteps0, hSeg', hRefl'⟩
  · -- Arm 2: internally still-running head → ≥ n+1 steps.
    intro st d env s ss n hApprox cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
    exact h.approx st d env s ss n hApprox cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl

/-! ## §3. `DivFamily L` closed on the drive + the two seams

Composes `divLoopProgress_of_seams` with `DivCorrClose.divFamily_closed`.  The
entry `DivEntryDrive` is threaded as a hypothesis — it is supplied by
`Vsa/Sim/DriveToLoopHeadSpans.lean`'s `driveToLoopHead_interpRunLayout` +
`Vsa/Sim/EntryDrive.lean`'s `divEntryDrive_of_driveToLoopHead` (whose three
`interp_run` prologue seams another agent owns); we do NOT close it here. -/

/-- **`DivFamily L` closed** on the shared entry drive (`hEntry`) plus the two
`interp_run` loop-head seams (`InterpRunLoopSeams`).  This is the divergence-arm
capstone reseated on exactly three honest machine residuals: the prologue drive
(shared with the term arm), the loop back-edge iteration (`iter`), and the
within-statement divergence simulation (`approx`).  Feed `hEntry` from
`divEntryDrive_of_driveToLoopHead (… driveToLoopHead_interpRunLayout …)`. -/
theorem divFamily_of_seams (L : Layout)
    (hEntry : DivCorrClose.DivEntryDrive Reflect L)
    (hSeams : InterpRunLoopSeams Reflect) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  DivCorrClose.divFamily_closed Reflect L hEntry (divLoopProgress_of_seams Reflect hSeams)

#print axioms divLoopProgress_of_seams
#print axioms divFamily_of_seams

end Vsa.Sim.DivLoopProgressClose
