import Vsa.Sim.DivFamily
import Vsa.Sim.EntryHalts

/-!
# `DivCorrFamily` reseated on a CONCRETE loop-head correspondence

`Vsa/Sim/DivFamily.lean` (`divFamily_of_corr`) reduces the divergence arm
`DivFamily L` to the per-load residual `DivCorrFamily L` — "for every loaded
`(p, c)`, a correspondence `Corr` with its per-step progress residual
`DivStep Corr` and the entry `Corr c initSt 0 0 p`".  `Vsa/Sim/TermAssembly.lean`
(`divStep_vacuous`) then recorded the machine-checked verdict that the ONLY
genuine gap is the ENTRY (the trivial `Corr := False` satisfies `DivStep`
vacuously but fails the entry).

This file supplies a **concrete** `Corr` — the loop-head `SegEntry`
correspondence, packaged with `StepsN`-reachability so the entry and the per-step
progress compose additively — and reduces `DivCorrFamily L` to TWO precisely-named
residuals, discharging the structural plumbing (the reachability threading and the
entry reindex) axiom-clean:

* **`DivEntryDrive L`** — from `Loaded L p c`, the machine reaches (in some number
  of steps) a loop-head `SegEntry` executing the whole program `p` as the
  top-level statement list, over the initial store `initSt`.  This is EXACTLY the
  content of `EntryPrologueSpan`/`InterpInitStoreRepr`'s drive
  (`Loaded → SegEntry@0x8000448c`), reused verbatim — the SAME drive the entry
  endgame is gated on.
* **`DivLoopProgress`** — from a loop-head `SegEntry` executing `s :: ss` for the
  spec node `(st, d, env)`, one spec statement step (`ExecS … s → st' .normal`)
  drives ≥ 1 non-halting machine step to a loop-head `SegEntry` executing `ss`
  for `st'`; and an INTERNALLY still-running head (`SApprox n`) drives ≥ n+1
  steps.  This is the still-running (progress-only) analog of the M4 `exec_stmt`
  case Triples' loop-back-edge — the machine forward-simulation content, named.

`divCorrFamily_of` composes them: the concrete `divCorr` carries the reachability
witness, so `DivStep`'s progress arms prepend the entry drive's steps to the
loop-body steps (both `StepsN`, composed by `StepsN.trans_add`), and the entry
`divCorr c initSt 0 0 p` is `DivEntryDrive` at `k = 0` reindex.

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

namespace Vsa.Sim.DivCorrClose

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The concrete loop-head correspondence

`divCorr c st d env ss` says: from `c`, the machine reaches (in `k` steps, for
some layout ghosts) a loop-head `SegEntry` executing the top-level statement list
`ss` for the spec node `(st, d, env)`.  The `StepsN k`-reachability indirection is
what lets the divergence forward simulation THREAD its accumulated run: the entry
correspondence is `k = 0` (the loop-head reached from the loaded entry by the
prologue drive), and each spec step advances the loop head to the tail's
`SegEntry`, composing the drive-steps and body-steps additively.

`SegEntry` pins the spec STATE `st` (store + output) but not WHICH statements
remain nor the active scope `Addr`.  The top-level statement loop reflects those
in its induction registers (`s0` = current `Stmt*` cursor, the loop bound `s2`,
the scope pointer) — a reflection this file does NOT re-derive.  We thread it as
the abstract per-node predicate `Reflect cH env ss` (a section variable): the
loop-head config `cH` reflects "executing statement list `ss` in scope `env`".
Making it a parameter keeps `divCorr` a FAITHFUL correspondence (distinct
`(env, ss)` are distinct nodes) while naming the reflection as the honest content
the loop-body progress residual supplies. -/

variable (Reflect : Config → Addr → List Stmt → Prop)

/-- **The loop-head divergence correspondence.**  `c` reaches, in `k` machine
steps, a loop-head `SegEntry` (`interpLoopHeadPC = 0x8000448c`) executing the
top-level statement list `ss` for spec state `st`, depth `d`, scope `env` — for
SOME layout ghosts — with the loop-head config reflecting `(env, ss)` via
`Reflect`.  The `∃`-packed ghosts are exactly the ones the loop-body progress
picks; the spec node `(st, d, env, ss)` is the divergence family's index. -/
def divCorr (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∃ (cH : Config) (k : Nat)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    StepsN k c cH ∧
    SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH ∧
    Reflect cH env ss

/-! ## §2. The two named residuals

The genuine machine content the divergence arm rests on. -/

/-- **The entry drive residual** — `Loaded → loop-head SegEntry executing `p``.
From a loaded `(p, c)`, the machine reaches a loop-head `SegEntry` executing the
whole program `p` (as the top-level statement list) over the initial store
`initSt`, `d = 0`, scope `0`.  This is the `StepsN`-form of
`EntryPrologueSpan`/`InterpInitStoreRepr`'s `Loaded → SegEntry@loopHead` drive —
the SAME prologue drive (spill + `setjmp` first-return + loop setup, over the
`interp_init`-built store) the term-arm entry endgame is gated on, phrased for the
divergence correspondence. -/
def DivEntryDrive (L : Layout) : Prop :=
  ∀ (p : Program) (c : Config), Loaded L p c → divCorr Reflect c initSt 0 0 p

/-- **The loop-body progress residual** — the still-running per-statement forward
simulation at the top-level statement loop.  Two arms, mirroring `DivStep`:

* a head statement `s` that runs normally (`ExecS st d env s st' .normal`), at a
  loop-head `SegEntry` executing `s :: ss`, drives ≥ 1 non-halting machine step to
  a loop-head `SegEntry` executing `ss` for `st'` (one loop iteration: dispatch,
  run `exec_stmt`/`value_print`, back-edge to the loop head);
* an INTERNALLY still-running head (`SApprox n st d env s`) drives ≥ n+1 machine
  steps from the loop head (the within-statement divergence).

This is the progress-only (no output, no final value) analog of the M4
`exec_stmt` case Triples, restricted to the top-level loop back-edge.  It is
discharged by the same `LoopSteps`/`execWhileStepOf`-shaped machine seams that
supply `hterm`, forgetting everything but "took ≥ 1 step, still corresponds". -/
def DivLoopProgress : Prop :=
  (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
    ExecS st d env s st' .normal →
    ∀ (cH : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
      Reflect cH env (s :: ss) →
      ∃ m c₁, 1 ≤ m ∧ StepsN m cH c₁ ∧ divCorr Reflect c₁ st' d env ss) ∧
  (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (n : Nat),
    SApprox n st d env s →
    ∀ (cH : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
      Reflect cH env (s :: ss) →
      ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁)

/-! ## §3. `DivStep divCorr` from `DivLoopProgress`

The reachability indirection makes both `DivStep` arms mechanical: destructure the
`divCorr` reachability witness (`StepsN k c cH ∧ SegEntry@loopHead`), run the
`DivLoopProgress` arm from `cH`, and prepend the `k` drive-steps with
`StepsN.trans_add`. -/

/-- **`DivStep divCorr` reduced to `DivLoopProgress`.**  The concrete loop-head
correspondence satisfies the divergence per-step residual, given the loop-body
progress residual.  Arm 1: from `divCorr c (s::ss)` (= `StepsN k c cH ∧
SegEntry@loopHead executing s::ss`), the loop-body progress runs ≥ 1 step from
`cH` to a `divCorr` for the tail; prepending the `k` drive-steps
(`StepsN.trans_add`) gives ≥ 1 step from `c`.  Arm 2 (internal still-running):
same prepend, ≥ n+1 from `cH` becomes ≥ n+1 from `c` (`k + (n+1) ≥ n+1`). -/
theorem divStep_of_loopProgress (h : DivLoopProgress Reflect) :
    Vsa.Sim.DivStep (divCorr Reflect) := by
  refine ⟨?_, ?_⟩
  · -- Arm 1: normal head step.
    intro st d env s ss st' hExec c hc
    obtain ⟨cH, k, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hsteps, hSeg, hRefl⟩ := hc
    obtain ⟨m, c₁, hm, hbody, hc₁⟩ :=
      h.1 st d env s ss st' hExec cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
    refine ⟨k + m, c₁, ?_, hsteps.trans_add hbody, hc₁⟩
    exact Nat.le_trans hm (Nat.le_add_left m k)
  · -- Arm 2: internally still-running head.
    intro st d env s ss n hApprox c hc
    obtain ⟨cH, k, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hsteps, hSeg, hRefl⟩ := hc
    obtain ⟨m, c₁, hm, hbody⟩ :=
      h.2 st d env s ss n hApprox cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
    refine ⟨k + m, c₁, ?_, hsteps.trans_add hbody⟩
    exact Nat.le_trans hm (Nat.le_add_left m k)

/-! ## §4. `DivCorrFamily` from the two residuals

The entry `divCorr c initSt 0 0 p` is `DivEntryDrive` verbatim; the per-step
residual is `divStep_of_loopProgress`. -/

/-- **`DivCorrFamily` reseated on `DivEntryDrive` + `DivLoopProgress`.**  For every
loaded `(p, c)`, the concrete `divCorr` is the divergence correspondence: its entry
`divCorr c initSt 0 0 p` is `DivEntryDrive` (the prologue drive to the loop head,
executing `p`), and its `DivStep` is `divStep_of_loopProgress` (the loop-body
forward simulation).  This reseats the whole divergence arm on the TWO honest
machine residuals — the SAME prologue drive as the term arm's entry, and the
still-running per-statement progress — with all the reachability plumbing proved.

Fed to `Vsa.Sim.DivFamily.divFamily_of_corr`, this closes `DivFamily L` modulo
these two named residuals. -/
theorem divCorrFamily_of (L : Layout)
    (hEntry : DivEntryDrive Reflect L) (hProgress : DivLoopProgress Reflect) :
    Vsa.Sim.DivFamily.DivCorrFamily L := by
  intro p c hL
  exact ⟨divCorr Reflect, divStep_of_loopProgress Reflect hProgress, hEntry p c hL⟩

/-- **`DivFamily L` closed** on `DivEntryDrive` + `DivLoopProgress`, composing
`divCorrFamily_of` with `DivFamily.divFamily_of_corr`.  This is the divergence-arm
capstone hook: `stuck_sim`'s divergence family now rests on exactly the prologue
drive (shared with the term arm) and the loop-body progress residual — for the
abstract loop-head reflection `Reflect` the caller instantiates. -/
theorem divFamily_closed (L : Layout)
    (hEntry : DivEntryDrive Reflect L) (hProgress : DivLoopProgress Reflect) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  Vsa.Sim.DivFamily.divFamily_of_corr L (divCorrFamily_of Reflect L hEntry hProgress)

#print axioms divStep_of_loopProgress
#print axioms divCorrFamily_of
#print axioms divFamily_closed

end Vsa.Sim.DivCorrClose
