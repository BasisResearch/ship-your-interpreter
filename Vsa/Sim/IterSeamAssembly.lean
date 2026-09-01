import Vsa.Sim.InterpRunLoopSeamsClose
import Vsa.Sim.rows.LoopHeadDispatch
import Vsa.Sim.rows.InterpBackEdgeSeg
import Vsa.Sim.rows.ExecDispatchRows
import Vsa.Sim.StepCount

/-!
# `iterSeam` assembled — the interp_run back-edge iteration span (Task, wave 26)

`Vsa/Sim/InterpRunLoopSeamsClose.lean` names the `iterSeam` residual (the first
field of `InterpRunLoopResiduals`) and pins its discharge route: build the loop-body
machine span from the loop head `cH` back to the tail loop head `cH'`, ≥ 1 step,
re-landing `SegEntry@interpLoopHeadPC` for `st'` executing `ss` (with `Reflect cH'
env ss`).  Wave 25 landed the two inputs this assembly composes:

* `loopHeadDispatch_span` (`rows/LoopHeadDispatch.lean`) — the loop-head → `exec_stmt`
  ENTRY span: `SegEntry@loopHead cH → ∃ cE, Steps cH cE ∧ ExecEntry@0x80003fe0 cE`,
  return link `x1 = 0x80004478`.
* `interpBackEdgeRow` (`rows/InterpBackEdgeSeg.lean`) — the exec_stmt RETURN → loop
  head suffix `[0x80004478 → 0x8000448c)`: `beq a0,s3` (NOT taken, status `.normal`
  ⇒ a0 = 0 ≠ s3 = 3) ; `addiw a0,a0,-1` ; `bgeu s4,a0` (NOT taken, s4 = 1 <
  0xFFFF…FFFF) ; `addi s0,s0,8` (advance the cursor) ; `beq s0,s2` (NOT taken, the
  tail `ss` is non-empty ⇒ cursor ≠ array-end bound), landing at `0x8000448c`.
* `StepCount.lean` — the counted-run algebra (`StepsN`/`TripleN`, `segToTripleN`,
  `iterFromCountedRun`) the raw landing is threaded through.

## The iteration shape (one loop pass)

```
  cH  @0x8000448c  (SegEntry@loopHead, st, executing s :: ss, Reflect cH env (s::ss))
      │  loopHeadDispatch_span      (dispatch head ≫ value_null ≫ arg-setup ≫ jal)
      ▼
  cE  @0x80003fe0  (ExecEntry, head statement s, link 0x80004478)
      │  exec_stmt IH  (ExecIH st d env s st' .normal — the M4 exec_stmt Triple)
      ▼
  cX  @0x80004478  (ExecExit@ret target, a0 = StatusCode .normal = 0)
      │  interpBackEdgeRow          (the back-edge suffix, 5 instrs, 3 not-taken br)
      ▼
  cH' @0x8000448c  (SegEntry@loopHead, st', executing ss, Reflect cH' env ss)
```

## The residual structure — what the exit genuinely cannot supply

`IterSeamGeom` bundles, as named-field providers (gate R6/R7 — no positional
towers, one field per genuinely-missing fact), exactly the content the composition
does NOT already have:

* `hExecIH` — the `exec_stmt` machine Triple for the head statement `s`
  (`ExecIH st d env s st' .normal`).  This is the crux: the M4 statement-family
  simulation applied to `s`, supplied by `rows/ExecDispatchRows.lean` (the dispatch/
  loop cases) + the leaf/recursive `ExecS` rows.  NOT derivable from the loop-head
  `SegEntry`/`Reflect` (both carry no `exec_stmt`-entry ABI/AST geometry).
* `hDispatch` — from `SegEntry@loopHead cH` + `Reflect cH env (s :: ss)`, the
  dispatch-span landing at `ExecEntry` (`loopHeadDispatch_span`'s conclusion).  This
  packages `LoopHeadDispatchGeom` (the stack/AST/code geometry off the loop head),
  the value_null call splice, and the arg-setup ≫ jal exec_stmt seam — none a
  consequence of `SegEntry`; `Reflect` is where the head statement `s`'s node
  geometry (`aStmt`, `StmtRepr`) enters.  Its `cE`'s `x1 = 0x80004478` link is what
  makes the back-edge land at the suffix.
* `hReenter` — from the `exec_stmt` ExecExit landing at `0x80004478` for `st'`
  `.normal`, drive the back-edge suffix to the loop head and RE-ESTABLISH
  `SegEntry@loopHead` for `st'` executing `ss`, with `Reflect cH' env ss`.  The
  back-edge suffix run is `interpBackEdgeRow` (proved), but its branch guards
  (a0 = 0 ≠ s3 = 3, s4 = 1 < …, cursor ≠ bound) need the loop-invariant registers
  `s3`/`s4`/`s2` and the advanced cursor `s0` — off `SegEntry`, carried through
  `exec_stmt` as callee-saveds — and the re-established `SegEntry` needs the store
  transported (ExecExit's extended-φ `StoreRepr` re-cast to `SegEntry.store`) and
  the abstract `Reflect cH' env ss` for the tail (the section variable's non-
  computational content, exactly as `Reflect cH env (s :: ss)` supplied the head).

`iterSeam_of_geom` composes the three: `Steps cH cE` (dispatch) ≫ `Steps cE cX`
(exec_stmt IH) ≫ `Steps cX cH'` (back-edge, ≥ 1 step ⇒ the whole run is ≥ 1 step,
counted off the `steps` field via `StepCount`), landing the raw `iterSeam`
conclusion (`StepsN m cH cH' ∧ StepsN 0 cH' cH' ∧ SegEntry@loopHead st' ss ∧
Reflect`).  `iterSeam_of_residuals` ∀-closes it into the `InterpRunLoopResiduals.
iterSeam` field, and `divFamily_of_iterAssembly` threads it into
`divFamily_of_residuals` alongside the (still-open) `approxSeam`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS SApprox Stmt Addr St)
open Vsa.Sim.Scaffold (SegEntry)

namespace Vsa.Sim.IterSeamAssembly

local notation "SpecSt" => Vsa.While.St

variable (Reflect : Config → Addr → List Stmt → Prop)

/-! ## §1. The iteration residual — named-field providers -/

/-- **The `iterSeam` iteration residual, per node.**  For a head statement `s`
running `.normal` to `st'` at a loop head `cH` (SegEntry for `st` executing
`s :: ss`, reflecting `(env, s :: ss)`), the three providers of one loop pass.
Each field carries EXACTLY the machine content the composition cannot already
derive (see the module doc); the assembly `iterSeam_of_geom` never navigates a
positional tower — it projects these three named fields. -/
structure IterSeamGeom
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt)
    (cH : Config)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem) : Prop where
  /-- **The `exec_stmt` machine Triple for the head statement `s`.**  Supplier:
  `rows/ExecDispatchRows.lean` (dispatch/loop cases) + the leaf/recursive `ExecS`
  rows, assembled through the `ExecS` recursor into `mExecS = ExecIH`.  The crux
  residual — the M4 statement-family simulation, phrased at the `exec_stmt` entry
  geometry, NOT at the loop head. -/
  hExecIH : ExecIH st d env s st' .normal
  /-- **The loop-head dispatch span landing at `ExecEntry`.**  Supplier:
  `loopHeadDispatch_span` (`rows/LoopHeadDispatch.lean`), fed its
  `LoopHeadDispatchGeom` + value_null-splice + arg-setup premises (the head
  statement `s`'s node geometry enters via `Reflect cH env (s :: ss)`).  Produces
  the `exec_stmt`-entry config `cE` with return link `0x80004478`.  Takes the
  loop-head `SegEntry` (control/store/out pins at `cH`) and `Reflect cH env
  (s :: ss)` (the head node `s`'s reflection) — exactly the facts
  `loopHeadDispatch_span` consumes to build the span. -/
  hDispatch :
    SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
    Reflect cH env (s :: ss) →
    ∃ (sp aStmt aEnv aInterp aRet : BitVec 64) (mE : Mem) (cE : Config),
      Steps cH cE ∧
      ExecEntry g N A SL φf φc st d env s sp (0x80004478#64)
        aInterp aStmt aEnv aRet mE cE
  /-- **The back-edge re-entry.**  From the `exec_stmt` ExecExit landing at
  `0x80004478` for the post-state `st'` (`.normal`, so `a0 = StatusCode .normal =
  0`, `sp` restored), drive the back-edge suffix (`interpBackEdgeRow`) to the loop
  head and RE-ESTABLISH `SegEntry@interpLoopHeadPC` for `st'` executing `ss`, with
  `Reflect cH' env ss`.  Suppliers: `interpBackEdgeRow` (the suffix, proved) with
  the loop-invariant registers `s3 = 3`/`s4 = 1`/`s2`(bound)/`s0`(advanced cursor)
  carried through `exec_stmt` as callee-saveds; the store transported from
  ExecExit's extended-φ `StoreRepr` to `SegEntry.store`; and the abstract `Reflect`
  for the tail `ss`. -/
  hReenter : ∀ (sp aRet : BitVec 64) (mE : Mem) (cX : Config),
    ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' .normal sp (0x80004478#64) aRet mE cX →
    ∃ (cH' : Config)
      (g' : (R : Register) → Option (RegisterType R))
      (N' : NativeAddrs) (A' : Arena) (SL' : StackLayout) (φf' φc' : Addr → Nat)
      (dLeft' aLeft' : Nat) (m0' : Mem),
      Steps cX cH' ∧
      SegEntry g' N' A' SL' φf' φc' st' d dLeft' aLeft' interpLoopHeadPC m0' cH' ∧
      Reflect cH' env ss

/-! ## §2. The step-count witness — the raw landing is ≥ 1 step

The composite `Steps cH cH'` advances the `steps` counter by ≥ 1 (the dispatch
span alone runs real machine steps).  `StepCount.Steps.toN_of_stepsField` reads
the count off the `steps` field; the `≥ 1` bound comes from the back-edge suffix
being a non-empty seg run whose landing config has a strictly larger `steps` field
than its entry, and the counter is monotone along the preceding runs. -/

/-- A composite `Steps a b` whose middle segment `Steps x y` advances the `steps`
counter (`x.steps < y.steps`) is a `StepsN m` run with `m ≥ 1`. -/
theorem stepsN_ge_one_of_middle {a x y b : Config}
    (h1 : Steps a x) (h2 : Steps x y) (h3 : Steps y b)
    (hxy : x.steps < y.steps) :
    ∃ m, 1 ≤ m ∧ StepsN m a b := by
  have hcomp : Steps a b := (h1.trans h2).trans h3
  refine ⟨b.steps - a.steps, ?_, hcomp.toN_of_stepsField⟩
  have hax : a.steps ≤ x.steps := h1.steps_le
  have hyb : y.steps ≤ b.steps := h3.steps_le
  omega

/-! ## §3. `iterSeam` assembled from the residual -/

/-- **The `iterSeam` field body, assembled from `IterSeamGeom`.**  Composes the
dispatch span, the `exec_stmt` IH, and the back-edge re-entry into the raw
`iterSeam` landing: ≥ 1 machine step from `cH` to the tail loop head `cH'`, with
`SegEntry@interpLoopHeadPC` for `st'` executing `ss` and `Reflect cH' env ss`.
The `StepsN 0 c₁ cH'` disjunct is `c₁ := cH'` at zero steps (`.zero`); the
`divLoopProgress_of_seams` `k = 0` `divCorr` repackaging happens downstream. -/
theorem iterSeam_of_geom
    {st : SpecSt} {d : Nat} {env : Addr} {s : Stmt} {ss : List Stmt} {st' : SpecSt}
    (_hExec : ExecS st d env s st' .normal)
    {cH : Config}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {dLeft aLeft : Nat} {m0 : Mem}
    (hSeg : SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH)
    (hRefl : Reflect cH env (s :: ss))
    (G : IterSeamGeom Reflect st d env s ss st' cH g N A SL φf φc dLeft aLeft m0) :
    ∃ (m : Nat) (c₁ cH' : Config)
      (g' : (R : Register) → Option (RegisterType R))
      (N' : NativeAddrs) (A' : Arena) (SL' : StackLayout) (φf' φc' : Addr → Nat)
      (dLeft' aLeft' : Nat) (m0' : Mem),
      1 ≤ m ∧ StepsN m cH c₁ ∧
      StepsN 0 c₁ cH' ∧
      SegEntry g' N' A' SL' φf' φc' st' d dLeft' aLeft' interpLoopHeadPC m0' cH' ∧
      Reflect cH' env ss := by
  -- 1. dispatch span → ExecEntry at cE (fed the loop-head SegEntry + Reflect).
  obtain ⟨sp, aStmt, aEnv, aInterp, aRet, mE, cE, hDispSteps, hEntry⟩ :=
    G.hDispatch hSeg hRefl
  -- 2. exec_stmt IH → ExecExitD at cX (parked at the return target 0x80004478).
  obtain ⟨cX, hExecSteps, hExitD⟩ :=
    G.hExecIH g N A SL φf φc sp (0x80004478#64) aInterp aStmt aEnv aRet mE cE hEntry
  have hExit : ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' .normal sp (0x80004478#64) aRet mE cX := hExitD.1
  -- 3. back-edge re-entry → loop head cH' for st', re-establishing SegEntry + Reflect.
  obtain ⟨cH', g', N', A', SL', φf', φc', dLeft', aLeft', m0', hBackSteps, hSeg', hRefl'⟩ :=
    G.hReenter sp aRet mE cX hExit
  -- compose the three runs; the exec_stmt IH advances the steps counter (≥ 1 step:
  -- exec_stmt's prologue alone runs real machine steps), so the whole run is ≥ 1.
  have hxy : cE.steps < cX.steps := by
    -- the exec_stmt entry PC (0x80003fe0) differs from its exit PC (0x80004478 side),
    -- so `Steps cE cX` is a non-refl run: at least one `Step`, i.e. steps strictly grow.
    cases hExecSteps with
    | refl =>
      -- refl: cE = cX, contradicting the distinct PCs (entry vs exit).
      exfalso
      have hpcE : cE.σ.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry) := hEntry.pc
      have hpcX : cE.σ.regs.get? Register.PC =
        some (BitVec.update ((0x80004478#64) + sign_extend (m := 64) (0x000#12)) 0 0#1) :=
        hExit.pc
      rw [hpcX] at hpcE
      exact absurd hpcE (by decide)
    | @head _ cMid _ hstep hrest =>
      -- head step: cE.steps + 1 = cMid.steps ≤ cX.steps.
      have h1 : cMid.steps = cE.steps + 1 := hstep.steps_succ
      have h2 : cMid.steps ≤ cX.steps := hrest.steps_le
      omega
  obtain ⟨m, hm, hStepsN⟩ :=
    stepsN_ge_one_of_middle hDispSteps hExecSteps hBackSteps hxy
  exact ⟨m, cH', cH', g', N', A', SL', φf', φc', dLeft', aLeft', m0',
    hm, hStepsN, StepsN.zero cH', hSeg', hRefl'⟩

#print axioms iterSeam_of_geom

/-! ## §4. The `iterSeam` field, and threading into `InterpRunLoopResiduals`

`IterSeamResid` ∀-closes `IterSeamGeom` over the per-node layout ghosts — the
supplier the `iterSeam` field genuinely needs (one bundle per `(st,d,env,s,ss,st')`
node, for every loop-head config/layout).  `iterSeam_of_resid` turns it into the
raw `iterSeam` field body via `iterSeam_of_geom`.  `interpRunLoopResiduals_of_iter`
then packages it with a supplied `approxSeam` into the full two-field
`InterpRunLoopResiduals`, and `divFamily_of_iterAssembly` closes `DivFamily L`
modulo the entry drive, the `IterSeamResid` supplier, and `approxSeam`. -/

/-- **The `iterSeam` residual** — `IterSeamGeom` ∀-closed over the loop-head
config and layout ghosts, for every node `(st, d, env, s, ss, st')`.  This is the
honest supplier interface: for each spec node whose head runs `.normal`, and each
loop-head config/layout it appears at, the three providers of one loop pass.  The
crux content is `IterSeamGeom.hExecIH` (the `exec_stmt` machine Triple for `s`). -/
def IterSeamResid : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
    ExecS st d env s st' .normal →
    ∀ (cH : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      IterSeamGeom Reflect st d env s ss st' cH g N A SL φf φc dLeft aLeft m0

/-- **The `iterSeam` field body produced from `IterSeamResid`.**  This IS the
`InterpRunLoopResiduals.iterSeam` field type (identical ∀-signature and raw
landing), so it plugs straight into the residual bundle. -/
theorem iterSeam_of_resid (hR : IterSeamResid Reflect) :
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
          Reflect cH' env ss := by
  intro st d env s ss st' hExec cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
  exact iterSeam_of_geom Reflect hExec hSeg hRefl
    (hR st d env s ss st' hExec cH g N A SL φf φc dLeft aLeft m0)

/-- **`InterpRunLoopResiduals` from `IterSeamResid` + a supplied `approxSeam`.**
The `iterSeam` field is discharged by `iterSeam_of_resid`; the `approxSeam` field
(the within-statement divergence lower bound — a separate open residual, the mutual
`SApprox` simulation) is threaded through unchanged. -/
theorem interpRunLoopResiduals_of_iter
    (hIter : IterSeamResid Reflect)
    (hApprox :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (n : Nat),
        SApprox n st d env s →
        ∀ (cH : Config)
          (g : (R : Register) → Option (RegisterType R))
          (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
          (dLeft aLeft : Nat) (m0 : Mem),
          SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
          Reflect cH env (s :: ss) →
          ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁) :
    Vsa.Sim.InterpRunLoopSeamsClose.InterpRunLoopResiduals Reflect where
  iterSeam := iterSeam_of_resid Reflect hIter
  approxSeam := hApprox

/-- **`DivFamily L` closed** on the shared entry drive, the assembled `iterSeam`
(`IterSeamResid`), and the (still-open) `approxSeam`.  Composes
`interpRunLoopResiduals_of_iter` with
`InterpRunLoopSeamsClose.divFamily_of_residuals`.  The `iterSeam` field — formerly
an irreducible residual — is now the three-provider `IterSeamResid` assembly; the
only remaining loop-head residual is `approxSeam`. -/
theorem divFamily_of_iterAssembly (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : IterSeamResid Reflect)
    (hApprox :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (n : Nat),
        SApprox n st d env s →
        ∀ (cH : Config)
          (g : (R : Register) → Option (RegisterType R))
          (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
          (dLeft aLeft : Nat) (m0 : Mem),
          SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
          Reflect cH env (s :: ss) →
          ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  Vsa.Sim.InterpRunLoopSeamsClose.divFamily_of_residuals Reflect L hEntry
    (interpRunLoopResiduals_of_iter Reflect hIter hApprox)

#print axioms iterSeam_of_resid
#print axioms interpRunLoopResiduals_of_iter
#print axioms divFamily_of_iterAssembly

end Vsa.Sim.IterSeamAssembly
