import Vsa.Sim.ExecWhile
import Vsa.Sim.ExecFor
import Vsa.Sim.EvalArgs
import Vsa.Sim.LoopStep

/-!
# `LoopSteps` — Shape-C step-contract PRODUCERS for the un-produced loop shapes

("Step 4" of `experiments/interp-sim-completion-plan.md`, Shape C of
`experiments/exponentiation-endgame-design.md`.)

The M4 loop cases (`while`, `for`, `block`-seq, call-`args`) are landed
CONDITIONAL on named per-iteration step contracts:

* `ExecWhileStep` — consumed by `execWhileExit`/`execWhileLoopSim`
  (`Vsa/Sim/ExecWhile.lean`, `ExecWhile2.lean`);
* `ExecForStep` — consumed by `execForExit`/`execForLoopSim`
  (`Vsa/Sim/ExecFor.lean`);
* `EvalArgsStep` — consumed by `evalArgsLoop`/`evalArgsCons`
  (`Vsa/Sim/EvalArgs.lean`);
* `ExecSeqStep` — consumed by `execSeqLoop` (`Vsa/Sim/ExecSeqLoop.lean`),
  **already produced** by `execBlockStep` (`Vsa/Sim/ExecBlock2.lean`).

`ExecSeqStep` is the exemplar: `execBlockStep` produces it from (a) the head
recursion IH (`ExecIH`, threaded through `armExec_rec` at the `jal exec_stmt`),
and (b) ONE mechanical machine-iteration oracle `hbody` (the ~250-line
setup ≫ `armExec_rec` ≫ status-split ≫ back-edge decode) plus the φ-alloc glue
`hphi`. The spec-side disjunct marshalling — the ~15 lines mapping the machine
outcome into `ExecSeqStep`'s `normal ∨ abrupt` post — is proven ONCE inside the
producer, not re-derived per site.

The other three shapes had **no producer** (their `hstep` was consumed only
abstractly). This file supplies them, in the exact `execBlockStep` mould, so
each shape's residual collapses to the same two mechanical inputs it does for
`ExecSeqStep`:

1. the recursion IH(s) — `EvalIH` for the cond eval and/or `ExecIH` for the
   body — which STAY hypothetical (mission point 3: the `jal eval_expr` /
   `jal exec_stmt` in the body IS the IH; a step contract with a callee `jal`
   is conditional on it, not discharged);
2. one machine-iteration **body oracle** `hbody`: from the loop-head config,
   the compiled body chain runs to the branch outcome, packaged as the
   contract's post disjunction. This is exactly the shape a
   `#derive_case`/`chain_facts` segment ≫ `armTail_rec`/`armExec_rec`
   (IH seam) ≫ `loopStep` back-edge produces (`LoopStep.loopStep`,
   `EvalRecCommon.armTail_rec`, `ExecBlock.armExec_rec`).

Because the post shape of each contract is FIXED (a `Config → Prop`
disjunction), the producer's job is pure `Triple`/disjunction algebra: it
consumes the oracle's raw `∃ c', Steps c c' ∧ (post-disjunction)` and re-emits
the `Triple`, threading the loop-back φ-upgrade (`stFin`-sized extension) where
the contract states its extension over `stFin` rather than the intermediate
`st'`. This is the `execBlockStep` marshalling, generalised.

## What is mechanical vs. what remains

MECHANICAL (this file): the disjunct/`Triple` marshalling for all three shapes,
proven once each — a ~10-line body per producer. The three are near-identical
(while/for share the two-disjunct `loop-back ∨ exit` post keyed on
`bodyStatus`; args has the degenerate single-disjunct always-loop-back post),
so this is the shape-level factoring the exponentiation mandate asks for.

REMAINS per shape (the genuine machine content, NOT dischargeable here — same
status as `execBlockStep`'s open `hbody`): the body oracle `hbody`, i.e. the
compiled loop-body chain decode. For while/for that chain is
`cond-eval-setup ≫ jal eval_expr (EvalIH) ≫ value_truthy ≫ jal exec_stmt
(ExecIH) ≫ status-dispatch ≫ back-edge` — a TWO-IH body; for args it is
`arg-load ≫ jal eval_expr (EvalIH) ≫ 24-byte Value copy ≫ i++ ≫ bne back-edge`
— a ONE-IH body. Neither loop body is yet decoded as a site battery
(`ExecWhileSites` covers only the trivial `li a0,0 ; j` exit tail; there is no
`for`/`args` body-site file), and `ExecBlock2.execBlockStep`'s analogous
`hbody` is likewise still open pending the mutual-recursor scaffolding +
`exprRepr_agreeP` (AST-repr transport across the `sd i` spill). So the honest
end-state is: the step-contract MARSHALLING is now uniform and closed for all
four loop shapes; the residual is the single per-shape body-chain oracle, which
is a `#derive_case` + `armTail_rec`/`armExec_rec` + `loopStep` assembly gated on
the same `exprRepr_agreeP`/mutual-recursor pieces the seq-loop shape already
awaits — reported precisely below and in `experiments/loop-fanout.md`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

local notation "St" => Vsa.While.St

/-! ## `execWhileStepOf` — produce `ExecWhileStep` from the body oracle

The `while` analogue of `execBlockStep`. `ExecWhileStep` is definitionally a
`Triple` from the loop-head `ExecEntry` (∧ output pin) to the two-disjunct post
`(loop-back re-entry) ∨ (exit)`. The producer takes:

* `hbody` — the machine iteration: from any loop-head config satisfying the
  entry precondition, the compiled body runs (`Steps`) to a config satisfying
  the SAME two-disjunct post, but with the loop-back φ-extension stated over the
  intermediate `stMid`'s store sizes (what the body itself establishes);
* `hphi` — the φ-alloc upgrade lifting that `stMid`-sized extension to the
  `stFin`-sized extension the contract's post demands (identical role to
  `execBlockStep`'s `hphi`; on the exit disjunct nothing to upgrade).

The body oracle `hbody` internally consumes the cond `EvalIH` and body `ExecIH`
(via `armTail_rec`/`armExec_rec`); they are the `jal` callees and stay inside
`hbody`, exactly as mission point 3 requires. -/
theorem execWhileStepOf
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stMid stFin : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (bodyStatus loopStatus : Status)
    -- the machine-iteration body oracle (the loop-body chain decode); φ-extension
    -- stated over the INTERMEDIATE `stMid`'s sizes (what one iteration establishes):
    (hbody : ∀ cfg : Config,
      (ExecEntry g N A SL φf φc st d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet m0 cfg
        ∧ cfg.σ.sailOutput = out0) →
      ∃ cfg' : Config, Vsa.Machine.Steps cfg cfg' ∧
        ((((bodyStatus = .normal ∨ bodyStatus = .cont) ∧
          ∃ (φf' φc' : Addr → Nat),
            PhiExtends φf φf' stMid.store.frames.size ∧
            PhiExtends φc φc' stMid.store.closures.size ∧
            ExecEntry g N A SL φf' φc' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
              cfg'.σ.mem cfg' ∧ cfg'.σ.sailOutput = out0 ∧
            (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
              cfg'.σ.mem[a]? = m0[a]?)))
        ∨ (¬ (bodyStatus = .normal ∨ bodyStatus = .cont) ∧
          ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size stMid loopStatus sp r aRet m0 cfg')))
    -- the loop-back φ-alloc upgrade (stMid-sized extension → stFin-sized), preserving
    -- the re-entry `ExecEntry` and its output/memory-agreement clauses:
    (hphi : ∀ (φf' φc' : Addr → Nat) (cfg' : Config),
      PhiExtends φf φf' stMid.store.frames.size →
      PhiExtends φc φc' stMid.store.closures.size →
      ExecEntry g N A SL φf' φc' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
        cfg'.σ.mem cfg' →
      ∃ (φf'' φc'' : Addr → Nat),
        PhiExtends φf φf'' stFin.store.frames.size ∧
        PhiExtends φc φc'' stFin.store.closures.size ∧
        ExecEntry g N A SL φf'' φc'' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
          cfg'.σ.mem cfg') :
    ExecWhileStep g N A SL φf φc st d env c b sp r aInterp aStmt aEnv aRet m0 out0
      stMid stFin bodyStatus loopStatus := by
  intro cfg hpre
  obtain ⟨cfg', hsteps, hpost⟩ := hbody cfg hpre
  refine ⟨cfg', hsteps, ?_⟩
  rcases hpost with ⟨hlb, φf', φc', hpf, hpc, hEntry, hout, hmem⟩ | ⟨hne, hexit⟩
  · -- loop-back: upgrade the φ-extension from `stMid`-sized to `stFin`-sized.
    left
    refine ⟨hlb, ?_⟩
    obtain ⟨φf'', φc'', hpf'', hpc'', hEntry''⟩ := hphi φf' φc' cfg' hpf hpc hEntry
    exact ⟨φf'', φc'', hpf'', hpc'', hEntry'', hout, hmem⟩
  · -- exit: no φ-upgrade needed (the exit is stated at the entry maps directly).
    right
    exact ⟨hne, hexit⟩

/-! ## `execForStepOf` — produce `ExecForStep` from the body oracle

Structurally IDENTICAL to `execWhileStepOf` (the `for` head sits at the child
scope `outer` over `.forStmt oinit ocond ostep b`; the post disjunction is the
same `loop-back ∨ exit` keyed on `bodyStatus`). This is the shape-level reuse:
one marshalling proof serves both re-dispatch loops. -/
theorem execForStepOf
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stMid stFin : St) (d : Nat) (outer : Addr)
    (oinit : Option Stmt) (ocond ostep : Option Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (bodyStatus loopStatus : Status)
    (hbody : ∀ cfg : Config,
      (ExecEntry g N A SL φf φc st d outer (.forStmt oinit ocond ostep b)
        sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0) →
      ∃ cfg' : Config, Vsa.Machine.Steps cfg cfg' ∧
        ((((bodyStatus = .normal ∨ bodyStatus = .cont) ∧
          ∃ (φf' φc' : Addr → Nat),
            PhiExtends φf φf' stMid.store.frames.size ∧
            PhiExtends φc φc' stMid.store.closures.size ∧
            ExecEntry g N A SL φf' φc' stMid d outer (.forStmt oinit ocond ostep b)
              sp r aInterp aStmt aEnv aRet cfg'.σ.mem cfg' ∧ cfg'.σ.sailOutput = out0 ∧
            (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
              cfg'.σ.mem[a]? = m0[a]?)))
        ∨ (¬ (bodyStatus = .normal ∨ bodyStatus = .cont) ∧
          ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size stMid loopStatus sp r aRet m0 cfg')))
    (hphi : ∀ (φf' φc' : Addr → Nat) (cfg' : Config),
      PhiExtends φf φf' stMid.store.frames.size →
      PhiExtends φc φc' stMid.store.closures.size →
      ExecEntry g N A SL φf' φc' stMid d outer (.forStmt oinit ocond ostep b)
        sp r aInterp aStmt aEnv aRet cfg'.σ.mem cfg' →
      ∃ (φf'' φc'' : Addr → Nat),
        PhiExtends φf φf'' stFin.store.frames.size ∧
        PhiExtends φc φc'' stFin.store.closures.size ∧
        ExecEntry g N A SL φf'' φc'' stMid d outer (.forStmt oinit ocond ostep b)
          sp r aInterp aStmt aEnv aRet cfg'.σ.mem cfg') :
    ExecForStep g N A SL φf φc st d outer oinit ocond ostep b
      sp r aInterp aStmt aEnv aRet m0 out0 stMid stFin bodyStatus loopStatus := by
  intro cfg hpre
  obtain ⟨cfg', hsteps, hpost⟩ := hbody cfg hpre
  refine ⟨cfg', hsteps, ?_⟩
  rcases hpost with ⟨hlb, φf', φc', hpf, hpc, hEntry, hout, hmem⟩ | ⟨hne, hexit⟩
  · left
    refine ⟨hlb, ?_⟩
    obtain ⟨φf'', φc'', hpf'', hpc'', hEntry''⟩ := hphi φf' φc' cfg' hpf hpc hEntry
    exact ⟨φf'', φc'', hpf'', hpc'', hEntry'', hout, hmem⟩
  · right
    exact ⟨hne, hexit⟩

/-! ## `evalArgsStepOf` — produce `EvalArgsStep` from the body oracle

The args-loop shape is strictly SIMPLER: no abrupt exit, so the post is the
single always-loop-back disjunct (no `bodyStatus` keying). `EvalArgsStep` is
definitionally `EvalE st d env e st' v → Triple (SegEntry) (loop-back post)`;
the producer discharges the spec-side `EvalE` premise then forwards the body
oracle's outcome, threading the `stFin`-sized φ-upgrade exactly as above. The
body oracle internally consumes the one arg `EvalIH` at its `jal eval_expr`. -/
theorem evalArgsStepOf
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stMid stFin : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
    (dLeft aLeft : Nat) (p : Nat) (m0 : Mem) (v : Value)
    -- the machine-iteration body oracle; φ-extension over the intermediate `stMid`:
    (hbody : ∀ cfg : Config,
      SegEntry g N A SL φf φc st d dLeft aLeft p m0 cfg →
      ∃ cfg' : Config, Vsa.Machine.Steps cfg cfg' ∧
        ∃ (φf' φc' : Addr → Nat),
          PhiExtends φf φf' stMid.store.frames.size ∧
          PhiExtends φc φc' stMid.store.closures.size ∧
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
            cfg'.σ.mem[a]? = m0[a]?) ∧
          SegEntry g N A SL φf' φc' stMid d dLeft aLeft p cfg'.σ.mem cfg')
    -- the φ-alloc upgrade (stMid-sized → stFin-sized), preserving the re-entry
    -- `SegEntry` and the memory-frame clause:
    (hphi : ∀ (φf' φc' : Addr → Nat) (cfg' : Config),
      PhiExtends φf φf' stMid.store.frames.size →
      PhiExtends φc φc' stMid.store.closures.size →
      SegEntry g N A SL φf' φc' stMid d dLeft aLeft p cfg'.σ.mem cfg' →
      ∃ (φf'' φc'' : Addr → Nat),
        PhiExtends φf φf'' stFin.store.frames.size ∧
        PhiExtends φc φc'' stFin.store.closures.size ∧
        SegEntry g N A SL φf'' φc'' stMid d dLeft aLeft p cfg'.σ.mem cfg') :
    EvalArgsStep g N A SL φf φc st d env e es dLeft aLeft p m0 stMid stFin v := by
  intro _hE cfg hpre
  obtain ⟨cfg', hsteps, φf', φc', hpf, hpc, hmem, hEntry⟩ := hbody cfg hpre
  refine ⟨cfg', hsteps, ?_⟩
  obtain ⟨φf'', φc'', hpf'', hpc'', hEntry''⟩ := hphi φf' φc' cfg' hpf hpc hEntry
  exact ⟨φf'', φc'', hpf'', hpc'', hmem, hEntry''⟩

/-! ## Discharging the loop rules from the producers

With the producers above, the loop rules become fully closed on the mechanical
body oracle: substitute `execWhileStepOf`/`execForStepOf`/`evalArgsStepOf` for
the abstract `hstep` at the consumers' application sites. These wrappers show
the exact substitution (each is the consumer with its `hstep` supplied by the
matching producer, leaving the body-oracle + φ-glue + IH as the sole residuals),
so no existing theorem statement changes. -/

/-- `execWhileExit` with its `hstep` supplied by `execWhileStepOf`: the three
non-recursive `whileStmt` exits, reduced to the per-shape body oracle. -/
theorem execWhileExit_of_bodyOracle
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (mkBody : ∀ (φf φc : Addr → Nat) (st stMid _stFin : St)
        (bodyStatus loopStatus : Status) (m0 : Mem) (out0 : Array String),
        ∀ cfg : Config,
          (ExecEntry g N A SL φf φc st d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet m0 cfg
            ∧ cfg.σ.sailOutput = out0) →
          ∃ cfg' : Config, Vsa.Machine.Steps cfg cfg' ∧
            ((((bodyStatus = .normal ∨ bodyStatus = .cont) ∧
              ∃ (φf' φc' : Addr → Nat),
                PhiExtends φf φf' stMid.store.frames.size ∧
                PhiExtends φc φc' stMid.store.closures.size ∧
                ExecEntry g N A SL φf' φc' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
                  cfg'.σ.mem cfg' ∧ cfg'.σ.sailOutput = out0 ∧
                (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
                  cfg'.σ.mem[a]? = m0[a]?)))
            ∨ (¬ (bodyStatus = .normal ∨ bodyStatus = .cont) ∧
              ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size stMid loopStatus sp r aRet m0 cfg')))
    (mkPhi : ∀ (φf φc : Addr → Nat) (stMid stFin : St),
        ∀ (φf' φc' : Addr → Nat) (cfg' : Config),
          PhiExtends φf φf' stMid.store.frames.size →
          PhiExtends φc φc' stMid.store.closures.size →
          ExecEntry g N A SL φf' φc' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
            cfg'.σ.mem cfg' →
          ∃ (φf'' φc'' : Addr → Nat),
            PhiExtends φf φf'' stFin.store.frames.size ∧
            PhiExtends φc φc'' stFin.store.closures.size ∧
            ExecEntry g N A SL φf'' φc'' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
              cfg'.σ.mem cfg')
    (φf φc : Addr → Nat) (st st' : St) (status : Status) (m0 : Mem)
    (out0 : Array String)
    (hExec : ExecS st d env (.whileStmt c b) st' status)
    (bodyStatus : Status) (hexit : ¬ (bodyStatus = .normal ∨ bodyStatus = .cont)) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet m0 cfg
        ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size st' status sp r aRet m0) :=
  execWhileExit g N A SL d env c b sp r aInterp aStmt aEnv aRet
    (fun φf φc st stMid stFin bs ls m0 out0 =>
      execWhileStepOf g N A SL φf φc st stMid stFin d env c b sp r aInterp aStmt aEnv aRet m0 out0
        bs ls (mkBody φf φc st stMid stFin bs ls m0 out0) (mkPhi φf φc stMid stFin))
    φf φc st st' status m0 out0 hExec bodyStatus hexit

#print axioms execWhileStepOf
#print axioms execForStepOf
#print axioms evalArgsStepOf
#print axioms execWhileExit_of_bodyOracle

end Vsa.Sim
