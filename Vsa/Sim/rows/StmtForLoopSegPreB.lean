import Vsa.Sim.ArmSegSplitTwins

/-!
# `StmtForLoopSegPreB` — the for-cond re-entry staging over `SegPreBundleB`
(Wave 44 pilot for twin 2)

The `stmtForLoop` field of `ApproxArmResid` lands at `FEntryC` — anchored on a
`SegEntry` at the for-cond control point `0x8000426c`.  The machine reaches that
point by **`j 0x8000426c` @0x80004258** (the post-init route; word `0x0140006f`)
or the taken `beqz a1,0x8000426c @0x80004244` (no-init) — interior control, NO
static `jal` targets it, so the jal-modelled `SegPreBundle` staging is
uninstantiable here (observation `nonevalchild-remaining-8-shape-map`).  This
pilot rides `SegPreBundleB` (`ArmSegSplitTwins` §2):

* `ForLoopReentryJSite` — the `j @0x80004258` site obs (`sigmaPost_jump_x0`;
  derivable from `stepObs_j` + the `Exec_stmtLoaded` byte pins; NAMED residual
  per Law 2).
* `ForLoopReentryInv` — the arm state at the `j` site with the light SegEntry
  facts staged.
* `forLoopSegPreB_of_inv` — **PROVED**: the inv marshals into
  `SegPreBundleB 0x8000426c` (the hop via `gregsHopInto_of_jx0Site` ≫
  `StepInto.of_gregsHop`) — the twin-2 instantiation at a real arm.
* `ForLoopReentryDispatch` — the dispatch residual (`SEntryC (.forStmt …)` +
  allocFrame + `ExecInit` → `LandedN 1` at the inv; the env_new ≫ init-exec ≫
  return routing is M4 arm-seg content).
* `stmtForLoop_field_of_dispatch` — the EXACT frozen `ApproxArmResid.stmtForLoop`
  field, composed through `stmtForLoop_splitB`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.While (St Stmt Expr Value Store Status Addr EvalE ForCond ExecInit ExecS)
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-- The for-cond re-entry control point (the `ld a2,16(s0)` cond load). -/
def forCondReentryPC : Nat := 0x8000426c

/-- **The `j @0x80004258` site obs** (word `0x0140006f`, `j 0x8000426c`) —
derivable from `stepObs_j` + the `Exec_stmtLoaded` byte pins at
`0x80004258..0x8000425b`; named residual per Law 2. -/
def ForLoopReentryJSite (σ : MState) (vmi : BitVec 64) : Prop :=
  ∀ (i u : Nat), i < 2 →
    ∃ (σ1 : MState) (i1 : Nat),
      Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
      ReadsLikePost σ1 (sigmaPost_jump_x0 σ 0x80004258#64 vmi
        (BitVec.ofNat 64 forCondReentryPC))

/-- **The for-loop re-entry bundle** — the machine at the `j` site with the light
SegEntry facts staged (store/out at the post-init spec state `st'`, budgets). -/
def ForLoopReentryInv (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (st' : SpecSt) (d dLeft aLeft : Nat) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004258#64) ∧
  (∃ vmi, c.σ.regs.get? Register.minstret = some vmi ∧
    ForLoopReentryJSite c.σ vmi) ∧
  c.σ.mem = m0 ∧
  Exec_stmtLoaded m0 ∧
  StoreRepr m0 N A φf φc st'.store ∧
  Machine.output c.σ = st'.out ∧
  d + dLeft = Vsa.While.maxCallDepth ∧
  A.lo + aLeft ≤ A.hi

/-- **The inv marshals into `SegPreBundleB` — PROVED.**  The `j` site obs
instantiates the terminator-agnostic hop (`gregsHopInto_of_jx0Site` ≫
`StepInto.of_gregsHop`); everything else carries.  This is the twin-2 pilot
content: a real interior-control arm inhabits the B bundle, where the jal-model
`SegPreBundle` was uninstantiable. -/
theorem forLoopSegPreB_of_inv (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (st' : SpecSt) (d dLeft aLeft : Nat) (m0 : Mem) (c : Config)
    (h : ForLoopReentryInv N A φf φc st' d dLeft aLeft m0 c) :
    SegPreBundleB forCondReentryPC c st' d dLeft aLeft := by
  obtain ⟨hG, htick, hpc, ⟨vmi, hmi, hsite⟩, hmem, hcode, hstore, hout, hd, ha⟩ := h
  exact ⟨N, A, φf, φc, m0,
    StepInto.of_gregsHop
      (gregsHopInto_of_jx0Site forCondReentryPC c.σ 0x80004258#64 vmi hmi hsite),
    hG, htick, hmem, hcode, hstore, hout, hd, ha⟩

#print axioms forLoopSegPreB_of_inv

/-- **The `stmtForLoop` dispatch residual** — from the parent
`SEntryC (.forStmt …)` plus allocFrame + `ExecInit`, land (`≥ 1` step: the
env_new ≫ init-exec ≫ return routing) at the re-entry bundle.  Genuinely
upstream M4 arm-seg content. -/
def ForLoopReentryDispatch (init : Option Stmt) (cnd step : Option Expr) (b : Stmt)
    (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (c : Config) : Prop :=
  st.store.allocFrame (some env) = (store', outer) →
  ExecInit ⟨store', st.out⟩ d outer init st' →
  SEntryC c st d env (.forStmt init cnd step b) →
  ∃ (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (dLeft aLeft : Nat) (m0 : Mem),
    LandedN 1 c (ForLoopReentryInv N A φf φc st' d dLeft aLeft m0)

/-- **The EXACT frozen `ApproxArmResid.stmtForLoop` field, machine-composed** —
dispatch residual ≫ `forLoopSegPreB_of_inv` ≫ `stmtForLoop_splitB` (twin 2). -/
theorem stmtForLoop_field_of_dispatch
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (SL : StackLayout)
    (hDisp : ForLoopReentryDispatch init cnd step b st st' d env store' outer c)
    (hAlloc : st.store.allocFrame (some env) = (store', outer))
    (hInit : ExecInit ⟨store', st.out⟩ d outer init st')
    (hSE : SEntryC c st d env (.forStmt init cnd step b)) :
    LandedN 1 c (fun c' => FEntryC c' st' d outer cnd step b) := by
  obtain ⟨N, A, φf, φc, dLeft, aLeft, m0, hLanded⟩ := hDisp hAlloc hInit hSE
  exact stmtForLoop_splitB init cnd step b c st st' d env store' outer
    forCondReentryPC dLeft aLeft SL
    (fun _ _ _ =>
      LandedN.weaken hLanded (fun c' hInv =>
        forLoopSegPreB_of_inv N A φf φc st' d dLeft aLeft m0 c' hInv))
    hAlloc hInit hSE

#print axioms stmtForLoop_field_of_dispatch

end Vsa.Sim
