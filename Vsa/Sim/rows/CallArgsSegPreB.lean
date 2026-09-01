import Vsa.Sim.ArmSegSplitTwins

/-!
# `CallArgsSegPreB` — the EX_CALL arg-loop setup entry staging over `SegPreBundleB`
(Wave 45 mail-merge of the `StmtForLoopSegPreB` pilot, twin 2)

The `callArgs` field of `ApproxArmResid` lands at `AEntryC` — anchored on a
`SegEntry` at the arg-loop head `evalArgsLoopPC = 0x800031dc`.  After the callee
node is evaluated (`jal eval_expr @0x800031bc`, returns at `0x800031c0`), the arm
runs the straight-line block `0x800031c0..0x800031d8` ending in
`blez a5,0x80003254 @0x800031d8`; the NOT-TAKEN fallthrough (`a5 = argc > 0`,
i.e. there is at least one argument) advances PC by 4 into the arg-loop head
`0x800031dc`.  Interior control — NO static `jal` aims at `0x800031dc`, so the
jal-modelled `SegPreBundle` is uninstantiable here (observation
`nonevalchild-remaining-8-shape-map`).  This row rides `SegPreBundleB`
(`ArmSegSplitTwins` §2), instantiated via the **branch-not-taken** hop
(`sigmaPost_branch_nottaken` — the fourth entry class; the pilot used the `j`
class, argsTail the taken-branch class, callC the `jalr` class).

* `gregsHopInto_of_branchNotTakenSite` — the missing fourth site instantiator
  (branch-NOT-taken ⇒ rich hop), built here off `pc_bnottaken_bt` /
  `mi_bnottaken_bt` / `frame_term_bnottaken_bt` /
  `sailOutput_sigmaPost_branch_nottaken` exactly as the twins-file
  `gregsHopInto_of_branchTakenSite` is built off the taken variants.
  (Report-only: promote to `ArmSegSplitTwins` beside the other three when the
  twins file is next touched.)
* `CallArgsSetupNotTakenSite` — the `blez a5,… @0x800031d8` not-taken site obs
  (NAMED residual per Law 2; derivable from `stepObs` + the `eval_expr` byte
  pins at `0x800031d8` under the `a5 > 0` guard).
* `CallArgsSetupInv` — the arm state at the `blez` site with the light SegEntry
  facts staged (store/out at the post-callee-eval spec state, budgets).
* `callArgsSegPreB_of_inv` — **PROVED**: the inv marshals into
  `SegPreBundleB 0x800031dc` (hop via `gregsHopInto_of_branchNotTakenSite` ≫
  `StepInto.of_gregsHop`) — the twin-2 instantiation at the arg-loop setup.
* `CallArgsSetupDispatch` — the dispatch residual (`EEntryC (.call f args)` +
  callee-eval → `LandedN 1` at the inv; the callee-eval ≫ arg-count check routing
  is M4 arm-seg content — consume the `CallArgLoopInv` carrier by name, see doc).
* `callArgs_field_of_dispatch` — the EXACT frozen `ApproxArmResid.callArgs` field,
  composed through `callArgs_splitB`.

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

/-- The EX_CALL arg-loop head control point (`ld a2,16(s0)`; = `evalArgsLoopPC`). -/
def callArgsLoopPC : Nat := 0x800031dc

/-- The `blez a5,0x80003254 @0x800031d8` argc-check site (arg-loop setup end). -/
def callArgsSetupPC : Nat := 0x800031d8

/-- **Branch-NOT-taken site ⇒ rich hop** — the fourth site instantiator, built
here exactly as `ArmSegSplitTwins.gregsHopInto_of_branchTakenSite` (taken) is
built.  A `sigmaPost_branch_nottaken` site obs at `σ` whose fallthrough
`bPC + 4` lands at `tgtPC` instantiates `GRegsHopInto tgtPC` — PC via
`pc_bnottaken_bt`, minstret via `mi_bnottaken_bt`, register frame via
`frame_term_bnottaken_bt`, out via `sailOutput_sigmaPost_branch_nottaken`. -/
theorem gregsHopInto_of_branchNotTakenSite (tgtPC : Nat) (σ : MState)
    (bPC vmi : BitVec 64)
    (htgt : BitVec.addInt bPC 4 = BitVec.ofNat 64 tgtPC)
    (hmi : σ.regs.get? Register.minstret = some vmi)
    (hsite : ∀ (i u : Nat), i < 2 →
      ∃ (σ1 : MState) (i1 : Nat),
        Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
        ReadsLikePost σ1 (sigmaPost_branch_nottaken σ bPC vmi)) :
    GRegsHopInto tgtPC σ := by
  intro i u hi
  obtain ⟨σ1, i1, hs, hi1, hG1, hmem1, hobs⟩ := hsite i u hi
  refine ⟨σ1, i1, hs, hi1, hG1, hmem1, ?_, mi_bnottaken_bt hobs, ?_,
    fun R hn => frame_term_bnottaken_bt hobs R hn⟩
  · have := pc_bnottaken_bt hobs; rwa [htgt] at this
  · rw [hobs.out, sailOutput_sigmaPost_branch_nottaken]

#print axioms gregsHopInto_of_branchNotTakenSite

/-- **The `blez a5,… @0x800031d8` not-taken site obs** (argc `> 0`) — derivable
from the `stepObs` branch-not-taken lemma + the `eval_expr` byte pins at
`0x800031d8..0x800031db` under the `a5 > 0` guard; named residual per Law 2. -/
def CallArgsSetupNotTakenSite (σ : MState) (vmi : BitVec 64) : Prop :=
  ∀ (i u : Nat), i < 2 →
    ∃ (σ1 : MState) (i1 : Nat),
      Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
      ReadsLikePost σ1 (sigmaPost_branch_nottaken σ 0x800031d8#64 vmi)

/-- **The arg-loop setup inv** — the machine at the `blez` site with the light
SegEntry facts staged (store/out at the post-callee-eval spec state `st'`,
budgets). -/
def CallArgsSetupInv (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (st' : SpecSt) (d dLeft aLeft : Nat) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x800031d8#64) ∧
  (∃ vmi, c.σ.regs.get? Register.minstret = some vmi ∧
    CallArgsSetupNotTakenSite c.σ vmi) ∧
  c.σ.mem = m0 ∧
  Exec_stmtLoaded m0 ∧
  StoreRepr m0 N A φf φc st'.store ∧
  Machine.output c.σ = st'.out ∧
  d + dLeft = Vsa.While.maxCallDepth ∧
  A.lo + aLeft ≤ A.hi

/-- **The inv marshals into `SegPreBundleB` — PROVED.**  The not-taken `blez`
site obs instantiates the terminator-agnostic hop
(`gregsHopInto_of_branchNotTakenSite` ≫ `StepInto.of_gregsHop`, fallthrough
`0x800031d8 + 4 = 0x800031dc`); everything else carries.  The arg-loop setup
inhabits the B bundle, where the jal-model `SegPreBundle` was uninstantiable. -/
theorem callArgsSegPreB_of_inv (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (st' : SpecSt) (d dLeft aLeft : Nat) (m0 : Mem) (c : Config)
    (h : CallArgsSetupInv N A φf φc st' d dLeft aLeft m0 c) :
    SegPreBundleB callArgsLoopPC c st' d dLeft aLeft := by
  obtain ⟨hG, htick, hpc, ⟨vmi, hmi, hsite⟩, hmem, hcode, hstore, hout, hd, ha⟩ := h
  exact ⟨N, A, φf, φc, m0,
    StepInto.of_gregsHop
      (gregsHopInto_of_branchNotTakenSite callArgsLoopPC c.σ 0x800031d8#64 vmi
        (by decide) hmi hsite),
    hG, htick, hmem, hcode, hstore, hout, hd, ha⟩

#print axioms callArgsSegPreB_of_inv

/-- **The `callArgs` dispatch residual** — from the parent `EEntryC (.call f args)`
plus the callee-eval `EvalE st d env f st' fv`, land (`≥ 1` step: the callee-eval
≫ arg-count check `0x800031c0..0x800031d8`) at the setup inv.  Genuinely upstream
M4 arm-seg content: consume the `CallArgLoopInv` carrier (`rows/CallClosureSplice`)
by name for the loop-head register pins; do NOT re-derive them. -/
def CallArgsSetupDispatch (f : Expr) (args : List Expr)
    (st st' : SpecSt) (d : Nat) (env : Addr) (fv : Value) (c : Config) : Prop :=
  EvalE st d env f st' fv →
  EEntryC c st d env (.call f args) →
  ∃ (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (dLeft aLeft : Nat) (m0 : Mem),
    LandedN 1 c (CallArgsSetupInv N A φf φc st' d dLeft aLeft m0)

/-- **The EXACT frozen `ApproxArmResid.callArgs` field, machine-composed** —
dispatch residual ≫ `callArgsSegPreB_of_inv` ≫ `callArgs_splitB` (twin 2). -/
theorem callArgs_field_of_dispatch
    (f : Expr) (args : List Expr) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (fv : Value) (SL : StackLayout)
    (hDisp : CallArgsSetupDispatch f args st st' d env fv c)
    (hE : EvalE st d env f st' fv)
    (hEE : EEntryC c st d env (.call f args)) :
    LandedN 1 c (fun c' => AEntryC c' st' d env args) := by
  obtain ⟨N, A, φf, φc, dLeft, aLeft, m0, hLanded⟩ := hDisp hE hEE
  exact callArgs_splitB f args c st st' d env fv callArgsLoopPC dLeft aLeft SL
    (fun _ _ =>
      LandedN.weaken hLanded (fun c' hInv =>
        callArgsSegPreB_of_inv N A φf φc st' d dLeft aLeft m0 c' hInv))
    hE hEE

#print axioms callArgs_field_of_dispatch

end Vsa.Sim
