import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecRetNull
import Vsa.Sim.ExecBlock

/-!
# Layer 4 — M4 leaf `ExecS` cases re-landed at `ExecExitD` (the statement shape-gap)

The statement-side twin of `EvalLeafD.lean`.  The recursive motive `mExecS` of
`execSeq_sim_of_cases` (the `ExecIH` shape, `ExecEntry … → ExecExitD …`;
`TermSimAssembly.mExecS = ExecBlock.ExecIH` by definitional unfolding) concludes
the presence/survival-*widened* exit `ExecExitD` (`= ExecExit` ∧ `MemExtends m0
mem` ∧ the `[SL.lo,SL.hi)`-`StoreRepr`-survival clause; see `ExecBlock.lean`).
The landed leaf statement lemmas (`execBrkSim`/`execContSim`/…) conclude the
plain `ExecExit` (over an entry precondition `ExecEntry ∧ sailOutput = out0`), so
`termSimClosed`'s statement minor premises (`hSBrk`/`hSCont`/…) don't yet match
the motive.  This file re-lands the register-only leaves at `ExecExitD`.

## The two gaps (bundle-only; NO new machine proof)

1. **entry `out0`** — the landed lemmas quantify the pre-`sailOutput` array `out0`
   and add `c.σ.sailOutput = out0` to the entry.  The row supplies it by `rfl`
   (`out0 := c.σ.sailOutput`).  This is pure marshalling.
2. **exit `ExecExit → ExecExitD`** — add `MemExtends m0 mem` and the
   `[SL.lo,SL.hi)`-store-survival clause.  For a register-only leaf the entire
   memory delta from `m0` is the four/five prologue `writeMap8` spills (all inside
   `[SL.lo, sp) ⊆ [SL.lo, SL.hi)`), which are presence-preserving; and the exit
   store `= st.store` is footprint-disjoint from `[SL.lo,SL.hi)`.  Both are TRUE
   of the exit but forgotten by `ExecExit`, so they are re-supplied as the honest
   widener residual `ExecLeafWiden` — the statement analog of `LeafWiden`
   (`EvalLeafD.lean`) and of the recursive cases' `hMcallPop`.

`ExecCaseGeom` (below) is the per-case geometry bundle the recursor supplies: the
jump-table slot pin + its stack-disjointness (the `execBlockA` inputs) + the
`ExecLeafWiden` widener.  Each `*D` lemma composes the landed leaf `Triple`
output with `execExitD_of_execExit` — it does NOT re-prove the machine run.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `ExecLeafWiden` — the two `ExecExitD` upgrade clauses, as an exit-quantified
     widener (the `LeafWiden` statement analog)

The two `ExecExitD` upgrade clauses are facts about the EXIT configuration, which
a leaf's `Triple` produces existentially.  So the widening residual is supplied as
a *widener*: a function that, for ANY config `c` satisfying the leaf's own
`ExecExit`, yields the two dropped clauses about `c`.  This is TRUE of every
register-only leaf exit (the delta is a `writeMap8` chain over `m0` — presence-
preserving — and the store footprint is disjoint from `[SL.lo,SL.hi)`), and is the
honest re-supply of what `ExecExit` forgets.  The recursor's leaf minor premise
provides it. -/
def ExecLeafWiden
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (status : Status) (sp r aRet : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c : Config, ExecExit g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' status sp r aRet m0 c →
    -- (a) presence monotonicity `MemExtends m0 (exit mem)`
    MemExtends m0 c.σ.mem ∧
    -- (b) the `[SL.lo, SL.hi)`-survival of the exit store
    (∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st'.store)

/-- **The leaf widening.** `ExecExit … c ∧ ExecLeafWiden …` gives `ExecExitD … c`
— the `mExecS` motive shape.  `ExecLeafWiden` at the (already-established)
`ExecExit` supplies the `MemExtends` clause and the `[SL.lo,SL.hi)`-survival
clause, at the identity `φ` extensions (a register-only leaf allocates nothing, so
`st'.store = st.store` at the entry maps). -/
theorem execExitD_of_execExit
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st' : Vsa.While.St} {status : Status} {sp r aRet : BitVec 64} {m0 : Mem} {c : Config}
    (hExit : ExecExit g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' status sp r aRet m0 c)
    (hW : ExecLeafWiden g N A SL φf φc st' status sp r aRet m0) :
    ExecExitD g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' status sp r aRet m0 c :=
  let ⟨hpres, hsurv⟩ := hW c hExit
  ⟨hExit, hpres, φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hsurv⟩

/-! ## `ExecCaseGeom` — the per-leaf geometry bundle (the recursor-supplied residual)

The union of the `execBlockA` jump-table inputs (`hslot` + its stack-disjointness
`htableStk`) and the `ExecLeafWiden` widener.  Parameterized by the case ROW
`(k, armPC, status)`.  This is the statement-side twin of the EvalE rows' per-case
residual (`IntLeafResid`/…): one bundle threaded once, projected per row. -/
def ExecCaseGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (status : Status) (k : Nat) (armPC : BitVec 64)
    (sp r aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned k armPC m0 ∧
  (stmtJumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * k) ∧
  ExecLeafWiden g N A SL φf φc st status sp r aRet m0

/-! ## The register-only leaf `*D` lemmas

Each composes the existing leaf simulation `Triple` (`execBrkSim`/`execContSim`)
with `execExitD_of_execExit`, threading the `ExecLeafWiden` widener from the
`ExecCaseGeom` bundle, and supplying the entry `out0 := c.σ.sailOutput` by `rfl`.
These are exactly the `mExecS`-motive (`ExecExitD`) minor premises `termSimClosed`
consumes as `hSBrk`/`hSCont`, at the recursor-supplied `ExecCaseGeom`. -/

/-- **`execBrkSimD`** — the `ExecS.brk` leaf at `ExecExitD` (the `ExecIH` shape). -/
theorem execBrkSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hE : ExecS st d env .brk st .brk)
    (hG : ExecCaseGeom g N A SL φf φc st .brk 7 execArmBrk sp r aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env .brk sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .brk sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execBrkSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput
      hE hslot htableStk c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit hExit hW⟩

/-- **`execContSimD`** — the `ExecS.cont` leaf at `ExecExitD` (the `ExecIH` shape). -/
theorem execContSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hE : ExecS st d env .cont st .cont)
    (hG : ExecCaseGeom g N A SL φf φc st .cont 8 execArmCont sp r aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env .cont sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .cont sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execContSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput
      hE hslot htableStk c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit hExit hW⟩

end Vsa.Sim
