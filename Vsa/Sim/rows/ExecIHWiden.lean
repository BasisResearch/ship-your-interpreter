import Vsa.Sim.rows.ExecRecRows

/-!
# Layer 4 — `execIH_of_exitSim`: the ONE exit-sim → `ExecIH` combinator

Every landed dispatch/loop statement simulation (`execIfNoneSim`,
`execWhileFalseSim`, `execIfTrueSim`, `execBlockSim`, `execWhileSim`,
`execForStartSim`, …) concludes the SAME packaged shape (at a fixed ghost layout):

    Triple (fun c => ExecEntry … c ∧ c.σ.sailOutput = out0) (ExecExit … st' status …)

quantified over the entry `sailOutput` array `out0`; while the `mExecS` recursor
motive (`TermSimAssembly.mExecS = ExecBlock.ExecIH` by defeq) demands the ghost-∀

    ExecIH … = ∀ ghosts, Triple (ExecEntry …) (ExecExitD … st' status …)

The gap is UNIFORM (per `rows/ExecCaseGeom.lean`, `rows/ExecRecRows.lean`):

1. entry `out0 := c.σ.sailOutput` by `rfl` (drop the `∧ … = out0` conjunct), and
2. exit `ExecExit → ExecExitD` via the parametric widener `ExecRecWiden`
   (`= Widen … (stackFoot SL)`) and its bridge `execExitD_of_execExit_rec`.

`execIH_of_exitSim` performs BOTH — over the FULL ghost-∀ — once, for ANY producer
of the packaged exit Triple.  Then every dispatch/loop `*SimD` is a ONE-LINE
instantiation: the case supplies (a) a ghost-∀ widener `hW` and (b) a ghost-∀ sim
`hSim` (the landed sim, its `out0` argument threaded), and `execIH_of_exitSim`
returns the `ExecIH` motive with NO `intro`/`obtain`/`refine` boilerplate and no
per-case marshalling.  This is the exponentiating layer
(`experiments/exponentiation-endgame-design.md` §T1.2): the widen-and-marshal is
proven ONCE and instantiated, not re-navigated per case.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## The exit-sim shape, named once

`ExecExitSim … status` is the packaged output every dispatch/loop sim produces at a
fixed ghost layout and entry `sailOutput` array `out0`: the `Triple` from the
`ExecEntry ∧ out=out0` precondition to the plain `ExecExit`. -/
def ExecExitSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun c => ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c
      ∧ c.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' status sp r aRet m0)

/-- **`execIH_of_exitSim`** — the ONE exit-sim → motive combinator, over the full
ghost-∀.  Given, for every ghost layout, a widener `hW` and a producer `hSim` of the
packaged exit Triple (at every entry `out0`), yields the `ExecIH` motive.  The body:
enter the ghost-∀, instantiate `out0 := c.σ.sailOutput` (`rfl` on the entry
conjunct), and widen the exit via `execExitD_of_execExit_rec`.  Every dispatch/loop
`*SimD` reduces to instantiating this. -/
theorem execIH_of_exitSim
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {s : Stmt} {status : Status}
    (hW : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
      ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0)
    (hSim : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String),
      ExecExitSim g N A SL φf φc st st' d env s status sp r aInterp aStmt aEnv aRet m0 out0) :
    ExecIH st d env s st' status := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    hSim g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit_rec hExit
    (hW g N A SL φf φc sp r aInterp aStmt aEnv aRet m0)⟩

end Vsa.Sim

#print axioms Vsa.Sim.execIH_of_exitSim
