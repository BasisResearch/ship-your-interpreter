import Vsa.Sim.ExecFor

/-!
# Layer 4 — M4 `forStmt` case: `ExecS.forStart` (the env_new + init bridge)

`ExecS.forStart` is the outer wrapper of the `for` statement (kind 5, arm
`0x80004234`). It allocates a child scope (`st.store.allocFrame (some env) =
(store', outer)`, the machine `env_new`), runs the optional `init` statement
(`ExecInit ⟨store', st.out⟩ d outer init st'`), then hands control to the
`ForLoop` proper (`ForLoop st' d outer cnd step b st'' status`), whose four
constructors are already discharged by `execForLoopBody` (`ExecFor.lean`).

## Machine path (arm `0x80004234`, kind 5 — the `forStart` prologue)

```
80004234:  mv   a0,s3            -- a0 := env
80004238:  jal  env_new          -- child scope (Store.allocFrame); a0 := new env `outer`
8000423c:  ld   a1,8(s0)         -- a1 := stmt->init   (offset 8)
80004240:  mv   s3,a0            -- s3 := outer env
80004244:  beqz a1,0x8000426c    -- no init → skip to cond head
80004248:  mv   a2,a0            -- (init present) a2 := outer env
8000424c:  mv   a3,s2            -- a3 := retslot
80004250:  mv   a0,s1            -- a0 := interp*
80004254:  jal  exec_stmt        -- init (ExecIH), link 0x80004258
80004258:  j    0x8000426c       -- → cond head (init's status = .normal, per ExecInit)
-- cond head 0x8000426c: the ForLoop head (see ExecFor.lean).
```

## Structure

`execForStartSim` mirrors `execBlockSim`'s `env_new` wiring (`ExecBlock2.lean`):
the arm prologue (`execBlockA` (kind 5) ≫ `env_new` (`Store.allocFrame` = `outer`)
≫ the optional `ExecInit` via `armExec_rec`/`ExecIH` ≫ landing at the cond head
`0x8000426c`) is delivered as the residual `hArm` — a bridge from the outer
`ExecEntry (.forStmt …)` at `env` to the ForLoop-head `ExecEntry (.forStmt …)` at
the child scope `outer` for the post-init state `st'`. `execForLoopBody`
(`ExecFor.lean`, proved unconditionally on its `hstep`/`hForIH` residuals) then
runs the loop from that head to the final `ExecExit`. Composing `hArm ≫
execForLoopBody` closes the `forStart` case conditional only on named residuals —
exactly the residual style of `execBlockSim`.

`hArm` bundles the `env_new` linkage (the child-scope allocation, `env_new_spec`,
`EnvNewSpec.lean`) and the `ExecInit` sub-derivation (the init statement's
`ExecIH` threaded through `armExec_rec`, `ExecBlock.lean`). `hstep`/`hForIH` are
the `execForLoopBody` per-iteration `ExecForStep` and recursive-sub-`for` IH
residuals (`ExecFor.lean`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
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

/-! ## `ExecForStartSimGoal` — the `ExecS.forStart` simulation Triple (packaged)

The post-state is the loop's final state `st''` with status `status`, exactly the
`ExecS.forStart` conclusion; the entry scope is the OUTER `env` (not the child
scope — the child `outer` is internal to the arm). -/
def ExecForStartSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun c => ExecEntry g N A SL φf φc st d env (.forStmt init cnd step b)
        sp r aInterp aStmt aEnv aRet m0 c ∧ c.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st'' status sp r aRet m0)

/-! ## `execForStartSim` — `ExecS.forStart`: `hArm (env_new + ExecInit) ≫ execForLoopBody`

Composes the whole `forStmt` arm. The arm prologue residual `hArm` bridges the
outer `ExecEntry (.forStmt …)` at `env` to the ForLoop-head `ExecEntry
(.forStmt …)` at the freshly-allocated child scope `outer` for the post-init state
`st'` (with extended φ-maps `φf'`/`φc'` accounting for the `env_new`/init store
growth, and a re-based memory baseline `m0'`). `execForLoopBody` then runs the
`ForLoop` from that head to the final `ExecExit`, which `hArm`'s memory framing
re-bases back to the outer entry. -/
theorem execForStartSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (status : Status)
    (store' : Store) (outer : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hAlloc : st.store.allocFrame (some env) = (store', outer))
    (_hInit : ExecInit ⟨store', st.out⟩ d outer init st')
    (hFor : ForLoop st' d outer cnd step b st'' status)
    -- the `execForLoopBody` per-iteration residual (`ExecForStep`), parametric in
    -- the intermediate state / maps / statuses / memory (delivered later by the
    -- mutual-recursor scaffolding + the cond/body/step machine decode):
    (hstep : ∀ (φf₀ φc₀ : Addr → Nat) (stM stMid stFin : Vsa.While.St)
        (bodyStatus loopStatus : Status) (m00 : Mem) (out00 : Array String),
        ExecForStep g N A SL φf₀ φc₀ stM d outer init cnd step b
          sp r aInterp aStmt aEnv aRet m00 out00 stMid stFin bodyStatus loopStatus)
    -- the recursive sub-`for` IH (`execForLoopBody`'s `hForIH`, from the mutual
    -- recursor — only the `ForLoop.loop` case consumes it):
    (hForIH : ∀ (φf' φc' : Addr → Nat) (stA stB : Vsa.While.St)
        (status' : Status) (m0' : Mem) (out0' : Array String),
        ForLoop stA d outer cnd step b stB status' →
        Triple
          (fun cfg => ExecEntry g N A SL φf' φc' stA d outer (.forStmt init cnd step b)
            sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0')
          (ExecExit g N A SL φf' φc' stB status' sp r aRet m0'))
    -- the arm prologue residual: from the outer block `ExecEntry` (at `env`), run
    -- `execBlockA` (kind 5) ≫ `env_new` (allocating `outer` per `env_new_spec`) ≫
    -- the optional `ExecInit` (init `ExecIH` via `armExec_rec`) ≫ the fall to the
    -- cond head, landing at the ForLoop head `ExecEntry (.forStmt …)` in scope
    -- `outer` over the post-init state `st'`, with extended φ-maps and a re-based
    -- memory baseline `m0'`. RESIDUAL (env_new/allocFrame linkage + ExecInit).
    (hArm : ∀ (φf' φc' : Addr → Nat),
      Triple
        (fun c => ExecEntry g N A SL φf φc st d env (.forStmt init cnd step b)
          sp r aInterp aStmt aEnv aRet m0 c ∧ c.σ.sailOutput = out0)
        (fun c => ∃ m0', PhiExtends φf φf' st'.store.frames.size ∧
          PhiExtends φc φc' st'.store.closures.size ∧
          ExecEntry g N A SL φf' φc' st' d outer (.forStmt init cnd step b)
            sp r aInterp aStmt aEnv aRet m0' c ∧ c.σ.sailOutput = out0))
    -- the epilogue residual: the ForLoop exit (at child-scope maps `φf'`/`φc'` and
    -- baseline `m0'`) re-bases back to the outer entry maps `φf`/`φc` / baseline
    -- `m0` (the frame-alloc/env_new φ-downgrade + memory framing, analog of
    -- `execBlockSim`'s `hEpi`):
    (hEpi : ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
      Triple
        (ExecExit g N A SL φf' φc' st'' status sp r aRet m0')
        (ExecExit g N A SL φf φc st'' status sp r aRet m0)) :
    ExecForStartSimGoal g N A SL φf φc st st'' d env init cnd step b status
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro c hpre
  -- run the arm prologue (env_new + ExecInit) to the ForLoop head at child scope
  -- `outer`, over the post-init state `st'`, with extended maps `φf`/`φc` (any pair
  -- accepted by `hArm`; we thread the entry pair).
  obtain ⟨cH, hstepsH, m0', hpf, hpc, hEntryH, houtH⟩ := hArm φf φc c hpre
  -- run the ForLoop proper from that head via `execForLoopBody` (unconditional on
  -- its `hstep`/`hForIH` residuals).
  have hloopT :=
    execForLoopBody g N A SL d outer init cnd step b
      sp r aInterp aStmt aEnv aRet hstep hForIH φf φc st' st'' status m0' out0 hFor
  obtain ⟨cQ, hstepsQ, hExitQ⟩ := hloopT cH ⟨hEntryH, houtH⟩
  -- re-base the loop exit back to the outer entry maps / baseline.
  obtain ⟨cE, hstepsE, hExitE⟩ := hEpi φf φc m0' cQ hExitQ
  exact ⟨cE, (hstepsH.trans hstepsQ).trans hstepsE, hExitE⟩

end Vsa.Sim
