import Vsa.Sim.rows.CallClosureRow
import Vsa.Sim.SpliceFold
import Vsa.Sim.CallFrameMeta
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvDefCompose
import Vsa.Sim.rows.CallClosureEnvNewCallGen
import Vsa.Sim.rows.CallClosureEnvDefineCallGen
import Vsa.Sim.rows.CallClosureValueNullCallGen
import Vsa.Sim.rows.CallClosureRetCopyGen
import Vsa.Sim.rows.CallClosureArgLoopEntryGen
import Vsa.Sim.rows.CallClosureNormalRet
import Vsa.Sim.rows.CallClosureRetClass
import Vsa.Sim.rows.CallClosureBodyExit
import Vsa.Sim.rows.CallClosureBodyEntry
import Vsa.Sim.rows.CallClosureEnvNewRet
import Vsa.Sim.rows.CallClosureFoldBack
import Vsa.Sim.rows.CallClosureDispatchStage
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.EvalNullSim
import Vsa.Sim.SegEffect

/-!
# `CallClosureSplice` — the EX_CALL closure-arm entry route composed (wave 37)

The splice layer for the `hCallClosure` crux: composes the closure-application
route toward `CallClosureGeom` (`rows/CallClosureRow.lean`, wave-37 amended
shape) over the REAL `env_new_spec` contract, the `storeChainList` params-fold,
and the generated seg rows, with every remaining machine span a NAMED premise.

## The route (decode: `CallEntry.lean`; disasm map: `experiments/logs/wave37-callcrux.md`)

```
callDispatchPC 0x80003254   fv-kind dispatch (spills fval; mv s7,a1)        [named: dispatch stage]
0x80003288..0x800032b0      closure head (arity a_2; depth guard a_3;
                            spills s5@1032/s3@1048 — frame-tracking)        [named: dispatch stage]
0x800032b4  callClosureEnvNewCallBridge (GEN) ≫ jal env_new @0x800029fc    [named: dispatch stage]
env_new                     REAL: env_new_spec, parentSpec := some cd.env,
                            ret := 0x800032c0 (a_4 = allocFrame)            [THREADED HERE]
0x800032c0..0x800032c8      return staging; blez a5 → ZERO-PARAM BYPASS     [named: fold entry / no-params]
0x800032cc..0x800032d8      fold init (s0 := sp+240; s6 := 8·n; a5 := 0)    [named: fold entry]
per param k < n:            staging ≫ callClosureEnvDefineCallBridge (GEN)
                            ≫ env_define (envDefContract) ≫ back-edge       [named seam family; storeChainList]
0x80003320..0x80003328      restore s6 ≫ callClosureValueNullCallBridge
                            (GEN) ≫ value_null @0x800027ec                  [named: handoff bridge]
0x8000332c..0x8000333c      body entry (a6 := cd->body; s0 := 0;
                            bgtz count — gated by cd.body ≠ [])             [named: handoff bridge]
callBodyLoopPC 0x80003354   → BodyHandoff (∃ g' φf' mB)                     [conclusion]
```

The return side (`callBodyRetPC 0x80003378 → callJoinPC 0x800033ec`) is the
status split: `.normal` via `0x80003954`, `.ret v` via the classification span
≫ `callClosureRetCopyRow` (GEN).  `callClosureRet_of_status` composes the two
guarded routes into the amended `ret` field shape.

Also here: the two loop INVARIANTS as named-field structures
(`CallArgLoopInv` for the EX_CALL arg loop at `evalArgsLoopPC`,
`CallParamFoldInv` for the param-define fold at `0x800032dc`), and the
red-zone mechanical layer for the generated staging segs (`LogInRZ` on the
reflected logs + one `rzSeamFrame_of_run` firing for the `env_new` seam —
kills the per-splice `AInv`/code-pin threading for the crux's callee seams).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no heartbeat raise.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The two loop invariants (named-field structures, CLAUDE.md R6) -/

/-- **The EX_CALL arg-loop invariant** at the loop head `evalArgsLoopPC`
(`0x800031dc`), for the state after the first `vsPre.length` of `n` arguments
have been evaluated into the arg vector at `sp+240+24·i`.  Register pins read
off the disasm (`a6`=index, `a5`=argc, `s0`=call node, `s2`=interp, `a3`=env);
the spec side carries the intermediate state `stK` and the evaluated prefix
`vsPre` (each value represented in its 24-byte slot). -/
structure CallArgLoopInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (stK : SpecSt) (vsPre : List Value) (n : Nat)
    (sp cnode ip envp : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalArgsLoopPC)
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `a6` — the running arg index. -/
  idx : c.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 vsPre.length)
  /-- `a5` — argc (spilled at `24(sp)` across each body call, reloaded). -/
  argc : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 n)
  /-- `s0` — the EX_CALL node (args array at `16(s0)`). -/
  node : c.σ.regs.get? Register.x8 = some cnode
  /-- `s2` — the interp pointer (`a1` arg of the recursive `eval_expr`). -/
  interp : c.σ.regs.get? Register.x18 = some ip
  /-- `a3` — the evaluation env (spilled at `8(sp)` across each body call). -/
  env : c.σ.regs.get? Register.x13 = some envp
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  store : StoreRepr c.σ.mem N A φf φc stK.store
  out : OutRepr c.σ stK
  /-- The evaluated prefix sits in the arg vector, one 24-byte slot each. -/
  slots : ∀ i, (hi : i < vsPre.length) →
    ValueRepr c.σ.mem N φc (sp.toNat + 240 + 24 * i) vsPre[i]
  /-- Writes so far are confined to stack + arena. -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?
  bound : vsPre.length ≤ n

/-- The param-define fold loop-head PC (`0x800032dc`). -/
def callParamFoldPC : Nat := 0x800032dc

/-- **The param-define fold invariant** at the loop head `0x800032dc`, for
param index `k` of `n := (cd.params.zip vs).length`.  Register pins off the
disasm: `s0` = arg-vector cursor `sp+240+24·k`, `a5` = byte index `8·k`,
`s6` = bound `8·n`, `s3` = the fresh frame's machine pointer, `s5` = the
closure record pointer (params names array at `16(s5)`).  The store carries
`foldStore … k` (the first `k` params bound) under the EXTENDED map `φf'`.
This is the `storeChainList` carrier of the params-fold
(`closureParamsFold`'s shape, machine-honest). -/
structure CallParamFoldInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp fp clp : BitVec 64) (m0 : Mem) (k : Nat)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 callParamFoldPC)
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `s0` — the arg-vector cursor (advanced by 24 per iteration). -/
  cursor : c.σ.regs.get? Register.x8
    = some (sp + 240#64 + 24#64 * BitVec.ofNat 64 k)
  /-- `a5` — the byte index into the params names array (`8·k`). -/
  idx : c.σ.regs.get? Register.x15 = some (8#64 * BitVec.ofNat 64 k)
  /-- `s6` — the loop bound (`8·n`, from `slli s6,a5,3` at the fold init). -/
  bound : c.σ.regs.get? Register.x22
    = some (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)
  /-- `s3` — the fresh frame's machine pointer (`mv s3,a0` after `env_new`). -/
  frameReg : c.σ.regs.get? Register.x19 = some fp
  /-- `s5` — the closure record pointer (params names at `16(s5)`). -/
  closReg : c.σ.regs.get? Register.x21 = some clp
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  /-- The first `k` params bound, under the extended frame map. -/
  store : StoreRepr c.σ.mem N A φf' φc (foldStore store' cd vs frame k)
  /-- The same state carries the allocator ledger and exact heap ownership
  for the current semantic fold store. -/
  heap : CallFoldHeapOwned A φf' φc (foldStore store' cd vs frame k)
    (sp.toNat + 240) vs c.σ.mem
  out : OutRepr c.σ st
  /-- Writes so far are confined to stack + arena (baseline: the arm's `m0`). -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?

/-- The fold carrier (the `storeChainList` index family over
`CallParamFoldInv`). -/
def callParamFoldCarrier
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp fp clp : BitVec 64) (m0 : Mem) (k : Nat) :
    Config → Prop :=
  fun c => CallParamFoldInv N A SL φf' φc st store' cd vs frame sp fp clp m0 k c

/-- Exact top-level `env_define` decomposition.  The call route supplies the
four contracts proved by `EnvDefCompose`; callers cannot replace the helper
with an arbitrary whole-route `Triple`. -/
structure EnvDefineCallStages (P Q : Config → Prop) : Type where
  Update : Config → Prop
  Append : Config → Prop
  Grow : Config → Prop
  dispatch : Triple P (fun c => Update c ∨ Append c ∨ Grow c)
  update : Triple Update Q
  append : Triple Append Q
  grow : Triple Grow Q

theorem envDefineCall_of_stages {P Q : Config → Prop}
    (S : EnvDefineCallStages P Q) : Triple P Q :=
  envDefContract S.dispatch S.update S.append S.grow

#print axioms envDefineCall_of_stages

/-! ## §2. The per-param seam factored (staging ≫ `env_define` ≫ back-edge)

One fold seam = the loop-body staging (`0x800032dc..0x80003308` 24-byte value
copy to `sp+64` + cursor bump, then the GEN `callClosureEnvDefineCallBridge`
jal seam) ≫ the `env_define` contract (`EnvDefCompose.envDefContract`, the
append≫grow≫dispatch join over the real Malloc/Realloc contracts) ≫ the return
+ back-edge (`0x80003314..0x8000331c`, `bne s6,a5` TAKEN — which requires
`k+1 < n`; wave-43 amendment, ledger `callparamfold-carrier-n-unreachable`:
the fold is a DO-WHILE, so for `k+1 = n` the machine falls through the bne and
the head PC — the carrier's pin — is NEVER re-reached; the last iteration
belongs to the `hFoldToHandoff` leg, obstruction
`foldBackLoop_facts_last_false` in `rows/CallCruxMarshal3.lean`). -/

/-- **Per-param seam from its three named pieces** — the naming theorem: any
discharge of one fold seam is `staging ≫ env_define ≫ back-edge` for SOME
`env_define` boundary pair `(PreDef, PostDef)` (supplied by `envDefContract`
over the real contracts). -/
theorem callParamFoldSeam_of
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp fp clp : BitVec 64} {m0 : Mem} {k : Nat}
    {PreDef PostDef : Config → Prop}
    (hStage : Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
      PreDef)
    (hDefine : Triple PreDef PostDef)
    (hBack : Triple PostDef
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 (k + 1))) :
    Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 (k + 1)) :=
  Triple.seq hStage (Triple.seq hDefine hBack)

/-! ## Exact `env_new` return adapters -/

/-- The positive-arity `env_new` return is reduced to the reflected fold-init
row.  The two functions are zero-step ABI marshals; all machine instructions
execute in `callClosureEnvNewRetFoldRow`. -/
structure ClosureEnvNewFoldStages
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp fp clp : BitVec 64) (m0 : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem) : Type where
  φf' : Addr → Nat
  a0v : BitVec 64
  s6v : BitVec 64
  lds : List (List (BitVec 8))
  rowMem : Mem
  phiExt : PhiExtends φf φf' st.store.frames.size
  toRow : ∀ c,
    env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
      extsE N φf φc (some cd.env) mEnvNew c →
    SegPre callClosureEnvNewRetFoldSeg
      (callClosureEnvNewRetL sp a0v s6v) lds 0x800032c0#64 rowMem c
  land : ∀ c,
    CallClosureEnvNewRetFoldPost sp a0v s6v lds rowMem c →
    callParamFoldCarrier N A SL φf' φc st store' cd vs frame
      sp fp clp m0 0 c

theorem envNewToFold_of_stages
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp fp clp : BitVec 64} {m0 : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {gE : (R : Register) → Option (RegisterType R)}
    {par s0E : BitVec 64} {extsE : List (Nat × Nat)} {mEnvNew : Mem}
    (S : ClosureEnvNewFoldStages N A SL φf φc st store' cd vs frame
      sp fp clp m0 M gE par s0E extsE mEnvNew) :
    Triple
      (env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE N φf φc (some cd.env) mEnvNew)
      (fun c => ∃ φf' : Addr → Nat,
        PhiExtends φf φf' st.store.frames.size ∧
        callParamFoldCarrier N A SL φf' φc st store' cd vs frame
          sp fp clp m0 0 c) :=
  Triple.seq (fun c hc => ⟨c, .refl c, S.toRow c hc⟩) <|
    Triple.seq (callClosureEnvNewRetFoldRow sp S.a0v S.s6v S.lds S.rowMem)
      (fun c hc => ⟨c, .refl c, S.φf', S.phiExt, S.land c hc⟩)

#print axioms envNewToFold_of_stages

/-! ## Exact closure dispatch adapter -/

/-- Reached state of the reflected closure-kind/arity/depth dispatch followed
by its `jal env_new`. -/
structure ClosureDispatchPost
    (σ0 : MState) (sp s0v a3v a5v s2v s5v s3v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x800029fc#64 : BitVec 64)
  ra : c.σ.regs.get? Register.x1 = some (0x800032c0#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  regs : GHolds c.σ (evalBlocks callClosureDispatchStageSeg
    (SegEvalState.init
      (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs
  mem : c.σ.mem = writeLog m0 (evalBlocks callClosureDispatchStageSeg
    (SegEvalState.init
      (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).log
  frame : ∀ R, AbiExceptS7S5 R = true → c.σ.regs.get? R = σ0.regs.get? R

/-- Exact inputs for the reflected closure dispatch.  `pins` and `land` are
zero-step ABI marshals.  `facts` are the concrete code/read/branch facts, and
`jal` is the single call-site observation. -/
structure ClosureDispatchStages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem) : Type where
  s0v : BitVec 64
  a3v : BitVec 64
  a5v : BitVec 64
  s2v : BitVec 64
  s5v : BitVec 64
  s3v : BitVec 64
  lds : List (List (BitVec 8))
  pins : ∀ c,
    CallEntryI g N A SL φf φc st d (.closure a) vs
      dLeft aLeft sp sret m0 c →
    GHolds c.σ (callClosureDispatchStageL
      sp s0v a3v a5v s2v s5v s3v)
  facts : ∀ c,
    CallEntryI g N A SL φf φc st d (.closure a) vs
      dLeft aLeft sp sret m0 c →
    ChainFacts c.σ.mem c.σ.mem (callClosureDispatchStageL
      sp s0v a3v a5v s2v s5v s3v) lds callClosureDispatchStageSeg
  keysOut : KeysOK (keysG (evalBlocks callClosureDispatchStageSeg
    (SegEvalState.init
      (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs)
  raOut : KeysAvoidRa (evalBlocks callClosureDispatchStageSeg
    (SegEvalState.init
      (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs
  jal : ∀ c,
    CallEntryI g N A SL φf φc st d (.closure a) vs
      dLeft aLeft sp sret m0 c →
    ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80003254#64
          (SegEvalState.init
            (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)
          callClosureDispatchStageSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks callClosureDispatchStageSeg
        (SegEvalState.init
          (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).log →
      GHolds σ' (evalBlocks callClosureDispatchStageSeg
        (SegEvalState.init
          (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs →
      JalStep 0x800029fc#64 0x800032c0#64 σ' i' u'
  land : ∀ c0,
    CallEntryI g N A SL φf φc st d (.closure a) vs
      dLeft aLeft sp sret m0 c0 →
    ∀ c1,
      ClosureDispatchPost c0.σ sp s0v a3v a5v s2v s5v s3v lds m0 c1 →
      env_new_pre A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE φf (some cd.env) mEnvNew c1

theorem closureDispatch_of_stages
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {a : Addr} {cd : ClosureData} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {gE : (R : Register) → Option (RegisterType R)}
    {par s0E : BitVec 64} {extsE : List (Nat × Nat)} {mEnvNew : Mem}
    (S : ClosureDispatchStages g N A SL φf φc st d a cd vs
      dLeft aLeft sp sret m0 M gE par s0E extsE mEnvNew) :
    Triple
      (CallEntryI g N A SL φf φc st d (.closure a) vs
        dLeft aLeft sp sret m0)
      (env_new_pre A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE φf (some cd.env) mEnvNew) := by
  intro c hc
  obtain ⟨vm, hmi⟩ := hc.1.good.minstret
  obtain ⟨σ2, i2, hs, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩ :=
    callClosureDispatchStageBridge c.σ c.tick c.steps vm
      sp S.s0v S.a3v S.a5v S.s2v S.s5v S.s3v S.lds m0
      hc.1.good hc.1.pc hmi hc.1.mem (S.pins c hc) (S.facts c hc)
      hc.1.tick S.keysOut S.raOut (S.jal c hc)
  let c2 : Config :=
    ⟨σ2, i2, c.steps + evalBlocksFuel callClosureDispatchStageSeg + 1⟩
  have hp : ClosureDispatchPost c.σ sp S.s0v S.a3v S.a5v S.s2v S.s5v S.s3v
      S.lds m0 c2 :=
    ⟨hG2, hi2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩
  exact ⟨c2, hs, S.land c hc c2 hp⟩

#print axioms closureDispatch_of_stages

/-! ## §3. The entry route composed — `env_new_spec` threaded for real

`callClosureEntrySplice` produces the AMENDED `CallClosureGeom.entryBase`
Triple.  The `env_new` callee is the REAL `env_new_spec` at
`parentSpec := some cd.env` and return address `0x800032c0` (the concrete link
the GEN `callClosureEnvNewCallBridge` establishes) — `a_4`'s
`allocFrame (some cd.env)` enters through `env_new_post`'s `FrameRepr` of the
empty frame `⟨some cd.env, []⟩`.  The params-fold is `storeChainList` over the
`CallParamFoldInv` carrier at the ∃-bound extended map `φf'` (bound by the
`hEnvNewToFold` bridge, which places the fresh frame: `φf' frame := p`, the
`env_new_post` pointer).  The zero-param route (`blez a5 @0x800032c8`) has its
own bridge.  Named premises (each a genuine machine span, doc'd inline):

* `hDispatchStage` — `callDispatchPC → env_new_pre`: the fv-kind dispatch +
  closure head (arity `a_2` / depth `a_3` guards; s5/s3/s7 spills —
  frame-tracking decode) + the GEN `callClosureEnvNewCallBridge` seg; must
  also produce `env_new_pre`'s side conditions (`Env_newLoaded`, `M.AInv`,
  `φf cd.env = par.toNat` from `StoreRepr`, the non-exhaustion selector).
* `hEnvNewToFold` — the `0x800032c0..0x800032d8` return staging + fold init,
  binding `φf'` (fresh frame at the `env_new_post` pointer).
* `hFoldSeam` — the per-param seam family (§2 shape).
* `hFoldToHandoff` — fold exit (`0x80003320`) ≫ GEN
  `callClosureValueNullCallBridge` ≫ `value_null_spec` ≫ body-entry staging
  (`bgtz` taken, gated by `cd.body ≠ []`), binding the body ghost `g'`.
* `hNoParams` — the `blez`-taken route straight to the same handoff. -/
theorem callClosureEntrySplice
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (d : Nat) (a : Addr) (dLeft aLeft : Nat)
    (sret : BitVec 64) (m0 : Mem)
    -- env_new call data (the contract's ghosts at this call site)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par sp s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem)
    -- fold carrier data
    (fp clp : BitVec 64)
    (_hbody : cd.body ≠ [])
    (hER : ∀ p : Nat, EnvRegions SL M.privFoot sp.toNat p)
    (hDispatchStage : ClosureDispatchStages g N A SL φf φc st d a cd vs
      dLeft aLeft sp sret m0 M gE par s0E extsE mEnvNew)
    (hEnvNewToFold : 0 < (cd.params.zip vs).length →
      ClosureEnvNewFoldStages N A SL φf φc st store' cd vs frame
        sp fp clp m0 M gE par s0E extsE mEnvNew)
    -- wave-43 amendment (ledger `callparamfold-carrier-n-unreachable`): the
    -- seam family covers ONLY the mid-loop back-edges `k + 1 < n` — the
    -- carrier at index `n` is machine-unreachable (do-while; the last bne
    -- falls through), obstruction `foldBackLoop_facts_last_false`.
    (hFoldSeam : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size →
      ∀ k, k + 1 < (cd.params.zip vs).length → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 (k + 1)))
    -- wave-43 amendment: sourced at `carrier (n-1)` — the LAST iteration
    -- (staging ≫ env_define ≫ EXIT-polarity back-edge ≫ value_null ≫ body
    -- entry) is this leg's machine content.
    (hFoldToHandoff : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
          ((cd.params.zip vs).length - 1))
        (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0))
    (hNoParams : (cd.params.zip vs).length = 0 → Triple
      (env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE N φf φc (some cd.env) mEnvNew)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0)) :
    Triple
      (CallEntryI g N A SL φf φc st d (.closure a) vs
        dLeft aLeft sp sret m0)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0) := by
  -- one SpliceChain: staging hop ≫ the REAL env_new contract ≫ the tail.
  refine spliceFold (.step (closureDispatch_of_stages hDispatchStage)
    (env_new_spec A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
      extsE N φf φc (some cd.env) mEnvNew hER)
    (.tail ?_))
  -- the tail: env_new_post → BodyHandoff, split on the zero-param bypass.
  rcases Nat.eq_zero_or_pos (cd.params.zip vs).length with h0 | hpos
  · exact hNoParams h0
  · -- fold route: bind φf', run the storeChainList fold over the n-1 mid-loop
    -- back-edges to `carrier (n-1)`, hand the LAST iteration to the handoff leg.
    intro c hc
    obtain ⟨c1, hs1, φf', hpe, hcar0⟩ :=
      envNewToFold_of_stages (hEnvNewToFold hpos) c hc
    obtain ⟨c2, hs2, hcarN⟩ :=
      storeChainList
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0)
        ((cd.params.zip vs).length - 1)
        (fun k hk => hFoldSeam φf' hpe k (by omega)) c1 hcar0
    obtain ⟨c3, hs3, hHand⟩ := hFoldToHandoff φf' hpe c2 hcarN
    exact ⟨c3, Steps.trans hs1 (Steps.trans hs2 hs3), hHand⟩

#print axioms callClosureEntrySplice

/-- Forget only the indexed callee/vector facts at the call-dispatch boundary.
This is the exact zero-step adapter used before the reflected closure dispatch
and parameter-fold splice. -/
theorem callEntryI_to_dispatchEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem) :
    Triple
      (CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0)
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0) := by
  intro c hc
  exact ⟨c, .refl c, hc.1⟩

#print axioms callEntryI_to_dispatchEntry

/-! ## §3a. Closure-body indexed entry marshal -/

/-- Facts not carried by the legacy `SegEntry` but required by the faithful
copy-indexed closure-body sequence entry. -/
structure ClosureBodyEntryABI
    (g' : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (stB : SpecSt) (dB : Nat) (frame : Addr) (body : List Stmt)
    (sp : BitVec 64) (mB : Mem) (c : Config) : Prop where
  cursor : ExecSeqCursorRepr .closureBody c.σ.mem φf' frame body
    sp (sp + 144#64) c.σ.regs.get?
  headGround : ExecSeqHeadGround .closureBody c.σ.mem c.σ.regs.get?
    SL A φf' sp (sp + 144#64) stB dB frame body
  storeSurvives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc stB.store
  envValid : EnvValid stB frame
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w

/-- Reclassify the reflected loop-head predicate as the exact closure-body
sequence entry.  Execution is reflexive; only the missing ABI facts are added. -/
theorem closureBodyEntryI_of_abi
    {g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {stB : SpecSt} {dB dLeft aLeft : Nat} {frame : Addr} {body : List Stmt}
    {sp : BitVec 64} {mB : Mem} {c : Config}
    (hne : body ≠ [])
    (ha : ClosureBodyEntryABI g' N A SL φf' φc stB dB frame body sp mB c)
    (hLoad : Vsa.Sim.Code.Eval_exprLoaded mB)
    (hc : SegEntry g' N A SL φf' φc stB dB dLeft aLeft callBodyLoopPC mB c) :
    ExecSeqEntryI .closureBody g' N A SL φf' φc stB dB frame body
      sp (sp + 144#64) mB c :=
  { good := hc.good
    tick := hc.tick
    pc := by
      cases hb : body with
      | nil => exact False.elim (hne hb)
      | cons s ss => simpa [execSeqEntryPC, hb] using hc.pc
    store := hc.store
    store_survives := ha.storeSurvives
    out := hc.out
    mem := hc.mem
    ready := fun _ =>
      { env_valid := ha.envValid
        code := by simpa [hc.mem] using hLoad
        cursor := ha.cursor
        head_ground := ha.headGround
        store_survives := ha.storeSurvives
        stack_ram := ha.stackRam
        stack_win := ha.stackWin }
    empty_status := fun hb => False.elim (hne hb)
    frame := fun R hR => hc.frame R hR.1
    minstret := ha.minstret }

theorem closureBodyEntry_of_abi
    {g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {stB : SpecSt} {dB dLeft aLeft : Nat} {frame : Addr} {body : List Stmt}
    {sp : BitVec 64} {mB : Mem}
    (hne : body ≠ [])
    (hABI : ∀ c,
      SegEntry g' N A SL φf' φc stB dB dLeft aLeft callBodyLoopPC mB c →
      ClosureBodyEntryABI g' N A SL φf' φc stB dB frame body sp mB c)
    (hLoad : Vsa.Sim.Code.Eval_exprLoaded mB) :
    Triple
      (SegEntry g' N A SL φf' φc stB dB dLeft aLeft callBodyLoopPC mB)
      (ExecSeqEntryI .closureBody g' N A SL φf' φc stB dB frame body
        sp (sp + 144#64) mB) := by
  intro c hc
  have ha := hABI c hc
  refine ⟨c, .refl c, ?_⟩
  exact closureBodyEntryI_of_abi hne ha hLoad hc

#print axioms closureBodyEntryI_of_abi
#print axioms closureBodyEntry_of_abi

/-! ## Empty-body value-null handoff -/

def EmptyBypassReady (clp : BitVec 64) : Config → Prop :=
  fun c => ∃ (lds : List (List (BitVec 8))) (m : Mem),
    SegPre callClosureBodyBypassSeg (callClosureBodyEntryL clp)
      lds 0x8000332c#64 m c

def EmptyBypassDone (clp : BitVec 64) : Config → Prop :=
  fun c => ∃ (lds : List (List (BitVec 8))) (m : Mem),
    CallClosureBodyBypassPost clp lds m c

theorem emptyBypassRun (clp : BitVec 64) :
    Triple (EmptyBypassReady clp) (EmptyBypassDone clp) := by
  intro c hc
  obtain ⟨lds, m, hp⟩ := hc
  obtain ⟨c', hs, hq⟩ := callClosureBodyBypassRow clp lds m c hp
  exact ⟨c', hs, lds, m, hq⟩

/-- Value-null staging facts for the empty-body polarity.  The final readback
uses the reflected not-taken body-count segment. -/
structure EmptyValueNullStage
    (N : NativeAddrs) (φc : Addr → Nat) (sp clp : BitVec 64)
    (stageLds : List (List (BitVec 8))) (m : Mem) (out0 : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x80003324#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = m
  spReg : c.σ.regs.get? Register.x2 = some sp
  closReg : c.σ.regs.get? Register.x21 = some clp
  out : c.σ.sailOutput = out0
  stageFacts : ChainFacts c.σ.mem c.σ.mem (callClosureValueNullCallL sp) []
    callClosureValueNullCallSeg
  jal : ∀ (σ' : MState) (i' u' : Nat),
    GoodState σ' → i' < 2 →
    σ'.regs.get? Register.PC = some (evalBlocksPC 0x80003324#64
      (SegEvalState.init (callClosureValueNullCallL sp) [])
      callClosureValueNullCallSeg) →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    σ'.mem = writeLog m (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).log →
    GHolds σ' (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).regs →
    JalStepO 0x800027ec#64 0x8000332c#64 σ' i' u'
  loaded : Vsa.Sim.Code.Value_nullLoaded c.σ.mem
  region : NullRegion (sp + 144#64)
  spNoWrap : sp.toNat + 168 < 2 ^ 64
  bypassReads : ∀ m2 : Mem,
    (∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = m2[k]?) →
    ChainFacts m2 m2 (callClosureBodyEntryL clp) stageLds
      callClosureBodyBypassSeg

/-- The empty reflected staging segment preserves ABI registers, all memory,
and output. -/
def emptyValueNullStageEffect : FrameEffect where
  regs := fun R => AbiPreserved R = true
  mem := fun _ => True
  output := True

/-- `value_null` preserves its ghost register frame, memory outside its
24-byte result slot, and output. -/
def valueNullFrameEffect (buf : BitVec 64) : FrameEffect where
  regs := NotWrittenV
  mem := fun k => ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24)
  output := True

/-- Execute the value-null staging/jal/helper and land the exact reflected
empty-body branch precondition. -/
theorem emptyValueNullRunFramed
    (N : NativeAddrs) (φc : Addr → Nat) (sp clp : BitVec 64)
    (stageLds : List (List (BitVec 8))) (m : Mem) (out0 : Array String) :
    FramedTriple
      (FrameEffect.comp emptyValueNullStageEffect
        (valueNullFrameEffect (sp + 144#64)))
      (EmptyValueNullStage N φc sp clp stageLds m out0)
      (EmptyBypassReady clp) := by
  refine ⟨fun c h => ?_⟩
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨σ2, i2, hs1, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2,
      hout2, habi2⟩ :=
    bridgeOfSegOut callClosureValueNullCallSeg (callClosureValueNullCallL sp) []
      c.σ c.tick c.steps 0x80003324#64 0x800027ec#64 0x8000332c#64 vm m
      h.good h.pc hmi h.mem ⟨h.spReg, trivial⟩
      (by show KeysOK [2]; decide) h.stageFacts h.tick
      (by show ChainOK 0x80003324#64 [2] callClosureValueNullCallSeg; decide)
      (by show WrChainAvoidAbi callClosureValueNullCallSeg; decide)
      (by show KeysOK [10, 2]; decide)
      (by show ∀ n ∈ ([10, 2] : List Nat), n ≠ 1; decide) h.jal
  have hmem2' : σ2.mem = c.σ.mem := by rw [hmem2, h.mem]; rfl
  have hx10 : σ2.regs.get? Register.x10 = some (sp + 144#64) := by
    have hx : gprGet σ2 10 = some
        (sp + sign_extend (m := 64) (0x090#12)) :=
      gholds_lookup _ hregs2 (by rfl)
    rw [show gprGet σ2 10 = σ2.regs.get? Register.x10 from rfl] at hx
    rwa [(by decide : (sign_extend (m := 64) (0x090#12) : BitVec 64) = 144#64)] at hx
  have hloaded2 : Vsa.Sim.Code.Value_nullLoaded σ2.mem := by
    rw [hmem2']; exact h.loaded
  let c2 : Config :=
    ⟨σ2, i2, c.steps + evalBlocksFuel callClosureValueNullCallSeg + 1⟩
  have hRunStage : FramedSteps emptyValueNullStageEffect c c2 := by
    refine
      { steps := by simpa [c2] using hs1
        frame := ?_ }
    exact
      { regs := ⟨fun R hR => by simpa [c2] using habi2 R hR⟩
        mem := fun k _ => by
          change σ2.mem[k]? = c.σ.mem[k]?
          rw [hmem2']
        output := fun _ => by simpa [c2] using hout2 }
  obtain ⟨c3, hs2, hp3⟩ :=
    value_null_spec_full (fun R => σ2.regs.get? R) (sp + 144#64) 0x8000332c#64
      N φc σ2.mem σ2.sailOutput c2
      ⟨hG2, hloaded2, rfl, hpc2, hx10, hra2, hmi2, hi2, h.region,
        (by decide), rfl, fun R _ => rfl⟩
  obtain ⟨hG3, hpc3, _hx10, _hra, hmi3, hi3, _hv, hout3,
    hframeMem, hframe3, _hext⟩ := hp3
  have hRunNull :
      FramedSteps (valueNullFrameEffect (sp + 144#64)) c2 c3 := by
    refine
      { steps := hs2
        frame := ?_ }
    exact
      { regs := ⟨fun R hR => by simpa [c2] using hframe3 R hR⟩
        mem := fun k hk => by simpa [c2] using (hframeMem k hk).symm
        output := fun _ => by simpa [c2] using hout3 }
  have hRun := hRunStage.comp hRunNull
  have hbufN : ((sp + 144#64 : BitVec 64)).toNat = sp.toNat + 144 := by
    have hlt := sp.isLt
    have hspw := h.spNoWrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hagree : ∀ k : Nat, ¬ (sp.toNat + 144 ≤ k ∧ k < sp.toNat + 168) →
      c.σ.mem[k]? = c3.σ.mem[k]? := by
    intro k hk
    have hnk : ¬ ((sp + 144#64 : BitVec 64).toNat ≤ k ∧
        k < (sp + 144#64 : BitVec 64).toNat + 24) := by
      rw [hbufN]; intro hh; exact hk ⟨hh.1, by omega⟩
    exact (hRun.frame.mem k ⟨trivial, hnk⟩).symm
  have hStageX21 : emptyValueNullStageEffect.regs Register.x21 := by
    change AbiPreserved Register.x21 = true
    decide
  have hNullX21 :
      (valueNullFrameEffect (sp + 144#64)).regs Register.x21 := by
    change NotWrittenV Register.x21
    decide
  have hx21 : c3.σ.regs.get? Register.x21 = some clp :=
    (hRun.frame.regs.eq Register.x21 ⟨hStageX21, hNullX21⟩).trans h.closReg
  have hpc3' : c3.σ.regs.get? Register.PC = some (0x8000332c#64 : BitVec 64) := by
    simpa using hpc3
  have hfacts := h.bypassReads c3.σ.mem hagree
  refine ⟨c3, ?_, hRun⟩
  exact ⟨stageLds, c3.σ.mem, hG3, rfl, hpc3', hmi3, ⟨hx21, trivial⟩,
    (by show KeysOK [21]; decide), hfacts, hi3⟩

/-- Compatibility projection for callers that do not consume the frame. -/
theorem emptyValueNullRun
    (N : NativeAddrs) (φc : Addr → Nat) (sp clp : BitVec 64)
    (stageLds : List (List (BitVec 8))) (m : Mem) (out0 : Array String) :
    Triple (EmptyValueNullStage N φc sp clp stageLds m out0)
      (EmptyBypassReady clp) :=
  (emptyValueNullRunFramed N φc sp clp stageLds m out0).triple

#print axioms emptyValueNullRunFramed
#print axioms emptyValueNullRun
#print axioms emptyBypassRun

/-- Last parameter iteration for the empty-body route.  The helper call is
split from the reflected not-taken fold back-edge. -/
structure ClosureEmptyLastStages
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp fp clp : BitVec 64) (m0 : Mem)
    (valueLds : List (List (BitVec 8))) (valueMem : Mem)
    (valueOut : Array String) : Type where
  PreDef : Config → Prop
  PostDef : Config → Prop
  s6v : BitVec 64
  exitLds : List (List (BitVec 8))
  exitMem : Mem
  stage : Triple
    (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
      ((cd.params.zip vs).length - 1)) PreDef
  define : EnvDefineCallStages PreDef PostDef
  toExit : ∀ c, PostDef c →
    SegPre callClosureFoldBackExitSeg (callClosureFoldBackL sp s6v)
      exitLds 0x80003314#64 exitMem c
  land : ∀ c,
    CallClosureFoldBackExitPost sp s6v exitLds exitMem c →
    EmptyValueNullStage N φc sp clp valueLds valueMem valueOut c

theorem closureEmptyLastRun
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp fp clp : BitVec 64} {m0 : Mem}
    {valueLds : List (List (BitVec 8))} {valueMem : Mem}
    {valueOut : Array String}
    (S : ClosureEmptyLastStages N A SL φf' φc st store' cd vs frame
      sp fp clp m0 valueLds valueMem valueOut) :
    Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
        ((cd.params.zip vs).length - 1))
      (EmptyValueNullStage N φc sp clp valueLds valueMem valueOut) :=
  Triple.seq S.stage <| Triple.seq (envDefineCall_of_stages S.define) <|
    Triple.seq (fun c hc => ⟨c, .refl c, S.toExit c hc⟩) <|
    Triple.seq (callClosureFoldBackExitRow sp S.s6v S.exitLds S.exitMem)
      (fun c hc => ⟨c, .refl c, S.land c hc⟩)

#print axioms closureEmptyLastRun

/-- Empty-body cuts.  The shared allocation/fold prefix stops before the
body-count branch; the concrete not-taken branch and jump to the indexed empty
boundary execute in `closureEmptyEntry_of_stages`. -/
structure ClosureEmptyStages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (d : Nat) (sp fp clp : BitVec 64) (m0 : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem) : Type where
  valueLds : List (List (BitVec 8))
  valueMem : Mem
  valueOut : Array String
  envRetA0 : BitVec 64
  envRetS6 : BitVec 64
  envRetLds : List (List (BitVec 8))
  envRetMem : Mem
  last : ∀ (φf' : Addr → Nat),
    PhiExtends φf φf' st.store.frames.size →
    ClosureEmptyLastStages N A SL φf' φc st store' cd vs frame
      sp fp clp m0 valueLds valueMem valueOut
  noParamsToRow : (cd.params.zip vs).length = 0 → ∀ c,
    (env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
      extsE N φf φc (some cd.env) mEnvNew) c →
    SegPre callClosureEnvNewRetBypassSeg
      (callClosureEnvNewRetL sp envRetA0 envRetS6) envRetLds
      0x800032c0#64 envRetMem c
  noParamsLand : ∀ c,
    CallClosureEnvNewRetBypassPost sp envRetA0 envRetS6 envRetLds envRetMem c →
    EmptyValueNullStage N φc sp clp valueLds valueMem valueOut c
  land : ∀ c, EmptyBypassDone clp c →
    IndexedBodyHandoff g N A SL φf φc st store' cd vs frame d sp m0 c

theorem closureEmptyEntry_of_stages
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {d : Nat} {a : Addr} {dLeft aLeft : Nat}
    {sp sret fp clp : BitVec 64} {m0 : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem)
    (S : ClosureEmptyStages g N A SL φf φc st store' cd vs frame
      d sp fp clp m0 M gE par s0E extsE mEnvNew)
    (hER : ∀ p : Nat, EnvRegions SL M.privFoot sp.toNat p)
    (hDispatchStage : ClosureDispatchStages g N A SL φf φc st d a cd vs
      dLeft aLeft sp sret m0 M gE par s0E extsE mEnvNew)
    (hEnvNewToFold : 0 < (cd.params.zip vs).length →
      ClosureEnvNewFoldStages N A SL φf φc st store' cd vs frame
        sp fp clp m0 M gE par s0E extsE mEnvNew)
    (hFoldSeam : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size →
      ∀ k, k + 1 < (cd.params.zip vs).length → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 (k + 1))) :
    Triple
      (CallEntryI g N A SL φf φc st d (.closure a) vs
        dLeft aLeft sp sret m0)
      (IndexedBodyHandoff g N A SL φf φc st store' cd vs frame d sp m0) :=
  Triple.seq (closureDispatch_of_stages hDispatchStage) <| Triple.seq
    (env_new_spec A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
      extsE N φf φc (some cd.env) mEnvNew hER) <| Triple.seq (by
        rcases Nat.eq_zero_or_pos (cd.params.zip vs).length with h0 | hpos
        · exact Triple.seq
            (fun c hc => ⟨c, .refl c, S.noParamsToRow h0 c hc⟩) <|
            Triple.seq
              (callClosureEnvNewRetBypassRow sp S.envRetA0 S.envRetS6
                S.envRetLds S.envRetMem)
              (fun c hc => ⟨c, .refl c, S.noParamsLand c hc⟩)
        · intro c hc
          obtain ⟨c1, hs1, φf', hpe, hcar0⟩ :=
            envNewToFold_of_stages (hEnvNewToFold hpos) c hc
          obtain ⟨c2, hs2, hcarN⟩ :=
            storeChainList
              (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0)
              ((cd.params.zip vs).length - 1)
              (fun k hk => hFoldSeam φf' hpe k (by omega)) c1 hcar0
          obtain ⟨c3, hs3, hstage⟩ :=
            closureEmptyLastRun (S.last φf' hpe) c2 hcarN
          exact ⟨c3, Steps.trans hs1 (Steps.trans hs2 hs3), hstage⟩) <|
      Triple.seq
        (emptyValueNullRun N φc sp clp S.valueLds S.valueMem S.valueOut) <|
      Triple.seq (emptyBypassRun clp)
        (fun c hc => ⟨c, .refl c, S.land c hc⟩)

#print axioms closureEmptyEntry_of_stages

/-! ## §3b. env_new_pre side-condition marshalling (wave 40)

The `hDispatchStage` residual owes `env_new_pre`'s side conditions.  The one
that is a pure `StoreRepr` projection is the parent-link selector at
`parentSpec := some cd.env`: the dispatch stage's `ld a0,8(a3)` (a3 = the
closure record `φc a`) reads `cd->env`, and `ClosureRepr` pins those bytes to
`φf cd.env ≠ 0` — so the load readback IS the selector's witness.  The
remaining pre conditions are NOT `SegEntry`-derivable and stay with the named
stage: `Env_newLoaded` (a code pin — `SegEntry` carries no Loaded clause, the
`segEntry_of_jalPrefix` class), `M.AInv`/`StackOK`/non-exhaustion (contract/
layout facts of the arm). -/

/-- **The closure record off the store** — `st.store.closures[a]? = some cd`
inverted through `StoreRepr.closures`. -/
theorem closureRepr_of_storeRepr
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {s : Store}
    {a : Addr} {cd : ClosureData}
    (hstore : StoreRepr m N A φf φc s)
    (hClos : s.closures[a]? = some cd) :
    ClosureRepr m φf (φc a) cd := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hClos
  have h := hstore.closures a hlt
  rwa [heq] at h

/-- **The env_new parent-link marshalling**: the `cd->env` field bytes at
`8(φc a)` are the extended-map image `φf cd.env`, non-NULL — exactly the
`env_new_pre` `parentSpec := some cd.env` selector's content, and the honest
`lds` instantiation for the dispatch bridge's `ld a0,8(a3)`. -/
theorem envNewParentLink_of_storeRepr
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {s : Store}
    {a : Addr} {cd : ClosureData}
    (hstore : StoreRepr m N A φf φc s)
    (hClos : s.closures[a]? = some cd) :
    read64 m (φc a + 8) = some (φf cd.env) ∧ φf cd.env ≠ 0 :=
  (closureRepr_of_storeRepr hstore hClos).2

/-- **The selector in `env_new_pre`'s match shape**: given the machine's
loaded parent word `par` (= the `8(φc a)` readback), the
`parentSpec = some cd.env` clause `φf cd.env = par.toNat ∧ par ≠ 0#64`. -/
theorem envNewParentSel_of_storeRepr
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {s : Store}
    {a : Addr} {cd : ClosureData} {par : BitVec 64}
    (hstore : StoreRepr m N A φf φc s)
    (hClos : s.closures[a]? = some cd)
    (hpar : par.toNat = φf cd.env) :
    φf cd.env = par.toNat ∧ par ≠ 0#64 := by
  refine ⟨hpar.symm, fun h0 => ?_⟩
  exact (envNewParentLink_of_storeRepr hstore hClos).2
    (by rw [← hpar, h0]; rfl)

#print axioms closureRepr_of_storeRepr
#print axioms envNewParentLink_of_storeRepr
#print axioms envNewParentSel_of_storeRepr

/-! ## §4. The return route — the status split named

The amended `ret` field is ONE Triple covering both `a_6` statuses; the machine
routes differ (`.normal` exits the body loop via `bge @0x80003350 →
0x80003954`, `.ret v` falls through the classification `0x8000337c..0x80003398`
into the GEN `callClosureRetCopyRow` span `0x8000339c ▷ j callJoinPC`).
`callClosureRet_of_status` composes the field from the two guarded routes —
each a named residual whose machine content is documented at its guard. -/

/-- The `ret`-field body shape (the amended `CallClosureGeom.ret` minus its
`cd.body ≠ []` guard), abbreviated for the status-split composer. -/
def CallRetShape
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (status : Status) (v : Value) (sp sret : BitVec 64)
    (m0 : Mem) : Prop :=
  -- wave 40: the entry-side spill image (the amended `mCall`/`ret` hypothesis).
  Scaffold.EntryImage callDispatchPC g m0 →
  ∀ (g' : (R : Register) → Option (RegisterType R)) (φf' : Addr → Nat) (mB : Mem),
    PhiExtends φf φf' st.store.frames.size →
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mB[a]? = m0[a]?) →
    BodyGhostTie g g' →
    (∀ spv : BitVec 64, g Register.x2 = some spv →
      CallerSpillSlots g spv mB m0) →
    Triple
      (ExecSeqExitI .closureBody g' N A SL φf' φc
        (closureBoundSt st store' cd vs frame).store.frames.size
        (closureBoundSt st store' cd vs frame).store.closures.size
        st' status sp (sp + 144#64) mB)
      (CallExitI g N A SL φf φc
        st.store.frames.size st.store.closures.size st' v sret m0)

/-- Normal-return cuts.  The first field covers only depth decrement and
`value_null`, stopping at the concrete reload row.  The reload row itself is
executed by `callClosureNormalRoute_of_stages`; the final field only marshals
its computed postcondition into `CallExitI`. -/
structure NormalDepthReady
    (s2v s1v : BitVec 64) (lds : List (List (BitVec 8)))
    (m : Mem) (out0 : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x80003954#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = m
  pins : GHolds c.σ (callClosureNormalDepthL s2v s1v)
  facts : ChainFacts c.σ.mem c.σ.mem
    (callClosureNormalDepthL s2v s1v) lds callClosureNormalDepthSeg
  out : c.σ.sailOutput = out0
  keysOut : KeysOK (keysG (evalBlocks callClosureNormalDepthSeg
    (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs)
  raOut : KeysAvoidRa (evalBlocks callClosureNormalDepthSeg
    (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs
  a0Out : lookupG 10 (evalBlocks callClosureNormalDepthSeg
    (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs = some s1v
  jal : ∀ (σ' : MState) (i' u' : Nat),
    GoodState σ' → i' < 2 →
    σ'.regs.get? Register.PC = some (evalBlocksPC 0x80003954#64
      (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)
      callClosureNormalDepthSeg) →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    σ'.mem = writeLog m (evalBlocks callClosureNormalDepthSeg
      (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log →
    GHolds σ' (evalBlocks callClosureNormalDepthSeg
      (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs →
    JalStepO 0x800027ec#64 0x80003968#64 σ' i' u'
  loaded : Vsa.Sim.Code.Value_nullLoaded (writeLog m (evalBlocks callClosureNormalDepthSeg
    (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log)
  region : NullRegion s1v

def NormalNullDone
    (N : NativeAddrs) (φc : Addr → Nat) (s1v : BitVec 64)
    (m outMem : Mem) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (0x80003968#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some s1v ∧
  c.σ.regs.get? Register.x1 = some (0x80003968#64 : BitVec 64) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.tick < 2 ∧
  ValueRepr c.σ.mem N φc s1v.toNat .null ∧
  c.σ.sailOutput = out0 ∧
  (∀ k : Nat, ¬ (s1v.toNat ≤ k ∧ k < s1v.toNat + 24) →
    outMem[k]? = c.σ.mem[k]?) ∧
  MemExtends outMem c.σ.mem

theorem normalDepthNullRun
    (N : NativeAddrs) (φc : Addr → Nat) (s2v s1v : BitVec 64)
    (lds : List (List (BitVec 8))) (m : Mem) (out0 : Array String) :
    Triple (NormalDepthReady s2v s1v lds m out0)
      (NormalNullDone N φc s1v m
        (writeLog m (evalBlocks callClosureNormalDepthSeg
          (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log) out0) := by
  intro c h
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨σ2, i2, hs1, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2,
      hout2, _hframe2⟩ :=
    bridgeOfSegOut callClosureNormalDepthSeg
      (callClosureNormalDepthL s2v s1v) lds c.σ c.tick c.steps
      0x80003954#64 0x800027ec#64 0x80003968#64 vm m
      h.good h.pc hmi h.mem h.pins
      (by show KeysOK [18, 9]; decide) h.facts h.tick
      (by show ChainOK 0x80003954#64 [18, 9] callClosureNormalDepthSeg; decide)
      (by decide) h.keysOut h.raOut h.jal
  let c2 : Config :=
    ⟨σ2, i2, c.steps + evalBlocksFuel callClosureNormalDepthSeg + 1⟩
  have hx10 : σ2.regs.get? Register.x10 = some s1v := by
    simpa [gprGet] using (gholds_lookup _ hregs2 h.a0Out)
  have hloaded2 : Vsa.Sim.Code.Value_nullLoaded c2.σ.mem := by
    rw [show c2.σ.mem = writeLog m (evalBlocks callClosureNormalDepthSeg
      (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log from hmem2]
    exact h.loaded
  obtain ⟨c3, hs2, hpost⟩ :=
    value_null_spec_full (fun R => σ2.regs.get? R) s1v 0x80003968#64
      N φc (writeLog m (evalBlocks callClosureNormalDepthSeg
        (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log)
      out0 c2
      ⟨hG2, hloaded2, hmem2, hpc2, hx10, hra2, hmi2, hi2, h.region,
        (by decide), hout2.trans h.out, fun _ _ => rfl⟩
  refine ⟨c3, hs1.trans hs2, ?_⟩
  rcases hpost with ⟨hG3, hpc3, hx103, hx13, hmi3, hi3, hv3, hout3,
    hmem3, _hframe3, hext3⟩
  refine ⟨hG3, ?_, hx103, hx13, hmi3, hi3, hv3, hout3, hmem3, hext3⟩
  simpa using hpc3

#print axioms normalDepthNullRun

structure ClosureNormalStages
    (g g' : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φf' : Addr → Nat)
    (st st' : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp sret : BitVec 64) (m0 mB : Mem) : Type where
  s2v : BitVec 64
  s1v : BitVec 64
  depthLds : List (List (BitVec 8))
  depthMem : Mem
  depthOut : Array String
  reloadLds : List (List (BitVec 8))
  reloadMem : Mem
  toDepth : ∀ c,
    ExecSeqExitI .closureBody g' N A SL φf' φc
      (closureBoundSt st store' cd vs frame).store.frames.size
      (closureBoundSt st store' cd vs frame).store.closures.size
      st' .normal sp (sp + 144#64) mB c →
    NormalDepthReady s2v s1v depthLds depthMem depthOut c
  nullToReload : ∀ c,
    NormalNullDone N φc s1v depthMem
      (writeLog depthMem (evalBlocks callClosureNormalDepthSeg
        (SegEvalState.init (callClosureNormalDepthL s2v s1v) depthLds)).log)
      depthOut c →
    SegPre callClosureNormalJoinSeg (callClosureNormalJoinL sp)
      reloadLds 0x80003968#64 reloadMem c
  reloadToExit : ∀ c,
    CallClosureNormalJoinPost sp reloadLds reloadMem c →
    CallExitI g N A SL φf φc
      st.store.frames.size st.store.closures.size st' .null sret m0 c

def ClosureNormalStageProvider
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp sret : BitVec 64) (m0 : Mem) : Type :=
  Scaffold.EntryImage callDispatchPC g m0 →
  ∀ (g' : (R : Register) → Option (RegisterType R)) (φf' : Addr → Nat)
    (mB : Mem),
    PhiExtends φf φf' st.store.frames.size →
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mB[a]? = m0[a]?) →
    BodyGhostTie g g' →
    (∀ spv : BitVec 64, g Register.x2 = some spv →
      CallerSpillSlots g spv mB m0) →
    ClosureNormalStages g g' N A SL φf φc φf'
      st st' store' cd vs frame sp sret m0 mB

/-- Compose the normal decrement/null stage with the concrete three-register
reload row and its exact exit marshal. -/
theorem callClosureNormalRoute_of_stages
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp sret : BitVec 64} {m0 : Mem}
    (hStages : ClosureNormalStageProvider g N A SL φf φc
      st st' store' cd vs frame sp sret m0) :
    CallRetShape g N A SL φf φc st st' store' cd vs frame
      .normal .null sp sret m0 := by
  intro hImg g' φf' mB hpe hfr htie hslots
  let hS := hStages hImg g' φf' mB hpe hfr htie hslots
  exact Triple.seq (fun c hc => ⟨c, .refl c, hS.toDepth c hc⟩) <| Triple.seq
    (normalDepthNullRun N φc hS.s2v hS.s1v hS.depthLds
      hS.depthMem hS.depthOut) <| Triple.seq
    (fun c hc => ⟨c, .refl c, hS.nullToReload c hc⟩) <| Triple.seq
    (callClosureNormalJoinRow sp hS.reloadLds hS.reloadMem)
    (fun c hc => ⟨c, .refl c, hS.reloadToExit c hc⟩)

/-- `.ret` cuts.  The concrete classification and result-copy rows execute in
the composer.  Premises are restricted to the two one-instruction marshals
around those rows and the final `CallExitI` reconstruction. -/
structure ClosureRetStages
    (g g' : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φf' : Addr → Nat)
    (st st' : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (v : Value) (sp sret : BitVec 64) (m0 mB : Mem) : Type where
  s2v : BitVec 64
  s0v : BitVec 64
  bodyExitLds : List (List (BitVec 8))
  classLds : List (List (BitVec 8))
  classMem : Mem
  copyLds : List (List (BitVec 8))
  copyMem : Mem
  toBodyExit : ∀ c,
    ExecSeqExitI .closureBody g' N A SL φf' φc
      (closureBoundSt st store' cd vs frame).store.frames.size
      (closureBoundSt st store' cd vs frame).store.closures.size
      st' (.ret v) sp (sp + 144#64) mB c →
    SegPre callClosureBodyExitRetSeg (callClosureBodyExitL 3#64 sp s0v)
      bodyExitLds 0x80003378#64 mB c
  bodyExitToClass : ∀ c,
    CallClosureBodyExitRetPost 3#64 sp s0v bodyExitLds mB c →
    SegPre callClosureRetClassSeg (callClosureRetClassL s2v 3#64)
      classLds 0x8000337c#64 classMem c
  classToCopy : ∀ c,
    CallClosureRetClassPost s2v 3#64 classLds classMem c →
    SegPre callClosureRetCopySeg (callClosureRetCopyL sp sret)
      copyLds 0x8000339c#64 copyMem c
  copyToExit : ∀ c,
    CallClosureRetCopyPost sp sret copyLds copyMem c →
    CallExitI g N A SL φf φc
      st.store.frames.size st.store.closures.size st' v sret m0 c

def ClosureRetStageProvider
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (v : Value) (sp sret : BitVec 64) (m0 : Mem) : Type :=
  Scaffold.EntryImage callDispatchPC g m0 →
  ∀ (g' : (R : Register) → Option (RegisterType R)) (φf' : Addr → Nat)
    (mB : Mem),
    PhiExtends φf φf' st.store.frames.size →
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mB[a]? = m0[a]?) →
    BodyGhostTie g g' →
    (∀ spv : BitVec 64, g Register.x2 = some spv →
      CallerSpillSlots g spv mB m0) →
    ClosureRetStages g g' N A SL φf φc φf'
      st st' store' cd vs frame v sp sret m0 mB

/-- Compose the `.ret` route through the concrete status classification and
24-byte result-copy rows. -/
theorem callClosureRetRoute_of_stages
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {v : Value} {sp sret : BitVec 64} {m0 : Mem}
    (hStages : ClosureRetStageProvider g N A SL φf φc
      st st' store' cd vs frame v sp sret m0) :
    CallRetShape g N A SL φf φc st st' store' cd vs frame
      (.ret v) v sp sret m0 := by
  intro hImg g' φf' mB hpe hfr htie hslots
  let hS := hStages hImg g' φf' mB hpe hfr htie hslots
  exact Triple.seq (fun c hc => ⟨c, .refl c, hS.toBodyExit c hc⟩) <| Triple.seq
    (callClosureBodyExitRetRow 3#64 sp hS.s0v hS.bodyExitLds mB) <|
    Triple.seq (fun c hc => ⟨c, .refl c, hS.bodyExitToClass c hc⟩) <| Triple.seq
    (callClosureRetClassRow hS.s2v 3#64 hS.classLds hS.classMem) <|
    Triple.seq (fun c hc => ⟨c, .refl c, hS.classToCopy c hc⟩) <| Triple.seq
      (callClosureRetCopyRow sp sret hS.copyLds hS.copyMem)
      (fun c hc => ⟨c, .refl c, hS.copyToExit c hc⟩)

#print axioms callClosureNormalRoute_of_stages
#print axioms callClosureRetRoute_of_stages

/-- **The status split.**  `hNormal` = the `.normal` route (`--call_depth` ≫
the `0x80003954` null-copy path ≫ join); `hRetV` = the `.ret v` route
(classification ≫ `callClosureRetCopyRow` ≫ join marshalling).  The
wave-37 residual-strength gap (`body-ih-no-caller-frame-slots`) is now SUPPLIED:
the body IH's `SegExit.stackWin` at the tabled `callBodyRetPC` (`k = 168`, see
`callerSlotsSurviveBody` below) preserves `[sp+168, SL.hi)` across the body, and
`CallRetShape`'s `BodyGhostTie`/`CallerSpillSlots` hypotheses carry the slot
contents + register ties around the IH.  The remaining ret-route residuals are
the status→`a0` ABI gap (`seqfor-motive-rows` class) and the `s7@1016` g-image
(`segentry-no-caller-spill-image`, entry-side). -/
theorem callClosureRet_of_status
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp sret : BitVec 64} {m0 : Mem} {status : Status} {v : Value}
    (hStatus : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v)
    (hNormal : status = Status.normal → v = Value.null →
      CallRetShape g N A SL φf φc st st' store' cd vs frame status v sp sret m0)
    (hRetV : status = Status.ret v →
      CallRetShape g N A SL φf φc st st' store' cd vs frame status v sp sret m0) :
    CallRetShape g N A SL φf φc st st' store' cd vs frame status v sp sret m0 := by
  rcases hStatus with ⟨h, hv⟩ | h
  · exact hNormal h hv
  · exact hRetV h

#print axioms callClosureRet_of_status

/-- **The caller slots survive the body** — the wave-38 `stackWin` clause
FIRING at its tabled exit PC.  From the body IH's `SegExit` at
`callBodyRetPC = 0x80003378` (table entry `k = 168`), the sp anchor
`g' x2 = some spv`, and the two geometry side conditions (the spill window
`[spv+1016, spv+1056)` lies inside the stack region and outside the arena —
`StackOK`-level facts the arm carries), every byte of the restore window
survives to the handoff memory `mB`.  Composed with `CallerSpillSlots` this
hands the ret-route discharger the exact bytes its `ld s3/s5/s7` reload. -/
theorem callerSlotsSurviveBody
    {g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {mB : Mem} {c : Config} {spv : BitVec 64}
    (hexit : SegExit g' N A SL φf' φc nf nc st' callBodyRetPC mB c)
    (hspv : g' Register.x2 = some spv)
    (hhi : spv.toNat + 1056 ≤ SL.hi)
    (hArena : ∀ a : Nat, spv.toNat + 1016 ≤ a → a < spv.toNat + 1056 →
      ¬ (A.lo ≤ a ∧ a < A.hi)) :
    ∀ a : Nat, spv.toNat + 1016 ≤ a → a < spv.toNat + 1056 →
      c.σ.mem[a]? = mB[a]? := by
  intro a hlo hhi'
  exact hexit.stackWin 168 (by decide) spv hspv a (by omega) (by omega)
    (hArena a hlo hhi')

#print axioms callerSlotsSurviveBody

/-- The indexed closure-body exit carries the same high-stack preservation
directly.  This is the fact consumed by the s3/s5/s7 reload routes. -/
theorem callerSlotsSurviveIndexedBody
    {g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {status : Status}
    {sp aRet : BitVec 64} {mB : Mem} {c : Config}
    (hexit : ExecSeqExitI .closureBody g' N A SL φf' φc nf nc
      st' status sp aRet mB c)
    (hhi : sp.toNat + 1056 ≤ SL.hi) :
    ∀ a : Nat, sp.toNat + 1016 ≤ a → a < sp.toNat + 1056 →
      c.σ.mem[a]? = mB[a]? := by
  intro a hlo hlt
  exact hexit.stack_frame a (by omega) (by omega)

#print axioms callerSlotsSurviveIndexedBody

/-- **The `s7` restore image at the body exit** — the wave-40 entry-side
spill-image clause MEETING the wave-38 carry: `EntryImage@callDispatchPC`
(table entry `(1016, 23)`) pins the `m0` bytes at `[sp+1016, sp+1024)` to the
arm ghost's `s7 = g x23`, and `CallerSpillSlots.s7carry` says the entry route
left that window untouched (`mB = m0` there).  Composed with
`callerSlotsSurviveBody` (the `stackWin` firing, `mExec = mB` on
`[sp+1016, sp+1056)`) the `.normal`/`.ret` restore segs' `ld s7,1016(sp)`
readback is the ghost value — the last register fact the join `frame` clause
needed (ledger `segentry-no-caller-spill-image`: RESOLVED at this seam). -/
theorem s7ImageAtBody
    {g : (R : Register) → Option (RegisterType R)} {spv w : BitVec 64}
    {mB m0 : Mem}
    (hImg : EntryImage callDispatchPC g m0)
    (hslots : CallerSpillSlots g spv mB m0)
    (hspv : g Register.x2 = some spv)
    (hw : g Register.x23 = some w) :
    ∀ i : Nat, i < 8 →
      mB[spv.toNat + 1016 + i]? = some (w.extractLsb' (8 * i) 8) := by
  intro i hi
  rw [hslots.s7carry i hi]
  exact hImg 1016 23 (by decide) spv hspv w (by rw [gGpr_x23]; exact hw) i hi

#print axioms s7ImageAtBody

/-- Exact saved-register byte images available to the closure return rows after
the recursive body. -/
structure ClosureReloadImage
    (g : (R : Register) → Option (RegisterType R))
    (sp : BitVec 64) (m : Mem) : Prop where
  s5 : ∀ w : BitVec 64, g Register.x21 = some w →
    ∀ i : Nat, i < 8 → m[sp.toNat + 1032 + i]? = some (w.extractLsb' (8 * i) 8)
  s3 : ∀ w : BitVec 64, g Register.x19 = some w →
    ∀ i : Nat, i < 8 → m[sp.toNat + 1048 + i]? = some (w.extractLsb' (8 * i) 8)
  s7 : ∀ w : BitVec 64, g Register.x23 = some w →
    ∀ i : Nat, i < 8 → m[sp.toNat + 1016 + i]? = some (w.extractLsb' (8 * i) 8)

/-- The indexed sequence frame and entry spill images jointly discharge every
saved-register load performed by the normal and `.ret` return rows. -/
theorem closureReloadImage_of_indexed
    {g g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {status : Status}
    {sp aRet : BitVec 64} {mB m0 : Mem} {c : Config}
    (hexit : ExecSeqExitI .closureBody g' N A SL φf' φc nf nc
      st' status sp aRet mB c)
    (hImg : EntryImage callDispatchPC g m0)
    (hslots : CallerSpillSlots g sp mB m0)
    (hgsp : g Register.x2 = some sp)
    (hhi : sp.toNat + 1056 ≤ SL.hi) :
    ClosureReloadImage g sp c.σ.mem := by
  constructor
  · intro w hw i hi
    rw [hexit.stack_frame (sp.toNat + 1032 + i) (by omega) (by omega)]
    exact hslots.s5 w hw i hi
  · intro w hw i hi
    rw [hexit.stack_frame (sp.toNat + 1048 + i) (by omega) (by omega)]
    exact hslots.s3 w hw i hi
  · intro w hw i hi
    rw [hexit.stack_frame (sp.toNat + 1016 + i) (by omega) (by omega)]
    exact s7ImageAtBody hImg hslots hgsp hw i hi

#print axioms closureReloadImage_of_indexed

/-- The faithful closure-body status route.  Normal completion already lands
at `0x80003954`; only `.ret` visits `0x80003378` and exposes `a0 = 3`. -/
structure BodyStatusABI (status : Status) (c : Config) : Prop where
  normal : status = Status.normal →
    c.σ.regs.get? Register.PC = some (0x80003954#64 : BitVec 64)
  retv : ∀ v : Value, status = Status.ret v →
    c.σ.regs.get? Register.PC = some (0x80003378#64 : BitVec 64) ∧
    c.σ.regs.get? Register.x10 = some (3#64 : BitVec 64)

theorem bodyStatusABI_of_indexed
    {g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {status : Status}
    {sp aRet : BitVec 64} {mB : Mem} {c : Config}
    (hexit : ExecSeqExitI .closureBody g' N A SL φf' φc nf nc
      st' status sp aRet mB c) :
    BodyStatusABI status c := by
  constructor
  · intro hs
    subst status
    exact hexit.pc
  · intro v hs
    subst status
    exact ⟨hexit.pc, by simpa [ExecSeqStatusABI] using hexit.status_abi⟩

#print axioms bodyStatusABI_of_indexed

/-! ## §5. Assembly into the residual slot -/

/-- **Assemble `CallClosureGeom`** from the three route providers (the amended
three-field shape).  `entryBase` comes from `callClosureEntrySplice` (§3);
`ret` from `callClosureRet_of_status` (§4); `emptyBypass` from the shared
entry splice up to the `bgtz` check plus the `.normal` return arm. -/
theorem callClosureGeom_of
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {a : Addr} {cd : ClosureData} {vs : List Value}
    {store' : Store} {frame : Addr} {status : Status} {v : Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem}
    -- Dispatch, `env_new`, and parameter-fold stage data.
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem)
    (fp clp : BitVec 64)
    (hStatus : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v)
    (hER : ∀ p : Nat, EnvRegions SL M.privFoot sp.toNat p)
    (hDispatchStage : ClosureDispatchStages g N A SL φf φc st d a cd vs
      dLeft aLeft sp sret m0 M gE par s0E extsE mEnvNew)
    (hEnvNewToFold : 0 < (cd.params.zip vs).length →
      ClosureEnvNewFoldStages N A SL φf φc st store' cd vs frame
        sp fp clp m0 M gE par s0E extsE mEnvNew)
    (hFoldSeam : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size →
      ∀ k, k + 1 < (cd.params.zip vs).length → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 (k + 1)))
    (hFoldToHandoff : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
          ((cd.params.zip vs).length - 1))
        (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0))
    (hNoParams : (cd.params.zip vs).length = 0 → Triple
      (env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE N φf φc (some cd.env) mEnvNew)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0))
    (hNormalStages : ClosureNormalStageProvider g N A SL φf φc
      st st' store' cd vs frame sp sret m0)
    (hRetStages : ClosureRetStageProvider g N A SL φf φc
      st st' store' cd vs frame v sp sret m0)
    (hEmpty : cd.body = [] → ClosureEmptyStages g N A SL φf φc
      st store' cd vs frame d sp fp clp m0 M gE par s0E extsE mEnvNew) :
    CallClosureGeom g N A SL φf φc st st' d a cd vs store' frame status v
      dLeft aLeft sp sret m0 :=
  { entryBase := fun hne =>
      callClosureEntrySplice g N A SL φf φc st store' cd vs frame
        d a dLeft aLeft sret m0 M gE par sp s0E extsE mEnvNew fp clp hne hER
        hDispatchStage hEnvNewToFold hFoldSeam hFoldToHandoff hNoParams
    ret := callClosureRet_of_status hStatus
      (fun hs hv => by
        subst status
        subst v
        exact callClosureNormalRoute_of_stages hNormalStages)
      (fun hs => by
        subst status
        exact callClosureRetRoute_of_stages hRetStages)
    emptyEntry := fun hb =>
      closureEmptyEntry_of_stages M gE par s0E extsE mEnvNew (hEmpty hb)
        hER hDispatchStage hEnvNewToFold hFoldSeam }

#print axioms callClosureGeom_of

/-! ## §6. The red-zone mechanical layer for the generated staging segs

`rzSeamFrame_of_run` (CallFrameMeta) turns ONE `LogInRZ` fact per staging seg
into the whole seam frame (ABI + mem-out + `AInv` survival + code-pin
survival).  The three stack-writing GEN segs of this arm get their containment
lemmas here; `callClosureValueNullCallSeg` writes NOTHING (log `= []` by
`rfl`), so its seam is memory-pure. -/

/-- The `sd a5,0(sp)` spill window of the `env_new` staging seg. -/
def callClosureEnvNewSpillRZ (sp : BitVec 64) : RedZone :=
  ⟨sp.toNat, sp.toNat + 8⟩

/-- **Log containment** for `callClosureEnvNewCallSeg` (`ld a0,8(a3) ;
sd a5,0(sp)`): one doubleword at `sp+0`. -/
theorem callClosureEnvNewSpill_logInRZ (a3 sp a5 : BitVec 64) :
    LogInRZ (callClosureEnvNewSpillRZ sp)
      (evalBlocks callClosureEnvNewCallSeg
        (SegEvalState.init (callClosureEnvNewCallL a3 sp a5) [])).log := by
  have hlog : (evalBlocks callClosureEnvNewCallSeg
      (SegEvalState.init (callClosureEnvNewCallL a3 sp a5) [])).log
      = [((sp + sign_extend (m := 64) (0x000#12)).toNat, 8, a5)] := by rfl
  rw [hlog]
  refine ⟨?_, trivial⟩
  rw [off0_addr sp]
  show (callClosureEnvNewSpillRZ sp).lo ≤ sp.toNat ∧
    sp.toNat + 8 ≤ (callClosureEnvNewSpillRZ sp).hi
  have hlo : (callClosureEnvNewSpillRZ sp).lo = sp.toNat := rfl
  have hhi : (callClosureEnvNewSpillRZ sp).hi = sp.toNat + 8 := rfl
  omega

/-- The `sd s7,1016(sp)` spill window of the arg-loop entry seg. -/
def callClosureArgSpillRZ (sp : BitVec 64) : RedZone :=
  ⟨(sp + 1016#64).toNat, (sp + 1016#64).toNat + 8⟩

/-- **Log containment** for `callClosureArgLoopEntrySeg` (`sd s7,1016(sp) ;
ld a3,0(sp) ; li a6,0 ▷ blez`): one doubleword at `sp+1016`. -/
theorem callClosureArgSpill_logInRZ (sp s7v a5v : BitVec 64) :
    LogInRZ (callClosureArgSpillRZ sp)
      (evalBlocks callClosureArgLoopEntrySeg
        (SegEvalState.init (callClosureArgLoopEntryL sp s7v a5v) [])).log := by
  have hlog : (evalBlocks callClosureArgLoopEntrySeg
      (SegEvalState.init (callClosureArgLoopEntryL sp s7v a5v) [])).log
      = [((sp + sign_extend (m := 64) (0x3f8#12)).toNat, 8, s7v)] := by rfl
  rw [hlog]
  refine ⟨?_, trivial⟩
  have hsext : (sign_extend (m := 64) (0x3f8#12) : BitVec 64) = 1016#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext]
  show (callClosureArgSpillRZ sp).lo ≤ (sp + 1016#64).toNat ∧
    (sp + 1016#64).toNat + 8 ≤ (callClosureArgSpillRZ sp).hi
  have hlo : (callClosureArgSpillRZ sp).lo = (sp + 1016#64).toNat := rfl
  have hhi : (callClosureArgSpillRZ sp).hi = (sp + 1016#64).toNat + 8 := rfl
  omega

/-- **The `value_null` staging seg writes nothing** (`addi a0,sp,144` only) —
its seam is memory-pure, so no red zone is needed at all. -/
theorem callClosureValueNull_log_nil (sp : BitVec 64) :
    (evalBlocks callClosureValueNullCallSeg
      (SegEvalState.init (callClosureValueNullCallL sp) [])).log = [] := rfl

/-- **The red-zone metatheorem FIRING on the `env_new` staging seam** — the
one-shot seam frame for the crux's `env_new` call site: given the seg run's
memory/ABI facts (`callClosureEnvNewCallBridge`'s conclusion) and the two
once-per-object stability facts, the WHOLE seam frame (ABI + mem-out + `AInv`
survival + `Env_newLoaded` survival — `env_new_pre`'s two hardest side
conditions) is one application.  No per-splice `hAInvStable*`/`hjalmem`
threading. -/
theorem callClosureEnvNewSeamFrame
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (CodeP : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (σ σ2 : MState)
    (a3 sp a5 : BitVec 64)
    (hmem0 : σ.mem = m0)
    (hmem2 : σ2.mem = writeLog m0
      (evalBlocks callClosureEnvNewCallSeg
        (SegEvalState.init (callClosureEnvNewCallL a3 sp a5) [])).log)
    (habi : ∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R)
    (hAInvStable : AInvStableOn AInv exts (callClosureEnvNewSpillRZ sp).foot)
    (hAInv : AInv σ exts)
    (hCodeStable : MemPredStableOn CodeP (callClosureEnvNewSpillRZ sp).foot)
    (hCode : CodeP m0) :
    RZSeamFrame (callClosureEnvNewSpillRZ sp) AInv exts CodeP m0 σ σ2 :=
  rzSeamFrame_of_run (callClosureEnvNewSpillRZ sp) AInv exts CodeP m0
    (evalBlocks callClosureEnvNewCallSeg
      (SegEvalState.init (callClosureEnvNewCallL a3 sp a5) [])).log σ σ2
    (callClosureEnvNewSpill_logInRZ a3 sp a5) hmem0 hmem2 habi
    hAInvStable hAInv hCodeStable hCode

#print axioms callClosureEnvNewSpill_logInRZ
#print axioms callClosureArgSpill_logInRZ
#print axioms callClosureValueNull_log_nil
#print axioms callClosureEnvNewSeamFrame
#print axioms callParamFoldSeam_of

end Vsa.Sim
