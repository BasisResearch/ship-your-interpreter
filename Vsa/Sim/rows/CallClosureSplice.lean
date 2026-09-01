import Vsa.Sim.rows.CallClosureRow
import Vsa.Sim.SpliceFold
import Vsa.Sim.CallFrameMeta
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.rows.CallClosureEnvNewCallGen
import Vsa.Sim.rows.CallClosureEnvDefineCallGen
import Vsa.Sim.rows.CallClosureValueNullCallGen
import Vsa.Sim.rows.CallClosureRetCopyGen
import Vsa.Sim.rows.CallClosureArgLoopEntryGen

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

/-! ## §2. The per-param seam factored (staging ≫ `env_define` ≫ back-edge)

One fold seam = the loop-body staging (`0x800032dc..0x80003308` 24-byte value
copy to `sp+64` + cursor bump, then the GEN `callClosureEnvDefineCallBridge`
jal seam) ≫ the `env_define` contract (`EnvDefCompose.envDefContract`, the
append≫grow≫dispatch join over the real Malloc/Realloc contracts) ≫ the return
+ back-edge (`0x80003314..0x8000331c`, `bne s6,a5` taken for `k+1 < n` — and
for `k+1 = n` the not-taken exit is the `hFoldToHandoff` bridge's entry, which
is why the carrier is stated at the HEAD PC only). -/

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
    (frame : Addr) (d dLeft aLeft : Nat) (m0 : Mem)
    -- env_new call data (the contract's ghosts at this call site)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (gE : (R : Register) → Option (RegisterType R))
    (par sp s0E : BitVec 64) (extsE : List (Nat × Nat)) (mEnvNew : Mem)
    -- fold carrier data
    (fp clp : BitVec 64)
    (_hbody : cd.body ≠ [])
    (hER : ∀ p : Nat, EnvRegions SL M.privFoot sp.toNat p)
    (hDispatchStage : Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (env_new_pre A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE φf (some cd.env) mEnvNew))
    (hEnvNewToFold : 0 < (cd.params.zip vs).length → Triple
      (env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE N φf φc (some cd.env) mEnvNew)
      (fun c => ∃ φf' : Addr → Nat,
        PhiExtends φf φf' st.store.frames.size ∧
        callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 0 c))
    (hFoldSeam : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size →
      ∀ k, k < (cd.params.zip vs).length → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 (k + 1)))
    (hFoldToHandoff : ∀ (φf' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size → Triple
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
          (cd.params.zip vs).length)
        (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0))
    (hNoParams : (cd.params.zip vs).length = 0 → Triple
      (env_new_post A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
        extsE N φf φc (some cd.env) mEnvNew)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0)) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0) := by
  -- one SpliceChain: staging hop ≫ the REAL env_new contract ≫ the tail.
  refine spliceFold (.step hDispatchStage
    (env_new_spec A SL gpv headroom maxReq M gE par (0x800032c0#64) sp s0E
      extsE N φf φc (some cd.env) mEnvNew hER)
    (.tail ?_))
  -- the tail: env_new_post → BodyHandoff, split on the zero-param bypass.
  rcases Nat.eq_zero_or_pos (cd.params.zip vs).length with h0 | hpos
  · exact hNoParams h0
  · -- fold route: bind φf', run the storeChainList fold, hand off.
    intro c hc
    obtain ⟨c1, hs1, φf', hpe, hcar0⟩ := hEnvNewToFold hpos c hc
    obtain ⟨c2, hs2, hcarN⟩ :=
      storeChainList
        (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0)
        (cd.params.zip vs).length
        (fun k hk => hFoldSeam φf' hpe k hk) c1 hcar0
    obtain ⟨c3, hs3, hHand⟩ := hFoldToHandoff φf' hpe c2 hcarN
    exact ⟨c3, Steps.trans hs1 (Steps.trans hs2 hs3), hHand⟩

#print axioms callClosureEntrySplice

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
    (frame : Addr) (m0 : Mem) : Prop :=
  ∀ (g' : (R : Register) → Option (RegisterType R)) (φf' : Addr → Nat) (mB : Mem),
    PhiExtends φf φf' st.store.frames.size →
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mB[a]? = m0[a]?) →
    BodyGhostTie g g' →
    (∀ spv : BitVec 64, g Register.x2 = some spv →
      CallerSpillSlots g spv mB m0) →
    Triple
      (SegExit g' N A SL φf' φc
        (closureBoundSt st store' cd vs frame).store.frames.size
        (closureBoundSt st store' cd vs frame).store.closures.size
        st' callBodyRetPC mB)
      (SegExit g N A SL φf φc
        st.store.frames.size st.store.closures.size st' callJoinPC m0)

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
    {frame : Addr} {m0 : Mem} {status : Status} {v : Value}
    (hStatus : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v)
    (hNormal : status = Status.normal →
      CallRetShape g N A SL φf φc st st' store' cd vs frame m0)
    (hRetV : status = Status.ret v →
      CallRetShape g N A SL φf φc st st' store' cd vs frame m0) :
    CallRetShape g N A SL φf φc st st' store' cd vs frame m0 := by
  rcases hStatus with ⟨h, _⟩ | h
  · exact hNormal h
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
    {dLeft aLeft : Nat} {m0 : Mem}
    (hEntry : cd.body ≠ [] → Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0))
    (hRet : cd.body ≠ [] →
      CallRetShape g N A SL φf φc st st' store' cd vs frame m0)
    (hEmpty : cd.body = [] →
      st' = closureBoundSt st store' cd vs frame →
      Triple
        (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
        (SegExit g N A SL φf φc
          st.store.frames.size st.store.closures.size st' callJoinPC m0)) :
    CallClosureGeom g N A SL φf φc st st' d a cd vs store' frame status v
      dLeft aLeft m0 :=
  { entryBase := hEntry, ret := hRet, emptyBypass := hEmpty }

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
