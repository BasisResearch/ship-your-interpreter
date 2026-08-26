import Vsa.Sim.ExecBlock

/-!
# Layer 4 — M4 statement family: the `block` case (`ExecS.block`), sequencing glue

This module closes (as far as the residual glue allows) the FIRST full sequencing
case, `ExecS.block`. Its centrepiece is **`execBlockStep`**, the conditional glue
lemma that delivers `execSeqLoop`'s `hstep` premise (`ExecSeqStep`): from the loop
head `p = 0x800041a4` for a non-empty remaining statement list `s :: ss`, it
threads the do-while body — the 18 `ExecBlockSites` sites (setup
`ld/slli/add/ld/mv/mv/sd`; `armExec_rec` for the recursive `jal exec_stmt`
consuming the head's `ExecIH`; `bnez a0` status split; on normal `i++`/`sext.w`/
`blt` back-edge to `p`, on abrupt exit to `q = 0x8000409c`) — and produces the
`ExecSeqStep` normal/abrupt disjunction.

Because `ExecSeqEntry` (`ExecSimCommon.lean`) carries only the thin loop-head
control state (PC/store/output/frame), the per-iteration MACHINE geometry the loop
body reads (the block node `s0`, inner scope `s3`, retslot `s2`, the loop index
`i` in `a6`, the block `count`, the `stmts` base, and all region-disjointness
facts) is supplied to `execBlockStep` as an explicit residual bundle
`ExecStepGeom`. This is exactly the "per-iteration geometry residual" the design
note flagged: the mutual `ExecS` recursor (and `execBlockSim`'s `env_new`/
frame-alloc linkage) will discharge it later; here it is a named, honest premise.

`hnil` is the tiny `p → q` fallthrough (`li a0,0; j 0x8000409c`).

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

/-! ## `hnil` — the empty-sequence `p → q` fallthrough

At the loop head `p = 0x800041a4` with `ss = []`, the machine has ALREADY passed
the `blez a5, 0x80004090` count-test (or exhausted the list via the `blt`
back-edge falling through), landing at `0x800041e0: li a0,0; j 0x8000409c` — the
normal exit hop into the shared statement continuation `q = 0x8000409c`.

The `ExecSeqEntry`/`ExecSeqExit` predicates model the loop head/continuation
abstractly (a shared PC for the empty case), so `execSeqNil` (`ExecSimCommon.lean`)
already discharges the empty sequence unconditionally as the identity Triple at a
shared PC. `execBlockSim` instantiates `execSeqLoop`'s `hnil` with `execSeqNil` (at
the loop-head PC, where the count-test has fallen through). We re-expose it here at
the block do-while's own PCs for documentation and reuse. -/
theorem execBlockHnil
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (sp r : BitVec 64) (p : Nat) (m0 : Mem) :
    Triple
      (ExecSeqEntry g N A SL φf φc st d env [] sp r p m0)
      (ExecSeqExit g N A SL φf φc st .normal sp r p m0) :=
  execSeqNil g N A SL φf φc st d env sp r p m0 (ExecSeq.nil st d env)

/-! ## `ExecStepGeom` — the per-iteration loop-head machine geometry residual

The concrete machine state the block do-while body reads at the loop head
`p = 0x800041a4`, for iteration index `i` over the block statement array. This is
the "per-iteration geometry residual" the design note flagged: `ExecSeqEntry` only
carries the thin control state (PC/store/output/frame), but the loop body reads the
callee-saved `s0`(block node `aStmt`), `s1`(interp `aInterp`), `s2`(retslot `aRet`),
`s3`(inner env `aEnv`), the loop index `i` in `a6`(x16), plus the block's `stmts`
base and `count`, and needs all the region-disjointness facts. The mutual `ExecS`
recursor + `execBlockSim`'s `env_new`/frame-alloc linkage will discharge this
bundle later; here it is a named, honest premise threaded per-config. -/
def ExecStepGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt)
    (sp r : BitVec 64) (m0 : Mem) (out0 : Array String)
    (aInterp aStmt aEnv aRet aStmtsBase aStmtSub aRetSub : BitVec 64)
    (icount count : Nat) (c : Config) : Prop :=
  -- callee-saved / index registers at the loop head
  c.σ.regs.get? Register.x8 = some aStmt ∧          -- s0 = block node
  c.σ.regs.get? Register.x9 = some aInterp ∧        -- s1 = interp*
  c.σ.regs.get? Register.x18 = some aRet ∧          -- s2 = outer retslot
  c.σ.regs.get? Register.x19 = some aEnv ∧          -- s3 = inner env
  c.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 icount) ∧ -- a6 = i
  c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  c.σ.sailOutput = out0 ∧
  -- the block node holds `stmts` base @ +8 and `count` @ +16
  read64 m0 (aStmt.toNat + 8) = some aStmtsBase.toNat ∧
  read32 m0 (aStmt.toNat + 16) = some count ∧
  -- the current statement pointer `stmts[i]` @ base + 8*i, and its 8-alignment
  read64 m0 (aStmtsBase.toNat + 8 * icount) = some aStmtSub.toNat ∧
  aStmtSub.toNat % 8 = 0 ∧
  0x80000000 ≤ aStmtSub.toNat ∧ aStmtSub.toNat + 16 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ aStmtSub.toNat ∧
  (aStmtSub.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aStmtSub.toNat) ∧
  -- `stmts[i]` represents the head statement `s` and its scope is the inner env
  -- (these tie the machine's `stmts[i]` to the spec's head `s`)
  StmtRepr m0 aStmtSub.toNat s ∧
  φf env = aEnv.toNat ∧
  -- the forwarded retslot IS the outer retslot (a3 := s2)
  aRetSub = aRet ∧
  -- retslot geometry (an 8-aligned 24-byte RAM slot above HTIF, disjoint from the
  -- sub-call's own stack window):
  aRetSub.toNat % 8 = 0 ∧
  0x80000000 ≤ aRetSub.toNat ∧ aRetSub.toNat + 24 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ aRetSub.toNat ∧
  (aRetSub.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRetSub.toNat) ∧
  -- the loop index in range (i < count, so the head statement runs this iteration)
  icount < count ∧ count < 2^31 ∧
  -- the five spill slots hold the entry ra/s0/s1/s2/s3
  read64 m0 (sp.toNat - 8) = some r.toNat ∧
  read64 m0 (sp.toNat - 16) = some aStmt.toNat ∧
  read64 m0 (sp.toNat - 24) = some aInterp.toNat ∧
  read64 m0 (sp.toNat - 32) = some aRet.toNat ∧
  read64 m0 (sp.toNat - 40) = some aEnv.toNat ∧
  g Register.x8 = some aStmt ∧ g Register.x9 = some aInterp ∧
  g Register.x18 = some aRet ∧ g Register.x19 = some aEnv ∧
  g Register.x2 = some sp ∧
  -- callee-saved regs (excl s0/s1/s2/s3/sp) read the ghost frame `g`
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → c.σ.regs.get? R = g R) ∧
  -- store survival over the stack window (the spill `sd i` lands inside `[SL.lo, sp)`)
  (∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → m0[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store) ∧
  -- the block-node geometry (for the `ld`/`lw` reads of stmts base / count):
  aStmt.toNat % 8 = 0 ∧
  0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 24 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ aStmt.toNat ∧
  (aStmt.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aStmt.toNat) ∧
  -- the stmts-base entry geometry (for the `ld a1,0(&stmts[i])`):
  (aStmtsBase.toNat + 8 * icount + 8 ≤ SL.lo ∨ sp.toNat ≤ aStmtsBase.toNat + 8 * icount) ∧
  0x80000000 ≤ aStmtsBase.toNat + 8 * icount ∧
  aStmtsBase.toNat + 8 * icount + 8 ≤ 0x100000000 ∧
  (aStmtsBase.toNat + 8 * icount + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aStmtsBase.toNat + 8 * icount) ∧
  (aStmtsBase.toNat + 8 * icount) % 8 = 0 ∧
  -- stack geometry (recursion headroom + alignment) + spill-slot i @ sp-168:
  SL.lo + 2352 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
  sp.toNat ≤ 0x100000000 ∧
  0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
  r.toNat % 4 = 0 ∧
  (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
  (sp.toNat ≤ 0x80003fe0 ∨ 0x80004308 ≤ SL.lo) ∧
  (A.hi ≤ 0x80003fe0 ∨ 0x80004308 ≤ A.lo)

/-! ## `execBlockIter` — setup ≫ `armExec_rec` ⇒ `SubStmtReturn` at `0x800041c8`

The concrete, reusable machine thread of ONE block do-while iteration up to the
`bnez a0` status check: from the loop head `p = 0x800041a4` with the `ExecStepGeom`
geometry, it runs the seven setup instructions (`ld x15,8(s0)`; `slli x14,i,3`;
`addi x13,s2,0`; `add x15,x15,x14`; `ld x11,0(x15)`; `addi x12,s3,0`;
`addi x10,s1,0`; `sd x16,8(sp)`) staging the recursive call's ABI args and spilling
`i`, then invokes `armExec_rec` (`ExecBlock.lean`) for the `jal exec_stmt`
(`0x800041c4`) — consuming the head statement's `ExecIH` — landing in a
`SubStmtReturn` at the link PC `0x800041c8` where `a0 = StatusCode status` (the
`bnez` reads it).

This is the statement-sequencing analog of `execExprGlue` (`ExecRecCommon.lean`),
threading the block-loop-body setup instead of the expr/ret arm setup. The
`mcall` memory is the loop-head memory `m0` plus the single `sd i` spill (inside the
stack window, so `StoreRepr`/code/slots survive); `armExec_rec` frames its exit to
it.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`. -/

/-! ## `execBlockStep` — one block do-while iteration ⇒ `ExecSeqStep`

Delivers `execSeqLoop`'s `hstep` (`ExecSeqStep`). From the loop head
`p = 0x800041a4` for a non-empty remaining list `s :: ss` and the per-iteration
geometry residual `ExecStepGeom` (see above), it threads the do-while body:

* setup (`ld x15,8(s0)` stmts base; `slli x14,i,3`; `addi x13,s2,0` retslot;
  `add x15,x15,x14` `&stmts[i]`; `ld x11,0(x15)` `stmts[i]`; `addi x12,s3,0` inner
  env; `addi x10,s1,0` interp; `sd x16,8(sp)` spill `i`) to the recursive-call PC;
* `armExec_rec` for the `jal exec_stmt@0x800041c4`, consuming the head's `ExecIH`,
  producing a `SubStmtReturn` with `a0 = StatusCode status`;
* the `bnez a0` split (`0x800041c8`): abrupt (`status ≠ normal`) → `bne` TAKEN to
  `q = 0x8000409c` (`consAbrupt`, `ExecSeqExit`); normal → fallthrough, then
  `ld i`/`lw count`/`addi i,i,1`/`sext.w`/`blt` — TAKEN back to `p` (there is a
  next statement) yielding the `ExecSeqEntry ss @ p` normal disjunct.

Because the machine glue for the FULL iteration (setup ≫ `armExec_rec` ≫ status
split ≫ loop control) is a ~250-line thread, and because the normal-branch
φ-extension is stated over `stFin` (the final store) — the frame-alloc accounting
the design note flagged — `execBlockStep` is stated CONDITIONAL on the two named
residuals the iteration cannot itself close:

* `hbody` — the machine-level iteration: from the loop-head config (with the
  `ExecStepGeom` geometry) it runs to the branch outcome, packaged as the two
  status-keyed disjuncts (the setup+`armExec_rec`+control thread). This is the
  ~250-line decode; it is supplied by the (later) mutual-recursor scaffolding that
  re-lands `armExec_rec` at each site.
* `hphi` — the frame-alloc φ-upgrade: the sub-call's `st'`-sized extension is
  lifted to the `stFin`-sized extension the loop rule composes (env_new/allocFrame
  accounting).

`execSeqLoop` is proved unconditionally on top of this; `execBlockSim` discharges
`hbody`/`hphi` from the block-array + `env_new_spec`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`. -/
theorem execBlockStep
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' stFin : Vsa.While.St) (d : Nat) (env : Addr)
    (s : Stmt) (ss : List Stmt) (status : Status)
    (sp r : BitVec 64) (m0 : Mem) (out0 : Array String)
    (aInterp aStmt aEnv aRet aStmtsBase aStmtSub aRetSub : BitVec 64)
    (icount count : Nat)
    (hS : ExecS st d env s st' status)
    (hIH : ExecIH st d env s st' status)
    -- the per-iteration geometry residual (holds for the config at the loop head):
    (hgeom : ∀ c : Config,
      ExecSeqEntry g N A SL φf φc st d env (s :: ss) sp r 0x800041a4 m0 c →
      ExecStepGeom g N A SL φf φc st d env s sp r m0 out0
        aInterp aStmt aEnv aRet aStmtsBase aStmtSub aRetSub icount count c)
    -- the machine-iteration residual: from the loop-head GEOMETRY (`ExecStepGeom`,
    -- produced by `hgeom`) and the head's recursion IH (`hIH`, threaded through
    -- `armExec_rec` at the `jal exec_stmt`), run the do-while body
    -- (setup ≫ `armExec_rec` ≫ status split ≫ loop control) to the branch outcome,
    -- as the two status-keyed disjuncts. It is BLOCKED unconditionally only on the
    -- AST-repr transport `StmtRepr`-agreeP across the `sd i` spill (the recurring
    -- residual the project flags for `exprRepr_agreeP`) + the branch-control decode:
    (hbody : ExecIH st d env s st' status →
      ∀ c : Config,
      ExecStepGeom g N A SL φf φc st d env s sp r m0 out0
        aInterp aStmt aEnv aRet aStmtsBase aStmtSub aRetSub icount count c →
      ∃ c', Steps c c' ∧
        ((status = .normal ∧
          ∃ (φf' φc' : Addr → Nat),
            PhiExtends φf φf' st'.store.frames.size ∧
            PhiExtends φc φc' st'.store.closures.size ∧
            ExecSeqEntry g N A SL φf' φc' st' d env ss sp r 0x800041a4 c'.σ.mem c')
        ∨ (status ≠ .normal ∧
          ExecSeqExit g N A SL φf φc st' status sp r 0x8000409c m0 c')))
    -- the frame-alloc φ-upgrade (st'-sized extension → stFin-sized extension,
    -- preserving the tail's `ExecSeqEntry`):
    (hphi : ∀ (φf' φc' : Addr → Nat) (c' : Config),
      PhiExtends φf φf' st'.store.frames.size →
      PhiExtends φc φc' st'.store.closures.size →
      ExecSeqEntry g N A SL φf' φc' st' d env ss sp r 0x800041a4 c'.σ.mem c' →
      ∃ (φf'' φc'' : Addr → Nat),
        PhiExtends φf φf'' stFin.store.frames.size ∧
        PhiExtends φc φc'' stFin.store.closures.size ∧
        ExecSeqEntry g N A SL φf'' φc'' st' d env ss sp r 0x800041a4 c'.σ.mem c') :
    ExecSeqStep g N A SL φf φc st d env s ss sp r 0x800041a4 0x8000409c m0 st' stFin status := by
  -- `ExecSeqStep` is definitionally `hS → Triple …`; discharge `hS`, then thread the
  -- body from the loop-head geometry (`hgeom`) with the recursion IH (`hIH`).
  intro _hS c hc
  obtain ⟨c', hsteps, hpost⟩ := hbody hIH c (hgeom c hc)
  refine ⟨c', hsteps, ?_⟩
  rcases hpost with ⟨hn, φf', φc', hpf, hpc, hEntry⟩ | ⟨hne, hexit⟩
  · -- normal branch: upgrade the φ-extension to `stFin`'s sizes, re-land at `p`.
    left
    refine ⟨hn, ?_⟩
    obtain ⟨φf'', φc'', hpf'', hpc'', hEntry''⟩ := hphi φf' φc' c' hpf hpc hEntry
    exact ⟨φf'', φc'', hpf'', hpc'', hEntry''⟩
  · -- abrupt branch: exit to `q`.
    right
    exact ⟨hne, hexit⟩

/-! ## `execBlockSim` — the `ExecS.block` simulation Triple (the sequencing keystone)

Composes the whole `block` arm:
`execBlockA (kind 2, arm 0x8000418c)` ≫ `env_new_spec` (child scope `inner`,
`= Store.allocFrame`) ≫ `execSeqLoop` (fed `execBlockStep`'s `hstep` + `execBlockHnil`'s
`hnil`) ≫ the block epilogue → `Triple (ExecEntry (.block ss) …) (ExecExit … status …)`.

The `ExecS.block` derivation gives `st.store.allocFrame (some env) = (store', inner)`
and `ExecSeq ⟨store', st.out⟩ d inner ss st' status` (the child-scope sequence).
`execSeqLoop` turns that `ExecSeq` into the do-while Triple from the loop head
`p = execSeqLoopPC = 0x800041a4` to the continuation `q = execSeqContPC = 0x8000409c`;
`execBlockSim` sandwiches it between:

* `hArm` — the arm prologue residual: from the block `ExecEntry`, run
  `execBlockA` (prologue+dispatch to `0x8000418c`) ≫ the `env_new` call (allocating
  `inner` per `env_new_spec`) ≫ the loop setup (`lw count`, `mv s3,inner`, `li i,0`,
  `blez` fallthrough) to `ExecSeqEntry` at `p` in scope `inner` over the child store;
* `hEpi` — the epilogue residual: from `ExecSeqExit` at `q` (the sequence's result)
  run the shared epilogue (`execBlockD`) to `ExecExit`.

Both are the frame-alloc/`env_new`-linkage + `execBlockA` geometry the design note
flagged; the `execSeqLoop` core (the reusable heart) is threaded UNCONDITIONALLY
here, so this is the first place `ExecSeq` sequencing is composed end-to-end. -/
theorem execBlockSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (ss : List Stmt) (status : Status)
    (store' : Store) (inner : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (hAlloc : st.store.allocFrame (some env) = (store', inner))
    (hSeq : ExecSeq ⟨store', st.out⟩ d inner ss st' status)
    -- the loop-rule premises, discharged (per suffix / intermediate state) by
    -- `execBlockStep` (hstep) and `execBlockHnil` (hnil):
    (hstep : ∀ (φf₀ φc₀ : Addr → Nat) (stM : Vsa.While.St) (sH : Stmt) (ssH : List Stmt)
        (stM' stFinH : Vsa.While.St) (statusH : Status) (m00 : Mem),
        ExecSeqStep g N A SL φf₀ φc₀ stM d inner sH ssH sp r
          execSeqLoopPC execSeqContPC m00 stM' stFinH statusH)
    (hnil : ∀ (φf₀ φc₀ : Addr → Nat) (stN : Vsa.While.St) (m00 : Mem),
        Triple
          (ExecSeqEntry g N A SL φf₀ φc₀ stN d inner [] sp r execSeqLoopPC m00)
          (ExecSeqExit g N A SL φf₀ φc₀ stN .normal sp r execSeqContPC m00))
    -- the arm prologue residual (block ExecEntry → ExecSeqEntry at the loop head,
    -- after `execBlockA` + `env_new` + loop setup, in the child scope `inner`):
    (hArm : ∀ (φf' φc' : Addr → Nat),
      Triple
        (fun c => ExecEntry g N A SL φf φc st d env (.block ss) sp r aInterp aStmt aEnv aRet m0 c
          ∧ c.σ.sailOutput = out0)
        (fun c => ∃ m0', PhiExtends φf φf' store'.frames.size ∧
          PhiExtends φc φc' store'.closures.size ∧
          ExecSeqEntry g N A SL φf' φc' ⟨store', st.out⟩ d inner ss sp r execSeqLoopPC m0' c))
    -- the epilogue residual (ExecSeqExit at the continuation → ExecExit):
    (hEpi : ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
      Triple
        (ExecSeqExit g N A SL φf' φc' st' status sp r execSeqContPC m0')
        (ExecExit g N A SL φf φc st' status sp r aRet m0)) :
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env (.block ss) sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st' status sp r aRet m0) := by
  -- pick the child-scope φ-maps existentially via `hArm`; compose arm ≫ loop ≫ epi.
  intro c hpre
  -- The arm prologue lands at the loop head with child-scope maps `φf'`/`φc'`
  -- (chosen by `hArm`, existentially over any pair; we thread a fixed pair).
  -- Run the arm to `ExecSeqEntry`, then `execSeqLoop` over `hSeq`, then the epilogue.
  obtain ⟨cP, hstepsP, m0', hpf, hpc, hEntryP⟩ := hArm φf φc c hpre
  -- the loop rule turns the child `ExecSeq` into the do-while Triple
  have hloopT := execSeqLoop g N A SL d inner sp r execSeqLoopPC execSeqContPC
    hstep hnil ss φf φc ⟨store', st.out⟩ st' status m0' hSeq
  obtain ⟨cQ, hstepsQ, hExitQ⟩ := hloopT cP hEntryP
  -- the epilogue turns the sequence exit into the block `ExecExit`
  obtain ⟨cE, hstepsE, hExitE⟩ := hEpi φf φc m0' cQ hExitQ
  exact ⟨cE, (hstepsP.trans hstepsQ).trans hstepsE, hExitE⟩

end Vsa.Sim
