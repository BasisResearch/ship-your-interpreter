import Vsa.Sim.rows.LoopHeadDispatchSeg
import Vsa.Sim.rows.LoopHeadArgSetupSeg
import Vsa.Sim.ExecEntry
import Vsa.Sim.InductionScaffold
import Vsa.Sim.ValueSpec

/-!
# `LoopHeadDispatch` — the interp_run loop-head → `exec_stmt` entry span (Task #69)

`Vsa/Sim/InterpRunLoopSeamsClose.lean` names the `iter` residual and pins the
MISSING bridge precisely (its header, `§ iter is NOT a forgetful shadow`):

> The bridge `SegEntry@loopHead → ExecEntry@0x80003fe0` is exactly the loop-head
> dispatch prefix — unbuilt machine content — and the abstract `Reflect cH env
> (s :: ss)` carries no facts to supply it.

This file BUILDS that span (the machine `Steps` run from the loop head to
`exec_stmt`'s entry) and marshals its landing into `ExecEntry`.  It serves THREE
consumers unchanged: `iterSeam`/`approxSeam` (`InterpRunLoopSeamsClose`) and the
`hterm` back-edge assembly.  We build ONLY the span; the consumers supply their own
`ExecExit`-side content.

## The decoded span (all body words decode-tabled, verified vs `experiments/disasm.txt`)

```
── DISPATCH HEAD  [0x8000448c, 0x80004494)  ── br-terminated (TAKEN, flag=0) ──────
  0x8000448c  ld   a5,8(sp)     x15 := *(sp+8)   — the REPL-echo flag
  0x80004490  ld   s1,0(s0)     x9  := *s0       — current Stmt* at the loop cursor
  0x80004494  beqz a5,0x80004458                 — TAKEN when flag=0 (non-REPL exec)
  (`loopHeadDispatchRow`, br seg → 0x80004458.  LOOP-EXIT edge is elsewhere:
   0x80004498 `lw a5,0(s1)` ; 0x8000449c `bnez a5,0x80004458` — the REPL echo path;
   and the array-end edge is the `beq s0,s2,0x80004514` at 0x80004488 BEFORE the
   head.  NEITHER exit edge is this task.)
── VALUE_NULL CALL  [0x80004458, 0x80004460)  ── a CALL (retslot init) ────────────
  0x80004458  addi a0,sp,88     a0 := &retslot @sp+88
  0x8000445c  jal  value_null   (link 0x80004460) — zero-init the retslot buffer
  (a call splice → NAMED premise `hValueNullSplice`, exactly like
   `DriveToLoopHeadSpans.SetjmpSplice`; value_null's `null_pre` buffer geometry
   is off the loop-head SegEntry.)
── ARG SETUP  [0x80004460, 0x80004474)  ── jal-terminated (CALL) ──────────────────
  0x80004460  ld   a5,0(sp)     a5 := *sp        — interp* pointer
  0x80004464  addi a3,sp,88     a3 := &retslot   — exec_stmt arg 3
  0x80004468  mv   a1,s1        a1 := s1         — the Stmt* node (arg 1)
  0x8000446c  ld   a2,0(a5)     a2 := *interp    — the scope/env addr (arg 2)
  0x80004470  mv   a0,a5        a0 := interp*    — arg 0
  0x80004474  jal  exec_stmt    (0x80003fe0, link 0x80004478)
  (`loopHeadArgSetupBridge`, bridgeOfSeg body ≫ jal exec_stmt.)
── EXEC_STMT ENTRY  @0x80003fe0  = ExecEntry entry PC ─────────────────────────────
```

The back-edge continuation PC (the `exec_stmt` return link) is `0x80004478`; that is
the address the `iter`/`hterm` back-edge suffix resumes at (`beq a0,s3,…` etc.).

## What SegEntry@loopHead CAN vs CANNOT supply — the geometry split

`SegEntry` (`Vsa/Sim/InductionScaffold.lean:150`) pins at the loop head: `good`,
`tick`, `pc`, `store` (`StoreRepr`), `out` (`OutRepr`), `mem = m0`, the blanket
ghost `frame`, and the depth/arena budgets.  `ExecEntry` (`Vsa/Sim/ExecEntry.lean:207`)
demands ALL of those AT the callee entry PLUS a rich ABI/AST/stack geometry that the
loop head has NO way to assert:

* the four ABI arg VALUES (`a0`=interp*, `a1`=Stmt*, `a2`=env, `a3`=retslot) — these
  are COMPUTED by the span (the seg write-log), so they come from the span landing,
  NOT a premise;
* the C-stack layout (`StackOK SL sp (176+1088)`, `stack_ram`, `stack_win`,
  `code_stack_disjoint`) — a `main`-prologue fact, off the loop head;
* the `Stmt` node geometry (`StmtRepr`, `stmt_stack_disjoint`, `stmt_align`,
  `stmt_ram`, `stmt_win`) — a fact of WHICH statement the cursor points at, exactly
  the content `Reflect cH env (s :: ss)` would carry if it were computational (it is
  NOT — a bare section variable);
* `code` (`Exec_stmtLoaded`), `ra_align`, `store_survives`, `spill_defined`.

These become the named-field `structure LoopHeadDispatchGeom` below, one field per
missing fact, each with a doc-commented supplier.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Status Stmt Addr)
open Vsa.Sim.Code (Exec_stmtLoaded)

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) The NEW predicates here ARE named-field
-- structures (LoopHeadDispatchGeom).  The `∃`s the counter sees are: (1) the two
-- LANDING bundles `ValueNullSplice`/`loopHeadDispatchLanded` + the `hArgSetup`
-- premise — Prop-valued `∃ Config, Steps ∧ …` that MUST be existentials (they carry
-- a reached `Config` as DATA and are BUILT from `Triple`/`setjmp_spec`-style
-- `Exists`; a `structure … : Prop` cannot project the data `Config`), the exact
-- sanctioned shape of `DriveToLoopHeadSpans.SetjmpSplice`/`SpillLanded`/`SegLanded`
-- in the SAME region; (2) `∃ w, … minstret` witnesses and `∃ v, … xN` spill
-- witnesses — inherent to the `SegEntry`/`ExecEntry` FIELD types this bridge
-- consumes, not new post towers.  Each landing bundle is destructured ONCE at its
-- consumer's binder via a flat `obtain` (no `.2.2.2` towers).

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-! ## §1. The value_null call splice (a CALL — a named residual)

`value_null` at `0x8000445c` (link `0x80004460`) zeros the retslot buffer at
`sp+88`.  Its `null_pre` (`Vsa/Sim/ValueSpec.lean:386`) demands the buffer be a
`NullRegion` and `value_null` be loaded — the setjmp-buffer-style geometry NOT on
the loop-head path.  So — exactly as `DriveToLoopHeadSpans.SetjmpSplice` names the
`jal setjmp` first-return — the value_null call is a NAMED `Steps` splice.

Its supplier: `callSeg` (`DeriveCallSeg`) over `value_null_spec` (already proved,
`Vsa/Sim/ValueSpec.lean:412`) applied at the call site, with the `addi a0,sp,88`
prefix and the return landing at `0x80004460`.  We phrase it as the `Steps` from the
config parked at `0x80004458` (the value_null prefix head) to the config parked at
`0x80004460` (the arg-setup head), preserving the loop-head memory outside the
retslot window (`sp+88`) and the ghost register frame. -/

/-- **The value_null call splice.**  From the config `c458` the dispatch head lands
(parked at `0x80004458`, `GoodState`, tick-bounded, memory `m458`, a `minstret`
witness, and the loop-head register frame it needs), running `addi a0,sp,88 ; jal
value_null` (and value_null's body) returns to `0x80004460` with the retslot buffer
at `sp+88` zero-initialised, memory `m460`, control good, and the ABI callee-saved
frame preserved back to `c458` (value_null preserves callee-saveds; `a5`/`a0`/… are
overwritten by the following arg-setup seg so are not tracked here).  A Prop-valued
existential over the reached config (carries DATA — the `Config` — so it MUST be a
`def … : Prop := ∃ …`, per the WidenMeta/landing-bundle gotcha). -/
def ValueNullSplice (c458 : Config) : Prop :=
  ∃ (c460 : Config),
    Steps c458 c460 ∧
    c460.σ.regs.get? Register.PC = some (0x80004460#64 : BitVec 64) ∧
    GoodState c460.σ ∧
    c460.tick < 2 ∧
    (∃ w, c460.σ.regs.get? Register.minstret = some w) ∧
    -- the ABI callee-saved frame survives the call (value_null is a leaf that
    -- restores its spills), so `sp`/`s0`/`s1`/`gp` reach the arg-setup head:
    (∀ R, AbiPreserved R = true → c460.σ.regs.get? R = c458.σ.regs.get? R)

/-- **The dispatch-head landing (a richer post than the generated `*Row`).**  Runs
the br seg via `segToTriple` directly, surfacing the reached-config tick bound
(`i' < 2`) and a `minstret` witness — the two facts the value_null splice consumes
that `LoopHeadDispatchPost` does not expose (identical to why
`DriveToLoopHeadSpans.hLoopA_of_row` goes through `segToTriple`).  Landing: parked at
`0x80004458`, control good, tick-bounded, a `minstret` witness. -/
theorem loopHeadDispatchLanded
    (sp s0 : BitVec 64) (m0 : Mem) (cH : Config)
    (hpre : SegPre loopHeadDispatchSeg (loopHeadDispatchL sp s0) [] 0x8000448c#64 m0 cH) :
    ∃ (c458 : Config),
      Steps cH c458 ∧
      c458.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64) ∧
      GoodState c458.σ ∧ c458.tick < 2 ∧
      (∃ w, c458.σ.regs.get? Register.minstret = some w) := by
  have hT :
      Triple (SegPre loopHeadDispatchSeg (loopHeadDispatchL sp s0) [] 0x8000448c#64 m0)
        (fun c => c.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64) ∧
          GoodState c.σ ∧ c.tick < 2 ∧
          (∃ w, c.σ.regs.get? Register.minstret = some w)) := by
    apply segToTriple loopHeadDispatchSeg (loopHeadDispatchL sp s0) [] 0x8000448c#64 m0 _
      (by have h : keysG (loopHeadDispatchL sp s0) = [2, 8] := rfl
          rw [h]; show ChainOK 0x8000448c#64 [2, 8] loopHeadDispatchSeg; decide)
    intro σ' i' u' hG' hi' _hmem' hpc' hmi' _hregs
    refine ⟨?_, hG', hi', hmi'⟩
    rw [hpc']
    show some (evalBlocksPC 0x8000448c#64 (SegEvalState.init (loopHeadDispatchL sp s0) []) loopHeadDispatchSeg)
      = some 0x80004458#64
    rfl
  obtain ⟨c458, hsteps, hpc, hG, htick, hmi⟩ := hT cH hpre
  exact ⟨c458, hsteps, hpc, hG, htick, hmi⟩

#print axioms loopHeadDispatchLanded

/-! ## §2. The `ExecEntry` geometry SegEntry@loopHead cannot supply

Named-field `structure` (the gate shape for a NEW entry-side predicate), one field
per `ExecEntry` fact that is NOT a consequence of `SegEntry g … interpLoopHeadPC …
cH`.  Each field's doc names its supplier.  The ABI arg VALUES are NOT here — they
are computed by the span (the seg write-log) and read off the landing.

`sp` is the C-stack pointer at the loop head (= the loop-head SegEntry's `x2`, spilled
by the interp_run prologue); `aStmt` is the `Stmt*` node the cursor `s0` points at
(the value the dispatch head loads into `s1`); `s` is the head statement (the `Reflect`
node).  Everything is stated at the `exec_stmt`-ENTRY memory `mE` (the loop-head `m0`
after value_null + the arg-setup seg have scribbled the stack/retslot window) — that
is the `ExecEntry.mem` witness the callee sees. -/
structure LoopHeadDispatchGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (sp aStmt : BitVec 64) (s : Stmt)
    (mE : Mem) : Prop where
  /-- **supplier: the interp_run prologue's `main`-established stack.**  `sp` is a
  good C stack pointer with `exec_stmt`'s frame + callee headroom.  Off the loop
  head (`SegEntry` has NO `SL`); the `DriveToLoopHeadSpans` spill-span reseated
  `sp = sp₀-176` but does not surface `StackOK` — a `main`-prologue fact. -/
  stackOK : StackOK SL sp (176 + 1088)
  /-- **supplier: `main`-prologue stack RAM bounds.** -/
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  /-- **supplier: the AST/code layout.**  `exec_stmt`'s code region is disjoint from
  the C-stack scribble `[SL.lo, sp)` — a load-time layout fact. -/
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  /-- **supplier: `Exec_stmtLoaded` at load time**, preserved by value_null + the
  arg-setup seg (both write only the stack/retslot window, disjoint from code) —
  stated at `mE`. -/
  code : Exec_stmtLoaded mE
  /-- **supplier: the loop-head cursor reflection** (the computational content
  `Reflect cH env (s :: ss)` would carry).  The `Stmt` node at `aStmt` represents the
  head statement `s` (in `mE`; the node lives in the AST, untouched by the stack
  scribble). -/
  stmt : StmtRepr mE aStmt.toNat s
  /-- **supplier: the AST-region layout** — the `Stmt` node is disjoint from the
  C-stack scribble `[SL.lo, sp)`. -/
  stmt_stack_disjoint : aStmt.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aStmt.toNat
  /-- **supplier: AST allocation alignment** (nodes are 8-aligned 16-byte slots). -/
  stmt_align : aStmt.toNat % 8 = 0
  stmt_ram : 0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000
  stmt_win : tohostAddr + 16 ≤ aStmt.toNat
  /-- **supplier: the loop-head SegEntry's `store` transported to `mE`.**  The store
  is represented in `mE` for the entry state `st` — the frames/closures live in the
  arena/AST, disjoint from the stack/retslot scribble value_null + arg-setup made,
  so the loop-head `StoreRepr m0` survives to `mE`.  (Discharged at the caller from
  `SegEntry.store` + the stack-window survival, exactly `ExecEntry.store_survives`.) -/
  store : StoreRepr mE N A φf φc st.store
  /-- **supplier: the same survival, exported for the callee.**  `StoreRepr` survives
  any further change confined to `[SL.lo, sp)` — the mirror of
  `ExecEntry.store_survives`. -/
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mE[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store

/-! ## §3. The span composition + `ExecEntry` marshalling

The bridge theorem.  It composes the three machine pieces (`loopHeadDispatchRow` +
`ValueNullSplice` + `loopHeadArgSetupBridge`) into a single `Steps` run from the
loop-head config to the `exec_stmt` entry config, and marshals the landing into
`ExecEntry`.

The ABI arg VALUES (`a0`=interp*, `a1`=Stmt*, `a2`=env, `a3`=retslot) are supplied
as the concrete landing pins the caller reads off the seg write-log (they are
computed, not premises) — quantified here as `aInterp aStmt aEnv aRet` with the
landing hypotheses `hLand*` that a `chain_facts`/seg readback discharges.  The
CONTROL + representation fields of `ExecEntry` come from: the span landing (PC, ra,
sp, minstret, mem, arg values), the loop-head SegEntry (`good`/`tick`/`store`/`out`/
`frame`), and `LoopHeadDispatchGeom` (the stack/AST/code geometry).

Because the value_null call splice and the jal exec_stmt seam are genuine off-path
CALLs, they are the NAMED premises `hValueNullSplice`/`hArgSetup`.  The `Steps`
composition between them is REAL. -/

/-- **`loopHeadDispatch_span`** — the interp_run loop-head → `exec_stmt` entry span.

From the loop-head config `cH` (parked at `interpLoopHeadPC = 0x8000448c`, control
good, tick-bounded, memory `m0`, the loop-head register pins `sp`/`s0` and a
`minstret` witness) the machine reaches (via the dispatch head ≫ value_null ≫
arg-setup ≫ jal exec_stmt) a config `cE` parked at `exec_stmt`'s entry
`0x80003fe0`, link `x1 = 0x80004478` (the back-edge continuation PC), and `cE`
satisfies `ExecEntry` for the head statement `s` in scope `aEnv`.

The four ABI arg VALUES are the span-computed landing pins (`hLand*`, discharged by a
seg readback at the caller); the CONTROL/representation come from the loop-head
SegEntry fields threaded through (`hStore`/`hOut`/`hFrame` — projected from
`SegEntry cH`), and the stack/AST/code geometry from `LoopHeadDispatchGeom`. -/
theorem loopHeadDispatch_span
    (cH : Config)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (env : Addr) (sp s0 aStmt aEnv aInterp aRet : BitVec 64)
    (s : Stmt) (m0 mE : Mem)
    -- loop-head control state (from `SegEntry cH`):
    (hGH : GoodState cH.σ) (htickH : cH.tick < 2)
    (hpcH : cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64))
    (hmemH : cH.σ.mem = m0)
    (hspH : cH.σ.regs.get? Register.x2 = some sp)
    (hs0H : cH.σ.regs.get? Register.x8 = some s0)
    (hmiH : ∃ w, cH.σ.regs.get? Register.minstret = some w)
    -- the dispatch-head memory decode (off `SegEntry`; supplier: a `chain_facts`
    -- over the loaded loop-head code at 0x8000448c — a load-time fact, exactly like
    -- `DriveToLoopHeadSpans.SegEntryData.facts`):
    (hDispatchFacts :
      ChainFacts cH.σ.mem cH.σ.mem (loopHeadDispatchL sp s0) [] loopHeadDispatchSeg)
    -- the geometry SegEntry cannot supply (stated at the exec_stmt-entry memory mE):
    (hGeom : LoopHeadDispatchGeom g N A SL φf φc st sp aStmt s mE)
    -- the value_null call splice (a CALL; supplier: callSeg over value_null_spec):
    (hValueNullSplice : ∀ (c458 : Config),
        c458.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64) →
        GoodState c458.σ → c458.tick < 2 →
        (∃ w, c458.σ.regs.get? Register.minstret = some w) →
        ValueNullSplice c458)
    -- the arg-setup body ≫ jal exec_stmt bridge (supplier: loopHeadArgSetupBridge
    -- + its jal seam), phrased as a Steps run to the exec_stmt entry with the four
    -- ABI arg values pinned and the back-edge link, memory `mE`, control good:
    (hArgSetup : ∀ (c460 : Config),
        c460.σ.regs.get? Register.PC = some (0x80004460#64 : BitVec 64) →
        GoodState c460.σ → c460.tick < 2 →
        (∃ w, c460.σ.regs.get? Register.minstret = some w) →
        ∃ (cE : Config),
          Steps c460 cE ∧
          cE.σ.regs.get? Register.PC = some (0x80003fe0#64 : BitVec 64) ∧
          cE.σ.regs.get? Register.x1 = some (0x80004478#64 : BitVec 64) ∧
          cE.σ.regs.get? Register.x10 = some aInterp ∧
          cE.σ.regs.get? Register.x11 = some aStmt ∧
          cE.σ.regs.get? Register.x12 = some aEnv ∧
          cE.σ.regs.get? Register.x13 = some aRet ∧
          cE.σ.regs.get? Register.x2 = some sp ∧
          GoodState cE.σ ∧ cE.tick < 2 ∧
          cE.σ.mem = mE ∧
          (∃ w, cE.σ.regs.get? Register.minstret = some w) ∧
          (∀ R : Register, AbiPreservedNoise R → cE.σ.regs.get? R = g R) ∧
          OutRepr cE.σ st ∧
          (∃ v, cE.σ.regs.get? Register.x8 = some v) ∧
          (∃ v, cE.σ.regs.get? Register.x9 = some v) ∧
          (∃ v, cE.σ.regs.get? Register.x18 = some v) ∧
          (∃ v, cE.σ.regs.get? Register.x19 = some v)) :
    ∃ (cE : Config),
      Steps cH cE ∧
      ExecEntry g N A SL φf φc st 0 env s sp (0x80004478#64) aInterp aStmt aEnv aRet mE cE := by
  -- 1. dispatch head → 0x80004458 (the br seg, via the richer landing).
  obtain ⟨vmH, hmiH'⟩ := hmiH
  have hDpre : SegPre loopHeadDispatchSeg (loopHeadDispatchL sp s0) [] 0x8000448c#64 m0 cH := by
    refine ⟨hGH, hmemH, hpcH, ⟨vmH, hmiH'⟩, ?_, ?_, ?_, htickH⟩
    · exact ⟨hspH, hs0H, trivial⟩
    · have h : keysG (loopHeadDispatchL sp s0) = [2, 8] := rfl
      rw [h]; decide
    · exact hDispatchFacts
  obtain ⟨c458, hstep458, hpc458, hG458, htick458, hmi458⟩ :=
    loopHeadDispatchLanded sp s0 m0 cH hDpre
  -- 2. value_null call → 0x80004460.
  obtain ⟨c460, hstep460, hpc460, hG460, htick460, hmi460, _hframe460⟩ :=
    hValueNullSplice c458 hpc458 hG458 htick458 hmi458
  -- 3. arg-setup ≫ jal exec_stmt → 0x80003fe0.
  obtain ⟨cE, hstepE, hpcE, hraE, ha0E, ha1E, ha2E, ha3E, hspE, hGE, htickE, hmemE,
          hmiE, hframeE, houtE, hx8E, hx9E, hx18E, hx19E⟩ :=
    hArgSetup c460 hpc460 hG460 htick460 hmi460
  -- compose the three runs.
  refine ⟨cE, Steps.trans (Steps.trans hstep458 hstep460) hstepE, ?_⟩
  -- marshal the ExecEntry structure.
  refine
    { good := hGE, tick := htickE, pc := hpcE
      a0 := ha0E, a1 := ha1E, a2 := ha2E, a3 := ha3E, ra := hraE
      ra_align := by decide
      spReg := hspE
      stackOK := hGeom.stackOK
      minstret := hmiE
      mem := hmemE
      code := hmemE ▸ hGeom.code
      stmt := hmemE ▸ hGeom.stmt
      store := hmemE ▸ hGeom.store
      store_survives := ?_
      out := houtE
      frame := hframeE
      code_stack_disjoint := hGeom.code_stack_disjoint
      stack_ram := hGeom.stack_ram
      stack_win := hGeom.stack_win
      stmt_stack_disjoint := hGeom.stmt_stack_disjoint
      stmt_align := hGeom.stmt_align
      stmt_ram := hGeom.stmt_ram
      stmt_win := hGeom.stmt_win
      spill_defined := ⟨hx8E, hx9E, hx18E, hx19E⟩ }
  · -- store survival: the callee sees `mem = mE`; a change confined to `[SL.lo, sp)`
    -- keeps the store representable, discharged by the geometry's `store_survives`.
    intro m' hm'
    exact hGeom.store_survives m' (by intro k hk; rw [← hmemE]; exact hm' k hk)

#print axioms loopHeadDispatch_span

end Vsa.Sim
