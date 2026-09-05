import Vsa.Sim.ExecEntry
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.Code.Interp_run

/-!
# Layer 4 — M4 statement family: shared `ExecSeq` entry/exit + the `nil` case

Companion to `Vsa/Sim/EvalSimCommon.lean` (the expression-side shared machinery)
for the STATEMENT family. It provides:

* **`ExecSeqEntry`/`ExecSeqExit`** — the machine entry/exit predicates for a
  statement *sequence* (`ExecSeq`), as executed by the `block` arm's loop in
  `exec_stmt` (and by `interp_run`'s top-level loop). A sequence is run in a
  fixed scope frame; the loop calls `exec_stmt` once per statement and stops at
  the first non-`normal` status. `ExecSeqEntry` is stated at a `loopPC` (the loop
  head, where the machine is about to run the remaining statement list `ss`);
  `ExecSeqExit` at a `contPC` (the loop's continuation, carrying the produced
  `Status`). Both carry `StoreRepr`/`OutRepr` (a sequence mutates both).

* **`execSeqNil`** — the `ExecSeq.nil` case: the empty sequence is a no-op that
  yields `.normal` with the store and output unchanged. When the loop head is
  reached with nothing left to run, the machine is ALREADY at the loop's normal
  exit (the block arm's `beq s0,s2` / `blt` exit test has fallen through to the
  return-normal path). We model this as the zero-step identity `Triple` at a
  shared PC `p` (`loopPC = contPC = p`): the entry predicate for `ss = []`
  literally IS the exit predicate for `.normal`, so `execSeqNil` is `Triple.rfl`
  up to the definitional unfolding. This mirrors how the spec `ExecSeq.nil`
  constructor is an axiom with no premises.

`consNormal`/`consAbrupt` are sketched in the module doc for the follow-up: each
runs `exec_stmt` once (`ExecEntry`/`ExecExit`, a `motive_ExecS` IH) then either
loops (`consNormal`, status normal) or exits abruptly (`consAbrupt`, status ≠
normal). They need the `block`-arm loop decode (env_new + the `0x800041a4`
do-while over the `Stmt**` array) which is the next statement-family milestone.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## `ExecSeqEntry` — the machine state at the sequence loop head

`p` is the loop-head PC (where the next statement is about to be dispatched, or
— when `ss = []` — where the loop has fallen through to its normal exit). `st` is
the spec pre-state, `env` the fixed scope, `ss` the remaining statement list. -/
structure ExecSeqEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
    (sp r : BitVec 64) (p : Nat)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Pinned control state. -/
  good : GoodState c.σ
  /-- Tick parity. -/
  tick : c.tick < 2
  /-- PC at the loop head. -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 p)
  /-- The whole spec store is represented. -/
  store : StoreRepr c.σ.mem N A φf φc st.store
  /-- The sequence scope names an allocated semantic frame. -/
  env_valid : EnvValid st env
  /-- Console output correspondence. -/
  out : OutRepr c.σ st
  /-- Machine memory is the pinned pre-memory. -/
  mem : c.σ.mem = m0
  /-- The blanket ghost frame. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- `minstret` present. -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

/-! ## `ExecSeqExit` — the machine state at the sequence loop continuation

`p` is the continuation PC; `status` the produced abrupt-completion status; `st'`
the spec post-state, re-represented with EXTENDED φ-maps. -/
structure ExecSeqExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : St) (status : Status)
    (sp r : BitVec 64) (p : Nat)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Control state re-established. -/
  good : GoodState c.σ
  /-- Tick parity still `< 2`. -/
  tick : c.tick < 2
  /-- PC at the continuation. -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 p)
  /-- The store re-represented for `st'` with extended maps. -/
  store : ∃ (φf' φc' : Addr → Nat),
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store
  /-- Console output for `st'`. -/
  out : OutRepr c.σ st'
  /-- The blanket ghost frame. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- `minstret` present. -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

/-! ## Indexed sequence ABI

`ExecSeqEntry`/`ExecSeqExit` above are retained as the legacy loop-engine
boundary.  They do not identify a physical loop copy, its statement cursor, or
the status ABI.  The recursive motive uses the indexed boundary below.

An empty suffix is not entered at a nonempty loop head.  Each copy has a
distinct empty-entry PC.  In particular, this avoids treating `ExecSeq.nil` as
an arbitrary loop-head-to-continuation span. -/

/-- The three physical statement-sequence loops in the binary. -/
inductive ExecSeqCopy where
  | interpRun
  | closureBody
  | blockBody
  deriving DecidableEq

/-- Machine entry PC for a semantic suffix. Empty suffixes start at that copy's
normal-completion point; nonempty suffixes start at its dispatch loop head. -/
def execSeqEntryPC : ExecSeqCopy → List Stmt → Nat
  | .interpRun, [] => 0x80004514
  | .interpRun, _ :: _ => 0x8000448c
  | .closureBody, [] => 0x80003954
  | .closureBody, _ :: _ => 0x80003354
  | .blockBody, [] => 0x8000409c
  | .blockBody, _ :: _ => 0x800041a4

/-- Machine exit PC for a completed semantic sequence. The closure copy sees
an abrupt child status at `0x80003378`; its normal completion is `0x80003954`. -/
def execSeqExitPC : ExecSeqCopy → Status → Nat
  | .interpRun, _ => 0x80004514
  | .closureBody, .normal => 0x80003954
  | .closureBody, _ => 0x80003378
  | .blockBody, _ => 0x8000409c

/-- Statuses implemented as semantic sequence returns by each physical copy.
The top-level interpreter loop only consumes normal program completion. -/
def ExecSeqCopy.Supports : ExecSeqCopy → Status → Prop
  | .interpRun, status => status = .normal
  | .closureBody, status => status = .normal ∨ ∃ v, status = .ret v
  | .blockBody, _ => True

/-- Code image for a physical sequence-loop copy. -/
def ExecSeqCopy.Loaded : ExecSeqCopy → Mem → Prop
  | .interpRun => Vsa.Sim.Code.Interp_runLoaded
  | .closureBody => Vsa.Sim.Code.Eval_exprLoaded
  | .blockBody => Vsa.Sim.Code.Exec_stmtLoaded

/-- Copy-specific status ABI at a semantic sequence exit.  The closure body's
normal bypass reaches `0x80003954` without establishing `a0 = 0`; its caller
constructs the null result on that path.  The other exits expose the status in
`a0`. -/
def ExecSeqStatusABI
    (copy : ExecSeqCopy) (status : Status)
    (regs : (R : Register) → Option (RegisterType R)) : Prop :=
  match copy, status with
  | .closureBody, .normal => True
  | _, status => regs Register.x10 = some (StatusCode status)

/-- Copy-specific stack preservation.  The closure-body loop uses bytes below
`sp+168` for its statement return buffer and scratch, but its caller restores
saved registers from the higher part of the same frame. -/
def ExecSeqStackFrame
    (copy : ExecSeqCopy) (SL : StackLayout) (sp : BitVec 64)
    (m0 m : Mem) : Prop :=
  match copy with
  | .closureBody => ∀ a : Nat, sp.toNat + 168 ≤ a → a < SL.hi → m[a]? = m0[a]?
  | _ => True

theorem ExecSeqStackFrame.trans
    {copy : ExecSeqCopy} {SL : StackLayout} {sp : BitVec 64}
    {m0 m1 m2 : Mem}
    (h01 : ExecSeqStackFrame copy SL sp m0 m1)
    (h12 : ExecSeqStackFrame copy SL sp m1 m2) :
    ExecSeqStackFrame copy SL sp m0 m2 := by
  cases copy with
  | closureBody =>
      intro a hlo hhi
      rw [h12 a hlo hhi, h01 a hlo hhi]
  | interpRun => trivial
  | blockBody => trivial

def execSeqChildRetPC : ExecSeqCopy → Nat
  | .interpRun => 0x80004478
  | .closureBody => 0x80003378
  | .blockBody => 0x800041c8

/-- Registers owned by a sequence copy are loop state, not an ABI frame.  The
interp copy advances `s0` and reloads `s1`; the closure copy advances `s0`.
Demanding those registers equal one fixed ghost frame at both entry and exit
would make every non-empty normal run inconsistent. -/
def ExecSeqFrameReg (copy : ExecSeqCopy) (R : Register) : Prop :=
  AbiPreservedNoise R ∧
  match copy with
  | .interpRun => R ≠ Register.x8 ∧ R ≠ Register.x9
  | .closureBody => R ≠ Register.x8
  | .blockBody => True

/-- Copy-specific values used to marshal the selected statement into a fresh
`exec_stmt` call.  These pins connect the semantic environment to the actual
machine argument source; cursor reflection alone does not determine them. -/
def ExecSeqCallABI
    (copy : ExecSeqCopy) (m : Mem)
    (regs : (R : Register) → Option (RegisterType R))
    (φf : Addr → Nat) (env : Addr) (sp aRet : BitVec 64) : Prop :=
  match copy with
  | .interpRun =>
      ∃ interp : BitVec 64,
        read64 m sp.toNat = some interp.toNat ∧
        read64 m interp.toNat = some (φf env) ∧
        aRet = sp + 88#64
  | .closureBody =>
      ∃ interp : BitVec 64,
        regs Register.x18 = some interp ∧
        regs Register.x19 = some (BitVec.ofNat 64 (φf env)) ∧
        aRet = sp + 144#64
  | .blockBody =>
      ∃ interp : BitVec 64,
        regs Register.x9 = some interp ∧
        regs Register.x19 = some (BitVec.ofNat 64 (φf env)) ∧
        regs Register.x18 = some aRet

/-- The exact head pointer selected by the physical cursor. -/
def ExecSeqHeadAt
    (copy : ExecSeqCopy) (m : Mem)
    (regs : (R : Register) → Option (RegisterType R)) (p : BitVec 64) : Prop :=
  match copy with
  | .interpRun =>
      ∃ cursor : BitVec 64, regs Register.x8 = some cursor ∧
        read64 m cursor.toNat = some p.toNat
  | .closureBody =>
      ∃ body base : BitVec 64, ∃ i : Nat,
        regs Register.x16 = some body ∧ regs Register.x8 = some (BitVec.ofNat 64 i) ∧
        read64 m (body.toNat + 8) = some base.toNat ∧
        read64 m (base.toNat + 8 * i) = some p.toNat
  | .blockBody =>
      ∃ block base : BitVec 64, ∃ i : Nat,
        regs Register.x8 = some block ∧ regs Register.x16 = some (BitVec.ofNat 64 i) ∧
        read64 m (block.toNat + 8) = some base.toNat ∧
        read64 m (base.toNat + 8 * i) = some p.toNat

/-- Static geometry needed to marshal the selected head into `ExecEntry`. -/
def ExecSeqHeadGround
    (copy : ExecSeqCopy) (m : Mem)
    (regs : (R : Register) → Option (RegisterType R))
    (SL : StackLayout) (A : Arena) (φf : Addr → Nat)
    (sp aRet : BitVec 64) (st : St) (d : Nat) (env : Addr)
    (ss : List Stmt) : Prop :=
  match ss with
  | [] => True
  | s :: _ =>
      ∃ p : BitVec 64,
        ExecSeqHeadAt copy m regs p ∧ StmtRepr m p.toNat s ∧
        ExecSeqCallABI copy m regs φf env sp aRet ∧
        ExecGround m SL A sp aRet p.toNat s ∧
        StackOK SL sp (176 + 1088) ∧
        StackOK SL sp
          (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Stmt.bodiesBound Vsa.While.perCallBudget s = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget

/-- Copy-specific statement cursor. This is the missing link from the machine
loop index to the exact remaining semantic statement list. -/
def ExecSeqCursorRepr
    (copy : ExecSeqCopy) (m : Mem) (φf : Addr → Nat) (env : Addr)
    (ss : List Stmt) (sp aRet : BitVec 64)
    (regs : (R : Register) → Option (RegisterType R)) : Prop :=
  match copy with
  | .interpRun =>
      ∃ cursor finish : BitVec 64,
        regs Register.x8 = some cursor ∧
        regs Register.x18 = some finish ∧
        regs Register.x2 = some sp ∧
        aRet = sp + 88#64 ∧
        finish.toNat = cursor.toNat + 8 * ss.length ∧
        read64 m (sp.toNat + 8) = some 0 ∧
        StmtArrayRepr m cursor.toNat ss.length ss
  | .closureBody =>
      ∃ (body base : BitVec 64) (i count : Nat),
        regs Register.x16 = some body ∧
        regs Register.x8 = some (BitVec.ofNat 64 i) ∧
        regs Register.x19 = some (BitVec.ofNat 64 (φf env)) ∧
        regs Register.x2 = some sp ∧
        aRet = sp + 144#64 ∧
        read64 m (body.toNat + 8) = some base.toNat ∧
        read32 m (body.toNat + 16) = some count ∧
        i + ss.length = count ∧
        count < 2^31 ∧
        StmtArrayRepr m (base.toNat + 8 * i) ss.length ss
  | .blockBody =>
      ∃ (block base : BitVec 64) (i count : Nat),
        regs Register.x8 = some block ∧
        regs Register.x16 = some (BitVec.ofNat 64 i) ∧
        regs Register.x19 = some (BitVec.ofNat 64 (φf env)) ∧
        regs Register.x18 = some aRet ∧
        regs Register.x2 = some sp ∧
        read64 m (block.toNat + 8) = some base.toNat ∧
        read32 m (block.toNat + 16) = some count ∧
        i + ss.length = count ∧
        count < 2^31 ∧
        StmtArrayRepr m (base.toNat + 8 * i) ss.length ss

/-- Faithful, copy-indexed sequence entry. It retains the scope and exact
remaining statement suffix in the machine predicate. -/
structure ExecSeqEntryI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC =
    some (BitVec.ofNat 64 (execSeqEntryPC copy ss))
  store : StoreRepr c.σ.mem N A φf φc st.store
  out : OutRepr c.σ st
  mem : c.σ.mem = m0
  code : copy.Loaded c.σ.mem
  cursor : ExecSeqCursorRepr copy c.σ.mem φf env ss sp aRet c.σ.regs.get?
  head_ground : ExecSeqHeadGround copy c.σ.mem c.σ.regs.get?
    SL A φf sp aRet st d env ss
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  /-- Empty suffixes are parked at their semantic exit boundary.  That boundary
  already carries every status fact the copy exposes. -/
  empty_status : ss = [] → ExecSeqStatusABI copy .normal c.σ.regs.get?
  frame : ∀ R : Register, ExecSeqFrameReg copy R → c.σ.regs.get? R = g R
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

/-- Faithful, copy-indexed sequence exit. Unlike the legacy `ExecSeqExit`, the
postcondition exposes the status in `a0` and the return value in the forwarded
return slot. -/
structure ExecSeqExitI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (nf nc : Nat)
    (st' : St) (status : Status)
    (sp aRet : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  supported : copy.Supports status
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC =
    some (BitVec.ofNat 64 (execSeqExitPC copy status))
  status_abi : ExecSeqStatusABI copy status c.σ.regs.get?
  store : ∃ (φf' φc' : Addr → Nat),
    PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧
      StoreRepr c.σ.mem N A φf' φc' st'.store
  out : OutRepr c.σ st'
  retval : ∀ v, status = .ret v →
    ∃ φc', PhiExtends φc φc' nc ∧
      ValueRepr c.σ.mem N φc' aRet.toNat v
  /-- Memory is stable outside the mutable stack and arena regions.  A global
  `MemExtends m0 c.σ.mem` would be false: sequence execution overwrites
  already-present stack and heap bytes. -/
  mem_frame : ∀ a : Nat,
    ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      c.σ.mem[a]? = m0[a]?
  /-- The physical copy's caller-owned high-stack window survives. -/
  stack_frame : ExecSeqStackFrame copy SL sp m0 c.σ.mem
  frame : ∀ R : Register, ExecSeqFrameReg copy R → c.σ.regs.get? R = g R
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

/-- The indexed empty-sequence case is an exact identity at the copy's empty
boundary.  No arbitrary entry/exit-PC pair remains. -/
theorem execSeqNilI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (sp aRet : BitVec 64) (m0 : Mem)
    (hsupport : copy.Supports .normal) :
    Triple
      (ExecSeqEntryI copy g N A SL φf φc st d env [] sp aRet m0)
      (ExecSeqExitI copy g N A SL φf φc st.store.frames.size
        st.store.closures.size st .normal sp aRet m0) := by
  intro c hc
  refine ⟨c, .refl c, ?_⟩
  exact
    { supported := hsupport
      good := hc.good
      tick := hc.tick
      pc := by cases copy <;> exact hc.pc
      status_abi := hc.empty_status rfl
      store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hc.store⟩
      out := hc.out
      retval := fun v hv => by cases hv
      mem_frame := fun a _ _ => by rw [hc.mem]
      stack_frame := by
        cases copy <;> simp [ExecSeqStackFrame, hc.mem]
      frame := hc.frame
      minstret := hc.minstret }

#print axioms execSeqNilI

/-! ## `execSeqNil` — the `ExecSeq.nil` case

The empty sequence produces `.normal` with the store and output unchanged. At the
loop head with nothing left to run, the machine has already reached the loop's
normal exit, so this is the zero-step identity `Triple` at a shared PC `p`. The
`ExecSeq.nil` derivation is threaded (unused, as the spec constructor has no
premises), matching the `motive_ExecSeq` minor-premise shape. -/
theorem execSeqNil
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (sp r : BitVec 64) (p : Nat) (m0 : Mem)
    (_hSeq : ExecSeq st d env [] st .normal) :
    Triple
      (ExecSeqEntry g N A SL φf φc st d env [] sp r p m0)
      (ExecSeqExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st .normal sp r p m0) := by
  intro c hc
  refine ⟨c, .refl c, ?_⟩
  exact
    { good := hc.good
      tick := hc.tick
      pc := hc.pc
      store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hc.store⟩
      out := hc.out
      frame := hc.frame
      minstret := hc.minstret }

end Vsa.Sim
