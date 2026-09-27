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

/-! ## `ExecSeqExit` — the machine state at the sequence loop continuation

`p` is the continuation PC; `status` the produced abrupt-completion status; `st'`
the spec post-state, re-represented with EXTENDED φ-maps. -/

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

/-- Code image for a physical sequence-loop copy. -/
def ExecSeqCopy.Loaded : ExecSeqCopy → Mem → Prop
  | .interpRun => Vsa.Sim.Code.Interp_runLoaded
  | .closureBody => Vsa.Sim.Code.Eval_exprLoaded
  | .blockBody => Vsa.Sim.Code.Exec_stmtLoaded

/-- Copy-specific stack preservation.  The closure-body loop uses bytes below
`sp+168` for its statement return buffer and scratch, but its caller restores
saved registers from the higher part of the same frame.  The block-body loop
runs in its parent's `exec_stmt` frame: the parent's saved registers at
`[sp+136, sp+176)` and everything above survive, except the forwarded return
slot `[aRet, aRet+24)`, which a returning child may write, and arena bytes,
which the children's own frames exclude. -/
def ExecSeqStackFrame
    (copy : ExecSeqCopy) (A : Arena) (SL : StackLayout) (sp aRet : BitVec 64)
    (m0 m : Mem) : Prop :=
  match copy with
  | .closureBody => ∀ a : Nat, sp.toNat + 168 ≤ a → a < SL.hi → m[a]? = m0[a]?
  | .blockBody => ∀ a : Nat, sp.toNat + 136 ≤ a → a < SL.hi →
      ¬ (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      m[a]? = m0[a]?
  | .interpRun => True

theorem ExecSeqStackFrame.trans
    {copy : ExecSeqCopy} {A : Arena} {SL : StackLayout} {sp aRet : BitVec 64}
    {m0 m1 m2 : Mem}
    (h01 : ExecSeqStackFrame copy A SL sp aRet m0 m1)
    (h12 : ExecSeqStackFrame copy A SL sp aRet m1 m2) :
    ExecSeqStackFrame copy A SL sp aRet m0 m2 := by
  cases copy with
  | closureBody =>
      intro a hlo hhi
      rw [h12 a hlo hhi, h01 a hlo hhi]
  | interpRun => trivial
  | blockBody =>
      intro a hlo hhi hr hA
      rw [h12 a hlo hhi hr hA, h01 a hlo hhi hr hA]

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

/-- Named facts of the interpreter loop's selected cursor. -/
structure ExecSeqInterpCursor
    (m : Mem) (ss : List Stmt) (sp aRet cursor finish : BitVec 64)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  cursorReg : regs Register.x8 = some cursor
  finishReg : regs Register.x18 = some finish
  spReg : regs Register.x2 = some sp
  retSlot : aRet = sp + 88#64
  remaining : finish.toNat = cursor.toNat + 8 * ss.length
  script : read64 m (sp.toNat + 8) = some 0
  array : StmtArrayRepr m cursor.toNat ss.length ss

/-- Expose the interpreter cursor's witnesses through named fields. -/
theorem ExecSeqCursorRepr.interp
    {m : Mem} {phiF : Addr → Nat} {env : Addr} {ss : List Stmt} {sp aRet : BitVec 64}
    {regs : (R : Register) → Option (RegisterType R)}
    (h : ExecSeqCursorRepr .interpRun m phiF env ss sp aRet regs) :
    ∃ cursor finish, ExecSeqInterpCursor m ss sp aRet cursor finish regs := by
  obtain ⟨cursor, finish, hc, hf, hs, hr, hn, hscript, ha⟩ := h
  exact ⟨cursor, finish, hc, hf, hs, hr, hn, hscript, ha⟩

/-- Named facts of the block loop's selected cursor. -/
structure ExecSeqBlockCursor
    (m : Mem) (phiF : Addr → Nat) (env : Addr) (ss : List Stmt)
    (sp aRet block base : BitVec 64) (index count : Nat)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  blockReg : regs Register.x8 = some block
  indexReg : regs Register.x16 = some (BitVec.ofNat 64 index)
  envReg : regs Register.x19 = some (BitVec.ofNat 64 (phiF env))
  retReg : regs Register.x18 = some aRet
  spReg : regs Register.x2 = some sp
  baseRead : read64 m (block.toNat + 8) = some base.toNat
  countRead : read32 m (block.toNat + 16) = some count
  remaining : index + ss.length = count
  countBound : count < 2^31
  array : StmtArrayRepr m (base.toNat + 8 * index) ss.length ss

/-- Expose the block cursor's witnesses through named fields. -/
theorem ExecSeqCursorRepr.block
    {m : Mem} {phiF : Addr → Nat} {env : Addr} {ss : List Stmt} {sp aRet : BitVec 64}
    {regs : (R : Register) → Option (RegisterType R)}
    (h : ExecSeqCursorRepr .blockBody m phiF env ss sp aRet regs) :
    ∃ block base index count, ExecSeqBlockCursor m phiF env ss sp aRet block base index count regs := by
  obtain ⟨block, base, index, count, hb, hi, he, hr, hs, hbase, hc, hn, hbound, ha⟩ := h
  exact ⟨block, base, index, count, hb, hi, he, hr, hs, hbase, hc, hn, hbound, ha⟩

/-! ## `execSeqNil` — the `ExecSeq.nil` case

The empty sequence produces `.normal` with the store and output unchanged. At the
loop head with nothing left to run, the machine has already reached the loop's
normal exit, so this is the zero-step identity `Triple` at a shared PC `p`. The
`ExecSeq.nil` derivation is threaded (unused, as the spec constructor has no
premises), matching the `motive_ExecSeq` minor-premise shape. -/

end Vsa.Sim
