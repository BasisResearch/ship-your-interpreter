import Vsa.Sim.ExecEntry

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
    PhiExtends φf φf' st'.store.frames.size ∧
    PhiExtends φc φc' st'.store.closures.size ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store
  /-- Console output for `st'`. -/
  out : OutRepr c.σ st'
  /-- The blanket ghost frame. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- `minstret` present. -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

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
      (ExecSeqExit g N A SL φf φc st .normal sp r p m0) := by
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
