import Vsa.Sim.ExecEntry
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.Code.Interp_run

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

inductive ExecSeqCopy where
  | interpRun
  | closureBody
  | blockBody
  deriving DecidableEq

def ExecSeqCopy.Loaded : ExecSeqCopy → Mem → Prop
  | .interpRun => Vsa.Sim.Code.Interp_runLoaded
  | .closureBody => Vsa.Sim.Code.Eval_exprLoaded
  | .blockBody => Vsa.Sim.Code.Exec_stmtLoaded

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

theorem ExecSeqCursorRepr.interp
    {m : Mem} {phiF : Addr → Nat} {env : Addr} {ss : List Stmt} {sp aRet : BitVec 64}
    {regs : (R : Register) → Option (RegisterType R)}
    (h : ExecSeqCursorRepr .interpRun m phiF env ss sp aRet regs) :
    ∃ cursor finish, ExecSeqInterpCursor m ss sp aRet cursor finish regs := by
  obtain ⟨cursor, finish, hc, hf, hs, hr, hn, hscript, ha⟩ := h
  exact ⟨cursor, finish, hc, hf, hs, hr, hn, hscript, ha⟩

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

theorem ExecSeqCursorRepr.block
    {m : Mem} {phiF : Addr → Nat} {env : Addr} {ss : List Stmt} {sp aRet : BitVec 64}
    {regs : (R : Register) → Option (RegisterType R)}
    (h : ExecSeqCursorRepr .blockBody m phiF env ss sp aRet regs) :
    ∃ block base index count, ExecSeqBlockCursor m phiF env ss sp aRet block base index count regs := by
  obtain ⟨block, base, index, count, hb, hi, he, hr, hs, hbase, hc, hn, hbound, ha⟩ := h
  exact ⟨block, base, index, count, hb, hi, he, hr, hs, hbase, hc, hn, hbound, ha⟩

end Vsa.Sim
