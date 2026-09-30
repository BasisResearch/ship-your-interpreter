import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Alloc
import Vsa.Triple
import Vsa.Sim.GoodState
import Vsa.Sim.Regions
import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.Code.Value_truthy
import Vsa.Sim.InterpEntry

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

def execStmtEntry : Nat := 0x80003fe0

def execStmtEnd : Nat := 0x80004308

def stmtJumpTableBase : Nat := 0x80019fb8

def StatusCode : Status → BitVec 64
  | .normal => 0#64
  | .brk    => 1#64
  | .cont   => 2#64
  | .ret _  => 3#64

@[simp] theorem statusCode_normal : StatusCode .normal = 0#64 := rfl
@[simp] theorem statusCode_brk : StatusCode .brk = 1#64 := rfl
@[simp] theorem statusCode_cont : StatusCode .cont = 2#64 := rfl
@[simp] theorem statusCode_ret (v : Value) : StatusCode (.ret v) = 3#64 := rfl

def execArmExpr    : BitVec 64 := 0x80004170#64
def execArmVarDecl : BitVec 64 := 0x800040d8#64
def execArmBlock   : BitVec 64 := 0x8000418c#64
def execArmIf      : BitVec 64 := 0x800041e8#64
def execArmWhile   : BitVec 64 := 0x8000403c#64
def execArmFor     : BitVec 64 := 0x80004234#64
def execArmRet     : BitVec 64 := 0x80004120#64
def execArmBrk     : BitVec 64 := 0x80004098#64
def execArmCont    : BitVec 64 := 0x800040b8#64

structure StmtSlotPinned (k : Nat) (armPC : BitVec 64) (m : Mem) : Prop where
  b0 : ∃ b0 b1 b2 b3 : BitVec 8,
    m[(stmtJumpTableBase + 4 * k + 0 : Nat)]? = some b0 ∧
    m[(stmtJumpTableBase + 4 * k + 1 : Nat)]? = some b1 ∧
    m[(stmtJumpTableBase + 4 * k + 2 : Nat)]? = some b2 ∧
    m[(stmtJumpTableBase + 4 * k + 3 : Nat)]? = some b3 ∧
    (BitVec.ofNat 64 stmtJumpTableBase +
      sign_extend (m := 64) (((b3.append b2).append b1).append b0)) = armPC

structure StmtTablePins (m : Mem) : Prop where
  slot0 : StmtSlotPinned 0 execArmExpr m
  slot1 : StmtSlotPinned 1 execArmVarDecl m
  slot2 : StmtSlotPinned 2 execArmBlock m
  slot3 : StmtSlotPinned 3 execArmIf m
  slot4 : StmtSlotPinned 4 execArmWhile m
  slot5 : StmtSlotPinned 5 execArmFor m
  slot6 : StmtSlotPinned 6 execArmRet m
  slot7 : StmtSlotPinned 7 execArmBrk m
  slot8 : StmtSlotPinned 8 execArmCont m

theorem stmtSlotPinned_agree {k : Nat} {armPC : BitVec 64} {m m' : Mem}
    (h : StmtSlotPinned k armPC m)
    (ha : ∀ a, stmtJumpTableBase + 4 * k ≤ a → a < stmtJumpTableBase + 4 * k + 4 →
      m[a]? = m'[a]?) :
    StmtSlotPinned k armPC m' := by
  obtain ⟨⟨t0, t1, t2, t3, h0, h1, h2, h3, he⟩⟩ := h
  exact ⟨⟨t0, t1, t2, t3,
    (ha _ (by omega) (by omega)).symm.trans h0,
    (ha _ (by omega) (by omega)).symm.trans h1,
    (ha _ (by omega) (by omega)).symm.trans h2,
    (ha _ (by omega) (by omega)).symm.trans h3, he⟩⟩

theorem StmtTablePins.transport {m m' : Mem} (h : StmtTablePins m)
    (ha : ∀ a, stmtJumpTableBase ≤ a → a < stmtJumpTableBase + 36 → m[a]? = m'[a]?) :
    StmtTablePins m' where
  slot0 := stmtSlotPinned_agree h.slot0 (fun a h1 h2 => ha a (by omega) (by omega))
  slot1 := stmtSlotPinned_agree h.slot1 (fun a h1 h2 => ha a (by omega) (by omega))
  slot2 := stmtSlotPinned_agree h.slot2 (fun a h1 h2 => ha a (by omega) (by omega))
  slot3 := stmtSlotPinned_agree h.slot3 (fun a h1 h2 => ha a (by omega) (by omega))
  slot4 := stmtSlotPinned_agree h.slot4 (fun a h1 h2 => ha a (by omega) (by omega))
  slot5 := stmtSlotPinned_agree h.slot5 (fun a h1 h2 => ha a (by omega) (by omega))
  slot6 := stmtSlotPinned_agree h.slot6 (fun a h1 h2 => ha a (by omega) (by omega))
  slot7 := stmtSlotPinned_agree h.slot7 (fun a h1 h2 => ha a (by omega) (by omega))
  slot8 := stmtSlotPinned_agree h.slot8 (fun a h1 h2 => ha a (by omega) (by omega))

structure StmtRegionSpec (m : Mem) (SL : StackLayout) (A : Arena)
    (aRet aStmt : Nat) (s : Vsa.While.Stmt) (lo hi : Nat) : Prop where
  nodes : StmtIn m lo hi aStmt s
  lo_ram : 0x80000000 ≤ lo

  hi_ram : hi + 8 ≤ 0x100000000
  win : tohostAddr + 16 ≤ lo
  stack_disjoint : hi ≤ SL.lo ∨ SL.hi ≤ lo
  ret_disjoint : hi ≤ aRet ∨ aRet + 24 ≤ lo
  arena_disjoint : hi ≤ A.lo ∨ A.hi ≤ lo

structure StmtRegionPins (m : Mem) (SL : StackLayout) (A : Arena)
    (aRet aStmt : Nat) (s : Vsa.While.Stmt) : Prop where
  region : ∃ lo hi, StmtRegionSpec m SL A aRet aStmt s lo hi

theorem StmtRegionSpec.transport {m m' : Mem} {SL : StackLayout} {A : Arena}
    {aRet aStmt : Nat} {s : Vsa.While.Stmt} {lo hi : Nat}
    (h : StmtRegionSpec m SL A aRet aStmt s lo hi)
    (ha : ∀ a, lo ≤ a → a < hi → m[a]? = m'[a]?) :
    StmtRegionSpec m' SL A aRet aStmt s lo hi where
  nodes := stmtIn_agreeP (fun a hp => ha a hp.1 hp.2) s h.nodes
  lo_ram := h.lo_ram
  hi_ram := h.hi_ram
  win := h.win
  stack_disjoint := h.stack_disjoint
  ret_disjoint := h.ret_disjoint
  arena_disjoint := h.arena_disjoint

structure RetSlotGeom (SL : StackLayout) (sp aRet : BitVec 64) : Prop where
  align : aRet.toNat % 8 = 0
  ram : 0x80000000 ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ aRet.toNat
  scribble_disjoint : aRet.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRet.toNat
  inSL : SL.lo ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ SL.hi

structure ExecGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp aRet : BitVec 64) (aStmt : Nat) (s : Vsa.While.Stmt) : Prop where
  table : StmtTablePins m
  table_stack : stmtJumpTableBase + 36 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase
  ast : StmtRegionPins m SL A aRet.toNat aStmt s
  arena_stack : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ execStmtEntry ∨ execStmtEnd ≤ A.lo
  arena_table : A.hi ≤ stmtJumpTableBase ∨ stmtJumpTableBase + 36 ≤ A.lo
  eval_call : EvalCallSupport m SL A sp

  stack_bytes : ∀ k : Nat, SL.lo ≤ k → k < SL.hi →
    ∃ b : BitVec 8, m[k]? = some b
  aret : RetSlotGeom SL sp aRet
  aret_table_disjoint : aRet.toNat + 24 ≤ stmtJumpTableBase ∨
    stmtJumpTableBase + 36 ≤ aRet.toNat

theorem ExecGround.survive_stack {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Vsa.While.Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hpop : ∀ k : Nat, SL.lo ≤ k → k < SL.hi →
      ∃ b : BitVec 8, m'[k]? = some b)
    (hag : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24) → m[k]? = m'[k]?) :
    ExecGround m' SL A sp aRet aStmt s where
  table := h.table.transport (fun a h1 h2 => by
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases h.table_stack with ht | ht <;> omega
    · rcases h.aret_table_disjoint with hs | hs <;> omega)
  table_stack := h.table_stack
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    refine ⟨lo, hi, spec.transport (fun a h1 h2 => ?_)⟩
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases spec.stack_disjoint with hs | hs
      · omega
      · have := h.aret.inSL; omega
    · rcases spec.ret_disjoint with hs | hs <;> omega⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  arena_table := h.arena_table
  eval_call := h.eval_call.transport (fun k hk => by
    have hs := h.eval_call.outsideStack hk
    have hr := h.aret.inSL
    exact (hag k (by omega) (by omega)).symm)
  stack_bytes := hpop
  aret := h.aret
  aret_table_disjoint := h.aret_table_disjoint

structure ExecEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (s : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where

  good : GoodState c.σ

  tick : c.tick < 2

  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry)

  a0 : c.σ.regs.get? Register.x10 = some aInterp

  a1 : c.σ.regs.get? Register.x11 = some aStmt

  a2 : c.σ.regs.get? Register.x12 = some aEnv

  envPtr : aEnv = BitVec.ofNat 64 (φf env)

  a3 : c.σ.regs.get? Register.x13 = some aRet

  ra : c.σ.regs.get? Register.x1 = some r

  ra_align : r.toNat % 4 = 0

  spReg : c.σ.regs.get? Register.x2 = some sp

  stackOK : StackOK SL sp (176 + 1088)

  stackBudget : StackOK SL sp
    (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)

  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget s = true

  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget

  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

  mem : c.σ.mem = m0

  code : Exec_stmtLoaded c.σ.mem

  stmt : StmtRepr c.σ.mem aStmt.toNat s

  store : StoreRepr c.σ.mem N A φf φc st.store

  env_valid : EnvValid st env

  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store

  out : OutRepr c.σ st

  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R

  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo

  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo

  stmt_stack_disjoint : aStmt.toNat + 4 ≤ SL.lo ∨ sp.toNat ≤ aStmt.toNat

  stmt_ram : 0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 4 ≤ 0x100000000
  stmt_win : aStmt.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat

  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x18 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x19 = some v)

  envset_defined : (∃ v, c.σ.regs.get? Register.x20 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x21 = some v)

  ground : ExecGround c.σ.mem SL A sp aRet aStmt.toNat s

theorem ExecEntry.store_survives_sp
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : St} {d : Nat} {env : Addr} {s : Stmt}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {c : Config}
    (hc : ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c) :
    ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store :=
  fun m' h => hc.store_survives m'
    (fun k hk => h k
      (fun hcon => hk ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hc.stackOK.2.1⟩))

end Vsa.Sim
