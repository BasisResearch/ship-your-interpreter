import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Alloc
import Vsa.While.StackNeed
import Vsa.Triple
import Vsa.Sim.GoodState
import Vsa.Sim.Regions
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.Code.Value_int
import Vsa.Sim.Code.Value_null
import Vsa.Sim.Code.Value_bool
import Vsa.Sim.Code.Value_str
import Vsa.Sim.Code.Value_truthy
import Vsa.Sim.MemRegion
import Vsa.Sim.StaticImageSupport

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

def evalExprEntry : Nat := 0x80003164

def EnvValid (st : Vsa.While.St) (env : Addr) : Prop :=
  env < st.store.frames.size

namespace EnvValid

end EnvValid

abbrev AbiPreservedNoise (R : Register) : Prop :=
  AbiPreserved R = true ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

def PhiExtends (φ φ' : Addr → Nat) (n : Nat) : Prop :=
  ∀ a, a < n → φ' a = φ a

def InterpCodeLoaded (m : Mem) : Prop :=
  Eval_exprLoaded m

def jumpTableBase : Nat := 0x80019f58

def IntSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 0 : Nat)]? = some (0xb0 : BitVec 8) ∧
  m[(jumpTableBase + 1 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 2 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 3 : Nat)]? = some (0xff : BitVec 8)

def StrSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 4 : Nat)]? = some (0xbc : BitVec 8) ∧
  m[(jumpTableBase + 5 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 6 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 7 : Nat)]? = some (0xff : BitVec 8)

def BoolSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 8 : Nat)]? = some (0xc8 : BitVec 8) ∧
  m[(jumpTableBase + 9 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 10 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 11 : Nat)]? = some (0xff : BitVec 8)

def NullSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 12 : Nat)]? = some (0xd4 : BitVec 8) ∧
  m[(jumpTableBase + 13 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 14 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 15 : Nat)]? = some (0xff : BitVec 8)

structure NBSPins (m : Mem) : Prop where
  null_code : Value_nullLoaded m
  bool_code : Value_boolLoaded m
  str_code : Value_strLoaded m
  null_slot : NullSlotPinned m
  bool_slot : BoolSlotPinned m
  str_slot : StrSlotPinned m

def KindSlotPinned (k : Nat) (armPC : BitVec 64) (m : Mem) : Prop :=
  ∃ t0 t1 t2 t3 : BitVec 8,
    m[(jumpTableBase + 4 * k + 0 : Nat)]? = some t0 ∧
    m[(jumpTableBase + 4 * k + 1 : Nat)]? = some t1 ∧
    m[(jumpTableBase + 4 * k + 2 : Nat)]? = some t2 ∧
    m[(jumpTableBase + 4 * k + 3 : Nat)]? = some t3 ∧
    (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
      + BitVec.ofNat 64 jumpTableBase) = armPC

structure KindTablePins (m : Mem) : Prop where
  slot0 : KindSlotPinned 0 (0x80003408#64) m
  slot1 : KindSlotPinned 1 (0x80003414#64) m
  slot2 : KindSlotPinned 2 (0x80003420#64) m
  slot3 : KindSlotPinned 3 (0x8000342c#64) m
  slot4 : KindSlotPinned 4 (0x80003434#64) m
  slot5 : KindSlotPinned 5 (0x8000347c#64) m
  slot6 : KindSlotPinned 6 (0x800034e8#64) m
  slot7 : KindSlotPinned 7 (0x8000355c#64) m
  slot8 : KindSlotPinned 8 (0x800035e0#64) m
  slot9 : KindSlotPinned 9 (0x800031b0#64) m
  slot10 : KindSlotPinned 10 (0x800033c4#64) m

structure AstRegionSpec (m : Mem) (SL : StackLayout) (A : Arena)
    (sret aExpr : Nat) (e : Vsa.While.Expr) (lo hi : Nat) : Prop where
  nodes : ExprIn m lo hi aExpr e
  lo_ram : 0x80000000 ≤ lo

  hi_ram : hi + 8 ≤ 0x100000000
  win : tohostAddr + 16 ≤ lo
  stack_disjoint : hi ≤ SL.lo ∨ SL.hi ≤ lo
  sret_disjoint : hi ≤ sret ∨ sret + 24 ≤ lo
  arena_disjoint : hi ≤ A.lo ∨ A.hi ≤ lo

structure AstRegionPins (m : Mem) (SL : StackLayout) (A : Arena)
    (sret aExpr : Nat) (e : Vsa.While.Expr) : Prop where
  region : ∃ lo hi, AstRegionSpec m SL A sret aExpr e lo hi

def EvalCallFootprint (k : Nat) : Prop := StaticImageByte k

structure EvalCallSupport (m : Mem) (SL : StackLayout) (A : Arena)
    (sp : BitVec 64) : Prop where
  image : StaticImageSupport m SL A
  pins : ∀ m' : Mem,
    (∀ k : Nat, EvalCallFootprint k → m'[k]? = m[k]?) →
      InterpCodeLoaded m' ∧ Value_intLoaded m' ∧ Value_truthyLoaded m' ∧
      IntSlotPinned m' ∧ NBSPins m' ∧ KindTablePins m'

structure EvalGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp sret : BitVec 64) (aExpr : Nat) (e : Vsa.While.Expr) : Prop where
  table : KindTablePins m

  eval_call : EvalCallSupport m SL A sp
  ast : AstRegionPins m SL A sret.toNat aExpr e
  arena_stack : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  arena_vi : A.hi ≤ 0x800027ec ∨ 0x8000282c ≤ A.lo
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  sret_table_disjoint : sret.toNat + 24 ≤ 0x80019f58 ∨ 0x80019f58 + 44 ≤ sret.toNat

  stack_bytes : ∀ k : Nat, SL.lo ≤ k → k < SL.hi →
    ∃ b : BitVec 8, m[k]? = some b

structure EvalEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (a : Addr) (e : Expr)
    (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where

  good : GoodState c.σ

  tick : c.tick < 2

  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)

  a0 : c.σ.regs.get? Register.x10 = some sret

  sret_words : ValueWordsTotal c.σ.mem sret.toNat

  a1 : c.σ.regs.get? Register.x11 = some aEnv

  a2 : c.σ.regs.get? Register.x12 = some aExpr

  ra : c.σ.regs.get? Register.x1 = some r

  ra_align : r.toNat % 4 = 0

  spReg : c.σ.regs.get? Register.x2 = some sp

  stackOK : StackOK SL sp (1088 + 1088)

  stackBudget : StackOK SL sp
    (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)

  expr_bodies : Expr.bodiesBound Vsa.While.perCallBudget e = true

  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget

  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

  mem : c.σ.mem = m0

  code : InterpCodeLoaded c.σ.mem

  expr : ExprRepr c.σ.mem aExpr.toNat e

  store : StoreRepr c.σ.mem N A φf φc st.store

  env_valid : EnvValid st a

  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store

  out : OutRepr c.σ st

  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R

  code_stack_disjoint : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo

  expr_stack_disjoint : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat

  expr_ram : 0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000
  expr_win : tohostAddr + 16 ≤ aExpr.toNat

  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat

  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x800027ec ∨ 0x8000282c ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat

  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat

  vicode_stack_disjoint : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec

  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo

  value_int_code : Value_intLoaded c.σ.mem

  int_slot : IntSlotPinned c.σ.mem

  table_stack_disjoint : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58

  nbs_pins : NBSPins c.σ.mem

  ground : EvalGround c.σ.mem SL A sp sret aExpr.toNat e

  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧ (∃ v, c.σ.regs.get? Register.x18 = some v)

  envset_defined : ∃ v19 v20 v21 : BitVec 64,
    c.σ.regs.get? Register.x19 = some v19 ∧
    c.σ.regs.get? Register.x20 = some v20 ∧
    c.σ.regs.get? Register.x21 = some v21

  envReg : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf a))

  x13_defined : ∃ v, c.σ.regs.get? Register.x13 = some v

structure EvalExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : St) (v : Value)
    (sp r sret : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where

  good : GoodState c.σ

  tick : c.tick < 2

  pc : c.σ.regs.get? Register.PC =
    some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1)

  a0 : c.σ.regs.get? Register.x10 = some sret

  ra : c.σ.regs.get? Register.x1 = some r

  spReg : c.σ.regs.get? Register.x2 = some sp

  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v

  result : ∃ φc', PhiExtends φc φc' nc ∧
    ValueRepr c.σ.mem N φc' sret.toNat v

  store : ∃ (φf' φc' : Addr → Nat),
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store

  out : OutRepr c.σ st'

  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R

  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ c.σ.mem[a]? = m0[a]?

end Vsa.Sim
