import Vsa.Sim.EvalSimCommon
import Vsa.Sim.StoreInvariant

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

def EvalExitD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop :=
  EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c ∧
  MemExtends m0 c.σ.mem ∧
  ValueWordsTotal c.σ.mem sret.toNat ∧
  ∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store

structure ReturnedWith (Result Extra : Config → Prop) (c : Config) : Prop where
  result : Result c
  extra : Extra c

end Vsa.Sim
