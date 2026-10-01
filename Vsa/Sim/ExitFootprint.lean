import Vsa.Sim.EvalRecCommon
import Vsa.Sim.BlockAdapter

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

structure MemFootprint (F : Nat → Prop) (m0 m : Mem) : Prop where
  agree : ∀ k, ¬ F k → m[k]? = m0[k]?

namespace MemFootprint

end MemFootprint

abbrev FootFam := StackLayout → Arena → Nat → Nat → Nat → Prop

abbrev EvalExtraM := NativeAddrs → Arena → StackLayout →
  (Addr → Nat) → (Addr → Nat) → BitVec 64 → BitVec 64 → Mem → Config → Prop

structure EvalIHWithM (Extra : EvalExtraM)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple
      (EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0)
      (ReturnedWith
        (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
          st' v sp r sret m0)
        (Extra N A SL φf φc sp sret m0))

abbrev footExtra (F : FootFam) : EvalExtraM :=
  fun _ A SL _ _ sp sret m0 c => MemFootprint (F SL A sp.toNat sret.toNat) m0 c.σ.mem

abbrev EvalIHF (F : FootFam) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (footExtra F) st d env e st' v

namespace EvalIHF

variable {F : FootFam} {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}

end EvalIHF

end Vsa.Sim
