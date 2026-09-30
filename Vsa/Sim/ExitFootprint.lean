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

theorem trans {F G : Nat → Prop} {m0 m1 m2 : Mem}
    (h1 : MemFootprint F m0 m1) (h2 : MemFootprint G m1 m2) :
    MemFootprint (fun k => F k ∨ G k) m0 m2 :=
  ⟨fun k hk => (h2.agree k (fun h => hk (Or.inr h))).trans (h1.agree k (fun h => hk (Or.inl h)))⟩

theorem mono {F G : Nat → Prop} {m0 m : Mem} (hFG : ∀ k, F k → G k)
    (h : MemFootprint F m0 m) : MemFootprint G m0 m :=
  ⟨fun k hk => h.agree k (fun hF => hk (hFG k hF))⟩

end MemFootprint

abbrev FootFam := StackLayout → Arena → Nat → Nat → Nat → Prop

def FootFam.le (F G : FootFam) : Prop :=
  ∀ SL A sp sret k, F SL A sp sret k → G SL A sp sret k

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

theorem EvalIHWithM.mono {Extra Extra' : EvalExtraM}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (himp : ∀ N A SL φf φc sp sret m0 c,
      Extra N A SL φf φc sp sret m0 c → Extra' N A SL φf φc sp sret m0 c)
    (h : EvalIHWithM Extra st d env e st' v) : EvalIHWithM Extra' st d env e st' v where
  run := fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    (h.run g N A SL φf φc sp r sret aEnv aExpr m0).conseq (fun _ hp => hp)
      (fun c hp => ⟨hp.result, himp N A SL φf φc sp sret m0 c hp.extra⟩)

abbrev footExtra (F : FootFam) : EvalExtraM :=
  fun _ A SL _ _ sp sret m0 c => MemFootprint (F SL A sp.toNat sret.toNat) m0 c.σ.mem

abbrev EvalIHF (F : FootFam) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (footExtra F) st d env e st' v

namespace EvalIHF

variable {F : FootFam} {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}

theorem mono {G : FootFam} (hFG : FootFam.le F G) (h : EvalIHF F st d env e st' v) :
    EvalIHF G st d env e st' v :=
  EvalIHWithM.mono (fun _ A SL _ _ sp sret _ _ hf =>
    hf.mono (fun k => hFG SL A sp.toNat sret.toNat k)) h

end EvalIHF

end Vsa.Sim
