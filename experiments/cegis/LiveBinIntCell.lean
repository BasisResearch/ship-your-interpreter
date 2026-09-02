import Vsa.Sim.rows.BinDispatchRow
/-! LIVE VALUE TEST target: the CURRENT still-false `BinIntCellResid` (the wave-48g
interlock's target), re-exposed as a fully-∀-quantified hermetic Prop (mirrors
`SkelHIAdd`, `AssemblySkeleton.lean:81`).  `cegis_cure.py` runs against THIS and
its top candidates are compared to the recorded wave-48g recipe (observations
`bin-cures-interlock-atomic-wave`).  NOTHING is amended — analysis only. -/
open LeanRV64DExecutable Sail Vsa Register
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim
open Vsa.Machine (Config)
open Vsa.Refine (Layout)

namespace CegisLive

/-- The `.add` int-cell residual, ∀-closed exactly as `SkelHIAdd` closes it. -/
def BinIntLive : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem),
    BinIntCellResid .add Vsa.Sim.AddResid g N A SL φf φc st st' st'' el er a b
      sp r sret aExpr m0

end CegisLive
