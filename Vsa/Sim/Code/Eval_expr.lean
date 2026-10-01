import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `eval_expr` is present as in the fixed image. -/
abbrev Eval_exprLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80003164 0x80003fe0 mem

end Vsa.Sim.Code
