import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `_exit` is present as in the fixed image. -/
abbrev _exitLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80000180 0x80000198 mem

end Vsa.Sim.Code
