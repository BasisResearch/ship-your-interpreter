import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `exit` is present as in the fixed image. -/
abbrev ExitLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80004764 0x80004790 mem

end Vsa.Sim.Code
