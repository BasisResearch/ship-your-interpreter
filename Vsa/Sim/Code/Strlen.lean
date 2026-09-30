import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `strlen` is present as in the fixed image. -/
abbrev StrlenLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80006cf0 0x80006dc4 mem

end Vsa.Sim.Code
