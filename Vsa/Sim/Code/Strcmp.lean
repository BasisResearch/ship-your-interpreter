import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `strcmp` is present as in the fixed image. -/
abbrev StrcmpLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80006ea0 0x80006fcc mem

end Vsa.Sim.Code
