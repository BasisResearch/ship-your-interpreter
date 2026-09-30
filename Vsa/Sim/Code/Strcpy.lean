import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `strcpy` is present as in the fixed image. -/
abbrev StrcpyLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80006dc4 0x80006ea0 mem

end Vsa.Sim.Code
