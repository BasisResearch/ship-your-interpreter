import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `memcpy` is present as in the fixed image. -/
abbrev MemcpyLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80006bc8 0x80006cf0 mem

end Vsa.Sim.Code
