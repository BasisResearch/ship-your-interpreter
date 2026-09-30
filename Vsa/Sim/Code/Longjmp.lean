import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `longjmp` is present as in the fixed image. -/
abbrev LongjmpLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x8000703c 0x80007080 mem

end Vsa.Sim.Code
