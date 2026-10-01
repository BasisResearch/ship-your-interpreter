import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `value_int` is present as in the fixed image. -/
abbrev Value_intLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x8000280c 0x8000281c mem

end Vsa.Sim.Code
