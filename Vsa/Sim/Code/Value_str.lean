import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `value_str` is present as in the fixed image. -/
abbrev Value_strLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x8000281c 0x8000282c mem

end Vsa.Sim.Code
