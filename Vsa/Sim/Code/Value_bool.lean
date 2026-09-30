import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `value_bool` is present as in the fixed image. -/
abbrev Value_boolLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x800027f8 0x8000280c mem

end Vsa.Sim.Code
