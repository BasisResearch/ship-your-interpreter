import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `value_null` is present as in the fixed image. -/
abbrev Value_nullLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x800027ec 0x800027f8 mem

end Vsa.Sim.Code
