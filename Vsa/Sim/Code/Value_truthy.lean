import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `value_truthy` is present as in the fixed image. -/
abbrev Value_truthyLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x8000282c 0x8000285c mem

end Vsa.Sim.Code
