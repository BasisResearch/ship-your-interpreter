import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `interp_run` is present as in the fixed image. -/
abbrev Interp_runLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x800043ec 0x80004588 mem

end Vsa.Sim.Code
