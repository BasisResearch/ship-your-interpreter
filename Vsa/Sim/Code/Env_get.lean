import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `env_get` is present as in the fixed image. -/
abbrev Env_getLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80002c10 0x80002cdc mem

end Vsa.Sim.Code
