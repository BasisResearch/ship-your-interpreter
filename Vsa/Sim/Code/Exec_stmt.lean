import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

/-- The code of `exec_stmt` is present as in the fixed image. -/
abbrev Exec_stmtLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop := CodeLoaded 0x80003fe0 0x80004308 mem

end Vsa.Sim.Code
