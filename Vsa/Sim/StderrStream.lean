import Vsa.Sim.ExitRuntimeData

open Vsa.MemRepr

namespace Vsa.Sim

structure StderrStream (m : Mem) : Prop where
  base : read64 m (exitStderr + 24) = some 0
  writer : read64 m (exitStderr + 64) = some consoleSwrite

end Vsa.Sim
