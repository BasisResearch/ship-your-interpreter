import VsaIris.Vsa.MallocFastSegs
import VsaIris.LocalRun

namespace VsaIris.MallocFast

open Vsa.MemRepr

def imgM (m : Mem) (a : Nat) : BitVec 8 := (m[a]?).getD 0

abbrev roR : List (Nat × BitVec 64) := [(gp, gpV)]

end VsaIris.MallocFast
