import VsaIris.Vsa.MallocFastSegs
import VsaIris.LocalRun

/-!
# Shared definitions of the allocator's runs

The total byte image of a memory (`imgM`) and the read-only register of every
allocator run (`roR`: `gp`). Both the fast-path chains (`MallocFastRun`) and
the symbolic layer (`SymRun`) use them. This module sits below the
allocator's spec modules (`MallocRun`, `Malloc`), so the generated step table
does not rebuild when a spec changes.
-/

namespace VsaIris.MallocFast

open Vsa.MemRepr

/-- The total byte image of a memory. -/
def imgM (m : Mem) (a : Nat) : BitVec 8 := (m[a]?).getD 0

/-- The read-only registers of the allocator's runs. -/
abbrev roR : List (Nat × BitVec 64) := [(gp, gpV)]

end VsaIris.MallocFast
