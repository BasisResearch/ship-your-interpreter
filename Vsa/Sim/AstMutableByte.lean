import Vsa.RuntimeRepr
import Vsa.Sim.Regions

/-!
Bytes excluded from immutable AST ownership at interpreter entry.

The ELF interval covers its writable sections for the fixed proof binary
(SHA256 b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0).
The remaining intervals are the supplied stack, arena, and initial global
environment, including both arrays through their full capacity.

The memory parameter is the initial snapshot: array bounds remain frozen
when transporting AST reads to later memories. This predicate states only
data separation; it does not assert that execution respects these bounds.
-/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

