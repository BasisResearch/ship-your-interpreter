import VsaIris.Interp.CmpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

#cmp_runs ge BinOp.ge 0x800036c8 0x80019380

end VsaIris.Interp
