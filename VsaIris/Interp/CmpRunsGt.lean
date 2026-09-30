import VsaIris.Interp.CmpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

#cmp_runs gt BinOp.gt 0x80003aec 0x800195d8

end VsaIris.Interp
