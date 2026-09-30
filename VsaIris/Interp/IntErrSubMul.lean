import VsaIris.Interp.IntOpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

#int_errs sub BinOp.sub 0x80003b7c 0x800196e8 0x800038e0 0x80003eec 0x80003ec4 0x80003b9c
#int_errs mul BinOp.mul 0x80003c5c 0x80019418 0x80003834 0x80003c80 0x80003c38 0x80003c7c

end VsaIris.Interp
