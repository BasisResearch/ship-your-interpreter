import VsaIris.Interp.IntOpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

#int_errs div BinOp.div 0x80003f38 0x80019420 0x800037dc 0x80003f5c 0x80003f14 0x80003f58
#int_errs mod BinOp.mod 0x80003bf0 0x80019440 0x80003784 0x80003c14 0x80003bcc 0x80003c10

#ix_seg IntOp.divZero1 : ZeroRun .div 0x80003d14#64 0x80019428#64 by zero_pre 0x800037dc
#ix_piece IntOp.divZero2 from IntOp.divZero1 by zero_post 0x80003d14
theorem IntOp.divZero : ZeroRun .div 0x80003d14#64 0x80019428#64 := IntOp.divZero1 IntOp.divZero2

#ix_seg IntOp.modZero1 : ZeroRun .mod 0x80003bc8#64 0x80019448#64 by zero_pre 0x80003784
#ix_piece IntOp.modZero2 from IntOp.modZero1 by zero_post 0x80003bc8
theorem IntOp.modZero : ZeroRun .mod 0x80003bc8#64 0x80019448#64 := IntOp.modZero1 IntOp.modZero2

end VsaIris.Interp
