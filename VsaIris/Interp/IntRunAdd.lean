import VsaIris.OmegaHint
import VsaIris.Interp.IntOpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

theorem IntOp.addRun : IntOpRun .add (fun _ _ => True) (fun a b => wrap64 (a + b)) 0x800038d4#64 := by
  int_pre 0x800038d4
  int_post toInt_add_wrap

theorem IntOp.subRun : IntOpRun .sub (fun _ _ => True) (fun a b => wrap64 (a - b)) 0x8000391c#64 := by
  int_pre 0x8000391c
  int_post toInt_sub_wrap

theorem epi_800038d8 : EpiRun 0x800038d8#64 := by epi_run
theorem epi_80003920 : EpiRun 0x80003920#64 := by epi_run

end VsaIris.Interp
