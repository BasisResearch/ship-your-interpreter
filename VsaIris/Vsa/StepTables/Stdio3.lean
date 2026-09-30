import VsaIris.Vsa.StepGen

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

#step_table stdio
  0x8000c128 0x8000c140  0x8000c2c0 0x8000c2d0

end VsaIris.Sym
