import VsaIris.Vsa.StepGen

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

#step_table stdio
  0x8000b088 0x8000b0a0  0x8000b32c 0x8000b368  0x8000b3b4 0x8000b450  0x8000b6a4 0x8000b6b0
  0x8000b8c4 0x8000b8d8  0x8000b8f8 0x8000b958

end VsaIris.Sym
