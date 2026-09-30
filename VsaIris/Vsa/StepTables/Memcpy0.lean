import VsaIris.Vsa.MemcpyRun
import VsaIris.Vsa.StepGen

namespace VsaIris.Memcpy

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast VsaIris.Sym
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

#step_table memcpy
  0x80006bc8 0x80006cf0

end VsaIris.Memcpy
