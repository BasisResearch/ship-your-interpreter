import VsaIris.Vsa.StepGen

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

#step_table alloc
  0x80000118 0x8000013c  0x80000158 0x80000180  0x80004790 0x80004acc  0x80004bc8 0x80004eb0
  0x80004f1c 0x80004f5c  0x80004f70 0x80004f8c  0x80004fa0 0x80004fe0  0x80005024 0x80005078
  0x8000527c 0x80005464

end VsaIris.Sym
