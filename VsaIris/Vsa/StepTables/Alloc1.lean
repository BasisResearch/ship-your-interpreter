import VsaIris.Vsa.StepGen

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

#step_table alloc
  0x80005464 0x800058c0  0x8000696c 0x800069a8  0x800069bc 0x800069d0  0x800069f0 0x80006a04
  0x80006a24 0x80006aec  0x80006fe0 0x80006fe4  0x80006ff8 0x80006ffc  0x8000722c 0x8000731c
  0x80007350 0x80007654

end VsaIris.Sym
