import VsaIris.Vsa.StepGen

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

#step_table stdio
  0x80006fd0 0x80006fe4  0x80006ff8 0x80006ffc  0x800070a8 0x800070e4  0x8000717c 0x800071a0
  0x8000a884 0x8000aa48  0x8000aab4 0x8000ab04  0x8000ab34 0x8000ac44  0x8000ac60 0x8000acc8
  0x8000ace8 0x8000acf0  0x8000af44 0x8000af78  0x8000afa8 0x8000afac  0x8000afe0 0x8000afe8

end VsaIris.Sym
