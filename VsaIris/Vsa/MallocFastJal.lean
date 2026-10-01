import VsaIris.Vsa.Tools
import VsaIris.Vsa.JalSite

namespace VsaIris.MallocFast

open Vsa.Sim VsaIris.Inst

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jal_exec_80004874 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004874 [0xef#8, 0x00#8, 0x40#8, 0x7f#8], live p.1) :
    JalExec (vsaModel live) 0x80004874 [0xef#8, 0x00#8, 0x40#8, 0x7f#8] 0x80005068#64 :=
  JalSite.exec (S := ⟨0x80004874, 0xef#8, 0x00#8, 0x40#8, 0x7f#8, 0x7f4000ef#32, 0x0007f4#21, 0x80005068#64⟩)
    ⟨by decide, by decide, fun σ h1 h2 h3 => Vsa.Sim.decodeW (w := 0x7f4000ef#32) σ h1 h2 h3,
     by decide, by decide, by decide, by decide, by decide⟩ live hlive

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jal_exec_80004c10 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8], live p.1) :
    JalExec (vsaModel live) 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8] 0x80005070#64 :=
  JalSite.exec (S := ⟨0x80004c10, 0xef#8, 0x00#8, 0x00#8, 0x46#8, 0x460000ef#32, 0x000460#21, 0x80005070#64⟩)
    ⟨by decide, by decide, fun σ h1 h2 h3 => Vsa.Sim.decodeW (w := 0x460000ef#32) σ h1 h2 h3,
     by decide, by decide, by decide, by decide, by decide⟩ live hlive

end VsaIris.MallocFast
