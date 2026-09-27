import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.EnvCallBridge

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

@[simp] private theorem updLine0 : mkLine 0x80002ac0#64 0x010a3783#32 =
    ⟨0x80002ac0#64, 0x010a3783#32, 0x83#8, 0x37#8, 0x0a#8, 0x01#8,
      .ld, 15, 20, 0, 0x010#12⟩ := by rfl
@[simp] private theorem updLine1 : mkLine 0x80002ac4#64 0x00141713#32 =
    ⟨0x80002ac4#64, 0x00141713#32, 0x13#8, 0x17#8, 0x14#8, 0x00#8,
      .slli, 14, 8, 0, 0x001#12⟩ := by rfl
@[simp] private theorem updLine2 : mkLine 0x80002ac8#64 0x000ab583#32 =
    ⟨0x80002ac8#64, 0x000ab583#32, 0x83#8, 0xb5#8, 0x0a#8, 0x00#8,
      .ld, 11, 21, 0, 0x000#12⟩ := by rfl
@[simp] private theorem updLine3 : mkLine 0x80002acc#64 0x008ab603#32 =
    ⟨0x80002acc#64, 0x008ab603#32, 0x03#8, 0xb6#8, 0x8a#8, 0x00#8,
      .ld, 12, 21, 0, 0x008#12⟩ := by rfl
@[simp] private theorem updLine4 : mkLine 0x80002ad0#64 0x010ab683#32 =
    ⟨0x80002ad0#64, 0x010ab683#32, 0x83#8, 0xb6#8, 0x0a#8, 0x01#8,
      .ld, 13, 21, 0, 0x010#12⟩ := by rfl
@[simp] private theorem updLine5 : mkLine 0x80002ad4#64 0x00870733#32 =
    ⟨0x80002ad4#64, 0x00870733#32, 0x33#8, 0x07#8, 0x87#8, 0x00#8,
      .add, 14, 14, 8, 0x000#12⟩ := by rfl
@[simp] private theorem updLine6 : mkLine 0x80002ad8#64 0x00371713#32 =
    ⟨0x80002ad8#64, 0x00371713#32, 0x13#8, 0x17#8, 0x37#8, 0x00#8,
      .slli, 14, 14, 0, 0x003#12⟩ := by rfl
@[simp] private theorem updLine7 : mkLine 0x80002adc#64 0x00e787b3#32 =
    ⟨0x80002adc#64, 0x00e787b3#32, 0xb3#8, 0x87#8, 0xe7#8, 0x00#8,
      .add, 15, 15, 14, 0x000#12⟩ := by rfl
@[simp] private theorem updLine8 : mkLine 0x80002ae0#64 0x00b7b023#32 =
    ⟨0x80002ae0#64, 0x00b7b023#32, 0x23#8, 0xb0#8, 0xb7#8, 0x00#8,
      .sd, 0, 15, 11, 0x000#12⟩ := by rfl
@[simp] private theorem updLine9 : mkLine 0x80002ae4#64 0x00c7b423#32 =
    ⟨0x80002ae4#64, 0x00c7b423#32, 0x23#8, 0xb4#8, 0xc7#8, 0x00#8,
      .sd, 0, 15, 12, 0x008#12⟩ := by rfl
@[simp] private theorem updLine10 : mkLine 0x80002ae8#64 0x00d7b823#32 =
    ⟨0x80002ae8#64, 0x00d7b823#32, 0x23#8, 0xb8#8, 0xd7#8, 0x00#8,
      .sd, 0, 15, 13, 0x010#12⟩ := by rfl

end Vsa.Sim
