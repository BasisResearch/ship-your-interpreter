import Vsa.Sim.rows.EnvDefineTailFramed
import Vsa.Sim.AllocOff
import Vsa.Sim.HelperCall
import Vsa.Sim.rows.EnvDefineGrowExact
import Vsa.Sim.rows.EnvDefineScanFramed

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved StackLayout StackOK)
open Vsa.Sim.Code (StrcmpLoaded FixedTextLoaded)
open Vsa.While (Addr Value)

namespace Vsa.Sim

@[simp] private theorem proLine0 : mkLine 0x80002a5c#64 0xfc010113#32 =
    ⟨0x80002a5c#64, 0xfc010113#32, 0x13#8, 0x01#8, 0x01#8, 0xfc#8, .addi, 2, 2, 0, 0xfc0#12⟩ := by rfl
@[simp] private theorem proLine1 : mkLine 0x80002a60#64 0x01313c23#32 =
    ⟨0x80002a60#64, 0x01313c23#32, 0x23#8, 0x3c#8, 0x31#8, 0x01#8, .sd, 0, 2, 19, 0x018#12⟩ := by rfl
@[simp] private theorem proLine2 : mkLine 0x80002a64#64 0x00052983#32 =
    ⟨0x80002a64#64, 0x00052983#32, 0x83#8, 0x29#8, 0x05#8, 0x00#8, .lw, 19, 10, 0, 0x000#12⟩ := by rfl
@[simp] private theorem proLine3 : mkLine 0x80002a68#64 0x03213023#32 =
    ⟨0x80002a68#64, 0x03213023#32, 0x23#8, 0x30#8, 0x21#8, 0x03#8, .sd, 0, 2, 18, 0x020#12⟩ := by rfl
@[simp] private theorem proLine4 : mkLine 0x80002a6c#64 0x01413823#32 =
    ⟨0x80002a6c#64, 0x01413823#32, 0x23#8, 0x38#8, 0x41#8, 0x01#8, .sd, 0, 2, 20, 0x010#12⟩ := by rfl
@[simp] private theorem proLine5 : mkLine 0x80002a70#64 0x01513423#32 =
    ⟨0x80002a70#64, 0x01513423#32, 0x23#8, 0x34#8, 0x51#8, 0x01#8, .sd, 0, 2, 21, 0x008#12⟩ := by rfl
@[simp] private theorem proLine6 : mkLine 0x80002a74#64 0x02113c23#32 =
    ⟨0x80002a74#64, 0x02113c23#32, 0x23#8, 0x3c#8, 0x11#8, 0x02#8, .sd, 0, 2, 1, 0x038#12⟩ := by rfl
@[simp] private theorem proLine7 : mkLine 0x80002a78#64 0x02813823#32 =
    ⟨0x80002a78#64, 0x02813823#32, 0x23#8, 0x38#8, 0x81#8, 0x02#8, .sd, 0, 2, 8, 0x030#12⟩ := by rfl
@[simp] private theorem proLine8 : mkLine 0x80002a7c#64 0x02913423#32 =
    ⟨0x80002a7c#64, 0x02913423#32, 0x23#8, 0x34#8, 0x91#8, 0x02#8, .sd, 0, 2, 9, 0x028#12⟩ := by rfl
@[simp] private theorem proLine9 : mkLine 0x80002a80#64 0x01613023#32 =
    ⟨0x80002a80#64, 0x01613023#32, 0x23#8, 0x30#8, 0x61#8, 0x01#8, .sd, 0, 2, 22, 0x000#12⟩ := by rfl
@[simp] private theorem proLine10 : mkLine 0x80002a84#64 0x00050a13#32 =
    ⟨0x80002a84#64, 0x00050a13#32, 0x13#8, 0x0a#8, 0x05#8, 0x00#8, .addi, 20, 10, 0, 0x000#12⟩ := by rfl
@[simp] private theorem proLine11 : mkLine 0x80002a88#64 0x00058913#32 =
    ⟨0x80002a88#64, 0x00058913#32, 0x13#8, 0x89#8, 0x05#8, 0x00#8, .addi, 18, 11, 0, 0x000#12⟩ := by rfl
@[simp] private theorem proLine12 : mkLine 0x80002a8c#64 0x00060a93#32 =
    ⟨0x80002a8c#64, 0x00060a93#32, 0x93#8, 0x0a#8, 0x06#8, 0x00#8, .addi, 21, 12, 0, 0x000#12⟩ := by rfl

@[simp] private theorem epiLine0 : mkLine 0x80002aec#64 0x03813083#32 =
    ⟨0x80002aec#64, 0x03813083#32, 0x83#8, 0x30#8, 0x81#8, 0x03#8, .ld, 1, 2, 0, 0x038#12⟩ := by rfl
@[simp] private theorem epiLine1 : mkLine 0x80002af0#64 0x03013403#32 =
    ⟨0x80002af0#64, 0x03013403#32, 0x03#8, 0x34#8, 0x01#8, 0x03#8, .ld, 8, 2, 0, 0x030#12⟩ := by rfl
@[simp] private theorem epiLine2 : mkLine 0x80002af4#64 0x02813483#32 =
    ⟨0x80002af4#64, 0x02813483#32, 0x83#8, 0x34#8, 0x81#8, 0x02#8, .ld, 9, 2, 0, 0x028#12⟩ := by rfl
@[simp] private theorem epiLine3 : mkLine 0x80002af8#64 0x02013903#32 =
    ⟨0x80002af8#64, 0x02013903#32, 0x03#8, 0x39#8, 0x01#8, 0x02#8, .ld, 18, 2, 0, 0x020#12⟩ := by rfl
@[simp] private theorem epiLine4 : mkLine 0x80002afc#64 0x01813983#32 =
    ⟨0x80002afc#64, 0x01813983#32, 0x83#8, 0x39#8, 0x81#8, 0x01#8, .ld, 19, 2, 0, 0x018#12⟩ := by rfl
@[simp] private theorem epiLine5 : mkLine 0x80002b00#64 0x01013a03#32 =
    ⟨0x80002b00#64, 0x01013a03#32, 0x03#8, 0x3a#8, 0x01#8, 0x01#8, .ld, 20, 2, 0, 0x010#12⟩ := by rfl
@[simp] private theorem epiLine6 : mkLine 0x80002b04#64 0x00813a83#32 =
    ⟨0x80002b04#64, 0x00813a83#32, 0x83#8, 0x3a#8, 0x81#8, 0x00#8, .ld, 21, 2, 0, 0x008#12⟩ := by rfl
@[simp] private theorem epiLine7 : mkLine 0x80002b08#64 0x00013b03#32 =
    ⟨0x80002b08#64, 0x00013b03#32, 0x03#8, 0x3b#8, 0x01#8, 0x00#8, .ld, 22, 2, 0, 0x000#12⟩ := by rfl
@[simp] private theorem epiLine8 : mkLine 0x80002b0c#64 0x04010113#32 =
    ⟨0x80002b0c#64, 0x04010113#32, 0x13#8, 0x01#8, 0x01#8, 0x04#8, .addi, 2, 2, 0, 0x040#12⟩ := by rfl

@[simp] private theorem sext0_64 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
@[simp] private theorem sext8_64 : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
@[simp] private theorem sext16_64 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
@[simp] private theorem sext24_64 : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
@[simp] private theorem sext32_64 : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide
@[simp] private theorem sext40_64 : (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 := by decide
@[simp] private theorem sext48_64 : (sign_extend (m := 64) (0x030#12) : BitVec 64).toNat = 48 := by decide
@[simp] private theorem sext56_64 : (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 := by decide

def envDefinePrologueL (sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2 : BitVec 64) : GRegs :=
  [(2, sp), (19, s3), (10, a0), (18, s2), (20, s4), (21, s5), (1, ra), (8, s0), (9, s1),
   (22, s6), (11, a1), (12, a2)]

def envDefineSaved (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) :
    (R : Register) → Option (RegisterType R) :=
  fun R => if h : R = Register.x1 then some (h ▸ r) else g R

@[simp] theorem envDefineSaved_x1 (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) :
    envDefineSaved g r Register.x1 = some r := by
  simp [envDefineSaved]

end Vsa.Sim
