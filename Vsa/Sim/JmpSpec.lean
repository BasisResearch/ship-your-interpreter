import Vsa.Sim.JmpSites
import Vsa.Sim.Code.Interp_run
import Vsa.Sim.ObsAvoid

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (LongjmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev NotWrittenJmp (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x9 == R) = false ∧
  (Register.x10 == R) = false ∧
  (Register.x18 == R) = false ∧ (Register.x19 == R) = false ∧
  (Register.x20 == R) = false ∧ (Register.x21 == R) = false ∧
  (Register.x22 == R) = false ∧ (Register.x23 == R) = false ∧
  (Register.x24 == R) = false ∧ (Register.x25 == R) = false ∧
  (Register.x26 == R) = false ∧ (Register.x27 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenJmp.pc {R : Register} (h : NotWrittenJmp R) : (Register.PC == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

structure WinRAM (jb : BitVec 64) : Prop where
  lo : 0x80000000 ≤ jb.toNat
  hi : jb.toNat + 112 ≤ 0x100000000
  win : tohostAddr + 16 ≤ jb.toNat
  align : jb.toNat % 8 = 0

  code_sj : jb.toNat + 112 ≤ 0x80006ffc ∨ 0x8000703c ≤ jb.toNat

  code_lj : jb.toNat + 112 ≤ 0x8000703c ∨ 0x80007080 ≤ jb.toNat

theorem sext64_id_jmp (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d
