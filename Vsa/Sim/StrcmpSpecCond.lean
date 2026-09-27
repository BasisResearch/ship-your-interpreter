import Vsa.Sim.StrcmpSpecW3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

structure StrcmpWSlack (p : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 8 ≤ 0x100000000
  nowrap : p.toNat + len + 8 < 2^64
  code : p.toNat + len + 8 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ p.toNat
  htif : p.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat

end Vsa.Sim
