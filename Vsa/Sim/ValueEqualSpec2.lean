import Vsa.Sim.ValueEqualSpec
import Vsa.Sim.StoreInvariant

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem ld_recon_lt (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (p : Nat)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
      (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p) :
    p < 2 ^ 64 := by have := b7.isLt; omega

theorem read64_lt (m0 : Mem) (a p : Nat) (h : read64 m0 a = some p) : p < 2 ^ 64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hrec⟩ := read64_bytes m0 a p h
  exact ld_recon_lt b0 b1 b2 b3 b4 b5 b6 b7 p hrec

end Vsa.Sim
