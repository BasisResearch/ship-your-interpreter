import Vsa.Sim.ValuePayloadCoverage
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.PinW
import Vsa.Sim.BlockTactics2
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.ExitFootprint
import Vsa.Sim.DecodeNF
import Vsa.While.Cost

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem sdData_sext_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 0 8 = b0 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 8 8 = b1 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 16 8 = b2 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 24 8 = b3 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 32 8 = b4 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 40 8 = b5 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 48 8 = b6 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 56 8 = b7 := by
  rw [sdData_val_id, sext_full]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
     rw [word8_toNat_recon]; omega)

end Vsa.Sim
