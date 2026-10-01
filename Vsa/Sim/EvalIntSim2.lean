import Vsa.Sim.EvalSimCommon
import Vsa.Sim.DecodeNF
import Vsa.Sim.DivLoops

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

theorem kind_bytes {m : Mem} {a k : Nat} (hk : read32 m a = some k) :
    ∃ b0 b1 b2 b3 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k :=
  read32_bytes m a k hk

theorem zext_kind (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 128)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (zero_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k := by
  have hlt : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat = k := by
    rw [word_toNat_recon]; exact hrec
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hlt,
    Nat.mod_eq_of_lt (show k < 2^64 by omega)]

theorem read64_writeMap8_disjoint_ee (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

end Vsa.Sim
