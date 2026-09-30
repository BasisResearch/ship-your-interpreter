import Vsa.Sim.SnprintfSpec18
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch15Part04

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem word4_eq_sp (w : BitVec 32) :
    ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8) : BitVec (8 * 4)) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_recon]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

theorem lw_cap_reassemble_sp (w : BitVec 32) :
    (sign_extend (m := 64)
      ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
        (w.extractLsb' 0 8) : BitVec (8 * 4)) : BitVec 64) = sign_extend (m := 64) w :=
  congrArg _ (word4_eq_sp w)

def Pin8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Prop :=
  mem[a]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[a + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[a + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[a + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[a + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[a + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[a + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[a + 7]? = some ((sdData_val v).extractLsb' 56 8)

def Pin4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) : Prop :=
  mem[a]? = some (w.extractLsb' 0 8) ∧
  mem[a + 1]? = some (w.extractLsb' 8 8) ∧
  mem[a + 2]? = some (w.extractLsb' 16 8) ∧
  mem[a + 3]? = some (w.extractLsb' 24 8)

theorem Pin4_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) :
    Pin4 (writeMap4 mem a w) a w :=
  ⟨getElem_writeMap4_0 _ _ _, getElem_writeMap4_1 _ _ _,
   getElem_writeMap4_2 _ _ _, getElem_writeMap4_3 _ _ _⟩

theorem Pin4_frame {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {w : BitVec 32}
    (hf : ∀ k, a ≤ k → k < a + 4 → mem'[k]? = mem[k]?) (h : Pin4 mem a w) : Pin4 mem' a w :=
  ⟨(hf a (by omega) (by omega)).trans h.1,
   (hf (a+1) (by omega) (by omega)).trans h.2.1,
   (hf (a+2) (by omega) (by omega)).trans h.2.2.1,
   (hf (a+3) (by omega) (by omega)).trans h.2.2.2⟩

abbrev NotWrittenSp (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x9 == R) = false ∧
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  NotWrittenMv R

theorem NotWrittenSp.mv {R : Register} (h : NotWrittenSp R) : NotWrittenMv R := h.2.2.2.2.2.2.2.2.2.2

end Vsa.Sim
