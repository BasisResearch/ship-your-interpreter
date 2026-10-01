import Vsa.Sim.ValueSites
import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Triple
import Vsa.Sim.ObsBasics

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

theorem getElem_insert_ne (mem : Std.ExtHashMap Nat (BitVec 8)) (i j : Nat) (v : BitVec 8)
    (hne : (j == i) = false) : (mem.insert j v)[i]? = mem[i]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]

theorem getElem_insert_self (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (v : BitVec 8) :
    (mem.insert i v)[i]? = some v := by
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by simp)]

theorem getElem_writeMap4_0 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a]? = some (d.extractLsb' 0 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap4_1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 1]? = some (d.extractLsb' 8 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_self]
theorem getElem_writeMap4_2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 2]? = some (d.extractLsb' 16 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap4_3 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap4]
  rw [getElem_insert_self]

theorem byte_lane (n m m' : Nat) (h : m * 256 = m') : n / m % 256 + 256 * (n / m') = n / m := by
  subst h; rw [← Nat.div_div_eq_div_mul]; exact Nat.mod_add_div _ _

theorem byte_top (n m k : Nat) (h : n < k) (hk : k = m * 256) : n / m % 256 = n / m :=
  Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (hk ▸ h))

theorem read32_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    read32 (writeMap4 mem a d) a = some d.toNat := by
  have e0 := getElem_writeMap4_0 mem a d
  have e1 := getElem_writeMap4_1 mem a d
  have e2 := getElem_writeMap4_2 mem a d
  have e3 := getElem_writeMap4_3 mem a d
  simp only [read32, readLE, e0, e1, e2, e3, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 32 := by have := d.isLt; simpa using this
  rw [Nat.mul_zero, Nat.add_zero, byte_top _ 16777216 _ hd rfl,
    byte_lane _ 65536 16777216 rfl, byte_lane _ 256 65536 rfl, Nat.mod_add_div]

theorem getElem_writeMap8_0 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a]? = some (d.extractLsb' 0 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 1]? = some (d.extractLsb' 8 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 2]? = some (d.extractLsb' 16 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_3 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 4]? = some (d.extractLsb' 32 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_5 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 5]? = some (d.extractLsb' 40 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_6 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 6]? = some (d.extractLsb' 48 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]
theorem getElem_writeMap8_7 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 7]? = some (d.extractLsb' 56 8) := by
  simp only [writeMap8]
  rw [getElem_insert_self]

theorem read64_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read64 (writeMap8 mem a d) a = some d.toNat := by
  have e0 := getElem_writeMap8_0 mem a d
  have e1 := getElem_writeMap8_1 mem a d
  have e2 := getElem_writeMap8_2 mem a d
  have e3 := getElem_writeMap8_3 mem a d
  have e4 := getElem_writeMap8_4 mem a d
  have e5 := getElem_writeMap8_5 mem a d
  have e6 := getElem_writeMap8_6 mem a d
  have e7 := getElem_writeMap8_7 mem a d
  simp only [read64, readLE, e0, e1, e2, e3, e4, e5, e6, e7, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 64 := by have := d.isLt; simpa using this
  rw [Nat.mul_zero, Nat.add_zero, byte_top _ 72057594037927936 _ hd rfl,
    byte_lane _ 281474976710656 72057594037927936 rfl, byte_lane _ 1099511627776 281474976710656 rfl,
    byte_lane _ 4294967296 1099511627776 rfl, byte_lane _ 16777216 4294967296 rfl,
    byte_lane _ 65536 16777216 rfl, byte_lane _ 256 65536 rfl, Nat.mod_add_div]

theorem getElem_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 k : Nat)
    (d : BitVec (8 * 8)) (hk : k < a8 ∨ a8 + 8 ≤ k) :
    (writeMap8 mem a8 d)[k]? = mem[k]? := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

theorem getElem_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 k : Nat)
    (d : BitVec (8 * 4)) (hk : k < a4 ∨ a4 + 4 ≤ k) :
    (writeMap4 mem a4 d)[k]? = mem[k]? := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

theorem getElem_writeMap2_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a2 k : Nat)
    (d : BitVec (8 * 2)) (hk : k < a2 ∨ a2 + 2 ≤ k) :
    ((mem.insert a2 (d.extractLsb' 0 8)).insert (a2 + 1) (d.extractLsb' 8 8))[k]? = mem[k]? := by
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

theorem swData_toNat (v : BitVec 64) : (swData v).toNat = v.toNat % 2 ^ 32 := by
  simp only [swData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftRight_zero]
  have key : ∀ W : Nat, (2:Nat) ^ W = 2 ^ 32 → (BitVec.ofNat W v.toNat).toNat = v.toNat % 2 ^ 32 := by
    intro W hW; rw [BitVec.toNat_ofNat, hW]
  exact key _ (by decide)

theorem sdData_toNat (v : BitVec 64) : (sdData_val v).toNat = v.toNat := by
  simp only [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftRight_zero]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have key : ∀ W : Nat, (2:Nat) ^ W = 2 ^ 64 → (BitVec.ofNat W v.toNat).toNat = v.toNat := by
    intro W hW; rw [BitVec.toNat_ofNat, hW, Nat.mod_eq_of_lt hv]
  exact key _ (by decide)

theorem obs_store_other_val {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5).trans hσ)

end Vsa.Sim
