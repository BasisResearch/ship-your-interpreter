import Vsa.Sim.ValueSites
import Vsa.Sim.Muldi3Spec
import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Triple

/-!
# Layer 3 — total-correctness specs for the `value_*` leaf constructors,
#           connected to the Layer-2 representation relation `ValueRepr`

This is the **first** Layer-2↔Layer-3 integration: the per-site observational steps
(`Vsa/Sim/ValueSites.lean`) compose into `Vsa.Logic.Triple`s whose postconditions
assert `Vsa.RuntimeRepr.ValueRepr m' N φc buf v` for the written buffer — the exact
shape every `env_*`/interp spec will use.

## The ValueRepr-connection pattern

The store instructions land the machine at `sigma3_store σ pc (writeMap{4,8} …)`.
Since `afterNextPC`/`afterPrelude` are register-only, that memory is
`writeMap{4,8} σ.mem addr d`. The bridge to `ValueRepr` is the read-back lemma
`readLE_writeMap{4,8}`: the little-endian `read32`/`read64` of the freshly-written
window returns the stored value's `toNat`. `ValueRepr .null` pins only
`read32 = 0`; `.int` pins `read32 = 2` and `readI64 = n`; the untouched payload
bytes stay unconstrained, exactly as `ValueRepr`'s per-variant shape permits.
-/

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

/-! ## Memory read-back over the store write-maps

`writeMap4 mem a d` inserts `d`'s four LE bytes at `a, a+1, a+2, a+3`; reading the
same four bytes back with `readLE _ a 4` recovers `d.toNat`. Likewise width 8. The
read-over-write disequalities are `omega`-trivial (the four/eight keys are distinct
and read in order). -/

/-- Read-over-write helper: `(mem.insert j v)[i]? = mem[i]?` when `j ≠ i`
(as a Bool disequality `(j == i) = false`). -/
theorem getElem_insert_ne (mem : Std.ExtHashMap Nat (BitVec 8)) (i j : Nat) (v : BitVec 8)
    (hne : (j == i) = false) : (mem.insert j v)[i]? = mem[i]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]

/-- Read-over-write helper: `(mem.insert i v)[i]? = some v`. -/
theorem getElem_insert_self (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (v : BitVec 8) :
    (mem.insert i v)[i]? = some v := by
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by simp)]

/-- The four bytes of `writeMap4 mem a d`, read back individually. -/
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

/-- `read32` of a freshly `writeMap4`-written window recovers `d.toNat`. -/
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
  omega

/-- The eight bytes of `writeMap8 mem a d`, read back individually. -/
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

/-- `read64` of a freshly `writeMap8`-written window recovers `d.toNat`. -/
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
  omega

/-- A single byte read at `k` disjoint from the `writeMap8`-window `[a8, a8+8)`
passes through to `mem`. -/
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

/-- A single byte read at `k` disjoint from the `writeMap4`-window `[a4, a4+4)`
passes through to `mem`. -/
theorem getElem_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 k : Nat)
    (d : BitVec (8 * 4)) (hk : k < a4 ∨ a4 + 4 ≤ k) :
    (writeMap4 mem a4 d)[k]? = mem[k]? := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

/-- `read32` at `a` is unaffected by a `writeMap8` whose window `[a8, a8+8)` is
disjoint from `[a, a+4)`. -/
theorem read32_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 4 ≤ a8 ∨ a8 + 8 ≤ a) :
    read32 (writeMap8 mem a8 d) a = read32 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  simp only [read32, readLE, g0, g1, g2, g3]

/-- `read32` at `a` is unaffected by a `writeMap4` whose window `[a4, a4+4)` is
disjoint from `[a, a+4)`. -/
theorem read32_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a a4 : Nat)
    (d : BitVec (8 * 4)) (hdis : a + 4 ≤ a4 ∨ a4 + 4 ≤ a) :
    read32 (writeMap4 mem a4 d) a = read32 mem a := by
  have g0 := getElem_writeMap4_disjoint mem a4 a d (by omega)
  have g1 := getElem_writeMap4_disjoint mem a4 (a + 1) d (by omega)
  have g2 := getElem_writeMap4_disjoint mem a4 (a + 2) d (by omega)
  have g3 := getElem_writeMap4_disjoint mem a4 (a + 3) d (by omega)
  simp only [read32, readLE, g0, g1, g2, g3]

/-- `read64` at `a` is unaffected by a `writeMap4` whose window `[a4, a4+4)` is
disjoint from `[a, a+8)`. -/
theorem read64_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a a4 : Nat)
    (d : BitVec (8 * 4)) (hdis : a + 8 ≤ a4 ∨ a4 + 4 ≤ a) :
    read64 (writeMap4 mem a4 d) a = read64 mem a := by
  have g0 := getElem_writeMap4_disjoint mem a4 a d (by omega)
  have g1 := getElem_writeMap4_disjoint mem a4 (a + 1) d (by omega)
  have g2 := getElem_writeMap4_disjoint mem a4 (a + 2) d (by omega)
  have g3 := getElem_writeMap4_disjoint mem a4 (a + 3) d (by omega)
  have g4 := getElem_writeMap4_disjoint mem a4 (a + 4) d (by omega)
  have g5 := getElem_writeMap4_disjoint mem a4 (a + 5) d (by omega)
  have g6 := getElem_writeMap4_disjoint mem a4 (a + 6) d (by omega)
  have g7 := getElem_writeMap4_disjoint mem a4 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

/-! ## `swData`/`sdData_val` value facts

The stored slice `swData v` (low 4 bytes) / `sdData_val v` (low 8 bytes) reads back
(as `.toNat`) as `v.toNat % 2^32` / `v.toNat`. For the small kind tags (0,2,3) and
the full 8-byte payload these give the exact `ValueRepr`-required numbers. -/

/-- `(swData v).toNat = v.toNat % 2^32`. -/
theorem swData_toNat (v : BitVec 64) : (swData v).toNat = v.toNat % 2 ^ 32 := by
  simp only [swData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftRight_zero]
  have key : ∀ W : Nat, (2:Nat) ^ W = 2 ^ 32 → (BitVec.ofNat W v.toNat).toNat = v.toNat % 2 ^ 32 := by
    intro W hW; rw [BitVec.toNat_ofNat, hW]
  exact key _ (by decide)

/-- `(sdData_val v).toNat = v.toNat`. -/
theorem sdData_toNat (v : BitVec 64) : (sdData_val v).toNat = v.toNat := by
  simp only [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftRight_zero]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have key : ∀ W : Nat, (2:Nat) ^ W = 2 ^ 64 → (BitVec.ofNat W v.toNat).toNat = v.toNat := by
    intro W hW; rw [BitVec.toNat_ofNat, hW, Nat.mod_eq_of_lt hv]
  exact key _ (by decide)

/-! ## STORE-observation consumers (local; mirror `MemcpySpec`'s `obs_store_*`) -/

theorem post_store_pc_val (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) :
    (sigmaPost_store σ pc vminstret m').regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg,
    reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_store_pc_val {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_store_pc_val σ pc vm m')

theorem obs_store_other_val {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5).trans hσ)

theorem obs_store_minstret_val {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- Ghost-frame disequality set for the value store constructors: the scratch
GPRs `x11`/`x15` (written by `li a5,k` / `snez a1,a1`) plus the noise registers.
The stores write only memory; the `ret` writes PC/nextPC. -/
abbrev NotWrittenV (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenV.x15 {R : Register} (h : NotWrittenV R) : (Register.x15 == R) = false := h.2.1

theorem frame_store_v {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenV R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

theorem frame_jr_v {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenV R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-- ALU frame step for the value constructors: `R` outside the write-set reads
back to `σ`. The `li a5,k` writes `x15`; `NotWrittenV` already excludes `x15`, so
the `rd ≠ R` disequality is `hR.x15` (all `li`/`snez` here write `x15` — except
`value_bool`'s `snez a1,a1` writes `x11`, also excluded). -/
theorem frame_alu_v {σ' σ : MState} {pc vm : BitVec 64} {v : RegisterType Register.x15}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm Register.x15 v)) (R : Register)
    (hR : NotWrittenV R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, hx15, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm Register.x15 v R hmi hpc hx15 hnpc hmii

/-- ALU frame step for `value_bool`'s `snez a1,a1` (writes `x11`, excluded by
`NotWrittenV.x11`). -/
theorem frame_alu_snez {σ' σ : MState} {pc vm : BitVec 64} {v : RegisterType Register.x11}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm Register.x11 v)) (R : Register)
    (hR : NotWrittenV R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hx11, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm Register.x11 v R hmi hpc hx11 hnpc hmii

/-! ## `value_null_spec` — the flagship ValueRepr connection

`value_null` writes the 24-byte buffer at `a0` (VAL_NULL tag at `+0`, zeroed
payload at `+8`) and returns via `ra`. The postcondition asserts
`ValueRepr m' N φc buf .null` — which pins only `read32 m' buf = 0`.

Region side-conditions on `buf` (`NullRegion`): the 8-aligned 24-byte buffer lives
in RAM, above the HTIF window, disjoint from the `value_null` code. -/

/-- Buffer region facts for a 24-byte `Value` write at `buf` (8-aligned RAM, above
the HTIF window). `+0` (tag, 4-aligned) and `+8` (payload, 8-aligned) both land in
the writable region. -/
structure NullRegion (buf : BitVec 64) : Prop where
  align : buf.toNat % 8 = 0
  lo : 0x80000000 ≤ buf.toNat
  hi : buf.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ buf.toNat
  -- the buffer is disjoint from the `value_null` code `[0x800027ec, 0x800027f8)`
  code_disjoint : buf.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ buf.toNat

/-- `Value_nullLoaded` survives a `writeMap4` at a window disjoint from the code
`[0x800027ec, 0x800027f8)`. -/
theorem loaded_null_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 : Nat) (d : BitVec (8 * 4))
    (hdis : a4 + 4 ≤ 0x800027ec ∨ 0x800027f8 ≤ a4) (h : Value_nullLoaded mem) :
    Value_nullLoaded (writeMap4 mem a4 d) := by
  simp only [Value_nullLoaded, value_nullChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-- `Value_nullLoaded` survives a `writeMap8` at a window disjoint from the code. -/
theorem loaded_null_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x800027ec ∨ 0x800027f8 ≤ a8) (h : Value_nullLoaded mem) :
    Value_nullLoaded (writeMap8 mem a8 d) := by
  simp only [Value_nullLoaded, value_nullChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-- The store target `buf + sext 0x000 = buf`, no wrap. -/
theorem null_tag_addr (buf : BitVec 64) :
    (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
  rw [BitVec.add_zero]

/-- The payload store target `buf + sext 0x008 = buf + 8`, no wrap. -/
theorem null_pay_addr (buf : BitVec 64) (hr : NullRegion buf) :
    (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hr.hi
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Precondition of `value_null`: at entry `0x800027ec` with buffer `buf` in `a0`,
return address `r` in `x1` (4-aligned target), `mem = m0`, and the region facts. -/
def null_pre (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_nullLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800027ec#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  NullRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- Postcondition of `value_null`: PC at the (bit-0-cleared) return target,
`x1 = r`, `x10 = buf`, and — the pilot Layer-2 assertion —
`ValueRepr m' N φc buf .null` for the post-memory `m'` (any `N`, `φc`; `.null`
uses neither). Buffer bytes outside `[buf, buf+16)` are unchanged. -/
def null_post (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  ValueRepr c.σ.mem N φc buf.toNat .null ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- **`value_null` total-correctness spec.** From `null_pre` the machine runs to
`null_post`: the returned buffer represents the spec value `.null`
(`ValueRepr … buf .null`, i.e. `read32 = 0`). This is the first Layer-2↔Layer-3
integration — the shape every `env_*`/interp spec reuses. -/
theorem value_null_spec (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (null_pre g buf r m0) (null_post g buf r N φc) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hreg, hrettgt, hframe⟩ := hpre
  -- region bounds for the two stores
  have htag := null_tag_addr buf
  have hpay := null_pay_addr buf hreg
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x800027ec: sw zero,0(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800027ec c.σ c.tick c.steps (0x800027ec#64) vmi buf hG hpc hmi ha0 hloaded rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) htick
  -- σ1.mem = writeMap4 c.σ.mem buf (swData 0), reads/pc via obs
  have hmem1' : σ1.mem = writeMap4 c.σ.mem buf.toNat (swData (0#64)) := by
    rw [hmem1, mem_afterNextPC, htag]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800027f0#64 : BitVec 64) := by
    have := obs_store_pc_val hobs1
    rwa [show BitVec.addInt (0x800027ec#64) 4 = (0x800027f0#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_store_other_val hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_store_other_val hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_store_minstret_val hobs1
  have hloaded1 : Value_nullLoaded σ1.mem := by
    rw [hmem1']
    exact loaded_null_writeMap4 c.σ.mem buf.toNat (swData (0#64))
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x800027f0: sd zero,8(a0) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800027f0 σ1 i1 (c.steps + 1) (0x800027f0#64) vmi1 buf hG1 hpc1 hmi1 ha0_1 hloaded1 rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi1
  have hmem2' : σ2.mem = writeMap8 (writeMap4 c.σ.mem buf.toNat (swData (0#64))) (buf.toNat + 8) (sdData_val (0#64)) := by
    rw [hmem2, mem_afterNextPC, hpay, hmem1']
  have hpc2 : σ2.regs.get? Register.PC = some (0x800027f4#64 : BitVec 64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x800027f0#64) 4 = (0x800027f4#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_store_other_val hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_store_other_val hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hloaded2 : Value_nullLoaded σ2.mem := by
    rw [hmem2']
    exact loaded_null_writeMap8 (writeMap4 c.σ.mem buf.toNat (swData (0#64))) (buf.toNat + 8)
      (sdData_val (0#64)) (by have := hreg.code_disjoint; have := hreg.hi; omega) (hmem1' ▸ hloaded1)
  -- === 0x800027f4: ret ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800027f4 σ2 i2 (c.steps + 1 + 1) (0x800027f4#64) vmi2 r hG2 hpc2 hmi2 hra_2 hloaded2 rfl
      hrettgt hi2
  -- assemble
  have hsteps : Steps c ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3))
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩, hsteps, hG3, obs_jr_pc hobs3,
    obs_jr_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2,
    obs_jr_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2,
    obs_jr_minstret hobs3, hi3, ?_,
    fun R hR => (frame_jr_v hobs3 R hR).trans
      ((frame_store_v hobs2 R hR).trans ((frame_store_v hobs1 R hR).trans (hframe R hR)))⟩
  -- ValueRepr .null: read32 m3 buf = some 0
  show ValueRepr σ3.mem N φc buf.toNat .null
  show read32 σ3.mem buf.toNat = some 0
  rw [hmem3, hmem2']
  rw [read32_writeMap8_disjoint _ _ _ _ (by omega), read32_writeMap4, swData_toNat]
  rfl

/-! ## `value_int_spec` — tag + payload connection

`value_int` writes VAL_INT (=2) at `+0` and the 8-byte payload `a1` at `+8`, then
returns. The postcondition asserts `ValueRepr m' N φc buf (.int n)` where
`n = (BitVec.ofNat 64 a1.toNat).toInt` (the two's-complement reading of the stored
payload), pinning both `read32 = 2` and `readI64 = n`. This is the full
tag+payload pilot: `int` uses both `ValueRepr` conjuncts. -/

structure IntRegion (buf : BitVec 64) : Prop where
  align : buf.toNat % 8 = 0
  lo : 0x80000000 ≤ buf.toNat
  hi : buf.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ buf.toNat
  code_disjoint : buf.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ buf.toNat

theorem int_pay_addr (buf : BitVec 64) (hr : IntRegion buf) :
    (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hr.hi
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem loaded_int_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 : Nat) (d : BitVec (8 * 4))
    (hdis : a4 + 4 ≤ 0x8000280c ∨ 0x8000281c ≤ a4) (h : Value_intLoaded mem) :
    Value_intLoaded (writeMap4 mem a4 d) := by
  simp only [Value_intLoaded, value_intChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])

theorem loaded_int_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x8000280c ∨ 0x8000281c ≤ a8) (h : Value_intLoaded mem) :
    Value_intLoaded (writeMap8 mem a8 d) := by
  simp only [Value_intLoaded, value_intChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

def int_pre (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_intLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x8000280c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some pay ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  IntRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  c.σ.sailOutput = out0 ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

def int_post (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  ValueRepr c.σ.mem N φc buf.toNat (.int (BitVec.ofNat 64 pay.toNat).toInt) ∧
  c.σ.sailOutput = out0 ∧
  -- memory outside the 24-byte buffer `[buf, buf+24)` is unchanged from `m0`
  -- (`value_int` writes only the tag `[buf,buf+4)` and payload `[buf+8,buf+16)`).
  (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- **`value_int` total-correctness spec.** From `int_pre` the machine runs to
`int_post`: `ValueRepr … buf (.int n)` with `n` the two's-complement reading of the
stored 8-byte payload — the tag (`read32 = 2`) and payload (`readI64 = n`) both
established. -/
theorem value_int_spec (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) :
    Triple (int_pre g buf pay r m0 out0) (int_post g buf pay r N φc m0 out0) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hrettgt, hout, hframe⟩ := hpre
  have hpay := int_pay_addr buf hreg
  have htag : (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    rw [BitVec.add_zero]
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x8000280c: li a5,2 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000280c c.σ c.tick c.steps (0x8000280c#64) vmi hG hpc hmi hloaded rfl htick
  have hmem1eq : σ1.mem = c.σ.mem := by rw [hmem1]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002810#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000280c#64) 4 = (0x80002810#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x002#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 0x80002810: sd a1,8(a0) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002810 σ1 i1 (c.steps + 1) (0x80002810#64) vmi1 buf pay hG1 hpc1 hmi1 ha0_1 ha1_1
      (by rw [hmem1eq]; exact hloaded) rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi1
  have hmem2' : σ2.mem = writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay) := by
    rw [hmem2, mem_afterNextPC, hpay, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002814#64 : BitVec 64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x80002810#64) 4 = (0x80002814#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_store_other_val hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_store_other_val hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_store_other_val hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hloaded2 : Value_intLoaded σ2.mem := by
    rw [hmem2']
    exact loaded_int_writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x80002814: sw a5,0(a0) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002814 σ2 i2 (c.steps + 1 + 1) (0x80002814#64) vmi2 buf
      ((0#64) + sign_extend (m := 64) (0x002#12)) hG2 hpc2 hmi2 ha0_2 ha5_2 hloaded2 rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) hi2
  have hmem3' : σ3.mem
      = writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
          (swData ((0#64) + sign_extend (m := 64) (0x002#12))) := by
    rw [hmem3, mem_afterNextPC, htag, hmem2']
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002818#64 : BitVec 64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80002814#64) 4 = (0x80002818#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_store_other_val hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hloaded3 : Value_intLoaded σ3.mem := by
    rw [hmem3']
    exact loaded_int_writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x002#12)))
      (by have := hreg.code_disjoint; have := hreg.hi; omega)
      (loaded_int_writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)
        (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded)
  -- === 0x80002818: ret ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002818 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002818#64) vmi3 r hG3 hpc3 hmi3 hra_3 hloaded3 rfl
      hrettgt hi3
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  -- output invariance: no step touches `sailOutput` (all regs/mem-only), so
  -- `σ4.sailOutput = c.σ.sailOutput = out0`. Thread via `.out` + `sailOutput_sigmaPost_*`.
  have hout4 : σ4.sailOutput = c.σ.sailOutput := by
    rw [hobs4.out, sailOutput_sigmaPost_jump_x0, hobs3.out, sailOutput_sigmaPost_store,
      hobs2.out, sailOutput_sigmaPost_store, hobs1.out, sailOutput_sigmaPost_alu]
  have hmem4eq0 : σ4.mem = writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x002#12))) := by rw [hmem4, hmem3']
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, hG4, obs_jr_pc hobs4,
    obs_jr_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3,
    obs_jr_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3,
    obs_jr_minstret hobs4, hi4, ?_, hout4.trans hout, ?_,
    fun R hR => (frame_jr_v hobs4 R hR).trans
      ((frame_store_v hobs3 R hR).trans ((frame_store_v hobs2 R hR).trans
        ((frame_alu_v hobs1 R hR).trans (hframe R hR))))⟩
  · -- ValueRepr (.int n): read32 = 2 ∧ readI64 (buf+8) = n
    show ValueRepr σ4.mem N φc buf.toNat (.int (BitVec.ofNat 64 pay.toNat).toInt)
    refine ⟨?_, ?_⟩
    · -- read32 buf = 2
      show read32 σ4.mem buf.toNat = some 2
      rw [hmem4eq0, read32_writeMap4, swData_toNat]
      rfl
    · -- readI64 (buf+8) = n
      show readI64 σ4.mem (buf.toNat + 8) = some (BitVec.ofNat 64 pay.toNat).toInt
      rw [hmem4eq0]
      simp only [readI64]
      rw [read64_writeMap4_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
      rfl
  · -- memFrame: outside [buf, buf+24) both writeMaps pass through to `m0 = c.σ.mem`
    intro k hk
    rw [hmem4eq0, getElem_writeMap4_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega), hmem]

/-! ## `value_bool_spec`

`value_bool` normalizes its `int` argument to `0/1` (`snez a1,a1`), writes VAL_BOOL
(=1) at `+0` and the normalized bool at `+8`, then returns. The postcondition
asserts `ValueRepr m' N φc buf (.bool (vb ≠ 0))`, pinning `read32 = 1` and
`read32 (buf+8) = cond (vb ≠ 0) 1 0`. The `snez`/`bool_to_bit`/`swData` chain
collapses to `0`/`1` exactly as `cond` demands. -/

/-- The `snez a1,a1` result byte, read back: `swData(zext(bool_to_bit(0<u vb))).toNat
= cond (vb ≠ 0) 1 0`. -/
theorem snez_readback (vb : BitVec 64) :
    (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb)))).toNat
      = cond (vb != 0#64) 1 0 := by
  rw [swData_toNat]
  by_cases h : vb = 0#64
  · subst h
    simp only [bne_self_eq_false, cond_false]
    decide
  · have htrue : zopz0zI_u (0#64) vb = true := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod,
        decide_eq_true_eq]
      have hp : 0 < vb.toNat := by
        rcases Nat.eq_zero_or_pos vb.toNat with h0 | hp
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
        · exact hp
      exact Int.ofNat_lt.mpr hp
    rw [htrue, show (vb != 0#64) = true from by simp only [bne_iff_ne, ne_eq]; exact h,
      cond_true]
    decide

structure BoolRegion (buf : BitVec 64) : Prop where
  align : buf.toNat % 8 = 0
  lo : 0x80000000 ≤ buf.toNat
  hi : buf.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ buf.toNat
  code_disjoint : buf.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ buf.toNat

theorem loaded_bool_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 : Nat) (d : BitVec (8 * 4))
    (hdis : a4 + 4 ≤ 0x800027f8 ∨ 0x8000280c ≤ a4) (h : Value_boolLoaded mem) :
    Value_boolLoaded (writeMap4 mem a4 d) := by
  simp only [Value_boolLoaded, value_boolChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])

theorem bool_pay_addr (buf : BitVec 64) (hr : BoolRegion buf) :
    (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hr.hi
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

def bool_pre (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_boolLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800027f8#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some vb ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  BoolRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

def bool_post (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  ValueRepr c.σ.mem N φc buf.toNat (.bool (vb != 0#64)) ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- **`value_bool` total-correctness spec.** From `bool_pre` the machine runs to
`bool_post`: `ValueRepr … buf (.bool (vb ≠ 0))` — tag `= 1` and the normalized
payload `= cond (vb ≠ 0) 1 0`. -/
theorem value_bool_spec (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (bool_pre g buf vb r m0) (bool_post g buf vb r N φc) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hrettgt, hframe⟩ := hpre
  have hpay := bool_pay_addr buf hreg
  have htag : (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    rw [BitVec.add_zero]
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x800027f8: snez a1,a1  (x11 := snez result) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800027f8 c.σ c.tick c.steps (0x800027f8#64) vmi vb hG hpc hmi ha1 hloaded rfl htick
  have hmem1eq : σ1.mem = c.σ.mem := by rw [hmem1]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800027fc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800027f8#64) 4 = (0x800027fc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha1_1 : σ1.regs.get? Register.x11 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 0x800027fc: li a5,1  (x15 := 1) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800027fc σ1 i1 (c.steps + 1) (0x800027fc#64) vmi1 hG1 hpc1 hmi1
      (by rw [hmem1eq]; exact hloaded) rfl hi1
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002800#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800027fc#64) 4 = (0x80002800#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha5_2 : σ2.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- === 0x80002800: sw a1,8(a0)  (writeMap4 at buf+8 with snez) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002800 σ2 i2 (c.steps + 1 + 1) (0x80002800#64) vmi2 buf (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))) hG2 hpc2 hmi2 ha0_2 ha1_2
      (by rw [hmem2eq]; exact hloaded) rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi2
  have hmem3' : σ3.mem = writeMap4 c.σ.mem (buf.toNat + 8) (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb)))) := by
    rw [hmem3, mem_afterNextPC, hpay, hmem2eq]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002804#64 : BitVec 64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80002800#64) 4 = (0x80002804#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_store_other_val hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha5_3 := obs_store_other_val hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hloaded3 : Value_boolLoaded σ3.mem := by
    rw [hmem3']
    exact loaded_bool_writeMap4 c.σ.mem (buf.toNat + 8) (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))))
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x80002804: sw a5,0(a0)  (writeMap4 at buf with tag 1) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002804 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002804#64) vmi3 buf
      ((0#64) + sign_extend (m := 64) (0x001#12)) hG3 hpc3 hmi3 ha0_3 ha5_3 hloaded3 rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) hi3
  have hmem4' : σ4.mem
      = writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))))) buf.toNat
          (swData ((0#64) + sign_extend (m := 64) (0x001#12))) := by
    rw [hmem4, mem_afterNextPC, htag, hmem3']
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002808#64 : BitVec 64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x80002804#64) 4 = (0x80002808#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other_val hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have hra_4 := obs_store_other_val hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hloaded4 : Value_boolLoaded σ4.mem := by
    rw [hmem4']
    exact loaded_bool_writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))))) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x001#12)))
      (by have := hreg.code_disjoint; have := hreg.hi; omega)
      (loaded_bool_writeMap4 c.σ.mem (buf.toNat + 8) (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))))
        (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded)
  -- === 0x80002808: ret ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002808 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80002808#64) vmi4 r hG4 hpc4 hmi4 hra_4 hloaded4 rfl
      hrettgt hi4
  have hsteps : Steps c ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ :=
    ((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)
  refine ⟨⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩, hsteps, hG5, obs_jr_pc hobs5,
    obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4,
    obs_jr_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4,
    obs_jr_minstret hobs5, hi5, ?_,
    fun R hR => (frame_jr_v hobs5 R hR).trans
      ((frame_store_v hobs4 R hR).trans ((frame_store_v hobs3 R hR).trans
        ((frame_alu_v hobs2 R hR).trans ((frame_alu_snez hobs1 R hR).trans (hframe R hR)))))⟩
  -- ValueRepr (.bool b): read32 buf = 1, read32 (buf+8) = cond (vb≠0) 1 0
  show ValueRepr σ5.mem N φc buf.toNat (.bool (vb != 0#64))
  have hmem5eq : σ5.mem = writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))))) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x001#12))) := by rw [hmem5, hmem4']
  refine ⟨?_, ?_⟩
  · show read32 σ5.mem buf.toNat = some 1
    rw [hmem5eq, read32_writeMap4, swData_toNat]; rfl
  · show read32 σ5.mem (buf.toNat + 8) = some (cond (vb != 0#64) 1 0)
    rw [hmem5eq, read32_writeMap4_disjoint _ _ _ _ (by omega), read32_writeMap4,
      snez_readback]

/-! ## `value_str_spec` -/

/-- `CStr` survives a single byte insert at a key `k` outside the string's byte
range `[p, p + cs.length]` (the `+ len` reaches the NUL terminator). -/
theorem cstr_insert_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    ∀ {p : Nat} {cs : List Char}, CStr mem p cs → (∀ j, p ≤ j → j ≤ p + cs.length → k ≠ j) →
      CStr (mem.insert k v) p cs := by
  intro p cs hcstr
  induction hcstr with
  | @nil a hnul =>
    intro hdis
    exact CStr.nil (by rw [getElem_insert_ne _ _ _ _ (by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hdis a (Nat.le_refl a) (by simp)), hnul])
  | @cons a b cs hb hbne hb128 hrest ih =>
    intro hdis
    refine CStr.cons (b := b) ?_ hbne hb128 (ih ?_)
    · rw [getElem_insert_ne _ _ _ _ (by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact hdis a (Nat.le_refl a) (by simp)), hb]
    · intro j hj hjle
      exact hdis j (by omega) (by simp only [List.length_cons]; omega)

/-- `CStr` survives a `writeMap4` whose window `[a4, a4+4)` is disjoint from the
string byte range `[p, p + cs.length]`. -/
theorem cstr_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 p : Nat)
    (d : BitVec (8 * 4)) (cs : List Char) (hcstr : CStr mem p cs)
    (hdis : a4 + 4 ≤ p ∨ p + cs.length < a4) :
    CStr (writeMap4 mem a4 d) p cs := by
  simp only [writeMap4]
  exact cstr_insert_disjoint _ _ _
    (cstr_insert_disjoint _ _ _
      (cstr_insert_disjoint _ _ _
        (cstr_insert_disjoint _ _ _ hcstr (fun j _ _ => by omega))
        (fun j _ _ => by omega))
      (fun j _ _ => by omega))
    (fun j _ _ => by omega)

/-- `CStr` survives a `writeMap8` whose window `[a8, a8+8)` is disjoint from the
string byte range `[p, p + cs.length]`. -/
theorem cstr_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 p : Nat)
    (d : BitVec (8 * 8)) (cs : List Char) (hcstr : CStr mem p cs)
    (hdis : a8 + 8 ≤ p ∨ p + cs.length < a8) :
    CStr (writeMap8 mem a8 d) p cs := by
  simp only [writeMap8]
  exact cstr_insert_disjoint _ _ _ (cstr_insert_disjoint _ _ _ (cstr_insert_disjoint _ _ _
    (cstr_insert_disjoint _ _ _ (cstr_insert_disjoint _ _ _ (cstr_insert_disjoint _ _ _
      (cstr_insert_disjoint _ _ _ (cstr_insert_disjoint _ _ _ hcstr
        (fun j _ _ => by omega)) (fun j _ _ => by omega)) (fun j _ _ => by omega))
      (fun j _ _ => by omega)) (fun j _ _ => by omega)) (fun j _ _ => by omega))
    (fun j _ _ => by omega)) (fun j _ _ => by omega)

structure StrRegion (buf p : BitVec 64) (len : Nat) : Prop where
  align : buf.toNat % 8 = 0
  lo : 0x80000000 ≤ buf.toNat
  hi : buf.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ buf.toNat
  code_disjoint : buf.toNat + 24 ≤ 0x8000281c ∨ 0x8000282c ≤ buf.toNat
  pnz : p.toNat ≠ 0
  str_disjoint : buf.toNat + 16 ≤ p.toNat ∨ p.toNat + len < buf.toNat

theorem str_pay_addr (buf : BitVec 64) (hr_hi : buf.toNat + 24 ≤ 0x100000000) :
    (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem loaded_str_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 : Nat) (d : BitVec (8 * 4))
    (hdis : a4 + 4 ≤ 0x8000281c ∨ 0x8000282c ≤ a4) (h : Value_strLoaded mem) :
    Value_strLoaded (writeMap4 mem a4 d) := by
  simp only [Value_strLoaded, value_strChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])

theorem loaded_str_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x8000281c ∨ 0x8000282c ≤ a8) (h : Value_strLoaded mem) :
    Value_strLoaded (writeMap8 mem a8 d) := by
  simp only [Value_strLoaded, value_strChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

def str_pre (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64) (s : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_strLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x8000281c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some pay ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  CString m0 pay.toNat s ∧ StrRegion buf pay s.length ∧
  (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

def str_post (g : (R : Register) → Option (RegisterType R)) (buf _pay r : BitVec 64) (s : String)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  ValueRepr c.σ.mem N φc buf.toNat (.str s) ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- **`value_str` total-correctness spec.** From `str_pre` the machine runs to
`str_post`: `ValueRepr … buf (.str s)` — tag `= 3`, and the stored `char *` payload
`= pay` (`≠ 0`) still points at the untouched `CString … s` (only the 24-byte
buffer, disjoint from the string, was written). -/
theorem value_str_spec (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
    (s : String) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (str_pre g buf pay r s m0) (str_post g buf pay r s N φc) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hcstr, hreg, hrettgt, hframe⟩ := hpre
  have hpay := str_pay_addr buf hreg.hi
  have htag : (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    rw [BitVec.add_zero]
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x8000281c: li a5,3 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000281c c.σ c.tick c.steps (0x8000281c#64) vmi hG hpc hmi hloaded rfl htick
  have hmem1eq : σ1.mem = c.σ.mem := by rw [hmem1]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002820#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000281c#64) 4 = (0x80002820#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x003#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 0x80002820: sd a1,8(a0) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002820 σ1 i1 (c.steps + 1) (0x80002820#64) vmi1 buf pay hG1 hpc1 hmi1 ha0_1 ha1_1
      (by rw [hmem1eq]; exact hloaded) rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi1
  have hmem2' : σ2.mem = writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay) := by
    rw [hmem2, mem_afterNextPC, hpay, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002824#64 : BitVec 64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x80002820#64) 4 = (0x80002824#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_store_other_val hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_store_other_val hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_store_other_val hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hloaded2 : Value_strLoaded σ2.mem := by
    rw [hmem2']
    exact loaded_str_writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x80002824: sw a5,0(a0) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002824 σ2 i2 (c.steps + 1 + 1) (0x80002824#64) vmi2 buf
      ((0#64) + sign_extend (m := 64) (0x003#12)) hG2 hpc2 hmi2 ha0_2 ha5_2 hloaded2 rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) hi2
  have hmem3' : σ3.mem
      = writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
          (swData ((0#64) + sign_extend (m := 64) (0x003#12))) := by
    rw [hmem3, mem_afterNextPC, htag, hmem2']
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002828#64 : BitVec 64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80002824#64) 4 = (0x80002828#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_store_other_val hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hloaded3 : Value_strLoaded σ3.mem := by
    rw [hmem3']
    exact loaded_str_writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x003#12)))
      (by have := hreg.code_disjoint; have := hreg.hi; omega)
      (loaded_str_writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)
        (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded)
  -- === 0x80002828: ret ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002828 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002828#64) vmi3 r hG3 hpc3 hmi3 hra_3 hloaded3 rfl
      hrettgt hi3
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, hG4, obs_jr_pc hobs4,
    obs_jr_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3,
    obs_jr_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3,
    obs_jr_minstret hobs4, hi4, ?_,
    fun R hR => (frame_jr_v hobs4 R hR).trans
      ((frame_store_v hobs3 R hR).trans ((frame_store_v hobs2 R hR).trans
        ((frame_alu_v hobs1 R hR).trans (hframe R hR))))⟩
  -- ValueRepr (.str s)
  show ValueRepr σ4.mem N φc buf.toNat (.str s)
  have hmem4eq : σ4.mem = writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x003#12))) := by rw [hmem4, hmem3']
  obtain ⟨cs, hcstr0, hlen⟩ := hcstr
  refine ⟨?_, pay.toNat, ?_, hreg.pnz, cs, ?_, hlen⟩
  · show read32 σ4.mem buf.toNat = some 3
    rw [hmem4eq, read32_writeMap4, swData_toNat]; rfl
  · show read64 σ4.mem (buf.toNat + 8) = some pay.toNat
    rw [hmem4eq, read64_writeMap4_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
  · rw [hmem4eq, hmem]
    have hslen : s.length = cs.length := by rw [hlen, String.length_ofList]
    apply cstr_writeMap4_disjoint
    · apply cstr_writeMap8_disjoint _ _ _ _ _ hcstr0
      have := hreg.str_disjoint; rw [← hslen]; omega
    · have := hreg.str_disjoint; rw [← hslen]; omega

end Vsa.Sim
