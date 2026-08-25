import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.ValueEqualSpec3
import Vsa.Sim.SsputsSites

/-!
# `SlotFrame` — unified stack-spill save / survive / reload API

Every verified function with a stack frame re-derives the same three facts:

1. **save** — after an `sd rs2,off(sp)` site, the 8 bytes at `sp+off` hold the
   value (`SlotHolds`, defined in `SnprintfSpec5`);
2. **survive** — `SlotHolds` transported across later disjoint writes (byte
   inserts, `writeMap4`/`writeMap8` stores, and whole verified sub-calls whose
   memory frame says "outside `[lo, hi)` unchanged");
3. **reload** — an `ld rd,off(sp)` site whose byte hypotheses are fed from
   `SlotHolds`, with the loaded sign-extended byte-append reassembling to the
   original value.

This file gathers the scattered machinery under uniform names:

* `slot_save`        — wraps `slotHolds_self`            (`SnprintfSpec5`);
* `slot_survives_insert`    — wraps `slotHolds_insert`   (`SnprintfSpec5`);
* `slot_survives_writeMap4` — two-sided generalization of
  `slotHolds_writeMap4_i2` (`SnprintfSpec17`), proved from `slotHolds_insert`;
* `slot_survives_writeMap8` — wraps `slotHolds_writeMap8` (`SnprintfSpec5`);
* `slot_survives_frame`     — NEW: transport across any pointwise
  "outside `[lo, hi)` unchanged" memory frame (the shape verified sub-call
  postconditions expose, e.g. `memmove_fwd_post` in `SnprintfSpec18`);
* `slot_reload_bytes`  — unpack `SlotHolds` into the eight `h0…h7` byte facts an
  `exec_ld`-style site wants;
* `slot_reassemble`    — wraps `ve_sext_reassemble` (`ValueEqualSpec3`): the
  sign-extended little-endian append of the eight stored bytes is the value.

Note on generality: `SlotHolds` (`SnprintfSpec5`) hardwires the effective
address as `base + sign_extend (BitVec.ofNat 12 off)`.  The `base` is an
arbitrary 64-bit pointer (usually `sp`, but nothing forces that); the offset is
a `Nat` fed through `ofNat12`, matching the 12-bit immediates of `sd`/`ld`
sites.  We keep exactly that shape here so the wrappers compose with all the
existing `SlotHolds` consumers without conversion.

A worked end-to-end `example` (sd postcondition → save → survive a later
disjoint `writeMap8` → reload bytes feeding the real `ld ra,56(sp)` site
`site_143e0_sp` from `SsputsSites` → reassemble) closes the file.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. save -/

/-- **save**: an `sd`-site memory postcondition
`mem' = writeMap8 mem k (sdData_val v)` with `k` the slot's effective address
`(base + sext (ofNat12 off)).toNat` establishes `SlotHolds base off v mem'`.
Wraps `slotHolds_self` (`SnprintfSpec5`); the two equations are `rfl` when
applied directly to a site's postcondition. -/
theorem slot_save (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem mem' : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (hk : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = k)
    (hmem : mem' = writeMap8 mem k (sdData_val v)) :
    SlotHolds base off v mem' := by
  rw [hmem]
  exact slotHolds_self base off k v mem hk

/-! ## 2. survive -/

/-- **survive** a disjoint single byte insert.  Wraps `slotHolds_insert`
(`SnprintfSpec5`); disjointness is a plain interval fact closable by `omega`. -/
theorem slot_survives_insert (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (b : BitVec 8)
    (hdis : k < (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat
      ∨ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k)
    (h : SlotHolds base off v mem) : SlotHolds base off v (mem.insert k b) :=
  slotHolds_insert base off v mem k b hdis h

/-- **survive** a disjoint 4-byte store (`sw`).  Two-sided generalization of
`slotHolds_writeMap4_i2` (`SnprintfSpec17`, which only covers stores strictly
above the slot); proved the same way, from four `slotHolds_insert` steps. -/
theorem slot_survives_writeMap4 (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 4))
    (hdis : k + 4 ≤ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat
      ∨ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k)
    (h : SlotHolds base off v mem) : SlotHolds base off v (writeMap4 mem k d) :=
  slotHolds_insert base off v _ _ _ (by omega)
    (slotHolds_insert base off v _ _ _ (by omega)
      (slotHolds_insert base off v _ _ _ (by omega)
        (slotHolds_insert base off v _ _ _ (by omega) h)))

/-- **survive** a disjoint 8-byte store (`sd`).  Wraps `slotHolds_writeMap8`
(`SnprintfSpec5`). -/
theorem slot_survives_writeMap8 (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (hdis : k + 8 ≤ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat
      ∨ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k)
    (h : SlotHolds base off v mem) : SlotHolds base off v (writeMap8 mem k d) :=
  slotHolds_writeMap8 base off v mem k d (by omega) h

/-- **survive** a whole verified sub-call: any memory transition with a
pointwise frame "outside `[lo, hi)` unchanged" (the exact shape of e.g.
`memmove_fwd_post`'s memory clause in `SnprintfSpec18`) preserves a slot whose
8-byte window lies entirely below `lo` or entirely at/above `hi`. -/
theorem slot_survives_frame (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem mem' : Std.ExtHashMap Nat (BitVec 8)) (lo hi : Nat)
    (hframe : ∀ a, (a < lo ∨ hi ≤ a) → mem'[a]? = mem[a]?)
    (hwin : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ lo
      ∨ hi ≤ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat)
    (h : SlotHolds base off v mem) : SlotHolds base off v mem' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hframe _ (by omega)] <;> assumption

/-! ## 3. reload -/

/-- **reload (bytes)**: unpack `SlotHolds` into the eight individual byte facts,
in exactly the `mem[addr + k]? = some bk` shape an `exec_ld`-style site's
`h0…h7` hypotheses want (with `bk = (sdData_val v).extractLsb' (8*k) 8`).
`SlotHolds` *is* this conjunction; the wrapper documents the interface. -/
theorem slot_reload_bytes (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (h : SlotHolds base off v mem) :
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat]?
      = some ((sdData_val v).extractLsb' 0 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 1]?
      = some ((sdData_val v).extractLsb' 8 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 2]?
      = some ((sdData_val v).extractLsb' 16 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 3]?
      = some ((sdData_val v).extractLsb' 24 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 4]?
      = some ((sdData_val v).extractLsb' 32 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 5]?
      = some ((sdData_val v).extractLsb' 40 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 6]?
      = some ((sdData_val v).extractLsb' 48 8) ∧
    mem[(base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 7]?
      = some ((sdData_val v).extractLsb' 56 8) := h

/-- **reload (value)**: the sign-extended little-endian append of the eight
stored bytes — exactly what the `ld` site writes to `rd` once its `b0…b7` are
instantiated from `slot_reload_bytes` — is the original value.  Wraps
`ve_sext_reassemble` (`ValueEqualSpec3`); typically used as
`rwa [slot_reassemble v] at hobs`. -/
theorem slot_reassemble (v : BitVec 64) :
    (sign_extend (m := 64)
      (((((((((sdData_val v).extractLsb' 56 8).append ((sdData_val v).extractLsb' 48 8)).append
        ((sdData_val v).extractLsb' 40 8)).append ((sdData_val v).extractLsb' 32 8)).append
        ((sdData_val v).extractLsb' 24 8)).append ((sdData_val v).extractLsb' 16 8)).append
        ((sdData_val v).extractLsb' 8 8)).append ((sdData_val v).extractLsb' 0 8)
        : BitVec (8 * 8)) : BitVec 64) = v :=
  ve_sext_reassemble v

/-! ## Worked example — save → survive → reload through a real `ld` site

`σ` sits at the `__ssputs_r` epilogue's `ld ra,56(sp)` (`site_143e0_sp`,
`SsputsSites`).  Its memory is: some base memory `m0`, then the spilling
`sd`'s `writeMap8` at `sp+56` (the postcondition equation an sd site leaves
behind), then a later disjoint 8-byte store at `k`.  The chain
`slot_save → slot_survives_writeMap8 → slot_reload_bytes → site_143e0_sp →
slot_reassemble` recovers the spilled `vra` in `ra`. -/
example (σ : MState) (i u : Nat) (vminstret v2 vra : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800143e0#64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hload : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    -- the sd site's postcondition, then a later disjoint store:
    (hmem : σ.mem = writeMap8
      (writeMap8 m0 (v2 + sign_extend (m := 64) (BitVec.ofNat 12 0x038)).toNat (sdData_val vra))
      k d)
    (hdis : (v2 + sign_extend (m := 64) (BitVec.ofNat 12 0x038)).toNat + 8 ≤ k)
    -- the ld site's address-range side conditions:
    (hlo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (hhiram : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (halign : (v2 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ (0x800143e0#64) vminstret Register.x1 vra) := by
  -- 1. save: `SlotHolds` right after the spilling sd
  have hsave : SlotHolds v2 0x038 vra
      (writeMap8 m0 (v2 + sign_extend (m := 64) (BitVec.ofNat 12 0x038)).toNat
        (sdData_val vra)) :=
    slot_save v2 0x038 vra m0 _ _ rfl rfl
  -- 2. survive the later disjoint 8-byte store
  have hsurv : SlotHolds v2 0x038 vra σ.mem := by
    rw [hmem]
    exact slot_survives_writeMap8 v2 0x038 vra _ k d (Or.inr hdis) hsave
  -- 3. reload: the eight byte facts, in the site's `h0…h7` shape
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := slot_reload_bytes v2 0x038 vra σ.mem hsurv
  -- 4. run the `ld ra,56(sp)` site with those bytes
  obtain ⟨σ', i', hstep, hi', hG', hm', hobs⟩ :=
    site_143e0_sp σ i u (0x800143e0#64) vminstret v2 _ _ _ _ _ _ _ _
      hG hpc hminstret hx2 hload rfl hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7 hi
  refine ⟨σ', i', hstep, hi', hG', hm', ?_⟩
  -- 5. reassemble: the loaded sign-extended byte append is `vra`
  rwa [slot_reassemble vra] at hobs

end Vsa.Sim
