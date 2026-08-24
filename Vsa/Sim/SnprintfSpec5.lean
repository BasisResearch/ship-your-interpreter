import Vsa.Sim.SnprintfSites3
import Vsa.Sim.SnprintfSpec3
import Vsa.Sim.SnprintfSpec4

/-!
# M3 Layer-3 — `SnprintfSpec5` : the loop-entry segment, composed (`_sn5`)

Closes the gap between the sign block (`SnprintfSpec4`) and the digit loop
(`SnprintfSpec3`): from the fast/multi split at `0x80008100` with the unsigned
magnitude in `a4`, step `li a5,9 → bltu(taken, magnitude>9) → 0x800082c8 …
0x800082f8` (buffer-(entryTop vsp) setup + five `sd` spills + one dead `ld` reload +
`s7 := 0`, `s11 := t1&1024 = 0`, `s0 := magnitude`) `→ j 0x8000831c` and one
mod-emit pass (`__umoddi3`, emit digit 0 at `(entryTop vsp)-1`, `s10 := (entryTop vsp)-1`,
`s7 := 1`, `beqz s11` taken), landing at the loop head `0x800082fc` in
`LSt g (entryTop vsp) m 0` — exactly `decimalLoop_spec`'s precondition `DLI g (entryTop vsp) m`.

* `loopEntry_spec` — `0x80008100` → `LSt g (entryTop vsp) m 0` at `0x800082fc`, `g` the
  final register file, `(entryTop vsp) = sp+348`;
* `entryToDigits_spec` — the capstone: `loopEntry_spec` ∘ `decimalLoop_spec`,
  from `0x80008100` to the loop exit `0x80008358` with the complete digit
  buffer `BufInv (entryTop vsp) m (p+1)` for the terminal `p`.

The single-digit fast path (`magnitude ≤ 9`, `bltu` not taken → `0x80008108`)
targets the flush segment directly and is a documented boundary, as are the
`0x800080f8/fc` flag-guard steps (sites provided in `SnprintfSites3`) and the
flush itself.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Small bridges -/

/-- Effective-address `toNat` for a small nonnegative 12-bit offset off `vsp`. -/
theorem addoff_toNat_sn5 (v : BitVec 64) (off : BitVec 12) (n : Nat) (hle : n ≤ 348)
    (hn : (sign_extend (m := 64) off : BitVec 64).toNat = n)
    (hnw : v.toNat + 348 < 2 ^ 64) :
    (v + sign_extend (m := 64) off).toNat = v.toNat + n := by
  rw [BitVec.toNat_add, hn, Nat.mod_eq_of_lt (by omega)]

/-- `v + sext 0xfff = ofNat (v.toNat - 1)` for any `v` with `1 ≤ v.toNat`. -/
theorem sub1_bv_sn5 (v : BitVec 64) (h1 : 1 ≤ v.toNat) :
    (v + sign_extend (m := 64) (0xfff#12)) = BitVec.ofNat 64 (v.toNat - 1) := by
  have hlt := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,
    show (sign_extend (m := 64) (0xfff#12) : BitVec 64).toNat = 2 ^ 64 - 1 from by decide,
    BitVec.toNat_ofNat]
  omega

/-- Machine `umod` by 10 is `Nat` mod: `w % 10#64 = ofNat (w.toNat % 10)`. -/
theorem umod10_sn5 (w : BitVec 64) : w % (10#64) = BitVec.ofNat 64 (w.toNat % 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- `bltu 9#64 w` is taken when `9 < w.toNat`. -/
theorem bltu9_true_sn5 (w : BitVec 64) (h9 : 9 < w.toNat) :
    zopz0zI_u (9#64) w = true := by
  rcases bltu_cases (9#64) w with hb | hb
  · exact hb
  · exfalso
    have := bltu_false (9#64) w hb
    rw [show (9#64 : BitVec 64).toNat = 9 from by decide] at this
    omega

/-! ## `…Loaded` predicates survive a `writeMap8` above the code region

`writeMap8` is eight chained byte inserts at `a … a+7`; each is covered by the
single-insert lemmas (`SnprintfSpec3`) once `0x80009000 ≤ a`. -/

theorem svfprintfSlice_writeMap8_sn5 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : 0x80009000 ≤ a) (h : SvfprintfSliceLoaded mem) :
    SvfprintfSliceLoaded (writeMap8 mem a d) :=
  svfprintfSlice_insert_sn3 _ _ _ (by omega) (svfprintfSlice_insert_sn3 _ _ _ (by omega)
    (svfprintfSlice_insert_sn3 _ _ _ (by omega) (svfprintfSlice_insert_sn3 _ _ _ (by omega)
    (svfprintfSlice_insert_sn3 _ _ _ (by omega) (svfprintfSlice_insert_sn3 _ _ _ (by omega)
    (svfprintfSlice_insert_sn3 _ _ _ (by omega) (svfprintfSlice_insert_sn3 _ _ _ (by omega) h)))))))

theorem umoddi3_writeMap8_sn5 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : 0x80009000 ≤ a) (h : Vsa.Sim.Code.__umoddi3Loaded mem) :
    Vsa.Sim.Code.__umoddi3Loaded (writeMap8 mem a d) :=
  umoddi3_insert_sn3 _ _ _ (by omega) (umoddi3_insert_sn3 _ _ _ (by omega)
    (umoddi3_insert_sn3 _ _ _ (by omega) (umoddi3_insert_sn3 _ _ _ (by omega)
    (umoddi3_insert_sn3 _ _ _ (by omega) (umoddi3_insert_sn3 _ _ _ (by omega)
    (umoddi3_insert_sn3 _ _ _ (by omega) (umoddi3_insert_sn3 _ _ _ (by omega) h)))))))

theorem cudivdi3_writeMap8_sn5 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : 0x80009000 ≤ a) (h : __hidden___udivdi3Loaded mem) :
    __hidden___udivdi3Loaded (writeMap8 mem a d) :=
  cudivdi3_insert_sn3 _ _ _ (by omega) (cudivdi3_insert_sn3 _ _ _ (by omega)
    (cudivdi3_insert_sn3 _ _ _ (by omega) (cudivdi3_insert_sn3 _ _ _ (by omega)
    (cudivdi3_insert_sn3 _ _ _ (by omega) (cudivdi3_insert_sn3 _ _ _ (by omega)
    (cudivdi3_insert_sn3 _ _ _ (by omega) (cudivdi3_insert_sn3 _ _ _ (by omega) h)))))))

/-- Read the PC of a `jump_x0` (`j`) step: `PC = tgt`. -/
theorem obs_jx0_pc_sn5 {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jump_x0_pc σ pc vm tgt)

/-- The buffer (entryTop vsp) of the multi-digit path: `sp + 348`. -/
def entryTop (vsp : BitVec 64) : BitVec 64 := vsp + sign_extend (m := 64) (0x15c#12)

/-- Reads outside an 8-byte `writeMap8` window are unchanged. -/
theorem getElem?_writeMap8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 8)) (a : Nat) (ha : a < k ∨ k + 8 ≤ a) :
    (writeMap8 mem k d)[a]? = mem[a]? := by
  show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
    (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-! ## `SlotHolds` — spilled 64-bit values readable byte-for-byte

`SlotHolds vsp off v mem` says the eight little-endian bytes of `v` (as
`sdData_val v`) sit at `sp+off … sp+off+7`.  This is exactly what a `sd v,off(sp)`
leaves behind (`slotHolds_self`), it survives any disjoint 8-byte store
(`slotHolds_writeMap8`) or single byte insert (`slotHolds_insert`), and it is the
form the restore block (`SnprintfSpec7`) reads back.  Defined here (rather than in
`SnprintfSpec7`) so `loopEntry_spec` can already surface the spill contents. -/
def SlotHolds (vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 7]? = some ((sdData_val v).extractLsb' 56 8)

/-- Slot facts survive a disjoint `writeMap8`. -/
theorem slotHolds_writeMap8 (vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (hdis : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k
      ∨ k + 8 ≤ (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat)
    (h : SlotHolds vsp off v mem) : SlotHolds vsp off v (writeMap8 mem k d) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [getElem?_writeMap8_out _ _ _ _ (by omega)] <;> assumption

/-- Slot facts survive a disjoint single byte insert. -/
theorem slotHolds_insert (vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (b : BitVec 8)
    (hdis : k < (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat
      ∨ (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k)
    (h : SlotHolds vsp off v mem) : SlotHolds vsp off v (mem.insert k b) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)] <;> assumption

/-- The eight bytes a `writeMap8 mem k (sdData_val v)` leaves at `k` are exactly
`v`'s little-endian bytes: `SlotHolds` holds immediately after the spilling `sd`,
when the store address equals `sp+off`. -/
theorem slotHolds_self (vsp : BitVec 64) (off k : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (hk : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = k) :
    SlotHolds vsp off v
      (writeMap8 mem k (sdData_val v)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hk] <;>
    show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
      (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[_]? = _
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]
  · rw [Std.ExtHashMap.getElem?_insert, if_pos (by simp only [beq_iff_eq])]

/-- A slot below the digit window `[top-20, top)` survives the whole digit loop:
`DigitFrame` maps each of its eight bytes back to the pre-loop memory `m0`, where
`SlotHolds` already holds.  This is the single "slot survives the window" bridge
the flush composition reuses for all six spill slots. -/
theorem slotHolds_digitFrame (top vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (haoff : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ top.toNat - 20)
    (hDF : DigitFrame top m0 mem) (h : SlotHolds vsp off v m0) :
    SlotHolds vsp off v mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hDF _ (Or.inl (by omega))] <;> assumption

/-- Memory frame of the loop-entry segment: everything outside the spill area
`sp+[32,128)` and the digit window `sp+[328,348)` reads as in the pre-entry
memory `m0`.  The sign byte (`sp+167`) and the caller's world are in-domain. -/
def EntryFrame (vsp : BitVec 64) (m0 mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
        vsp.toNat + 348 ≤ a) → mem[a]? = m0[a]?

theorem entryFrame_rfl (vsp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    EntryFrame vsp m0 m0 := fun _ _ => rfl

/-- A spill (`sd` inside `sp+[32,128)`) preserves the entry frame. -/
theorem entryFrame_writeMap8_sn5 (vsp : BitVec 64)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (hk : vsp.toNat + 32 ≤ k ∧ k + 8 ≤ vsp.toNat + 128)
    (h : EntryFrame vsp m0 mem) : EntryFrame vsp m0 (writeMap8 mem k d) := by
  intro a ha
  rw [getElem?_writeMap8_out mem k d a (by omega)]
  exact h a ha

/-- A digit-window byte insert (`sp+[328,348)`) preserves the entry frame. -/
theorem entryFrame_insert_sn5 (vsp : BitVec 64)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : vsp.toNat + 328 ≤ k ∧ k < vsp.toNat + 348)
    (h : EntryFrame vsp m0 mem) : EntryFrame vsp m0 (mem.insert k v) := by
  intro a ha
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]
  exact h a ha

/-! ## `loopEntry_spec` — `0x80008100` → `LSt g (entryTop vsp) m 0` at the loop head

From the split point with the magnitude `w` (`9 < w.toNat`) in `a4`, the stack
pointer in `sp` (8-aligned, `TopOk`-compatible window), and the `%lld` flag word
in `t1` with the grouping bit clear, the machine steps to the loop head
`0x800082fc` in `LSt g (sp+348) w.toNat 0` where `g` is the final register file.
The spill values (`s7`,`s4`,`s0`,`t3`,`t1` old contents) must merely exist. -/
theorem loopEntry_spec (w vsp vt1 v20 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008100#64))
    (hx14 : c.σ.regs.get? Register.x14 = some w)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hflag : vt1 &&& sign_extend (m := 64) (0x400#12) = 0#64)
    (hx8e : ∃ v, c.σ.regs.get? Register.x8 = some v)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23e : ∃ v, c.σ.regs.get? Register.x23 = some v)
    (hx28e : ∃ v, c.σ.regs.get? Register.x28 = some v)
    (hx12e : ∃ v, c.σ.regs.get? Register.x12 = some v)
    (hx13e : ∃ v, c.σ.regs.get? Register.x13 = some v)
    (hm9 : 9 < w.toNat)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧
      LSt (fun R => c'.σ.regs.get? R) (entryTop vsp) w.toNat 0 c' ∧
      TopOk (entryTop vsp) ∧ EntryFrame vsp c.σ.mem c'.σ.mem ∧
      -- `sp` survives; the entry block reloads `s4` (`x20`) from slot 104 with a
      -- dead value (`vs4j`, merely existential); the six spilled slots hold the
      -- spilled entry values byte-for-byte.  The width slot 56 holds the *named*
      -- entry `x20` value `v20` — the field width the `%`-parse produced (the
      -- `sd s4,56(sp)` at `0x800082d0` spills `s4 = x20 = v20`):
      c'.σ.regs.get? Register.x2 = some vsp ∧
      (∃ vs4j, c'.σ.regs.get? Register.x20 = some vs4j) ∧
      SlotHolds vsp 0x038 v20 c'.σ.mem ∧             -- s4  = width = v20 (named)
      ∃ vwid vt3 vs7 vs0,
        SlotHolds vsp 0x070 (entryTop vsp) c'.σ.mem ∧  -- s6  = top of buffer
        SlotHolds vsp 0x038 vwid c'.σ.mem ∧            -- s4  = width
        SlotHolds vsp 0x028 vt1 c'.σ.mem ∧             -- t1  = flags
        SlotHolds vsp 0x020 vt3 c'.σ.mem ∧             -- t3  (spare)
        SlotHolds vsp 0x030 vs7 c'.σ.mem ∧             -- s7  (spare)
        SlotHolds vsp 0x078 vs0 c'.σ.mem := by         -- s0  (spare)
  have htohv : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  obtain ⟨v8₀, hx8₀⟩ := hx8e
  have hx20₀ : c.σ.regs.get? Register.x20 = some v20 := hx20
  obtain ⟨v23₀, hx23₀⟩ := hx23e
  obtain ⟨v28₀, hx28₀⟩ := hx28e
  obtain ⟨v12₀, hx12₀⟩ := hx12e
  obtain ⟨v13₀, hx13₀⟩ := hx13e
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=
    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw
  have htopok : TopOk (entryTop vsp) := ⟨by omega, by omega⟩
  -- === 8100: li a5,9 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80008100_sn5 c.σ c.tick c.steps (0x80008100#64) vmi0 hG hpc hmi0 hload rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80008104#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80008100#64 : BitVec 64) 4 = (0x80008104#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_1 : σ1.regs.get? Register.x15 = some (9#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li9] at this
  have hx14_1 : σ1.regs.get? Register.x14 = some w :=
    obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx8_1 : σ1.regs.get? Register.x8 = some v8₀ :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8₀
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20₀
  have hx23_1 : σ1.regs.get? Register.x23 = some v23₀ :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23₀
  have hx28_1 : σ1.regs.get? Register.x28 = some v28₀ :=
    obs_alu_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28₀
  have hx12_1 : σ1.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12₀
  have hx13_1 : σ1.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13₀
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have huload1 : Vsa.Sim.Code.__umoddi3Loaded σ1.mem := hmem1 ▸ huload
  have hcuload1 : __hidden___udivdi3Loaded σ1.mem := hmem1 ▸ hcuload
  have hEF1 : EntryFrame vsp c.σ.mem σ1.mem := hmem1 ▸ entryFrame_rfl vsp c.σ.mem
  -- === 8104: bltu a5,a4 TAKEN (9 < w) ⇒ PC := 82c8 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80008104_taken_sn5 σ1 i1 (c.steps+1) (0x80008104#64) vmi1 (9#64) w
      hG1 hpc1 hmi1 hx15_1 hx14_1 hload1 rfl (bltu9_true_sn5 w hm9) hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800082c8#64) := by
    have := obs_btaken_pc hobs2
    rwa [show (0x80008104#64 : BitVec 64) + sign_extend (m := 64) (0x01c4#13)
      = (0x800082c8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some w :=
    obs_btaken_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_1
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8₀ :=
    obs_btaken_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_btaken_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx23_2 : σ2.regs.get? Register.x23 = some v23₀ :=
    obs_btaken_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx28_2 : σ2.regs.get? Register.x28 = some v28₀ :=
    obs_btaken_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hx12_2 : σ2.regs.get? Register.x12 = some v12₀ :=
    obs_btaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hx13_2 : σ2.regs.get? Register.x13 = some v13₀ :=
    obs_btaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
  obtain ⟨vmi2, hmi2⟩ := obs_btaken_minstret hobs2
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have huload2 : Vsa.Sim.Code.__umoddi3Loaded σ2.mem := hmem2 ▸ huload1
  have hcuload2 : __hidden___udivdi3Loaded σ2.mem := hmem2 ▸ hcuload1
  have hEF2 : EntryFrame vsp c.σ.mem σ2.mem := hmem2 ▸ hEF1
  -- === 82c8: addi s6,sp,348 ⇒ x22 := (entryTop vsp) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800082c8_sn5 σ2 i2 (c.steps+1+1) (0x800082c8#64) vmi2 vsp hG2 hpc2 hmi2 hx2_2 hload2 rfl hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800082cc#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800082c8#64 : BitVec 64) 4 = (0x800082cc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx22_3 : σ3.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_3 : σ3.regs.get? Register.x14 = some w :=
    obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8₀ :=
    obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx23_3 : σ3.regs.get? Register.x23 = some v23₀ :=
    obs_alu_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hx28_3 : σ3.regs.get? Register.x28 = some v28₀ :=
    obs_alu_other hobs3 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_2
  have hx12_3 : σ3.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hx13_3 : σ3.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have huload3 : Vsa.Sim.Code.__umoddi3Loaded σ3.mem := hmem3 ▸ huload2
  have hcuload3 : __hidden___udivdi3Loaded σ3.mem := hmem3 ▸ hcuload2
  have hEF3 : EntryFrame vsp c.σ.mem σ3.mem := hmem3 ▸ hEF2
  -- === 82cc: sd s7,48(sp) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_800082cc_sn5 σ3 i3 (c.steps+1+1+1) (0x800082cc#64) vmi3 vsp v23₀
      hG3 hpc3 hmi3 hx2_3 hx23_3 hload3 rfl
      (by rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega) hi3
  have hstep4 : Step ⟨σ3,i3,c.steps+1+1+1⟩ ⟨σ4,i4,c.steps+1+1+1+1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x800082d0#64) := by
    have := obs_store_pc_sn4 hobs4
    rwa [show BitVec.addInt (0x800082cc#64 : BitVec 64) 4 = (0x800082d0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_4 : σ4.regs.get? Register.x14 = some w :=
    obs_store_other_sn4 Register.x14 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_3
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx6_4 : σ4.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8₀ :=
    obs_store_other_sn4 Register.x8 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4 Register.x20 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx22_4 : σ4.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x22 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx28_4 : σ4.regs.get? Register.x28 = some v28₀ :=
    obs_store_other_sn4 Register.x28 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_3
  have hx12_4 : σ4.regs.get? Register.x12 = some v12₀ :=
    obs_store_other_sn4 Register.x12 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  have hx13_4 : σ4.regs.get? Register.x13 = some v13₀ :=
    obs_store_other_sn4 Register.x13 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_sn4 hobs4
  have hNP3 : (afterNextPC (afterPrelude σ3) (0x800082cc#64)).mem = σ3.mem := rfl
  have hka : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat := by
    rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega
  have hload4 : SvfprintfSliceLoaded σ4.mem := by
    rw [hmem4, hNP3]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hka hload3
  have huload4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := by
    rw [hmem4, hNP3]; exact umoddi3_writeMap8_sn5 _ _ _ hka huload3
  have hcuload4 : __hidden___udivdi3Loaded σ4.mem := by
    rw [hmem4, hNP3]; exact cudivdi3_writeMap8_sn5 _ _ _ hka hcuload3
  have hEF4 : EntryFrame vsp c.σ.mem σ4.mem := by
    rw [hmem4, hNP3]
    exact entryFrame_writeMap8_sn5 vsp _ _ _ _
      ⟨by rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega,
       by rw [addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw]; omega⟩ hEF3
  -- === 82d0: sd s4,56(sp) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_800082d0_sn5 σ4 i4 (c.steps+1+1+1+1) (0x800082d0#64) vmi4 vsp v20
      hG4 hpc4 hmi4 hx2_4 hx20_4 hload4 rfl
      (by rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega) hi4
  have hstep5 : Step ⟨σ4,i4,c.steps+1+1+1+1⟩ ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x800082d4#64) := by
    have := obs_store_pc_sn4 hobs5
    rwa [show BitVec.addInt (0x800082d0#64 : BitVec 64) 4 = (0x800082d4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_5 : σ5.regs.get? Register.x14 = some w :=
    obs_store_other_sn4 Register.x14 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_4
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx6_5 : σ5.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8₀ :=
    obs_store_other_sn4 Register.x8 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx22_5 : σ5.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x22 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_4
  have hx28_5 : σ5.regs.get? Register.x28 = some v28₀ :=
    obs_store_other_sn4 Register.x28 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_4
  have hx12_5 : σ5.regs.get? Register.x12 = some v12₀ :=
    obs_store_other_sn4 Register.x12 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
  have hx13_5 : σ5.regs.get? Register.x13 = some v13₀ :=
    obs_store_other_sn4 Register.x13 hobs5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret_sn4 hobs5
  have hNP4 : (afterNextPC (afterPrelude σ4) (0x800082d0#64)).mem = σ4.mem := rfl
  have hkb : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat := by
    rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega
  have hload5 : SvfprintfSliceLoaded σ5.mem := by
    rw [hmem5, hNP4]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hkb hload4
  have huload5 : Vsa.Sim.Code.__umoddi3Loaded σ5.mem := by
    rw [hmem5, hNP4]; exact umoddi3_writeMap8_sn5 _ _ _ hkb huload4
  have hcuload5 : __hidden___udivdi3Loaded σ5.mem := by
    rw [hmem5, hNP4]; exact cudivdi3_writeMap8_sn5 _ _ _ hkb hcuload4
  have hEF5 : EntryFrame vsp c.σ.mem σ5.mem := by
    rw [hmem5, hNP4]
    exact entryFrame_writeMap8_sn5 vsp _ _ _ _
      ⟨by rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega,
       by rw [addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw]; omega⟩ hEF4
  -- === 82d4: sd s0,120(sp) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_800082d4_sn5 σ5 i5 (c.steps+1+1+1+1+1) (0x800082d4#64) vmi5 vsp v8₀
      hG5 hpc5 hmi5 hx2_5 hx8_5 hload5 rfl
      (by rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega) hi5
  have hstep6 : Step ⟨σ5,i5,c.steps+1+1+1+1+1⟩ ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x800082d8#64) := by
    have := obs_store_pc_sn4 hobs6
    rwa [show BitVec.addInt (0x800082d4#64 : BitVec 64) 4 = (0x800082d8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_6 : σ6.regs.get? Register.x14 = some w :=
    obs_store_other_sn4 Register.x14 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_5
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx6_6 : σ6.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_5
  have hx22_6 : σ6.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x22 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hx28_6 : σ6.regs.get? Register.x28 = some v28₀ :=
    obs_store_other_sn4 Register.x28 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_5
  have hx12_6 : σ6.regs.get? Register.x12 = some v12₀ :=
    obs_store_other_sn4 Register.x12 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
  have hx13_6 : σ6.regs.get? Register.x13 = some v13₀ :=
    obs_store_other_sn4 Register.x13 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret_sn4 hobs6
  have hNP5 : (afterNextPC (afterPrelude σ5) (0x800082d4#64)).mem = σ5.mem := rfl
  have hkc : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x078#12)).toNat := by
    rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega
  have hload6 : SvfprintfSliceLoaded σ6.mem := by
    rw [hmem6, hNP5]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hkc hload5
  have huload6 : Vsa.Sim.Code.__umoddi3Loaded σ6.mem := by
    rw [hmem6, hNP5]; exact umoddi3_writeMap8_sn5 _ _ _ hkc huload5
  have hcuload6 : __hidden___udivdi3Loaded σ6.mem := by
    rw [hmem6, hNP5]; exact cudivdi3_writeMap8_sn5 _ _ _ hkc hcuload5
  have hEF6 : EntryFrame vsp c.σ.mem σ6.mem := by
    rw [hmem6, hNP5]
    exact entryFrame_writeMap8_sn5 vsp _ _ _ _
      ⟨by rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega,
       by rw [addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw]; omega⟩ hEF5
  -- === 82d8: ld s4,104(sp) (value dead) ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_800082d8_sn5 σ6 i6 (c.steps+1+1+1+1+1+1) (0x800082d8#64) vmi6 vsp
      hG6 hpc6 hmi6 hx2_6 hload6 rfl
      (by rw [addoff_toNat_sn5 vsp (0x068#12) 104 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x068#12) 104 (by omega) (by decide) hnw]; omega)
      (Or.inr (by rw [addoff_toNat_sn5 vsp (0x068#12) 104 (by omega) (by decide) hnw]; omega))
      (by rw [addoff_toNat_sn5 vsp (0x068#12) 104 (by omega) (by decide) hnw]; omega) hi6
  have hstep7 : Step ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x800082dc#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800082d8#64 : BitVec 64) 4 = (0x800082dc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_7 : σ7.regs.get? Register.x14 = some w :=
    obs_alu_other hobs7 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_6
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx6_7 : σ7.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hx22_7 : σ7.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hx28_7 : σ7.regs.get? Register.x28 = some v28₀ :=
    obs_alu_other hobs7 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_6
  have hx12_7 : σ7.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  have hx13_7 : σ7.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs7 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have huload7 : Vsa.Sim.Code.__umoddi3Loaded σ7.mem := hmem7 ▸ huload6
  have hcuload7 : __hidden___udivdi3Loaded σ7.mem := hmem7 ▸ hcuload6
  have hEF7 : EntryFrame vsp c.σ.mem σ7.mem := hmem7 ▸ hEF6
  -- === 82dc: mv s9,s6 ⇒ x25 := (entryTop vsp) ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_800082dc_sn5 σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x800082dc#64) vmi7 (entryTop vsp)
      hG7 hpc7 hmi7 hx22_7 hload7 rfl hi7
  have hstep8 : Step ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x800082e0#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x800082dc#64 : BitVec 64) 4 = (0x800082e0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx25_8 : σ8.regs.get? Register.x25 = some (entryTop vsp) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (entryTop vsp)] at this
  have hx14_8 : σ8.regs.get? Register.x14 = some w :=
    obs_alu_other hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_7
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx6_8 : σ8.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_7
  have hx22_8 : σ8.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_alu_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hx28_8 : σ8.regs.get? Register.x28 = some v28₀ :=
    obs_alu_other hobs8 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_7
  have hx12_8 : σ8.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_7
  have hx13_8 : σ8.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs8 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have huload8 : Vsa.Sim.Code.__umoddi3Loaded σ8.mem := hmem8 ▸ huload7
  have hcuload8 : __hidden___udivdi3Loaded σ8.mem := hmem8 ▸ hcuload7
  have hEF8 : EntryFrame vsp c.σ.mem σ8.mem := hmem8 ▸ hEF7
  -- === 82e0: sd t3,32(sp) ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_800082e0_sn5 σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x800082e0#64) vmi8 vsp v28₀
      hG8 hpc8 hmi8 hx2_8 hx28_8 hload8 rfl
      (by rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega) hi8
  have hstep9 : Step ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x800082e4#64) := by
    have := obs_store_pc_sn4 hobs9
    rwa [show BitVec.addInt (0x800082e0#64 : BitVec 64) 4 = (0x800082e4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_9 : σ9.regs.get? Register.x14 = some w :=
    obs_store_other_sn4 Register.x14 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_8
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx6_9 : σ9.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_8
  have hx22_9 : σ9.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x22 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_8
  have hx25_9 : σ9.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x25 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_8
  have hx12_9 : σ9.regs.get? Register.x12 = some v12₀ :=
    obs_store_other_sn4 Register.x12 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_8
  have hx13_9 : σ9.regs.get? Register.x13 = some v13₀ :=
    obs_store_other_sn4 Register.x13 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_sn4 hobs9
  have hNP8 : (afterNextPC (afterPrelude σ8) (0x800082e0#64)).mem = σ8.mem := rfl
  have hkd : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat := by
    rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega
  have hload9 : SvfprintfSliceLoaded σ9.mem := by
    rw [hmem9, hNP8]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hkd hload8
  have huload9 : Vsa.Sim.Code.__umoddi3Loaded σ9.mem := by
    rw [hmem9, hNP8]; exact umoddi3_writeMap8_sn5 _ _ _ hkd huload8
  have hcuload9 : __hidden___udivdi3Loaded σ9.mem := by
    rw [hmem9, hNP8]; exact cudivdi3_writeMap8_sn5 _ _ _ hkd hcuload8
  have hEF9 : EntryFrame vsp c.σ.mem σ9.mem := by
    rw [hmem9, hNP8]
    exact entryFrame_writeMap8_sn5 vsp _ _ _ _
      ⟨by rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega,
       by rw [addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw]; omega⟩ hEF8
  -- === 82e4: sd t1,40(sp) ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_800082e4_sn5 σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x800082e4#64) vmi9 vsp vt1
      hG9 hpc9 hmi9 hx2_9 hx6_9 hload9 rfl
      (by rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega) hi9
  have hstep10 : Step ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x800082e8#64) := by
    have := obs_store_pc_sn4 hobs10
    rwa [show BitVec.addInt (0x800082e4#64 : BitVec 64) 4 = (0x800082e8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_10 : σ10.regs.get? Register.x14 = some w :=
    obs_store_other_sn4 Register.x14 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_9
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_9
  have hx6_10 : σ10.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_9
  have hx22_10 : σ10.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x22 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_9
  have hx25_10 : σ10.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x25 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_9
  have hx12_10 : σ10.regs.get? Register.x12 = some v12₀ :=
    obs_store_other_sn4 Register.x12 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_9
  have hx13_10 : σ10.regs.get? Register.x13 = some v13₀ :=
    obs_store_other_sn4 Register.x13 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret_sn4 hobs10
  have hNP9 : (afterNextPC (afterPrelude σ9) (0x800082e4#64)).mem = σ9.mem := rfl
  have hke : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat := by
    rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega
  have hload10 : SvfprintfSliceLoaded σ10.mem := by
    rw [hmem10, hNP9]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hke hload9
  have huload10 : Vsa.Sim.Code.__umoddi3Loaded σ10.mem := by
    rw [hmem10, hNP9]; exact umoddi3_writeMap8_sn5 _ _ _ hke huload9
  have hcuload10 : __hidden___udivdi3Loaded σ10.mem := by
    rw [hmem10, hNP9]; exact cudivdi3_writeMap8_sn5 _ _ _ hke hcuload9
  have hEF10 : EntryFrame vsp c.σ.mem σ10.mem := by
    rw [hmem10, hNP9]
    exact entryFrame_writeMap8_sn5 vsp _ _ _ _
      ⟨by rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega,
       by rw [addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw]; omega⟩ hEF9
  -- === 82e8: li s7,0 ⇒ x23 := 0 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_800082e8_sn5 σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x800082e8#64) vmi10
      hG10 hpc10 hmi10 hload10 rfl hi10
  have hstep11 : Step ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x800082ec#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x800082e8#64 : BitVec 64) 4 = (0x800082ec#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx23_11 : σ11.regs.get? Register.x23 = some (0#64) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (0#64)] at this
  have hx14_11 : σ11.regs.get? Register.x14 = some w :=
    obs_alu_other hobs11 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_10
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_10
  have hx6_11 : σ11.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs11 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_10
  have hx22_11 : σ11.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_alu_other hobs11 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_10
  have hx25_11 : σ11.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs11 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_10
  have hx12_11 : σ11.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs11 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_10
  have hx13_11 : σ11.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs11 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hload11 : SvfprintfSliceLoaded σ11.mem := hmem11 ▸ hload10
  have huload11 : Vsa.Sim.Code.__umoddi3Loaded σ11.mem := hmem11 ▸ huload10
  have hcuload11 : __hidden___udivdi3Loaded σ11.mem := hmem11 ▸ hcuload10
  have hEF11 : EntryFrame vsp c.σ.mem σ11.mem := hmem11 ▸ hEF10
  -- === 82ec: andi s11,t1,1024 ⇒ x27 := 0 (grouping flag clear) ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_800082ec_sn5 σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x800082ec#64) vmi11 vt1
      hG11 hpc11 hmi11 hx6_11 hload11 rfl hi11
  have hstep12 : Step ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x800082f0#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x800082ec#64 : BitVec 64) 4 = (0x800082f0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx27_12 : σ12.regs.get? Register.x27 = some (0#64) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hflag] at this
  have hx14_12 : σ12.regs.get? Register.x14 = some w :=
    obs_alu_other hobs12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_11
  have hx2_12 : σ12.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_11
  have hx22_12 : σ12.regs.get? Register.x22 = some (entryTop vsp) :=
    obs_alu_other hobs12 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_11
  have hx23_12 : σ12.regs.get? Register.x23 = some (0#64) :=
    obs_alu_other hobs12 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_11
  have hx25_12 : σ12.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs12 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_11
  have hx12_12 : σ12.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_11
  have hx13_12 : σ12.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs12 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hload12 : SvfprintfSliceLoaded σ12.mem := hmem12 ▸ hload11
  have huload12 : Vsa.Sim.Code.__umoddi3Loaded σ12.mem := hmem12 ▸ huload11
  have hcuload12 : __hidden___udivdi3Loaded σ12.mem := hmem12 ▸ hcuload11
  have hEF12 : EntryFrame vsp c.σ.mem σ12.mem := hmem12 ▸ hEF11
  -- === 82f0: sd s6,112(sp) ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_800082f0_sn5 σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x800082f0#64) vmi12 vsp (entryTop vsp)
      hG12 hpc12 hmi12 hx2_12 hx22_12 hload12 rfl
      (by rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega)
      (by rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega) hi12
  have hstep13 : Step ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x800082f4#64) := by
    have := obs_store_pc_sn4 hobs13
    rwa [show BitVec.addInt (0x800082f0#64 : BitVec 64) 4 = (0x800082f4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_13 : σ13.regs.get? Register.x14 = some w :=
    obs_store_other_sn4 Register.x14 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_12
  have hx23_13 : σ13.regs.get? Register.x23 = some (0#64) :=
    obs_store_other_sn4 Register.x23 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_12
  have hx25_13 : σ13.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_store_other_sn4 Register.x25 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_12
  have hx27_13 : σ13.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn4 Register.x27 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_12
  have hx12_13 : σ13.regs.get? Register.x12 = some v12₀ :=
    obs_store_other_sn4 Register.x12 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_12
  have hx13_13 : σ13.regs.get? Register.x13 = some v13₀ :=
    obs_store_other_sn4 Register.x13 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_12
  obtain ⟨vmi13, hmi13⟩ := obs_store_minstret_sn4 hobs13
  have hNP12 : (afterNextPC (afterPrelude σ12) (0x800082f0#64)).mem = σ12.mem := rfl
  have hkf : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x070#12)).toNat := by
    rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega
  have hload13 : SvfprintfSliceLoaded σ13.mem := by
    rw [hmem13, hNP12]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hkf hload12
  have huload13 : Vsa.Sim.Code.__umoddi3Loaded σ13.mem := by
    rw [hmem13, hNP12]; exact umoddi3_writeMap8_sn5 _ _ _ hkf huload12
  have hcuload13 : __hidden___udivdi3Loaded σ13.mem := by
    rw [hmem13, hNP12]; exact cudivdi3_writeMap8_sn5 _ _ _ hkf hcuload12
  have hEF13 : EntryFrame vsp c.σ.mem σ13.mem := by
    rw [hmem13, hNP12]
    exact entryFrame_writeMap8_sn5 vsp _ _ _ _
      ⟨by rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega,
       by rw [addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw]; omega⟩ hEF12
  -- === spill-slot contents at σ13 (all six spills done): SlotHolds for each ===
  -- slot toNat addresses
  have ha48 : (vsp + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat + 48 :=
    addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw
  have ha56 : (vsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat + 56 :=
    addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw
  have ha120 : (vsp + sign_extend (m := 64) (0x078#12)).toNat = vsp.toNat + 120 :=
    addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw
  have ha32 : (vsp + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 32 :=
    addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw
  have ha40 : (vsp + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat + 40 :=
    addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw
  have ha112 : (vsp + sign_extend (m := 64) (0x070#12)).toNat = vsp.toNat + 112 :=
    addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw
  -- σ4.mem = writeMap8 σ3.mem @48 (sdData_val v23₀), etc.  Build at birth, transport forward.
  -- slot 48 (s7 = v23₀), born at σ4
  have hslot48_13 : SlotHolds vsp 0x030 v23₀ σ13.mem := by
    have hb : SlotHolds vsp 0x030 v23₀ σ4.mem := by
      rw [hmem4, hNP3]; exact slotHolds_self vsp 0x030 _ v23₀ σ3.mem rfl
    -- σ4 → σ5 (@56) → σ6 (@120) → σ7=σ6 → σ8=σ7 → σ9 (@32) → σ10 (@40) → σ11=σ10 → σ12=σ11 → σ13 (@112)
    have h5 : SlotHolds vsp 0x030 v23₀ σ5.mem := by
      rw [hmem5, hNP4]; exact slotHolds_writeMap8 vsp 0x030 v23₀ σ4.mem _ _ (by rw [ha48, ha56]; omega) hb
    have h6 : SlotHolds vsp 0x030 v23₀ σ6.mem := by
      rw [hmem6, hNP5]; exact slotHolds_writeMap8 vsp 0x030 v23₀ σ5.mem _ _ (by rw [ha48, ha120]; omega) h5
    have h9 : SlotHolds vsp 0x030 v23₀ σ9.mem := by
      rw [hmem9, hNP8]; exact slotHolds_writeMap8 vsp 0x030 v23₀ σ8.mem _ _ (by rw [ha48, ha32]; omega) (hmem8 ▸ hmem7 ▸ h6)
    have h10 : SlotHolds vsp 0x030 v23₀ σ10.mem := by
      rw [hmem10, hNP9]; exact slotHolds_writeMap8 vsp 0x030 v23₀ σ9.mem _ _ (by rw [ha48, ha40]; omega) h9
    rw [hmem13, hNP12]
    exact slotHolds_writeMap8 vsp 0x030 v23₀ σ12.mem _ _ (by rw [ha48, ha112]; omega) (hmem12 ▸ hmem11 ▸ h10)
  -- slot 56 (s4 = v20), born at σ5
  have hslot56_13 : SlotHolds vsp 0x038 v20 σ13.mem := by
    have hb : SlotHolds vsp 0x038 v20 σ5.mem := by
      rw [hmem5, hNP4]; exact slotHolds_self vsp 0x038 _ v20 σ4.mem rfl
    have h6 : SlotHolds vsp 0x038 v20 σ6.mem := by
      rw [hmem6, hNP5]; exact slotHolds_writeMap8 vsp 0x038 v20 σ5.mem _ _ (by rw [ha56, ha120]; omega) hb
    have h9 : SlotHolds vsp 0x038 v20 σ9.mem := by
      rw [hmem9, hNP8]; exact slotHolds_writeMap8 vsp 0x038 v20 σ8.mem _ _ (by rw [ha56, ha32]; omega) (hmem8 ▸ hmem7 ▸ h6)
    have h10 : SlotHolds vsp 0x038 v20 σ10.mem := by
      rw [hmem10, hNP9]; exact slotHolds_writeMap8 vsp 0x038 v20 σ9.mem _ _ (by rw [ha56, ha40]; omega) h9
    rw [hmem13, hNP12]
    exact slotHolds_writeMap8 vsp 0x038 v20 σ12.mem _ _ (by rw [ha56, ha112]; omega) (hmem12 ▸ hmem11 ▸ h10)
  -- slot 120 (s0 = v8₀), born at σ6
  have hslot120_13 : SlotHolds vsp 0x078 v8₀ σ13.mem := by
    have hb : SlotHolds vsp 0x078 v8₀ σ6.mem := by
      rw [hmem6, hNP5]; exact slotHolds_self vsp 0x078 _ v8₀ σ5.mem rfl
    have h9 : SlotHolds vsp 0x078 v8₀ σ9.mem := by
      rw [hmem9, hNP8]; exact slotHolds_writeMap8 vsp 0x078 v8₀ σ8.mem _ _ (by rw [ha120, ha32]; omega) (hmem8 ▸ hmem7 ▸ hb)
    have h10 : SlotHolds vsp 0x078 v8₀ σ10.mem := by
      rw [hmem10, hNP9]; exact slotHolds_writeMap8 vsp 0x078 v8₀ σ9.mem _ _ (by rw [ha120, ha40]; omega) h9
    rw [hmem13, hNP12]
    exact slotHolds_writeMap8 vsp 0x078 v8₀ σ12.mem _ _ (by rw [ha120, ha112]; omega) (hmem12 ▸ hmem11 ▸ h10)
  -- slot 32 (t3 = v28₀), born at σ9
  have hslot32_13 : SlotHolds vsp 0x020 v28₀ σ13.mem := by
    have hb : SlotHolds vsp 0x020 v28₀ σ9.mem := by
      rw [hmem9, hNP8]; exact slotHolds_self vsp 0x020 _ v28₀ σ8.mem rfl
    have h10 : SlotHolds vsp 0x020 v28₀ σ10.mem := by
      rw [hmem10, hNP9]; exact slotHolds_writeMap8 vsp 0x020 v28₀ σ9.mem _ _ (by rw [ha32, ha40]; omega) hb
    rw [hmem13, hNP12]
    exact slotHolds_writeMap8 vsp 0x020 v28₀ σ12.mem _ _ (by rw [ha32, ha112]; omega) (hmem12 ▸ hmem11 ▸ h10)
  -- slot 40 (t1 = vt1), born at σ10
  have hslot40_13 : SlotHolds vsp 0x028 vt1 σ13.mem := by
    have hb : SlotHolds vsp 0x028 vt1 σ10.mem := by
      rw [hmem10, hNP9]; exact slotHolds_self vsp 0x028 _ vt1 σ9.mem rfl
    rw [hmem13, hNP12]
    exact slotHolds_writeMap8 vsp 0x028 vt1 σ12.mem _ _ (by rw [ha40, ha112]; omega) (hmem12 ▸ hmem11 ▸ hb)
  -- slot 112 (s6 = entryTop vsp), born at σ13
  have hslot112_13 : SlotHolds vsp 0x070 (entryTop vsp) σ13.mem := by
    rw [hmem13, hNP12]; exact slotHolds_self vsp 0x070 _ (entryTop vsp) σ12.mem rfl
  -- === 82f4: mv s0,a4 ⇒ x8 := w ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_800082f4_sn5 σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800082f4#64) vmi13 w
      hG13 hpc13 hmi13 hx14_13 hload13 rfl hi13
  have hstep14 : Step ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x800082f8#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x800082f4#64 : BitVec 64) 4 = (0x800082f8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8_14 : σ14.regs.get? Register.x8 = some w := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 w] at this
  have hx23_14 : σ14.regs.get? Register.x23 = some (0#64) :=
    obs_alu_other hobs14 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_13
  have hx25_14 : σ14.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs14 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_13
  have hx27_14 : σ14.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs14 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_13
  have hx12_14 : σ14.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs14 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_13
  have hx13_14 : σ14.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs14 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hload14 : SvfprintfSliceLoaded σ14.mem := hmem14 ▸ hload13
  have huload14 : Vsa.Sim.Code.__umoddi3Loaded σ14.mem := hmem14 ▸ huload13
  have hcuload14 : __hidden___udivdi3Loaded σ14.mem := hmem14 ▸ hcuload13
  have hEF14 : EntryFrame vsp c.σ.mem σ14.mem := hmem14 ▸ hEF13
  -- === 82f8: j 0x8000831c ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_800082f8_sn5 σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800082f8#64) vmi14
      hG14 hpc14 hmi14 hload14 rfl (by decide) hi14
  have hstep15 : Step ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x8000831c#64) := by
    have := obs_jx0_pc_sn5 hobs15
    rwa [show (0x800082f8#64 : BitVec 64) + sign_extend (m := 64) (0x000024#21)
      = (0x8000831c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8_15 : σ15.regs.get? Register.x8 = some w := by
    rw [frame_jr hobs15 Register.x8 (by decide)]; exact hx8_14
  have hx23_15 : σ15.regs.get? Register.x23 = some (0#64) := by
    rw [frame_jr hobs15 Register.x23 (by decide)]; exact hx23_14
  have hx25_15 : σ15.regs.get? Register.x25 = some (entryTop vsp) := by
    rw [frame_jr hobs15 Register.x25 (by decide)]; exact hx25_14
  have hx27_15 : σ15.regs.get? Register.x27 = some (0#64) := by
    rw [frame_jr hobs15 Register.x27 (by decide)]; exact hx27_14
  have hx12_15 : σ15.regs.get? Register.x12 = some v12₀ :=
    obs_jr_other hobs15 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_14
  have hx13_15 : σ15.regs.get? Register.x13 = some v13₀ :=
    obs_jr_other hobs15 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_14
  obtain ⟨vmi15, hmi15⟩ := hG15.minstret
  have hload15 : SvfprintfSliceLoaded σ15.mem := hmem15 ▸ hload14
  have huload15 : Vsa.Sim.Code.__umoddi3Loaded σ15.mem := hmem15 ▸ huload14
  have hcuload15 : __hidden___udivdi3Loaded σ15.mem := hmem15 ▸ hcuload14
  have hEF15 : EntryFrame vsp c.σ.mem σ15.mem := hmem15 ▸ hEF14
  -- === 831c: li a1,10 ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_8000831c_sn σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000831c#64) vmi15
      hG15 hpc15 hmi15 hload15 rfl hi15
  have hstep16 : Step ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x80008320#64) := obs_alu_pc hobs16
  have hx11_16 : σ16.regs.get? Register.x11 = some (10#64) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li10] at this
  have hx8_16 : σ16.regs.get? Register.x8 = some w :=
    obs_alu_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_15
  have hx23_16 : σ16.regs.get? Register.x23 = some (0#64) :=
    obs_alu_other hobs16 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_15
  have hx25_16 : σ16.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs16 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_15
  have hx27_16 : σ16.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs16 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_15
  have hx12_16 : σ16.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_15
  have hx13_16 : σ16.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs16 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_15
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hload16 : SvfprintfSliceLoaded σ16.mem := hmem16 ▸ hload15
  have huload16 : Vsa.Sim.Code.__umoddi3Loaded σ16.mem := hmem16 ▸ huload15
  have hcuload16 : __hidden___udivdi3Loaded σ16.mem := hmem16 ▸ hcuload15
  have hEF16 : EntryFrame vsp c.σ.mem σ16.mem := hmem16 ▸ hEF15
  -- === 8320: mv a0,s0 ⇒ x10 := w ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80008320_sn σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008320#64) vmi16 w
      hG16 hpc16 hmi16 hx8_16 hload16 rfl hi16
  have hstep17 : Step ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80008324#64) := by
    have := obs_alu_pc hobs17
    rwa [show BitVec.addInt (0x80008320#64 : BitVec 64) 4 = (0x80008324#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_17 : σ17.regs.get? Register.x10 = some w := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 w] at this
  have hx11_17 : σ17.regs.get? Register.x11 = some (10#64) :=
    obs_alu_other hobs17 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_16
  have hx8_17 : σ17.regs.get? Register.x8 = some w :=
    obs_alu_other hobs17 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_16
  have hx23_17 : σ17.regs.get? Register.x23 = some (0#64) :=
    obs_alu_other hobs17 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_16
  have hx25_17 : σ17.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs17 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_16
  have hx27_17 : σ17.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs17 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_16
  have hx12_17 : σ17.regs.get? Register.x12 = some v12₀ :=
    obs_alu_other hobs17 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_16
  have hx13_17 : σ17.regs.get? Register.x13 = some v13₀ :=
    obs_alu_other hobs17 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_16
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hload17 : SvfprintfSliceLoaded σ17.mem := hmem17 ▸ hload16
  have huload17 : Vsa.Sim.Code.__umoddi3Loaded σ17.mem := hmem17 ▸ huload16
  have hcuload17 : __hidden___udivdi3Loaded σ17.mem := hmem17 ▸ hcuload16
  have hEF17 : EntryFrame vsp c.σ.mem σ17.mem := hmem17 ▸ hEF16
  -- === 8324: jal __umoddi3 ⇒ x1 := 8328, PC := 46f4; then umoddi3_loopframe_spec ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80008324_sn σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008324#64) vmi17
      hG17 hpc17 hmi17 hload17 rfl hi17
  have hstep18 : Step ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x800046f4#64) := by
    have := obs_jal_pc hobs18
    rwa [show (0x80008324#64 : BitVec 64) + sign_extend (m := 64) (0x1fc3d0#21)
      = (0x800046f4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_18 : σ18.regs.get? Register.x1 = some (0x80008328#64) := by
    have := obs_jal_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80008324#64 : BitVec 64) 4 = (0x80008328#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_18 : σ18.regs.get? Register.x10 = some w :=
    obs_jal_other hobs18 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_17
  have hx11_18 : σ18.regs.get? Register.x11 = some (10#64) :=
    obs_jal_other hobs18 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_17
  have hx8_18 : σ18.regs.get? Register.x8 = some w :=
    obs_jal_other hobs18 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_17
  have hx23_18 : σ18.regs.get? Register.x23 = some (0#64) :=
    obs_jal_other hobs18 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_17
  have hx25_18 : σ18.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_jal_other hobs18 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_17
  have hx27_18 : σ18.regs.get? Register.x27 = some (0#64) :=
    obs_jal_other hobs18 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_17
  have hx12_18 : σ18.regs.get? Register.x12 = some v12₀ :=
    obs_jal_other hobs18 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_17
  have hx13_18 : σ18.regs.get? Register.x13 = some v13₀ :=
    obs_jal_other hobs18 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_17
  obtain ⟨vmi18, hmi18⟩ := obs_jal_minstret hobs18
  have hload18 : SvfprintfSliceLoaded σ18.mem := hmem18 ▸ hload17
  have huload18 : Vsa.Sim.Code.__umoddi3Loaded σ18.mem := hmem18 ▸ huload17
  have hcuload18 : __hidden___udivdi3Loaded σ18.mem := hmem18 ▸ hcuload17
  have hEF18 : EntryFrame vsp c.σ.mem σ18.mem := hmem18 ▸ hEF17
  -- the mod call: n := w, d := 10, r := 8328; preserves x8/x23/x25/x27
  have humpre : umoddi3_pre w (10#64) (0x80008328#64) σ18.mem
      ⟨σ18, i18, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ :=
    ⟨hG18, huload18, hcuload18, rfl, hpc18, hx10_18, hx11_18, hx1_18, ⟨vmi18, hmi18⟩,
      ⟨v12₀, hx12_18⟩, ⟨v13₀, hx13_18⟩, hi18, by decide, by decide⟩
  obtain ⟨c19, hs19, hG19, hmem19, hpc19, hrem19, htick19, hmi19,
    hx8_19, hx23_19, hx25_19, hx27_19, hx12_19, hx13_19, hx1_19, hframe19⟩ :=
    umoddi3_loopframe_spec (fun R => σ18.regs.get? R) w (10#64) (0x80008328#64) σ18.mem
      w (0#64) (entryTop vsp) (0#64)
      ⟨σ18, i18, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ humpre
      hx8_18 hx23_18 hx25_18 hx27_18 (fun R _ => rfl)
  -- x10 = w % 10 = ofNat (m % 10)
  have hrem19' : c19.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (w.toNat % 10)) := by
    rw [hrem19]; congr 1; exact umod10_sn5 w
  have hload19 : SvfprintfSliceLoaded c19.σ.mem := hmem19 ▸ hload18
  have huload19 : Vsa.Sim.Code.__umoddi3Loaded c19.σ.mem := hmem19 ▸ huload18
  have hcuload19 : __hidden___udivdi3Loaded c19.σ.mem := hmem19 ▸ hcuload18
  obtain ⟨vmi19, hmi19'⟩ := hmi19
  have hEF19 : EntryFrame vsp c.σ.mem c19.σ.mem := hmem19 ▸ hEF18
  -- === 8328: addiw a0,a0,48 ⇒ x10 := '0' + (m % 10) ===
  have hd_lt : w.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_80008328_sn c19.σ c19.tick c19.steps (0x80008328#64) vmi19
      (BitVec.ofNat 64 (w.toNat % 10)) hG19 hpc19 hmi19' hrem19' hload19 rfl htick19
  have hstep20 : Step c19 ⟨σ20, i20, c19.steps+1⟩ := by cases c19; exact hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x8000832c#64) := obs_alu_pc hobs20
  have hx10_20 : σ20.regs.get? Register.x10 =
      some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 (w.toNat % 10)) + sign_extend (m := 64) (0x030#12)) 31 0)) :=
    obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx8_20 : σ20.regs.get? Register.x8 = some w :=
    obs_alu_other hobs20 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_19
  have hx23_20 : σ20.regs.get? Register.x23 = some (0#64) :=
    obs_alu_other hobs20 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_19
  have hx25_20 : σ20.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs20 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_19
  have hx27_20 : σ20.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs20 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_19
  have hx12_20 : ∃ v, σ20.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_19
    exact ⟨v, obs_alu_other hobs20 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_20 : ∃ v, σ20.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_19
    exact ⟨v, obs_alu_other hobs20 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx1_20 : ∃ v, σ20.regs.get? Register.x1 = some v := by
    obtain ⟨v, hv⟩ := hx1_19
    exact ⟨v, obs_alu_other hobs20 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hload20 : SvfprintfSliceLoaded σ20.mem := hmem20 ▸ hload19
  have huload20 : Vsa.Sim.Code.__umoddi3Loaded σ20.mem := hmem20 ▸ huload19
  have hcuload20 : __hidden___udivdi3Loaded σ20.mem := hmem20 ▸ hcuload19
  have hEF20 : EntryFrame vsp c.σ.mem σ20.mem := hmem20 ▸ hEF19
  -- === 832c: sb a0,-1(s9) ⇒ mem[(entryTop vsp)-1] := '0' + m%10 ===
  have h1top : 1 ≤ (entryTop vsp).toNat := by omega
  have haddr_eq : ((entryTop vsp) + sign_extend (m := 64) (0xfff#12)) = BitVec.ofNat 64 ((entryTop vsp).toNat - 1) :=
    sub1_bv_sn5 (entryTop vsp) h1top
  have haddr_toNat : ((entryTop vsp) + sign_extend (m := 64) (0xfff#12)).toNat = (entryTop vsp).toNat - 1 := by
    rw [haddr_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_8000832c_sn σ20 i20 (c19.steps+1) (0x8000832c#64) vmi20 (entryTop vsp)
      (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 (w.toNat % 10)) + sign_extend (m := 64) (0x030#12)) 31 0))
      hG20 hpc20 hmi20 hx25_20 hx10_20 hload20 rfl
      (by rw [haddr_toNat]; omega) (by rw [haddr_toNat]; omega) (by rw [haddr_toNat]; omega) hi20
  have hstep21 : Step ⟨σ20,i20,c19.steps+1⟩ ⟨σ21,i21,c19.steps+1+1⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x80008330#64) := obs_store_pc_sn3 hobs21
  have hx8_21 : σ21.regs.get? Register.x8 = some w :=
    obs_store_other_sn3 Register.x8 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_20
  have hx23_21 : σ21.regs.get? Register.x23 = some (0#64) :=
    obs_store_other_sn3 Register.x23 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_20
  have hx25_21 : σ21.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_store_other_sn3 Register.x25 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_20
  have hx27_21 : σ21.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn3 Register.x27 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_20
  have hx12_21 : ∃ v, σ21.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_20
    exact ⟨v, obs_store_other_sn3 Register.x12 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_21 : ∃ v, σ21.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_20
    exact ⟨v, obs_store_other_sn3 Register.x13 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx1_21 : ∃ v, σ21.regs.get? Register.x1 = some v := by
    obtain ⟨v, hv⟩ := hx1_20
    exact ⟨v, obs_store_other_sn3 Register.x1 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi21, hmi21⟩ := obs_store_minstret_sn3 hobs21
  -- the new memory and BufInv (entryTop vsp) m 1
  have hNP20 : (afterNextPC (afterPrelude σ20) (0x8000832c#64)).mem = σ20.mem := rfl
  have hmem21q : σ21.mem = σ20.mem.insert ((entryTop vsp).toNat - 1)
      (stData 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 (w.toNat % 10)) + sign_extend (m := 64) (0x030#12)) 31 0))) := by
    rw [hmem21, hNP20, haddr_toNat]
  have hbufinv21 : BufInv (entryTop vsp) w.toNat (0 + 1) σ21.mem := by
    rw [hmem21q]
    have hstd : stData 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 (w.toNat % 10)) + sign_extend (m := 64) (0x030#12)) 31 0))
        = BitVec.ofNat 8 (48 + w.toNat % 10) := emit_byte (w.toNat % 10) hd_lt
    rw [hstd]
    have hbase : BufInv (entryTop vsp) w.toNat 0 σ20.mem := fun j hj => absurd hj (Nat.not_lt_zero j)
    have := bufinv_store (entryTop vsp) w.toNat 0 σ20.mem hbase (by omega)
    rw [Nat.pow_zero, Nat.div_one] at this
    exact this
  have hload21 : SvfprintfSliceLoaded σ21.mem := by
    rw [hmem21q]
    exact svfprintfSlice_insert_sn3 _ _ _ (by omega) hload20
  have huload21 : Vsa.Sim.Code.__umoddi3Loaded σ21.mem := by
    rw [hmem21q]
    exact umoddi3_insert_sn3 _ _ _ (by omega) huload20
  have hcuload21 : __hidden___udivdi3Loaded σ21.mem := by
    rw [hmem21q]
    exact cudivdi3_insert_sn3 _ _ _ (by omega) hcuload20
  have hEF21 : EntryFrame vsp c.σ.mem σ21.mem := by
    rw [hmem21q]
    exact entryFrame_insert_sn5 vsp _ _ _ _ ⟨by omega, by omega⟩ hEF20
  -- === 8330: addi s10,s9,-1 ⇒ x26 := (entryTop vsp)-1 ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_80008330_sn σ21 i21 (c19.steps+1+1) (0x80008330#64) vmi21 (entryTop vsp)
      hG21 hpc21 hmi21 hx25_21 hload21 rfl hi21
  have hstep22 : Step ⟨σ21,i21,c19.steps+1+1⟩ ⟨σ22,i22,c19.steps+1+1+1⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some (0x80008334#64) := obs_alu_pc hobs22
  have hx26_22 : σ22.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1)) := by
    have := obs_alu_rd hobs22 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [haddr_eq] at this
  have hx8_22 : σ22.regs.get? Register.x8 = some w :=
    obs_alu_other hobs22 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_21
  have hx23_22 : σ22.regs.get? Register.x23 = some (0#64) :=
    obs_alu_other hobs22 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_21
  have hx25_22 : σ22.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs22 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_21
  have hx27_22 : σ22.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs22 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_21
  have hx12_22 : ∃ v, σ22.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_21
    exact ⟨v, obs_alu_other hobs22 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_22 : ∃ v, σ22.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_21
    exact ⟨v, obs_alu_other hobs22 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx1_22 : ∃ v, σ22.regs.get? Register.x1 = some v := by
    obtain ⟨v, hv⟩ := hx1_21
    exact ⟨v, obs_alu_other hobs22 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi22, hmi22⟩ := obs_alu_minstret hobs22
  have hload22 : SvfprintfSliceLoaded σ22.mem := hmem22 ▸ hload21
  have huload22 : Vsa.Sim.Code.__umoddi3Loaded σ22.mem := hmem22 ▸ huload21
  have hcuload22 : __hidden___udivdi3Loaded σ22.mem := hmem22 ▸ hcuload21
  have hbufinv22 : BufInv (entryTop vsp) w.toNat (0 + 1) σ22.mem := by rw [hmem22]; exact hbufinv21
  have hEF22 : EntryFrame vsp c.σ.mem σ22.mem := hmem22 ▸ hEF21
  -- === 8334: addiw s7,s7,1 ⇒ x23 := 1 ===
  obtain ⟨σ23, i23, hs23, hi23, hG23, hmem23, hobs23⟩ :=
    site_80008334_sn σ22 i22 (c19.steps+1+1+1) (0x80008334#64) vmi22 (BitVec.ofNat 64 0)
      hG22 hpc22 hmi22 hx23_22 hload22 rfl hi22
  have hstep23 : Step ⟨σ22,i22,c19.steps+1+1+1⟩ ⟨σ23,i23,c19.steps+1+1+1+1⟩ := hs23
  have hpc23 : σ23.regs.get? Register.PC = some (0x80008338#64) := obs_alu_pc hobs23
  have hx23_23 : σ23.regs.get? Register.x23 = some (BitVec.ofNat 64 (0 + 1)) := by
    have := obs_alu_rd hobs23 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addiw1_sn3 0 (by omega)] at this
  have hx8_23 : σ23.regs.get? Register.x8 = some w :=
    obs_alu_other hobs23 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_22
  have hx25_23 : σ23.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_alu_other hobs23 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_22
  have hx26_23 : σ23.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1)) :=
    obs_alu_other hobs23 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_22
  have hx27_23 : σ23.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs23 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_22
  have hx12_23 : ∃ v, σ23.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_22
    exact ⟨v, obs_alu_other hobs23 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_23 : ∃ v, σ23.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_22
    exact ⟨v, obs_alu_other hobs23 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx1_23 : ∃ v, σ23.regs.get? Register.x1 = some v := by
    obtain ⟨v, hv⟩ := hx1_22
    exact ⟨v, obs_alu_other hobs23 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi23, hmi23⟩ := obs_alu_minstret hobs23
  have hload23 : SvfprintfSliceLoaded σ23.mem := hmem23 ▸ hload22
  have huload23 : Vsa.Sim.Code.__umoddi3Loaded σ23.mem := hmem23 ▸ huload22
  have hcuload23 : __hidden___udivdi3Loaded σ23.mem := hmem23 ▸ hcuload22
  have hbufinv23 : BufInv (entryTop vsp) w.toNat (0 + 1) σ23.mem := by rw [hmem23]; exact hbufinv22
  have hEF23 : EntryFrame vsp c.σ.mem σ23.mem := hmem23 ▸ hEF22
  -- === 8338: beqz s11 TAKEN ⇒ PC := 82fc ===
  obtain ⟨σ24, i24, hs24, hi24, hG24, hmem24, hobs24⟩ :=
    site_80008338_taken_sn σ23 i23 (c19.steps+1+1+1+1) (0x80008338#64) vmi23 (0#64)
      hG23 hpc23 hmi23 hx27_23 hload23 rfl (by decide) hi23
  have hstep24 : Step ⟨σ23,i23,c19.steps+1+1+1+1⟩ ⟨σ24,i24,c19.steps+1+1+1+1+1⟩ := hs24
  have hpc24 : σ24.regs.get? Register.PC = some (0x800082fc#64) := by
    have := obs_btaken_pc hobs24
    rwa [show (0x80008338#64 : BitVec 64) + sign_extend (m := 64) (0x1fc4#13)
      = (0x800082fc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8_24 : σ24.regs.get? Register.x8 = some w :=
    obs_btaken_other hobs24 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_23
  have hx23_24 : σ24.regs.get? Register.x23 = some (BitVec.ofNat 64 (0 + 1)) :=
    obs_btaken_other hobs24 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_23
  have hx25_24 : σ24.regs.get? Register.x25 = some (entryTop vsp) :=
    obs_btaken_other hobs24 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_23
  have hx26_24 : σ24.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1)) :=
    obs_btaken_other hobs24 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_23
  have hx27_24 : σ24.regs.get? Register.x27 = some (0#64) :=
    obs_btaken_other hobs24 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_23
  have hx12_24 : ∃ v, σ24.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_23
    exact ⟨v, obs_btaken_other hobs24 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_24 : ∃ v, σ24.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_23
    exact ⟨v, obs_btaken_other hobs24 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx1_24 : ∃ v, σ24.regs.get? Register.x1 = some v := by
    obtain ⟨v, hv⟩ := hx1_23
    exact ⟨v, obs_btaken_other hobs24 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi24, hmi24⟩ := obs_btaken_minstret hobs24
  have hload24 : SvfprintfSliceLoaded σ24.mem := hmem24 ▸ hload23
  have huload24 : Vsa.Sim.Code.__umoddi3Loaded σ24.mem := hmem24 ▸ huload23
  have hcuload24 : __hidden___udivdi3Loaded σ24.mem := hmem24 ▸ hcuload23
  have hbufinv24 : BufInv (entryTop vsp) w.toNat (0 + 1) σ24.mem := by rw [hmem24]; exact hbufinv23
  have hEF24 : EntryFrame vsp c.σ.mem σ24.mem := hmem24 ▸ hEF23
  -- === transport the six SlotHolds σ13 → σ24 (mem changes only via the σ21 digit insert) ===
  -- σ13.mem = σ20.mem (σ14..σ20 preserve), then σ21 inserts @entryTop-1 (disjoint), then σ22..σ24 preserve.
  have hmemEq13_20 : σ20.mem = σ13.mem := by
    rw [hmem20, hmem19, hmem18, hmem17, hmem16, hmem15, hmem14]
  have hdig_addr : (entryTop vsp).toNat - 1 = vsp.toNat + 347 := by
    rw [htop_toNat]; omega
  have slotTo24 : ∀ (off : Nat) (vv : BitVec 64),
      (vsp.toNat + off + 8 ≤ vsp.toNat + 347) → SlotHolds vsp off vv σ13.mem →
      (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = vsp.toNat + off →
      SlotHolds vsp off vv σ24.mem := by
    intro off vv hlt h13 haoff
    have h20 : SlotHolds vsp off vv σ20.mem := hmemEq13_20 ▸ h13
    have h21 : SlotHolds vsp off vv σ21.mem := by
      rw [hmem21q]
      exact slotHolds_insert vsp off vv σ20.mem _ _
        (Or.inr (by rw [haoff, hdig_addr]; omega)) h20
    exact hmem24 ▸ hmem23 ▸ hmem22 ▸ h21
  have hslot48_24 : SlotHolds vsp 0x030 v23₀ σ24.mem :=
    slotTo24 0x030 v23₀ (by omega) hslot48_13 ha48
  have hslot56_24 : SlotHolds vsp 0x038 v20 σ24.mem :=
    slotTo24 0x038 v20 (by omega) hslot56_13 ha56
  have hslot120_24 : SlotHolds vsp 0x078 v8₀ σ24.mem :=
    slotTo24 0x078 v8₀ (by omega) hslot120_13 ha120
  have hslot32_24 : SlotHolds vsp 0x020 v28₀ σ24.mem :=
    slotTo24 0x020 v28₀ (by omega) hslot32_13 ha32
  have hslot40_24 : SlotHolds vsp 0x028 vt1 σ24.mem :=
    slotTo24 0x028 vt1 (by omega) hslot40_13 ha40
  have hslot112_24 : SlotHolds vsp 0x070 (entryTop vsp) σ24.mem :=
    slotTo24 0x070 (entryTop vsp) (by omega) hslot112_13 ha112
  -- === transport x2 (σ12) and x20 (σ8) forward to σ24 (both in NotWrittenL, never written) ===
  have hx2_13 : σ13.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_12
  have hx2_14 : σ14.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_13
  have hx2_15 : σ15.regs.get? Register.x2 = some vsp := by
    rw [frame_jr hobs15 Register.x2 (by decide)]; exact hx2_14
  have hx2_16 : σ16.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_15
  have hx2_17 : σ17.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_16
  have hx2_18 : σ18.regs.get? Register.x2 = some vsp :=
    obs_jal_other hobs18 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_17
  have hx2_19 : c19.σ.regs.get? Register.x2 = some vsp := by
    rw [hframe19 Register.x2 (by decide)]; exact hx2_18
  have hx2_20 : σ20.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_19
  have hx2_21 : σ21.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn3 Register.x2 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_20
  have hx2_22 : σ22.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs22 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_21
  have hx2_23 : σ23.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs23 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_22
  have hx2_24 : σ24.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs24 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_23
  -- x20 (`s4`) is reloaded (dead) at σ7's `ld s4,104(sp)`; track its existence forward.
  obtain ⟨vs4j, hx20_7⟩ : ∃ v, σ7.regs.get? Register.x20 = some v :=
    ⟨_, obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have hx20_8 : σ8.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_7
  have hx20_9 : σ9.regs.get? Register.x20 = some vs4j :=
    obs_store_other_sn4 Register.x20 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_8
  have hx20_10 : σ10.regs.get? Register.x20 = some vs4j :=
    obs_store_other_sn4 Register.x20 hobs10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_9
  have hx20_11 : σ11.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs11 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_10
  have hx20_12 : σ12.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs12 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_11
  have hx20_13 : σ13.regs.get? Register.x20 = some vs4j :=
    obs_store_other_sn4 Register.x20 hobs13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_12
  have hx20_14 : σ14.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs14 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_13
  have hx20_15 : σ15.regs.get? Register.x20 = some vs4j := by
    rw [frame_jr hobs15 Register.x20 (by decide)]; exact hx20_14
  have hx20_16 : σ16.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs16 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_15
  have hx20_17 : σ17.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs17 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_16
  have hx20_18 : σ18.regs.get? Register.x20 = some vs4j :=
    obs_jal_other hobs18 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_17
  have hx20_19 : c19.σ.regs.get? Register.x20 = some vs4j := by
    rw [hframe19 Register.x20 (by decide)]; exact hx20_18
  have hx20_20 : σ20.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs20 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_19
  have hx20_21 : σ21.regs.get? Register.x20 = some vs4j :=
    obs_store_other_sn3 Register.x20 hobs21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_20
  have hx20_22 : σ22.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs22 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_21
  have hx20_23 : σ23.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs23 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_22
  have hx20_24 : σ24.regs.get? Register.x20 = some vs4j :=
    obs_btaken_other hobs24 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_23
  -- === assemble LSt g (entryTop vsp) m 0 at σ24 ===
  refine ⟨⟨σ24, i24, c19.steps+1+1+1+1+1⟩, ?_, ?_, htopok, hEF24,
    hx2_24, ⟨vs4j, hx20_24⟩, hslot56_24, v20, v28₀, v23₀, v8₀,
    hslot112_24, hslot56_24, hslot40_24, hslot32_24, hslot48_24, hslot120_24⟩
  · -- Steps chain
    exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
      ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans
      (hs19.trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans
      ((Steps.single hstep22).trans ((Steps.single hstep23).trans
      (Steps.single hstep24)))))))))))))))))))))))
  · refine {
      good := hG24, loaded := hload24, uloaded := huload24, culoaded := hcuload24,
      pc := hpc24, s0 := ?_, s9 := ?_, s10 := ?_, s7 := hx23_24, s11 := hx27_24,
      x12 := hx12_24, x13 := hx13_24, x1 := hx1_24, minstret := ⟨vmi24, hmi24⟩, tick := hi24,
      bufinv := hbufinv24, hframe := fun R _ => rfl }
    · -- s0 : x8 = ofNat (m / 10^0) = w
      rw [show w.toNat / 10 ^ 0 = w.toNat from by rw [Nat.pow_zero, Nat.div_one]]
      rw [show BitVec.ofNat 64 w.toNat = w from by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]]
      exact hx8_24
    · -- s9 : x25 = ofNat ((entryTop vsp).toNat - 0) = (entryTop vsp)
      rw [show (entryTop vsp).toNat - 0 = (entryTop vsp).toNat from rfl]
      rw [show BitVec.ofNat 64 (entryTop vsp).toNat = (entryTop vsp) from by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (entryTop vsp).isLt]]
      exact hx25_24
    · -- s10 : x26 = ofNat ((entryTop vsp).toNat - 1 - 0)
      rw [show (entryTop vsp).toNat - 1 - 0 = (entryTop vsp).toNat - 1 from rfl]
      exact hx26_24

/-! ## The capstone: entry → complete digit buffer at the loop exit -/

/-- From the fast/multi split at `0x80008100` with magnitude `w` (`> 9`), the
machine runs the whole multi-digit conversion and exits at `0x80008358` with the
complete decimal digit string of `w.toNat` in the descending buffer below
`sp+348` (`BufInv`), digit count `p+1` where `p` is terminal
(`w.toNat / 10^p ≤ 9`). -/
theorem entryToDigits_spec (w vsp vt1 v20 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008100#64))
    (hx14 : c.σ.regs.get? Register.x14 = some w)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hflag : vt1 &&& sign_extend (m := 64) (0x400#12) = 0#64)
    (hx8e : ∃ v, c.σ.regs.get? Register.x8 = some v)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23e : ∃ v, c.σ.regs.get? Register.x23 = some v)
    (hx28e : ∃ v, c.σ.regs.get? Register.x28 = some v)
    (hx12e : ∃ v, c.σ.regs.get? Register.x12 = some v)
    (hx13e : ∃ v, c.σ.regs.get? Register.x13 = some v)
    (hm9 : 9 < w.toNat)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ ∃ p, w.toNat / 10 ^ p ≤ 9 ∧ p + 1 ≤ 20 ∧
      c'.σ.regs.get? Register.PC = some (0x80008358#64) ∧
      c'.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p + 1)) ∧
      BufInv (entryTop vsp) w.toNat (p + 1) c'.σ.mem ∧
      GoodState c'.σ ∧ c'.tick < 2 ∧
      (∃ v, c'.σ.regs.get? Register.minstret = some v) ∧
      EntryFrame vsp c.σ.mem c'.σ.mem ∧
      -- surfaced for the flush restore block (`exitToPrint_spec`):
      SvfprintfSliceLoaded c'.σ.mem ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      (∃ vs4j, c'.σ.regs.get? Register.x20 = some vs4j) ∧
      c'.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) ∧
      -- the width slot 56 holds the *named* entry `x20` value `v20` (the parsed field width):
      SlotHolds vsp 0x038 v20 c'.σ.mem ∧
      ∃ vwid vt3 vs7 vs0,
        SlotHolds vsp 0x070 (entryTop vsp) c'.σ.mem ∧
        SlotHolds vsp 0x038 vwid c'.σ.mem ∧
        SlotHolds vsp 0x028 vt1 c'.σ.mem ∧
        SlotHolds vsp 0x020 vt3 c'.σ.mem ∧
        SlotHolds vsp 0x030 vs7 c'.σ.mem ∧
        SlotHolds vsp 0x078 vs0 c'.σ.mem := by
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=
    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw
  obtain ⟨c1, hs1, hLSt, htopok, hEF1,
    hx2_1, hx20_1e, hslot56v20, vwid, vt3, vs7, vs0,
    hslot112, hslot56, hslot40, hslot32, hslot48, hslot120⟩ :=
    loopEntry_spec w vsp vt1 v20 c hG hload huload hcuload hpc hx14 hx2 hx6 hflag
      hx8e hx20 hx23e hx28e hx12e hx13e hm9 htlo hhi halign htick
  obtain ⟨c2, hs2, p, hexit, hpb, hpc', hx23', hbuf', hG', htick', hmi', hDF, hx26', hload', hframeL⟩ :=
    decimalLoop_spec (fun R => c1.σ.regs.get? R) (entryTop vsp) w.toNat w.isLt htopok
      c1.σ.mem c1 ⟨⟨0, hLSt, by omega⟩, digitFrame_rfl (entryTop vsp) c1.σ.mem⟩
  have hEF : EntryFrame vsp c.σ.mem c2.σ.mem := by
    intro a ha
    rw [hDF a (by omega)]
    exact hEF1 a ha
  -- x2/x20 survive the loop (both ∈ NotWrittenL, frame back to c1)
  have hx2_2 : c2.σ.regs.get? Register.x2 = some vsp := by
    rw [hframeL Register.x2 (by decide)]; exact hx2_1
  have hx20_2 : ∃ vs4j, c2.σ.regs.get? Register.x20 = some vs4j := by
    obtain ⟨vs4j, hvs4j⟩ := hx20_1e
    exact ⟨vs4j, by rw [hframeL Register.x20 (by decide)]; exact hvs4j⟩
  -- SlotHolds survive the loop (each slot below the digit window [top-20, top))
  have hslotDF : ∀ (off : Nat) (vv : BitVec 64),
      (vsp.toNat + off + 8 ≤ (entryTop vsp).toNat - 20) →
      (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = vsp.toNat + off →
      SlotHolds vsp off vv c1.σ.mem → SlotHolds vsp off vv c2.σ.mem := by
    intro off vv hb haoff h
    exact slotHolds_digitFrame (entryTop vsp) vsp off vv c1.σ.mem c2.σ.mem
      (by rw [haoff]; omega) hDF h
  have ha48 : (vsp + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat + 48 :=
    addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw
  have ha56 : (vsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat + 56 :=
    addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw
  have ha120 : (vsp + sign_extend (m := 64) (0x078#12)).toNat = vsp.toNat + 120 :=
    addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw
  have ha32 : (vsp + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 32 :=
    addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw
  have ha40 : (vsp + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat + 40 :=
    addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw
  have ha112 : (vsp + sign_extend (m := 64) (0x070#12)).toNat = vsp.toNat + 112 :=
    addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw
  refine ⟨c2, hs1.trans hs2, p, hexit, hpb, hpc', hx23', hbuf', hG', htick', hmi', hEF,
    hload', hx2_2, hx20_2, hx26',
    hslotDF 0x038 v20 (by rw [htop_toNat]; omega) ha56 hslot56v20,
    vwid, vt3, vs7, vs0,
    hslotDF 0x070 (entryTop vsp) (by rw [htop_toNat]; omega) ha112 hslot112,
    hslotDF 0x038 vwid (by rw [htop_toNat]; omega) ha56 hslot56,
    hslotDF 0x028 vt1 (by rw [htop_toNat]; omega) ha40 hslot40,
    hslotDF 0x020 vt3 (by rw [htop_toNat]; omega) ha32 hslot32,
    hslotDF 0x030 vs7 (by rw [htop_toNat]; omega) ha48 hslot48,
    hslotDF 0x078 vs0 (by rw [htop_toNat]; omega) ha120 hslot120⟩

end Vsa.Sim
