import Vsa.Sim.SnprintfSpec18
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch15Part04

/-!
# M3 Layer-3 — `SnprintfSpec19` : the `__ssputs_r` fast path (`_sp`), composed with `memmove`

Total-correctness spec for the `__ssputs_r` fast path (`0x8001438c … 0x800143f0`),
composed with `memmove_fwd_spec` (SnprintfSpec18) at the `jal` site `0x800143c0`.

From the entry with the sink struct pointer `p` in `a1`, the source base `s` in
`a2`, the length `n` (`1 ≤ n ≤ 31`) in `a3`, the cursor `d` pinned at `[p, p+8)`
and the capacity word `cap32` at `[p+12, p+16)` (with `n < sext32 cap32` — the
fast-path guard), the machine runs to `ret` (`PC = r`) with:

* `a0 = 0` (success),
* the `n` source bytes copied to `[d, d+n)`,
* the cursor slot `[p, p+8)` holding `d + n`,
* the capacity slot `[p+12, p+16)` holding the `subw` result `spNewCap cap32 n`,
* callee-saved `s0/s1/sp` restored (`v8`/`v9`/`vsp`), and
* all memory outside `[d,d+n) ∪ [p,p+8) ∪ [p+12,p+16) ∪ [vsp-24,vsp)` unchanged.

The stack frame is 64 bytes (`addi sp,sp,-64`); the three spill slots actually
written are `vsp-24` (`s1`), `vsp-16` (`s0`), `vsp-8` (`ra`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Small value bridges -/

/-- The 4-byte LE reassembly of the byte slices of a 32-bit word is the word. -/
theorem word4_eq_sp (w : BitVec 32) :
    ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8) : BitVec (8 * 4)) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_recon]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

/-- The `lw` of the 4 pinned `cap32` bytes yields `sext32 cap32`. -/
theorem lw_cap_reassemble_sp (w : BitVec 32) :
    (sign_extend (m := 64)
      ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
        (w.extractLsb' 0 8) : BitVec (8 * 4)) : BitVec 64) = sign_extend (m := 64) w :=
  congrArg _ (word4_eq_sp w)

/-! ## Code-region survival (`__ssputs_r` spans `[0x8001438c, 0x80014520)`) -/

/-! ## 8-byte / 4-byte slot pins -/

/-- The 8 little-endian bytes of `sdData_val v` pinned at `[a, a+8)`. -/
def Pin8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Prop :=
  mem[a]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[a + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[a + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[a + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[a + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[a + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[a + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[a + 7]? = some ((sdData_val v).extractLsb' 56 8)

/-- The 4 little-endian bytes of a 32-bit word pinned at `[a, a+4)`. -/
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

/-! ## The three-slot stack image -/

/-! ## Region / side-condition bundle -/

/-! ## Blanket ghost-frame predicate (`NotWrittenSp`) + per-class helpers

The fast path writes GPRs `x1, x2, x8, x9, x10, x11, x12, x14, x15`; `x13` is
written inside `memmove` (its frame only guarantees `NotWrittenMv`), so it is
excluded too. -/
abbrev NotWrittenSp (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x9 == R) = false ∧
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  NotWrittenMv R

theorem NotWrittenSp.mv {R : Register} (h : NotWrittenSp R) : NotWrittenMv R := h.2.2.2.2.2.2.2.2.2.2

/-! ## Pre / mid / post condition -/

/-! ## Head: entry `0x8001438c` → `memmove` → back at `0x800143c4` -/

/-! ## Tail: `0x800143c4` → cursor/capacity update → epilogue → `ret` -/

/-! ## The composed fast-path spec -/

end Vsa.Sim
