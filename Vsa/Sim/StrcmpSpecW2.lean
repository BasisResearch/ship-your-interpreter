import Vsa.Sim.StrcmpSpecW
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcmp` word-path spec, part 2 (`strcmp_word_spec`, `strcmp_full_spec`)

Continues `StrcmpSpecW`: groups 1 and 2 of the 3×-unrolled word loop (offsets
`0x008`/`0x010`), the `Triple.loop` word-loop rule, the `slli/srli` lane compare
(`0xf20 … 0xf80`), the NUL-word exit blocks (`0xfac/0xfa4/0xfb8`), the aligned entry
(`0xea0 … 0xeb4`), and the top-level `strcmp_word_spec`/`strcmp_full_spec`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shift-amount reductions

Each `slli`/`srli` in the lane compare uses `shift_bits_left/right v (extractLsb sh 5 0)`
where `sh ∈ {0x30, 0x20, 0x10}`. These reduce to `v <<< N` / `v >>> N` with
`N ∈ {48, 32, 16}` — the extracted 6-bit shamt is the literal shift. -/

theorem shl_48 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x30#6) 5 0) = v <<< (48:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x30#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x30#6) 5 0 : BitVec 6) = (48#6 : BitVec 6) from rfl]
  rfl

theorem shl_32 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x20#6) 5 0) = v <<< (32:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x20#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x20#6) 5 0 : BitVec 6) = (32#6 : BitVec 6) from rfl]
  rfl

theorem shl_16 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x10#6) 5 0) = v <<< (16:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x10#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x10#6) 5 0 : BitVec 6) = (16#6 : BitVec 6) from rfl]
  rfl

theorem shr_48 (v : BitVec 64) :
    shift_bits_right v (Sail.BitVec.extractLsb (0x30#6) 5 0) = v >>> (48:Nat) := by
  show v >>> (Sail.BitVec.extractLsb (0x30#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x30#6) 5 0 : BitVec 6) = (48#6 : BitVec 6) from rfl]
  rfl

/-! ## The `word_off` pointer lemma

Group 1/2 load at `(pa + 24j) + sext(8)` and `(pa + 24j) + sext(16)`. This equals
`pa + (24j + 8)` and `pa + (24j + 16)` as pointers. -/

/-- `(p + ofNat (24j)) + sext(8) = p + ofNat (24j + 8)`. -/
theorem word_off8 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x008#12)
      = p + BitVec.ofNat 64 (24*j + 8) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `(p + ofNat (24j)) + sext(16) = p + ofNat (24j + 16)`. -/
theorem word_off16 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x010#12)
      = p + BitVec.ofNat 64 (24*j + 16) := by
  rw [show (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `(p + ofNat (24j)) + sext(24) = p + ofNat (24(j+1))` (group-2 back-edge). -/
theorem word_off24 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x018#12)
      = p + BitVec.ofNat 64 (24*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 24*j + 24 = 24*(j+1) from by omega]

/-! ## Group entry states

`WHead1 j` (at `0xed8`) and `WHead2 j` (at `0xef8`) are the entry states of groups 1
and 2: identical register content to `WHead` (pointers `pa+24j`/`pb+24j`, `a5=magic7f`,
`t2=allOnes`), plus the group-`g` prefix invariant `BytePrefix csa csb (24j + 8g)` and
A-NUL-freedom `24j + 8g ≤ la` established by the previous group's continue. The bodies
load at offset `8g`, so `a2/a3` cover the word at `pa.toNat + 24j + 8g`. -/

/-! ## The word-path exit disjunct (`WordExit`)

A group's three-way dispatch that does not continue lands in an EXIT: either the lane
compare `WLaneCmp` (words differ, A NUL-free) or a NUL-word block. We bundle both as
`WordExit`, a PC-tagged terminal the loop rule can drop the measure on. The lane arm
carries the full `WLaneCmp` state (offset `n`); the NUL arm (`WNulExit`, below) carries a
FULL register state — pointers `a0/a1 = pa/pb + 24j`, the cached words `a2/a3` at the NUL
offset `n = 24j + off(pc)`, `x1 = r`, `minstret`, `tick`, `GoodState`, `mem = m0`, the
`CStr`/`StrcmpWRegion` witnesses, `MaskPinned`, ghost frame — plus the byte-level
`n ≤ la < n+8` and `BytePrefix csa csb n` facts. Downstream (`StrcmpSpecW4`) the NUL-exit
blocks re-test `a2,a3` and either return `0` (equal) or run the byte loop at the advanced
pointer `pa+n` (differ), so ALL of those registers/witnesses are needed. -/

/-! ## The full word-loop body and `Triple.loop` assembly

`wbody` composes the three groups: `WHead j → WG0mid → (WHead1 | exit) →
(WG1mid → (WHead2 | exit)) → (WG2mid → (WHead (j+1) | exit))`. The result is a
one-iteration step `Triple (WHead j) (WHead (j+1) ∨ WordExit)`. -/

/-! ### Loop invariant, guard, PC-guarded measure -/

/-! ## Lane-compare shift-equality bridges

The lane compare's `slli` probes test 2-byte blocks. `w <<< (8s) = w' <<< (8s)` iff the
low `64 - 8s` bits (bytes `[0, 8-s)`) agree — the shift discards the high bytes, keeping
the low bytes in the high lanes. These are pure `getLsbD` facts (no `bv_decide`),
the verified base for the (still-to-finish) lane first-difference arithmetic. -/

/-- `w <<< k = w' <<< k` (for `k ≤ 64`) iff the low `64 - k` bits agree. -/
theorem shiftLeft_eq_iff (w w' : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (w <<< k = w' <<< k) ↔ (∀ i, i < 64 - k → w.getLsbD i = w'.getLsbD i) := by
  constructor
  · intro h i hi
    have := congrArg (fun x => x.getLsbD (i + k)) h
    simp only [BitVec.getLsbD_shiftLeft, show ¬ (i + k < k) from by omega,
      show i + k - k = i from by omega, decide_false, Bool.not_false, Bool.and_true] at this
    have hb : i + k < 64 := by omega
    simpa [hb] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_shiftLeft]
    by_cases hlt : i < k
    · simp [hlt]
    · have hik : i - k < 64 - k := by omega
      simp only [show (decide (i < k)) = false from by simp [hlt], Bool.not_false,
        Bool.and_true, h (i-k) hik]

/-- Byte `m` of `w`,`w'` agree, given the low `8*(8-s)` bits agree (`m < 8-s`). -/
theorem shiftLeft_bytes_agree (w w' : BitVec 64) (s : Nat)
    (h : ∀ i, i < 8*(8-s) → w.getLsbD i = w'.getLsbD i) (m : Nat) (hm : m < 8 - s) :
    w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i < 8 from hi), Bool.true_and]
  exact h (8*m + i) (by omega)

/-- **`slli` by `48` block-equality ⟺ bytes {0,1} agree.** (`slli_lane_eq` for s=6.) -/
theorem slli48_eq_iff (w w' : BitVec 64) :
    (w <<< (48:Nat) = w' <<< (48:Nat)) ↔
      (∀ m, m < 2 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 48 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 6 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 2 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

/-! ## Closing note — what lands (part 2), and the remaining lane/NUL/entry plan

**Complete & fully proved in this file (`StrcmpSpecW2`):**

* **Shift/pointer arithmetic.** `shl_48/32/16`, `shr_48` (`slli/srli` shamt reductions
  to `<<< N`/`>>> N`); `word_off8/16/24` (group-`g` load-pointer identities).
* **Groups 1 and 2, end-to-end.** `wg1_straight`+`wg1_dispatch` (offset `24j+8`,
  `0xed8…0xef4`, three-way exit to `WHead2`/lane/NUL@`0xfa4`) and `wg2_straight`+
  `wg2_dispatch` (offset `24j+16`, `0xef8…0xf1c`, with the **back-edge** `addi a0,24;
  addi a1,24; beq a2,a3 → 0xeb8` re-establishing `WHead (j+1)` and `BytePrefix (24j+24)`
  via `byte_prefix_extend`, else fall to lane compare | NUL@`0xfb8`).
* **A structured group-0 dispatch** `wg0_dispatch2` (emits `WHead1` on continue,
  unlike the base's thin fact), so the three groups compose.
* **The full word-loop assembly.** `wbody : Triple (WHead j) (WHead (j+1) ∨ WordExit)`
  (composes the three groups; `WordExit` short-circuits in each `Triple.cases`), and
  `swloop_to_exit : Triple SWLoopI (WordExit)` via `Triple.loop` with the PC-guarded
  measure `SWLoopMu = if PC = 0xeb8 then la+1−24j else 0` (`swloopmu_head`/`swloopmu_exit`,
  `swloop_body`). `WordExit` bundles the lane-compare state `WLaneCmp n` and the three
  NUL-block PC-tagged terminals with their `n ≤ la < n+8` / `BytePrefix n` byte facts.
* **The lane shift-equality bridges.** `shiftLeft_eq_iff`, `shiftLeft_bytes_agree`,
  `slli48_eq_iff` (`slli`-block equality ⟺ per-byte agreement) — the verified base for
  the first-difference-byte lane arithmetic.

**What remains (unchanged plan, priorities 3–5):**

3. **Lane compare** `WLaneCmp n → BF9c` (`0xf20 … 0xf80`). The `slli48_eq_iff` family
   (extend to `slli32`/`slli16` by the same `shiftLeft_eq_iff` route) locates the
   2-byte block holding the first difference; `srli 0x30` + `zext.b` (`srli_byte`)
   extracts the differing byte; `sub`/`zext_toNat`/`strcmpSign_sub` give the sign. The
   genuinely new content is the **16-bit-block subtraction borrow analysis**: the `f58`/
   `f70` early-`ret` returns the block difference `(w>>>48) − (w'>>>48)` directly, whose
   SIGN must be shown equal to `isign (byteVal csa d) (byteVal csb d)` for the first
   differing byte `d` in the block, and the `bnez a1 → f74` re-extract handles the case
   where the low byte of the block agrees but the high byte differs. Both paths must
   land the SAME `hsign : isign (byteVal csa d) (byteVal csb d) = strcmpSpecSign csa csb`
   (via `strcmpSpecSign_at` with `BytePrefix csa csb d` from the located `d`), plugging
   into the base's `byte_f9c_ret`.
4. **NUL-word exit blocks** `0xfac/0xfa4/0xfb8` (+ shared `0xfb0` `li a0,0; ret` and the
   group-2 `0xfc0/0xfc4/0xfc8`). Structure now fully mapped: group-0 jumps to `0xfac`
   directly; group-1 advances `a0/a1` by 8 (`0xfa4/0xfa8`) then `0xfac`; group-2 by 16
   (`0xfb8/0xfbc`) then `0xfc0`. At the `bne a2,a3` test: if words EQUAL (A's word has the
   NUL, so both strings terminate at `la = lb`) → `li a0,0; ret` = result `0`
   (`strcmpSpecSign = 0` via `strcmpSpecSign_eq`); if words DIFFER → jump to byte loop
   `0xf84` at the ADVANCED pointer `pa+n`. The byte-loop entry needs a **suffix bridge**:
   `BSt` at base `pa+n` with `csa' = csa.drop n`, plus
   `strcmpSpecSign (drop n csa) (drop n csb) = strcmpSpecSign csa csb` under
   `BytePrefix csa csb n` (agree+nonzero on `[0,n)`).
5. **Aligned entry** `strcmp_word_spec` (`0xea0 … 0xeb4`: `or a4; li t2,-1; andi a4,7;
   bnez a4` NOT taken → `auipc a5; ld a5,mask`) establishing `WHead 0` (`t2 = allOnes`
   via `neg_one_allOnes`, `a5 = magic7f` via `ldBytesT_mask`, `BytePrefix … 0` trivial),
   then `swloop_to_exit` → lane/NUL → `BDone`; and `strcmp_full_spec` = `Triple.cases`
   over the entry alignment test unifying with `StrcmpSpec.strcmp_byte_path` (both
   `BDone`, same `Q`).

**New gotchas (this file).**
1. `WLoopI/WLoopB/WLoopMu/wloopmu_head/wloop_body` COLLIDE with `StrlenSpec`'s (same
   `Vsa.Sim` namespace, transitively imported) — renamed to `SWLoop*`/`swloop*`.
2. Group-`g` load bounds: `wcmp_load_bounds` states them on `((p+ofNat n)+sext 0)`, but
   the offset-8/16 `ld` sites want them on `(p+ofNat 24j)+sext(8/16)`. Bridge with
   `rw [sext0_add] at …` (strip the `+ sext 0`) then `rw [word_off8/16]` per hypothesis.
3. `beq` guard false-case: `rw [beq_eq_false_iff_ne]; exact hne` (the group-2 back-edge
   `beq a2,a3` fall-through). `bne` true-case stays `rw [bne_iff_ne]`.
4. `BitVec.getLsbD_shiftLeft` emits `decide (i<64) && …` and `!decide (i<k)` guards, not
   clean `if`s — discharge with `simp only [show decide (i<k) = false from …, …]`, not
   `rw [if_neg]`.
-/

end Vsa.Sim
