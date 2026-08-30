import Vsa.Sim.SsprintSites
import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.SnprintfSpec9
import Vsa.Sim.RegPins
import Vsa.Sim.PtrArith
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec20` : the `__ssprint_r` 2-iovec flush loop (`_sr`)

Total-correctness spec for the `%lld`-flush call of `__ssprint_r`
(`0x8000e908 … 0x8000e9c8`), composed twice with the verified `__ssputs_r`
fast path (`ssputs_fast_spec`, SnprintfSpec19) at the `jal` site `0x8000e97c`.

`__ssprint_r(reent, cursor_struct, uio)` is entered with

* `a0 = va0` (the reent pointer, passed through to `__ssputs_r`),
* `a1 = p` (the string-sink cursor struct: cursor `d` at `[p,p+8)`, capacity
  word `cap32` at `[p+12,p+16)`),
* `a2 = q` (the `_uio`-like struct: iov base pointer `viov` at `[q,q+8)`,
  iov count (= `2`) at `[q+8,q+12)`, resid (= `n1+n2`) at `[q+16,q+24)`),

and a 2-entry iov array at `viov`: `iov[0] = (s1, n1)` (the sign byte,
`bs1`) and `iov[1] = (s2, n2)` (the digits, `bs2`).  On this path the
`beqz`-empty short circuit at `0x8000e91c` is NOT taken, the loop runs
exactly twice (count `2 → 1 → 0`, resid `n1+n2 → n2 → 0`), each iteration
calls `__ssputs_r(reent, p, iov[i].base, iov[i].len)`, and the common tail
restores `ra/s0/s1/s2/s3/s4/s5/sp`, clears the `q` resid/count fields and
returns `0`.

The deliverable `ssprint_iov2_spec` : from the entry, the machine runs to
`PC = r` with `a0 = 0`, `[d,d+n1) = bs1`, `[d+n1,d+n1+n2) = bs2`, the cursor
slot advanced to `d + (n1+n2)`, the capacity word decremented twice
(`cap32 - n1 - n2`), the `q` resid/count fields zeroed, all callee-saves and
`sp` restored, and every byte outside the six written windows unchanged.

The second call's capacity guard comes from the first call's postcondition:
`swData (spNewCap cap32 n1) = cap32 - ofNat n1` (`swData_spNewCap`), whose
sign-extension is `cap32.toNat - n1` under the caller-level side conditions
`n1 + n2 < cap32.toNat < 2^31`.

Composition: `tr_ssprint_entry` (16 sites, `0xe908 → 0xe950`) `.seq`
`tr_ssprint_iter1` (18 sites + call 1, back to `0xe950`) `.seq`
`tr_ssprint_iter2` (18 sites + call 2, to `0xe99c`) `.seq`
`tr_ssprint_tail` (12 sites, to `ret`).

Sites are the generated `Vsa/Sim/SsprintSites.lean` battery
(`scripts/ssprint_sites.tsv`); the single `sub a4,a4,s2` site at `0x8000e98c`
is hand-written below (`gen_sites.py` has no RTYPE-SUB class).  Register
threading uses the `RegPins` pin lists (`pins_alu`/`pins_store`/… + one
`pins_of_frame` per call).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemmoveLoaded __ssprint_rLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Small value bridges -/

/-- `swData (sign_extend z) = z` for a 32-bit `z`: the low-32 extract of the
64-bit sign extension is the original word. -/
theorem swData_sext32 (z : BitVec 32) : swData (sign_extend (m := 64) z) = z := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat (31 - 0 + 1) ((sign_extend (m := 64) z : BitVec 64).toNat >>> 0)).toNat
    = z.toNat
  rw [Nat.shiftRight_zero, BitVec.toNat_ofNat]
  show (z.signExtend 64).toNat % 2 ^ 32 = z.toNat
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have h1 := z.isLt
  cases hm : z.msb <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

theorem extract32_sext32 (z : BitVec 32) :
    (Sail.BitVec.extractLsb (sign_extend (m := 64) z : BitVec 64) 31 0) = z := swData_sext32 z

theorem extract32_ofNat64 (n : Nat) :
    (Sail.BitVec.extractLsb (BitVec.ofNat 64 n : BitVec 64) 31 0) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat (31 - 0 + 1) ((BitVec.ofNat 64 n : BitVec 64).toNat >>> 0)).toNat = _
  rw [Nat.shiftRight_zero, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The capacity word written back by the `__ssputs_r` fast path is the plain
32-bit subtraction: `swData (spNewCap w n) = w - ofNat n`. -/
theorem swData_spNewCap (w : BitVec 32) (n : Nat) :
    swData (spNewCap w n) = w - BitVec.ofNat 32 n := by
  unfold spNewCap
  rw [extract32_sext32 w, extract32_ofNat64 n, swData_sext32]

theorem sub32_toNat (w : BitVec 32) (n : Nat) (_hn : n < 2^32) (hle : n ≤ w.toNat) :
    (w - BitVec.ofNat 32 n).toNat = w.toNat - n := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := w.isLt
  omega

/-- Sign extension of a 32-bit word below `2^31` keeps the `toNat` value. -/
theorem sext32_toNat_small (w : BitVec 32) (h : w.toNat < 2^31) :
    (sign_extend (m := 64) w : BitVec 64).toNat = w.toNat := by
  show (w.signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]
  have hmsb : w.msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [hmsb]
  have := w.isLt
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_setWidth]
  omega

theorem beq64_false_of_toNat_ne (a b : BitVec 64) (h : a.toNat ≠ b.toNat) : (a == b) = false := by
  rw [beq_eq_false_iff_ne]
  intro he; exact h (by rw [he])

theorem bne64_true_of_toNat_ne (a b : BitVec 64) (h : a.toNat ≠ b.toNat) : (a != b) = true := by
  simp only [bne, beq64_false_of_toNat_ne a b h, Bool.not_false]

theorem ofNat_sub_left (a b : Nat) (_h : a + b < 2^64) :
    BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem add_ofNat_ofNat (d : BitVec 64) (a b : Nat) :
    d + BitVec.ofNat 64 a + BitVec.ofNat 64 b = d + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem add_ofNat_toNat (d : BitVec 64) (n : Nat) (h : d.toNat + n < 2^64) :
    (d + BitVec.ofNat 64 n).toNat = d.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `li s5,-1` value: `0 + sext 0xfff = 0xffffffffffffffff`. -/
theorem li_neg1_sr :
    (0#64) + sign_extend (m := 64) (0xfff#12) = (0xffffffffffffffff#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The `addiw a2,a5,-1` value at count 2: `sext32(low32(2 + (-1))) = 1`. -/
theorem addiw_cnt2_sr :
    (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((2#64) + sign_extend (m := 64) (0xfff#12)) 31 0) : BitVec 64)
      = BitVec.ofNat 64 1 := by
  rw [show (2#64) + sign_extend (m := 64) (0xfff#12) = 1#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  exact sext_word_small _ 1 (by omega) (by decide)

/-- The `addiw a2,a5,-1` value at count 1: `sext32(low32(1 + (-1))) = 0`. -/
theorem addiw_cnt1_sr :
    (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((1#64) + sign_extend (m := 64) (0xfff#12)) 31 0) : BitVec 64)
      = BitVec.ofNat 64 0 := by
  rw [show (1#64) + sign_extend (m := 64) (0xfff#12) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  exact sext_word_small _ 0 (by omega) (by decide)

/-- `lw` of the four pinned count bytes followed by the folds above: the
sign-extended byte reassembly of a pinned 32-bit word `w` is `sext32 w`
(`lw_cap_reassemble_sp`), and for the concrete counts `2`/`1` this is the
64-bit constant. -/
theorem lw_count2_sr :
    (sign_extend (m := 64)
      (((((2#32).extractLsb' 24 8).append ((2#32).extractLsb' 16 8)).append
        ((2#32).extractLsb' 8 8)).append ((2#32).extractLsb' 0 8) : BitVec (8 * 4))
      : BitVec 64) = 2#64 := by
  rw [lw_cap_reassemble_sp (2#32)]
  exact sext_word_small _ 2 (by omega) (by decide)

theorem lw_count1_sr :
    (sign_extend (m := 64)
      (((((1#32).extractLsb' 24 8).append ((1#32).extractLsb' 16 8)).append
        ((1#32).extractLsb' 8 8)).append ((1#32).extractLsb' 0 8) : BitVec (8 * 4))
      : BitVec 64) = 1#64 := by
  rw [lw_cap_reassemble_sp (1#32)]
  exact sext_word_small _ 1 (by omega) (by decide)

theorem swData_one_sr : swData (BitVec.ofNat 64 1) = 1#32 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem swData_zero_sr : swData (BitVec.ofNat 64 0) = 0#32 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem swData_zero_sr' : swData (0#64) = 0#32 := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Code-region survival

`__ssprint_r` spans `[0x8000e908, 0x8000e9f8)`; `__ssputs_r` ends at
`0x80014520`; `memmove` ends at `0x80006b00`.  All data windows on this path
sit above `tohostAddr + 16 = 0x8001ad10`, above all three code regions. -/

/-- Pointwise low-memory frame (`< 0x8000e9f8`) transports `__ssprint_rLoaded`. -/
theorem ssprint_frame_sr (mem mem' : Std.ExtHashMap Nat (BitVec 8))
    (hf : ∀ a, a < 0x8000e9f8 → mem'[a]? = mem[a]?)
    (h : __ssprint_rLoaded mem) : __ssprint_rLoaded mem' := by
  unfold __ssprint_rLoaded Vsa.Sim.Code.__ssprint_rChunk0 Vsa.Sim.Code.__ssprint_rChunk1
    Vsa.Sim.Code.__ssprint_rChunk2 Vsa.Sim.Code.__ssprint_rChunk3 at h ⊢
  simp (disch := omega) only [hf]
  exact h

/-- Pointwise low-memory frame (`< 0x80006b00`) transports `MemmoveLoaded`. -/
theorem memmove_frame_sr (mem mem' : Std.ExtHashMap Nat (BitVec 8))
    (hf : ∀ a, a < 0x80006b00 → mem'[a]? = mem[a]?)
    (h : MemmoveLoaded mem) : MemmoveLoaded mem' := by
  unfold MemmoveLoaded Vsa.Sim.Code.memmoveChunk0 Vsa.Sim.Code.memmoveChunk1
    Vsa.Sim.Code.memmoveChunk2 Vsa.Sim.Code.memmoveChunk3 Vsa.Sim.Code.memmoveChunk4 at h ⊢
  simp (disch := omega) only [hf]
  exact h

theorem memmove_writeMap4_sr (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4))
    (ha : 0x80006b00 ≤ a) (h : MemmoveLoaded mem) : MemmoveLoaded (writeMap4 mem a d) :=
  memmove_insert_mv _ _ _ (by omega) (memmove_insert_mv _ _ _ (by omega)
    (memmove_insert_mv _ _ _ (by omega) (memmove_insert_mv _ _ _ (by omega) h)))

/-! ## The hand-written RTYPE-SUB site (`gen_sites.py` gap)

`0x8000e98c: sub a4,a4,s2` — the generator supports `alu_add`/`subw` but not
64-bit `SUB`; this mirrors the `alu_add` template with
`execute_rtype_sub_char`. -/
theorem site_8000e98c_sr (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : __ssprint_rLoaded σ.mem)
    (hpcv : pc = (0x8000e98c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 - v18)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e98c hmem
  exact stepObs_alu σ i u (0x8000e98c#64) vminstret (0x41270733#32)
    (instruction.RTYPE (regidx.Regidx 0x12#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, rop.SUB))
    Register.x14 (v14 - v18)
    (0x33#8) (0x07#8) (0x27#8) (0x41#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_41270733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_sub_char (regidx.Regidx 0x12#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5)
      v14 v18 (afterNextPC (afterPrelude σ) (0x8000e98c#64))
      (sigma3_alu σ (0x8000e98c#64) Register.x14 (v14 - v18))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x8000e98c#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x18 _ v18
        (by rw [get?_afterNextPC σ (0x8000e98c#64) _ (by decide) (by decide)]; exact hx18))
      (wX_bits_x14 _ (v14 - v18)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## The seven-slot stack image

`__ssprint_r`'s prologue spills, in program order: `s1@sp+40`, `ra@sp+56`,
`s0@sp+48`, `s3@sp+24`, `s4@sp+16`, `s5@sp+8`, `s2@sp+32` (with the new
`sp = vsp - 64`), i.e. absolute slots `vsp-24, vsp-8, vsp-16, vsp-40,
vsp-48, vsp-56, vsp-32`. -/
def srStackMem (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
    (vsp.toNat - 24) (sdData_val v9))
    (vsp.toNat - 8) (sdData_val r))
    (vsp.toNat - 16) (sdData_val v8))
    (vsp.toNat - 40) (sdData_val v19))
    (vsp.toNat - 48) (sdData_val v20))
    (vsp.toNat - 56) (sdData_val v21))
    (vsp.toNat - 32) (sdData_val v18)

theorem srStackMem_frame (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) (a : Nat) (ha : a < vsp.toNat - 56 ∨ vsp.toNat ≤ a) :
    (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)[a]? = m0[a]? := by
  unfold srStackMem
  rw [getElem_writeMap8_disjoint _ _ _ _ (by omega), getElem_writeMap8_disjoint _ _ _ _ (by omega),
    getElem_writeMap8_disjoint _ _ _ _ (by omega), getElem_writeMap8_disjoint _ _ _ _ (by omega),
    getElem_writeMap8_disjoint _ _ _ _ (by omega), getElem_writeMap8_disjoint _ _ _ _ (by omega),
    getElem_writeMap8_disjoint _ _ _ _ (by omega)]

theorem srStackMem_s2 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 32) v18 :=
  Pin8_writeMap8 _ _ _

theorem srStackMem_s5 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 56) v21 := by
  unfold srStackMem
  exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
    (Pin8_writeMap8 _ _ _)

theorem srStackMem_s4 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 48) v20 := by
  unfold srStackMem
  exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)])
    (Pin8_writeMap8 _ _ _)

theorem srStackMem_s3 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 40) v19 := by
  unfold srStackMem
  exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)])
    (Pin8_writeMap8 _ _ _)

theorem srStackMem_s0 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 16) v8 := by
  unfold srStackMem
  exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)])
    (Pin8_writeMap8 _ _ _)

theorem srStackMem_ra (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 8) r := by
  unfold srStackMem
  exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)])
    (Pin8_writeMap8 _ _ _)

theorem srStackMem_s1 (m0 : Std.ExtHashMap Nat (BitVec 8)) (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : 128 ≤ vsp.toNat) :
    Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - 24) v9 := by
  unfold srStackMem
  exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)])
    (Pin8_writeMap8 _ _ _)

theorem srStackMem_ssprintloaded (m0 : Std.ExtHashMap Nat (BitVec 8))
    (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : tohostAddr + 16 + 128 ≤ vsp.toNat) (h : __ssprint_rLoaded m0) :
    __ssprint_rLoaded (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  unfold srStackMem
  exact ssprint_writeMap8_ss _ _ _ (by omega) (ssprint_writeMap8_ss _ _ _ (by omega)
    (ssprint_writeMap8_ss _ _ _ (by omega) (ssprint_writeMap8_ss _ _ _ (by omega)
    (ssprint_writeMap8_ss _ _ _ (by omega) (ssprint_writeMap8_ss _ _ _ (by omega)
    (ssprint_writeMap8_ss _ _ _ (by omega) h))))))

theorem srStackMem_ssloaded (m0 : Std.ExtHashMap Nat (BitVec 8))
    (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : tohostAddr + 16 + 128 ≤ vsp.toNat) (h : Vsa.Sim.Code.__ssputs_rLoaded m0) :
    Vsa.Sim.Code.__ssputs_rLoaded (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  unfold srStackMem
  exact ssputs_writeMap8_ss _ _ _ (by omega) (ssputs_writeMap8_ss _ _ _ (by omega)
    (ssputs_writeMap8_ss _ _ _ (by omega) (ssputs_writeMap8_ss _ _ _ (by omega)
    (ssputs_writeMap8_ss _ _ _ (by omega) (ssputs_writeMap8_ss _ _ _ (by omega)
    (ssputs_writeMap8_ss _ _ _ (by omega) h))))))

theorem srStackMem_mvloaded (m0 : Std.ExtHashMap Nat (BitVec 8))
    (vsp r v8 v9 v18 v19 v20 v21 : BitVec 64)
    (hsp : tohostAddr + 16 + 128 ≤ vsp.toNat) (h : MemmoveLoaded m0) :
    MemmoveLoaded (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  unfold srStackMem
  exact memmove_writeMap8_ss _ _ _ (by omega) (memmove_writeMap8_ss _ _ _ (by omega)
    (memmove_writeMap8_ss _ _ _ (by omega) (memmove_writeMap8_ss _ _ _ (by omega)
    (memmove_writeMap8_ss _ _ _ (by omega) (memmove_writeMap8_ss _ _ _ (by omega)
    (memmove_writeMap8_ss _ _ _ (by omega) h))))))

/-! ## Ghost register frame (`NotWrittenSr`) and the callee-frame adapter -/

/-- Registers `__ssprint_r` itself may write: the `__ssputs_r` write-set
(`NotWrittenSp`, which includes memmove noise) plus `s2/s3/s4/s5`. -/
abbrev NotWrittenSr (R : Register) : Prop :=
  (Register.x18 == R) = false ∧ (Register.x19 == R) = false ∧
  (Register.x20 == R) = false ∧ (Register.x21 == R) = false ∧
  NotWrittenSp R

theorem NotWrittenSr.x18 {R : Register} (h : NotWrittenSr R) : (Register.x18 == R) = false := h.1
theorem NotWrittenSr.x19 {R : Register} (h : NotWrittenSr R) : (Register.x19 == R) = false := h.2.1
theorem NotWrittenSr.x20 {R : Register} (h : NotWrittenSr R) : (Register.x20 == R) = false := h.2.2.1
theorem NotWrittenSr.x21 {R : Register} (h : NotWrittenSr R) : (Register.x21 == R) = false := h.2.2.2.1
theorem NotWrittenSr.sp {R : Register} (h : NotWrittenSr R) : NotWrittenSp R := h.2.2.2.2

/-- The `__ssputs_r` write-set in list form, for `pins_of_frame`. -/
def sputsW : List Register :=
  [Register.x1, Register.x2, Register.x8, Register.x9, Register.x10, Register.x11,
   Register.x12, Register.x13, Register.x14, Register.x15, Register.PC, Register.nextPC,
   Register.minstret, Register.minstret_increment, Register.mcycle, Register.mtime,
   Register.mip]

/-- Avoiding `sputsW` gives `NotWrittenSp` (adapter used once per call). -/
theorem notWrittenSp_of_avoid {R : Register} (h : ∀ r ∈ sputsW, (r == R) = false) :
    NotWrittenSp R :=
  ⟨h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide),
   h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide),
   h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide),
   h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide),
   h _ (by decide)⟩

/-! ## Region / side-condition bundle -/

/-- Caller-level region facts for the 2-iovec flush: RAM/HTIF-window bounds and
alignment for the `q` struct (`[q,q+24)`), the iov array (`[viov,viov+32)`),
the sink struct (`[p,p+16)`), the destination window (`[d,d+n1+n2)`), the two
source windows and the 128-byte stack region (`[vsp-128,vsp)`, covering our
64-byte frame and the callee's), plus all needed pairwise disjointness as
`.toNat` interval facts. -/
structure SrRegions (q viov p d s1 s2 vsp : BitVec 64) (n1 n2 : Nat) : Prop where
  n1_1 : 1 ≤ n1
  n1_31 : n1 ≤ 31
  n2_1 : 1 ≤ n2
  n2_31 : n2 ≤ 31
  q_lo : 0x80000000 ≤ q.toNat
  q_hi : q.toNat + 24 ≤ 0x100000000
  q_win : tohostAddr + 16 ≤ q.toNat
  q_align : q.toNat % 8 = 0
  v_lo : 0x80000000 ≤ viov.toNat
  v_hi : viov.toNat + 32 ≤ 0x100000000
  v_win : tohostAddr + 16 ≤ viov.toNat
  v_align : viov.toNat % 8 = 0
  p_lo : 0x80000000 ≤ p.toNat
  p_hi : p.toNat + 16 ≤ 0x100000000
  p_win : tohostAddr + 16 ≤ p.toNat
  p_align : p.toNat % 8 = 0
  d_lo : 0x80000000 ≤ d.toNat
  d_hi : d.toNat + n1 + n2 ≤ 0x100000000
  d_win : tohostAddr + 16 ≤ d.toNat
  s1_lo : 0x80000000 ≤ s1.toNat
  s1_hi : s1.toNat + n1 ≤ 0x100000000
  s1_win : tohostAddr + 16 ≤ s1.toNat
  s2_lo : 0x80000000 ≤ s2.toNat
  s2_hi : s2.toNat + n2 ≤ 0x100000000
  s2_win : tohostAddr + 16 ≤ s2.toNat
  sp_lo : 0x80000000 + 128 ≤ vsp.toNat
  sp_hi : vsp.toNat ≤ 0x100000000
  sp_win : tohostAddr + 16 + 128 ≤ vsp.toNat
  sp_align : vsp.toNat % 8 = 0
  dst_src1 : d.toNat + n1 ≤ s1.toNat ∨ s1.toNat + n1 ≤ d.toNat
  dst_src2 : d.toNat + n1 + n2 ≤ s2.toNat ∨ s2.toNat + n2 ≤ d.toNat
  sink_dst : p.toNat + 16 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ p.toNat
  sink_stack : p.toNat + 16 ≤ vsp.toNat - 128 ∨ vsp.toNat ≤ p.toNat
  sink_src2 : p.toNat + 16 ≤ s2.toNat ∨ s2.toNat + n2 ≤ p.toNat
  stack_dst : vsp.toNat ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ vsp.toNat - 128
  stack_src1 : vsp.toNat ≤ s1.toNat ∨ s1.toNat + n1 ≤ vsp.toNat - 128
  stack_src2 : vsp.toNat ≤ s2.toNat ∨ s2.toNat + n2 ≤ vsp.toNat - 128
  q_dst : q.toNat + 24 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ q.toNat
  q_sink : q.toNat + 24 ≤ p.toNat ∨ p.toNat + 16 ≤ q.toNat
  q_stack : q.toNat + 24 ≤ vsp.toNat - 128 ∨ vsp.toNat ≤ q.toNat
  q_src1 : q.toNat + 24 ≤ s1.toNat ∨ s1.toNat + n1 ≤ q.toNat
  q_src2 : q.toNat + 24 ≤ s2.toNat ∨ s2.toNat + n2 ≤ q.toNat
  v_dst : viov.toNat + 32 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ viov.toNat
  v_sink : viov.toNat + 32 ≤ p.toNat ∨ p.toNat + 16 ≤ viov.toNat
  v_stack : viov.toNat + 32 ≤ vsp.toNat - 128 ∨ vsp.toNat ≤ viov.toNat
  v_q : viov.toNat + 32 ≤ q.toNat ∨ q.toNat + 24 ≤ viov.toNat

/-! ## Pin-list surgery helpers

`pins_cons` re-adds a register at the head after a site wrote it;
`pins_dropK` removes the `K`-th pin before transporting across a site that
writes that register. -/

theorem pins_cons {σ : MState} (R : Register) (v : RegisterType R) {L : List Pin}
    (h : σ.regs.get? R = some v) (hL : PinsHold σ L) : PinsHold σ (⟨R, v⟩ :: L) := ⟨h, hL⟩

theorem pins_drop2 {σ : MState} {a b : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: L)) : PinsHold σ (a :: L) :=
  ⟨h.1, h.2.2⟩

theorem pins_drop4 {σ : MState} {a b c d : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: L)) : PinsHold σ (a :: b :: c :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem pins_drop3 {σ : MState} {a b c : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: L)) : PinsHold σ (a :: b :: L) :=
  ⟨h.1, h.2.1, h.2.2.2⟩

theorem pins_drop5 {σ : MState} {a b c d e : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: L)) : PinsHold σ (a :: b :: c :: d :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem pins_drop6 {σ : MState} {a b c d e f : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem pins_drop8 {σ : MState} {a b c d e f g' h' : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2⟩

theorem pins_drop9 {σ : MState} {a b c d e f g' h' i : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop10 {σ : MState} {a b c d e f g' h' i j : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: j :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop11 {σ : MState} {a b c d e f g' h' i j k : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: j :: k :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: j :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2⟩

theorem pins_drop12 {σ : MState} {a b c d e f g' h' i j k l : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: j :: k :: l :: L)) :
    PinsHold σ (a :: b :: c :: d :: e :: f :: g' :: h' :: i :: j :: k :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## Pre / mid conditions -/

/-- Entry configuration at `0x8000e908` (see the module docstring for the
role of each ghost). -/
structure PreSr (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __ssprint_rLoaded c.σ.mem
  sloaded : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem
  mvloaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x8000e908#64 : BitVec 64)
  ra : c.σ.regs.get? Register.x1 = some r
  sp : c.σ.regs.get? Register.x2 = some vsp
  a0 : c.σ.regs.get? Register.x10 = some va0
  a1 : c.σ.regs.get? Register.x11 = some p
  a2 : c.σ.regs.get? Register.x12 = some q
  cs0 : c.σ.regs.get? Register.x8 = some v8
  cs1 : c.σ.regs.get? Register.x9 = some v9
  cs2 : c.σ.regs.get? Register.x18 = some v18
  cs3 : c.σ.regs.get? Register.x19 = some v19
  cs4 : c.σ.regs.get? Register.x20 = some v20
  cs5 : c.σ.regs.get? Register.x21 = some v21
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : SrRegions q viov p d s1 s2 vsp n1 n2
  hviov : Pin8 m0 q.toNat viov
  hcount : Pin4 m0 (q.toNat + 8) (2#32)
  hresid : Pin8 m0 (q.toNat + 16) (BitVec.ofNat 64 (n1 + n2))
  hiov0b : Pin8 m0 viov.toNat s1
  hiov0l : Pin8 m0 (viov.toNat + 8) (BitVec.ofNat 64 n1)
  hiov1b : Pin8 m0 (viov.toNat + 16) s2
  hiov1l : Pin8 m0 (viov.toNat + 24) (BitVec.ofNat 64 n2)
  hcursor : Pin8 m0 p.toNat d
  hcap : Pin4 m0 (p.toNat + 12) cap32
  hbs1 : MvBytes m0 s1 n1 bs1
  hbs2 : MvBytes m0 s2 n2 bs2
  hcaplt : n1 + n2 < cap32.toNat
  hcap31 : cap32.toNat < 2^31
  memeq : c.σ.mem = m0
  hframe : ∀ R : Register, NotWrittenSr R → c.σ.regs.get? R = g R

/-- Loop-head configuration at `0x8000e950` before iteration 1: prologue done,
seven callee-saves spilled (`srStackMem`), `s0 = viov`, `s1 = q`,
`a4 = resid = n1+n2`, `s3/s4/s5` loaded. -/
structure St1Sr (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __ssprint_rLoaded c.σ.mem
  sloaded : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem
  mvloaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x8000e950#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (vsp - 64#64)
  s0r : c.σ.regs.get? Register.x8 = some viov
  s1r : c.σ.regs.get? Register.x9 = some q
  a4r : c.σ.regs.get? Register.x14 = some (BitVec.ofNat 64 (n1 + n2))
  s3r : c.σ.regs.get? Register.x19 = some va0
  s4r : c.σ.regs.get? Register.x20 = some p
  s5r : c.σ.regs.get? Register.x21 = some (0xffffffffffffffff#64 : BitVec 64)
  tick : c.tick < 2
  regions : SrRegions q viov p d s1 s2 vsp n1 n2
  hcount : Pin4 m0 (q.toNat + 8) (2#32)
  hresid : Pin8 m0 (q.toNat + 16) (BitVec.ofNat 64 (n1 + n2))
  hiov0b : Pin8 m0 viov.toNat s1
  hiov0l : Pin8 m0 (viov.toNat + 8) (BitVec.ofNat 64 n1)
  hiov1b : Pin8 m0 (viov.toNat + 16) s2
  hiov1l : Pin8 m0 (viov.toNat + 24) (BitVec.ofNat 64 n2)
  hcursor : Pin8 m0 p.toNat d
  hcap : Pin4 m0 (p.toNat + 12) cap32
  hbs1 : MvBytes m0 s1 n1 bs1
  hbs2 : MvBytes m0 s2 n2 bs2
  hcaplt : n1 + n2 < cap32.toNat
  hcap31 : cap32.toNat < 2^31
  memeq : c.σ.mem = srStackMem m0 vsp r v8 v9 v18 v19 v20 v21
  hframe : ∀ R : Register, NotWrittenSr R → c.σ.regs.get? R = g R

/-! ## Entry: `0x8000e908 → 0x8000e950` (16 sites, `beqz` NOT taken) -/

theorem tr_ssprint_entry (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) :
    Triple (PreSr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2)
      (St1Sr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2) := by
  intro c hPre
  obtain ⟨hgood, hload, hsload, hmvload, hpc, hra, hsp, ha0, ha1, ha2, hcs0, hcs1, hcs2, hcs3,
    hcs4, hcs5, ⟨vmi, hmi⟩, htick, hreg, hviov, hcount, hresid, hiov0b, hiov0l, hiov1b, hiov1l,
    hcursor, hcap, hbs1, hbs2, hcaplt, hcap31, hmemeq, hgframe⟩ := hPre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hn11 := hreg.n1_1; have hn131 := hreg.n1_31
  have hn21 := hreg.n2_1; have hn231 := hreg.n2_31
  have hqlo := hreg.q_lo; have hqhi := hreg.q_hi
  have hqwin := hreg.q_win; have hqal := hreg.q_align
  have hvlo := hreg.v_lo; have hvhi := hreg.v_hi
  have hvwin := hreg.v_win; have hval := hreg.v_align
  have hsplo := hreg.sp_lo; have hsphi := hreg.sp_hi
  have hspwin := hreg.sp_win; have hspal := hreg.sp_align
  have hqstk := hreg.q_stack
  -- address bridges
  have hspN : (vsp - 64#64).toNat = vsp.toNat - 64 := sp_sub64_toNat vsp (by omega)
  have hq16 : ((q : BitVec 64) + sign_extend (m := 64) (0x010#12)).toNat = q.toNat + 16 :=
    ptr_addoff q _ 16 (by decide) (by omega)
  have hq0 : ((q : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = q.toNat :=
    off_ed_00 q
  have ha24 : ((vsp - 64#64) + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat - 24 := by
    rw [ptr_addoff _ _ 40 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha8 : ((vsp - 64#64) + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat - 8 := by
    rw [ptr_addoff _ _ 56 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha16 : ((vsp - 64#64) + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat - 16 := by
    rw [ptr_addoff _ _ 48 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha40 : ((vsp - 64#64) + sign_extend (m := 64) (0x018#12)).toNat = vsp.toNat - 40 := by
    rw [ptr_addoff _ _ 24 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha48 : ((vsp - 64#64) + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat - 48 := by
    rw [ptr_addoff _ _ 16 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha56 : ((vsp - 64#64) + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat - 56 := by
    rw [ptr_addoff _ _ 8 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha32 : ((vsp - 64#64) + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat - 32 := by
    rw [ptr_addoff _ _ 32 (by decide) (by rw [hspN]; omega), hspN]; omega
  have hload0 : __ssprint_rLoaded m0 := hmemeq ▸ hload
  have hsload0 : Vsa.Sim.Code.__ssputs_rLoaded m0 := hmemeq ▸ hsload
  have hmvload0 : MemmoveLoaded m0 := hmemeq ▸ hmvload
  -- === e908: ld a4,16(a2)  (resid = n1+n2) ===
  have hpinR : Pin8 c.σ.mem ((q + sign_extend (m := 64) (0x010#12)).toNat)
      (BitVec.ofNat 64 (n1 + n2)) := by
    rw [hq16, hmemeq]; exact hresid
  -- pin list L0: [x1, x2, x8, x9, x10, x11, x12, x18, x19, x20, x21]
  have hp0 : PinsHold c.σ [⟨Register.x1, r⟩, ⟨Register.x2, vsp⟩, ⟨Register.x8, v8⟩,
      ⟨Register.x9, v9⟩, ⟨Register.x10, va0⟩, ⟨Register.x11, p⟩, ⟨Register.x12, q⟩,
      ⟨Register.x18, v18⟩, ⟨Register.x19, v19⟩, ⟨Register.x20, v20⟩, ⟨Register.x21, v21⟩] :=
    ⟨hra, hsp, hcs0, hcs1, ha0, ha1, ha2, hcs2, hcs3, hcs4, hcs5, trivial⟩
  obtain ⟨σ1, i1, hstp1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000e908_sr c.σ c.tick c.steps _ vmi q _ _ _ _ _ _ _ _
      hgood hpc hmi ha2 hload rfl
      (by rw [hq16]; omega) (by rw [hq16]; omega) (Or.inr (by rw [hq16]; omega))
      (by rw [hq16]; omega)
      hpinR.1 hpinR.2.1 hpinR.2.2.1 hpinR.2.2.2.1 hpinR.2.2.2.2.1 hpinR.2.2.2.2.2.1
      hpinR.2.2.2.2.2.2.1 hpinR.2.2.2.2.2.2.2 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000e90c#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000e908#64) 4 = (0x8000e90c#64 : BitVec 64) from by decide] at this
  have ha14_1 : σ1.regs.get? Register.x14 = some (BitVec.ofNat 64 (n1 + n2)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- L1: [x14, x1, x2, x8, x9, x10, x11, x12, x18, x19, x20, x21]
  have hp1 := pins_cons Register.x14 (BitVec.ofNat 64 (n1 + n2)) ha14_1
    (pins_alu hobs1 (by rfl) hp0)
  have hload1 : __ssprint_rLoaded σ1.mem := hmem1 ▸ hload
  -- === e90c: addi sp,sp,-64 ===
  obtain ⟨σ2, i2, hstp2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000e90c_sr σ1 i1 (c.steps + 1) _ vmi1 vsp
      hG1 hpc1 hmi1 hp1.2.2.1 hload1 rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000e910#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000e90c#64) 4 = (0x8000e910#64 : BitVec 64) from by decide] at this
  have hsp2 : σ2.regs.get? Register.x2 = some (vsp - 64#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_sub64 vsp] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- L2: [x2, x14, x1, x8, x9, x10, x11, x12, x18, x19, x20, x21]
  have hp2 := pins_cons Register.x2 (vsp - 64#64) hsp2
    (pins_alu hobs2 (by rfl) (pins_drop3 hp1))
  have hload2 : __ssprint_rLoaded σ2.mem := hmem2 ▸ hload1
  -- === e910: sd s1,40(sp) ===
  obtain ⟨σ3, i3, hstp3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000e910_sr σ2 i2 (c.steps + 1 + 1) _ vmi2 (vsp - 64#64) v9
      hG2 hpc2 hmi2 hp2.1 hp2.2.2.2.2.1 hload2 rfl
      (by rw [ha24]; omega) (by rw [ha24]; omega) (by rw [ha24]; omega) (by rw [ha24]; omega) hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000e914#64 : BitVec 64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x8000e910#64) 4 = (0x8000e914#64 : BitVec 64) from by decide] at this
  have hm3 : σ3.mem = writeMap8 m0 (vsp.toNat - 24) (sdData_val v9) := by
    rw [hmem3, mem_afterNextPC, hmem2, hmem1, hmemeq, ha24]
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hp3 := pins_store hobs3 (by rfl) hp2
  have hload3 : __ssprint_rLoaded σ3.mem := by
    rw [hm3]; exact ssprint_writeMap8_ss _ _ _ (by omega) hload0
  -- === e914: sd ra,56(sp) ===
  obtain ⟨σ4, i4, hstp4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000e914_sr σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 (vsp - 64#64) r
      hG3 hpc3 hmi3 hp3.1 hp3.2.2.1 hload3 rfl
      (by rw [ha8]; omega) (by rw [ha8]; omega) (by rw [ha8]; omega) (by rw [ha8]; omega) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000e918#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x8000e914#64) 4 = (0x8000e918#64 : BitVec 64) from by decide] at this
  have hm4 : σ4.mem = writeMap8 (writeMap8 m0 (vsp.toNat - 24) (sdData_val v9))
      (vsp.toNat - 8) (sdData_val r) := by
    rw [hmem4, mem_afterNextPC, hm3, ha8]
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hload4 : __ssprint_rLoaded σ4.mem := by
    rw [hm4]; exact ssprint_writeMap8_ss _ _ _ (by omega) (hm3 ▸ hload3)
  -- === e918: mv s1,a2  (s1 := q) ===
  obtain ⟨σ5, i5, hstp5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000e918_sr σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 q
      hG4 hpc4 hmi4 hp4.2.2.2.2.2.2.2.1 hload4 rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000e91c#64 : BitVec 64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000e918#64) 4 = (0x8000e91c#64 : BitVec 64) from by decide] at this
  have hx9_5 : σ5.regs.get? Register.x9 = some q := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add q] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  -- L5: [x9, x2, x14, x1, x8, x10, x11, x12, x18, x19, x20, x21]
  have hp5 := pins_cons Register.x9 q hx9_5 (pins_alu hobs5 (by rfl) (pins_drop5 hp4))
  have hload5 : __ssprint_rLoaded σ5.mem := hmem5 ▸ hload4
  -- === e91c: beqz a4 NOT taken (resid = n1+n2 ≠ 0) ===
  have hv6 : ((BitVec.ofNat 64 (n1 + n2)) == (0#64 : BitVec 64)) = false :=
    beq64_false_of_toNat_ne _ _ (by simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨σ6, i6, hstp6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000e91c_nottaken_sr σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5
      (BitVec.ofNat 64 (n1 + n2))
      hG5 hpc5 hmi5 hp5.2.2.1 hload5 rfl hv6 hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000e920#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs6
    rwa [show BitVec.addInt (0x8000e91c#64) 4 = (0x8000e920#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_bnottaken_minstret hobs6
  have hp6 := pins_bnottaken hobs6 (by rfl) hp5
  have hload6 : __ssprint_rLoaded σ6.mem := hmem6 ▸ hload5
  -- === e920: sd s0,48(sp) ===
  obtain ⟨σ7, i7, hstp7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000e920_sr σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi6 (vsp - 64#64) v8
      hG6 hpc6 hmi6 hp6.2.1 hp6.2.2.2.2.1 hload6 rfl
      (by rw [ha16]; omega) (by rw [ha16]; omega) (by rw [ha16]; omega) (by rw [ha16]; omega) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x8000e924#64 : BitVec 64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x8000e920#64) 4 = (0x8000e924#64 : BitVec 64) from by decide] at this
  have hm7 : σ7.mem = writeMap8 (writeMap8 (writeMap8 m0 (vsp.toNat - 24) (sdData_val v9))
      (vsp.toNat - 8) (sdData_val r)) (vsp.toNat - 16) (sdData_val v8) := by
    rw [hmem7, mem_afterNextPC, hmem6, hmem5, hm4, ha16]
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hload7 : __ssprint_rLoaded σ7.mem := by
    rw [hm7]; exact ssprint_writeMap8_ss _ _ _ (by omega) (hm4 ▸ hload4)
  -- === e924: sd s3,24(sp) ===
  obtain ⟨σ8, i8, hstp8, hi8, hG8, hmem8, hobs8⟩ :=
    site_8000e924_sr σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi7 (vsp - 64#64) v19
      hG7 hpc7 hmi7 hp7.2.1 hp7.2.2.2.2.2.2.2.2.2.1 hload7 rfl
      (by rw [ha40]; omega) (by rw [ha40]; omega) (by rw [ha40]; omega) (by rw [ha40]; omega) hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000e928#64 : BitVec 64) := by
    have := obs_store_pc hobs8
    rwa [show BitVec.addInt (0x8000e924#64) 4 = (0x8000e928#64 : BitVec 64) from by decide] at this
  have hm8 : σ8.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
      (vsp.toNat - 24) (sdData_val v9)) (vsp.toNat - 8) (sdData_val r))
      (vsp.toNat - 16) (sdData_val v8)) (vsp.toNat - 40) (sdData_val v19) := by
    rw [hmem8, mem_afterNextPC, hm7, ha40]
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hp8 := pins_store hobs8 (by rfl) hp7
  have hload8 : __ssprint_rLoaded σ8.mem := by
    rw [hm8]; exact ssprint_writeMap8_ss _ _ _ (by omega) (hm7 ▸ hload7)
  -- === e928: sd s4,16(sp) ===
  obtain ⟨σ9, i9, hstp9, hi9, hG9, hmem9, hobs9⟩ :=
    site_8000e928_sr σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi8 (vsp - 64#64) v20
      hG8 hpc8 hmi8 hp8.2.1 hp8.2.2.2.2.2.2.2.2.2.2.1 hload8 rfl
      (by rw [ha48]; omega) (by rw [ha48]; omega) (by rw [ha48]; omega) (by rw [ha48]; omega) hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000e92c#64 : BitVec 64) := by
    have := obs_store_pc hobs9
    rwa [show BitVec.addInt (0x8000e928#64) 4 = (0x8000e92c#64 : BitVec 64) from by decide] at this
  have hm9 : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
      (vsp.toNat - 24) (sdData_val v9)) (vsp.toNat - 8) (sdData_val r))
      (vsp.toNat - 16) (sdData_val v8)) (vsp.toNat - 40) (sdData_val v19))
      (vsp.toNat - 48) (sdData_val v20) := by
    rw [hmem9, mem_afterNextPC, hm8, ha48]
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret hobs9
  have hp9 := pins_store hobs9 (by rfl) hp8
  have hload9 : __ssprint_rLoaded σ9.mem := by
    rw [hm9]; exact ssprint_writeMap8_ss _ _ _ (by omega) (hm8 ▸ hload8)
  -- === e92c: sd s5,8(sp) ===
  obtain ⟨σ10, i10, hstp10, hi10, hG10, hmem10, hobs10⟩ :=
    site_8000e92c_sr σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi9 (vsp - 64#64) v21
      hG9 hpc9 hmi9 hp9.2.1 hp9.2.2.2.2.2.2.2.2.2.2.2.1 hload9 rfl
      (by rw [ha56]; omega) (by rw [ha56]; omega) (by rw [ha56]; omega) (by rw [ha56]; omega) hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000e930#64 : BitVec 64) := by
    have := obs_store_pc hobs10
    rwa [show BitVec.addInt (0x8000e92c#64) 4 = (0x8000e930#64 : BitVec 64) from by decide] at this
  have hm10 : σ10.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
      (vsp.toNat - 24) (sdData_val v9)) (vsp.toNat - 8) (sdData_val r))
      (vsp.toNat - 16) (sdData_val v8)) (vsp.toNat - 40) (sdData_val v19))
      (vsp.toNat - 48) (sdData_val v20)) (vsp.toNat - 56) (sdData_val v21) := by
    rw [hmem10, mem_afterNextPC, hm9, ha56]
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret hobs10
  have hp10 := pins_store hobs10 (by rfl) hp9
  have hload10 : __ssprint_rLoaded σ10.mem := by
    rw [hm10]; exact ssprint_writeMap8_ss _ _ _ (by omega) (hm9 ▸ hload9)
  -- === e930: ld s0,0(a2)  (s0 := viov) ===
  have hpinV : Pin8 σ10.mem ((q + sign_extend (m := 64) (0x000#12)).toNat) viov := by
    rw [hq0, hm10]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]) hviov
  obtain ⟨σ11, i11, hstp11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000e930_sr σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi10 q
      _ _ _ _ _ _ _ _
      hG10 hpc10 hmi10 hp10.2.2.2.2.2.2.2.1 hload10 rfl
      (by rw [hq0]; omega) (by rw [hq0]; omega) (Or.inr (by rw [hq0]; omega))
      (by rw [hq0]; omega)
      hpinV.1 hpinV.2.1 hpinV.2.2.1 hpinV.2.2.2.1 hpinV.2.2.2.2.1 hpinV.2.2.2.2.2.1
      hpinV.2.2.2.2.2.2.1 hpinV.2.2.2.2.2.2.2 hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000e934#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x8000e930#64) 4 = (0x8000e934#64 : BitVec 64) from by decide] at this
  have hx8_11 : σ11.regs.get? Register.x8 = some viov := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  -- L11: [x8, x9, x2, x14, x1, x10, x11, x12, x18, x19, x20, x21]
  have hp11 := pins_cons Register.x8 viov hx8_11 (pins_alu hobs11 (by rfl) (pins_drop5 hp10))
  have hload11 : __ssprint_rLoaded σ11.mem := hmem11 ▸ hload10
  -- === e934: sd s2,32(sp)  (memory now the full srStackMem image) ===
  obtain ⟨σ12, i12, hstp12, hi12, hG12, hmem12, hobs12⟩ :=
    site_8000e934_sr σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi11
      (vsp - 64#64) v18
      hG11 hpc11 hmi11 hp11.2.2.1 hp11.2.2.2.2.2.2.2.2.1 hload11 rfl
      (by rw [ha32]; omega) (by rw [ha32]; omega) (by rw [ha32]; omega) (by rw [ha32]; omega) hi11
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000e938#64 : BitVec 64) := by
    have := obs_store_pc hobs12
    rwa [show BitVec.addInt (0x8000e934#64) 4 = (0x8000e938#64 : BitVec 64) from by decide] at this
  have hm12 : σ12.mem = srStackMem m0 vsp r v8 v9 v18 v19 v20 v21 := by
    rw [hmem12, mem_afterNextPC, hmem11, hm10, ha32]; rfl
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret hobs12
  have hp12 := pins_store hobs12 (by rfl) hp11
  have hloadS : __ssprint_rLoaded (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) :=
    srStackMem_ssprintloaded m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) hload0
  have hload12 : __ssprint_rLoaded σ12.mem := by rw [hm12]; exact hloadS
  -- === e938: mv s3,a0  (s3 := va0) ===
  obtain ⟨σ13, i13, hstp13, hi13, hG13, hmem13, hobs13⟩ :=
    site_8000e938_sr σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi12 va0
      hG12 hpc12 hmi12 hp12.2.2.2.2.2.1 hload12 rfl hi12
  have hpc13 : σ13.regs.get? Register.PC = some (0x8000e93c#64 : BitVec 64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x8000e938#64) 4 = (0x8000e93c#64 : BitVec 64) from by decide] at this
  have hx19_13 : σ13.regs.get? Register.x19 = some va0 := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add va0] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  -- L13: [x19, x8, x9, x2, x14, x1, x10, x11, x12, x18, x20, x21]
  have hp13 := pins_cons Register.x19 va0 hx19_13 (pins_alu hobs13 (by rfl) (pins_drop10 hp12))
  have hload13 : __ssprint_rLoaded σ13.mem := hmem13 ▸ hload12
  -- === e93c: mv s4,a1  (s4 := p) ===
  obtain ⟨σ14, i14, hstp14, hi14, hG14, hmem14, hobs14⟩ :=
    site_8000e93c_sr σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _
      vmi13 p
      hG13 hpc13 hmi13 hp13.2.2.2.2.2.2.2.1 hload13 rfl hi13
  have hpc14 : σ14.regs.get? Register.PC = some (0x8000e940#64 : BitVec 64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x8000e93c#64) 4 = (0x8000e940#64 : BitVec 64) from by decide] at this
  have hx20_14 : σ14.regs.get? Register.x20 = some p := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add p] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  -- L14: [x20, x19, x8, x9, x2, x14, x1, x10, x11, x12, x18, x21]
  have hp14 := pins_cons Register.x20 p hx20_14 (pins_alu hobs14 (by rfl) (pins_drop11 hp13))
  have hload14 : __ssprint_rLoaded σ14.mem := hmem14 ▸ hload13
  -- === e940: li s5,-1 ===
  obtain ⟨σ15, i15, hstp15, hi15, hG15, hmem15, hobs15⟩ :=
    site_8000e940_sr σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _
      vmi14
      hG14 hpc14 hmi14 hload14 rfl hi14
  have hpc15 : σ15.regs.get? Register.PC = some (0x8000e944#64 : BitVec 64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x8000e940#64) 4 = (0x8000e944#64 : BitVec 64) from by decide] at this
  have hx21_15 : σ15.regs.get? Register.x21 = some (0xffffffffffffffff#64 : BitVec 64) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li_neg1_sr] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  -- L15: [x21, x20, x19, x8, x9, x2, x14, x1, x10, x11, x12, x18]
  have hp15 := pins_cons Register.x21 (0xffffffffffffffff#64 : BitVec 64) hx21_15
    (pins_alu hobs15 (by rfl) (pins_drop12 hp14))
  have hload15 : __ssprint_rLoaded σ15.mem := hmem15 ▸ hload14
  -- === e944: j 0x8000e950 ===
  obtain ⟨σ16, i16, hstp16, hi16, hG16, hmem16, hobs16⟩ :=
    site_8000e944_sr σ15 i15
      (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi15
      hG15 hpc15 hmi15 hload15 rfl (by decide) hi15
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000e950#64 : BitVec 64) := by
    have := obs_jr_pc hobs16
    rwa [show (0x8000e944#64 : BitVec 64) + sign_extend (m := 64) (0x00000c#21)
        = (0x8000e950#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp16 := pins_jr hobs16 (by rfl) hp15
  have hm16 : σ16.mem = srStackMem m0 vsp r v8 v9 v18 v19 v20 v21 := by
    rw [hmem16, hmem15, hmem14, hmem13, hm12]
  -- assemble St1
  refine ⟨⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩,
    ?_, hG16, hm16 ▸ hloadS,
    hm16 ▸ (srStackMem_ssloaded m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) hsload0),
    hm16 ▸ (srStackMem_mvloaded m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) hmvload0),
    hpc16, hp16.2.2.2.2.2.1, hp16.2.2.2.1, hp16.2.2.2.2.1, hp16.2.2.2.2.2.2.1,
    hp16.2.2.1, hp16.2.1, hp16.1, hi16, hreg,
    hcount, hresid, hiov0b, hiov0l, hiov1b, hiov1l, hcursor, hcap, hbs1, hbs2,
    hcaplt, hcap31, hm16, ?_⟩
  · exact (((((((((((((((Steps.single hstp1).trans (Steps.single hstp2)).trans
      (Steps.single hstp3)).trans (Steps.single hstp4)).trans (Steps.single hstp5)).trans
      (Steps.single hstp6)).trans (Steps.single hstp7)).trans (Steps.single hstp8)).trans
      (Steps.single hstp9)).trans (Steps.single hstp10)).trans (Steps.single hstp11)).trans
      (Steps.single hstp12)).trans (Steps.single hstp13)).trans (Steps.single hstp14)).trans
      (Steps.single hstp15)).trans (Steps.single hstp16)
  · intro R hR
    have hmv := hR.sp.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.sp.x14 hmv
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.sp.x2 hmv
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_store_mv hobs3 R hmv
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_mv hobs4 R hmv
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_alu_mv hobs5 R hR.sp.x9 hmv
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_bnottaken_mv hobs6 R hmv
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_store_mv hobs7 R hmv
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_store_mv hobs8 R hmv
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_store_mv hobs9 R hmv
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_store_mv hobs10 R hmv
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.sp.x8 hmv
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_store_mv hobs12 R hmv
    have e13 : σ13.regs.get? R = σ12.regs.get? R := frame_alu_mv hobs13 R hR.x19 hmv
    have e14 : σ14.regs.get? R = σ13.regs.get? R := frame_alu_mv hobs14 R hR.x20 hmv
    have e15 : σ15.regs.get? R = σ14.regs.get? R := frame_alu_mv hobs15 R hR.x21 hmv
    have e16 : σ16.regs.get? R = σ15.regs.get? R := frame_jr_mv hobs16 R hmv
    rw [e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
    exact hgframe R hR

/-! ## Mid-states after iteration 1 and after the loop -/

/-- Loop-head configuration at `0x8000e950` before iteration 2: iov[0] flushed
(`[d,d+n1) = bs1`), sink cursor at `d+n1`, capacity `cap32 - n1`, count `1`,
resid `n2`, `s0 = viov+16`, the seven spills and iov[1] intact. -/
structure St2Sr (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __ssprint_rLoaded c.σ.mem
  sloaded : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem
  mvloaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x8000e950#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (vsp - 64#64)
  s0i : c.σ.regs.get? Register.x8 = some (viov + sign_extend (m := 64) (0x010#12))
  s1r : c.σ.regs.get? Register.x9 = some q
  a4r : c.σ.regs.get? Register.x14 = some (BitVec.ofNat 64 n2)
  s3r : c.σ.regs.get? Register.x19 = some va0
  s4r : c.σ.regs.get? Register.x20 = some p
  s5r : c.σ.regs.get? Register.x21 = some (0xffffffffffffffff#64 : BitVec 64)
  tick : c.tick < 2
  regions : SrRegions q viov p d s1 s2 vsp n1 n2
  hcaplt : n1 + n2 < cap32.toNat
  hcap31 : cap32.toNat < 2^31
  count1 : Pin4 c.σ.mem (q.toNat + 8) (1#32)
  resid1 : Pin8 c.σ.mem (q.toNat + 16) (BitVec.ofNat 64 n2)
  hiov1b : Pin8 c.σ.mem (viov.toNat + 16) s2
  hiov1l : Pin8 c.σ.mem (viov.toNat + 24) (BitVec.ofNat 64 n2)
  cursor1 : Pin8 c.σ.mem p.toNat (d + BitVec.ofNat 64 n1)
  cap1 : Pin4 c.σ.mem (p.toNat + 12) (cap32 - BitVec.ofNat 32 n1)
  copied1 : ∀ k, k < n1 → c.σ.mem[(d.toNat + k)]? = some (bs1 k)
  hsrc2 : MvBytes c.σ.mem s2 n2 bs2
  save_ra : Pin8 c.σ.mem (vsp.toNat - 8) r
  save_s0 : Pin8 c.σ.mem (vsp.toNat - 16) v8
  save_s1 : Pin8 c.σ.mem (vsp.toNat - 24) v9
  save_s2 : Pin8 c.σ.mem (vsp.toNat - 32) v18
  save_s3 : Pin8 c.σ.mem (vsp.toNat - 40) v19
  save_s4 : Pin8 c.σ.mem (vsp.toNat - 48) v20
  save_s5 : Pin8 c.σ.mem (vsp.toNat - 56) v21
  mframe : ∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n1 + n2) →
    ¬(p.toNat ≤ a ∧ a < p.toNat + 8) → ¬(p.toNat + 12 ≤ a ∧ a < p.toNat + 16) →
    ¬(q.toNat + 8 ≤ a ∧ a < q.toNat + 12) → ¬(q.toNat + 16 ≤ a ∧ a < q.toNat + 24) →
    ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat) →
    c.σ.mem[a]? = m0[a]?
  hframe : ∀ R : Register, NotWrittenSr R → c.σ.regs.get? R = g R

/-- Loop-exit configuration at `0x8000e99c`: both iovecs flushed, cursor at
`d+(n1+n2)`, capacity decremented twice, spills intact, `s1 = q` for the two
clearing stores in the tail. -/
structure St3Sr (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __ssprint_rLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x8000e99c#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (vsp - 64#64)
  s1r : c.σ.regs.get? Register.x9 = some q
  tick : c.tick < 2
  regions : SrRegions q viov p d s1 s2 vsp n1 n2
  copied1 : ∀ k, k < n1 → c.σ.mem[(d.toNat + k)]? = some (bs1 k)
  copied2 : ∀ k, k < n2 → c.σ.mem[(d.toNat + n1 + k)]? = some (bs2 k)
  cursorF : Pin8 c.σ.mem p.toNat (d + BitVec.ofNat 64 (n1 + n2))
  capF : Pin4 c.σ.mem (p.toNat + 12) (cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2)
  save_ra : Pin8 c.σ.mem (vsp.toNat - 8) r
  save_s0 : Pin8 c.σ.mem (vsp.toNat - 16) v8
  save_s1 : Pin8 c.σ.mem (vsp.toNat - 24) v9
  save_s2 : Pin8 c.σ.mem (vsp.toNat - 32) v18
  save_s3 : Pin8 c.σ.mem (vsp.toNat - 40) v19
  save_s4 : Pin8 c.σ.mem (vsp.toNat - 48) v20
  save_s5 : Pin8 c.σ.mem (vsp.toNat - 56) v21
  mframe : ∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n1 + n2) →
    ¬(p.toNat ≤ a ∧ a < p.toNat + 8) → ¬(p.toNat + 12 ≤ a ∧ a < p.toNat + 16) →
    ¬(q.toNat + 8 ≤ a ∧ a < q.toNat + 12) → ¬(q.toNat + 16 ≤ a ∧ a < q.toNat + 24) →
    ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat) →
    c.σ.mem[a]? = m0[a]?
  hframe : ∀ R : Register, NotWrittenSr R → c.σ.regs.get? R = g R

/-! ## Iteration 1: `0x8000e950 → … → jal __ssputs_r (iov[0]) → … → 0x8000e950` -/

theorem tr_ssprint_iter1 (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) :
    Triple (St1Sr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2)
      (St2Sr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2) := by
  intro c hSt
  obtain ⟨hgood, hload, hsload, hmvload, hpc, hsp, hs0r, hs1r, ha4r, hs3r, hs4r, hs5r, htick,
    hreg, hcount, hresid, hiov0b, hiov0l, hiov1b, hiov1l, hcursor, hcap, hbs1, hbs2,
    hcaplt, hcap31, hmemeq, hgframe⟩ := hSt
  obtain ⟨vmi, hmi⟩ := hgood.minstret
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hn11 := hreg.n1_1; have hn131 := hreg.n1_31
  have hn21 := hreg.n2_1; have hn231 := hreg.n2_31
  have hqlo := hreg.q_lo; have hqhi := hreg.q_hi
  have hqwin := hreg.q_win; have hqal := hreg.q_align
  have hvlo := hreg.v_lo; have hvhi := hreg.v_hi
  have hvwin := hreg.v_win; have hval := hreg.v_align
  have hplo := hreg.p_lo; have hphi := hreg.p_hi
  have hpwin := hreg.p_win; have hpal := hreg.p_align
  have hdlo := hreg.d_lo; have hdhi := hreg.d_hi; have hdwin := hreg.d_win
  have hs1lo := hreg.s1_lo; have hs1hi := hreg.s1_hi; have hs1win := hreg.s1_win
  have hs2lo := hreg.s2_lo; have hs2hi := hreg.s2_hi; have hs2win := hreg.s2_win
  have hsplo := hreg.sp_lo; have hsphi := hreg.sp_hi
  have hspwin := hreg.sp_win; have hspal := hreg.sp_align
  have hds1 := hreg.dst_src1; have hds2 := hreg.dst_src2
  have hsd := hreg.sink_dst; have hsstk := hreg.sink_stack; have hss2 := hreg.sink_src2
  have hstkd := hreg.stack_dst; have hstks1 := hreg.stack_src1; have hstks2 := hreg.stack_src2
  have hqd := hreg.q_dst; have hqsink := hreg.q_sink; have hqstk := hreg.q_stack
  have hqs1 := hreg.q_src1; have hqs2 := hreg.q_src2
  have hvd := hreg.v_dst; have hvsink := hreg.v_sink; have hvstk := hreg.v_stack
  have hvq := hreg.v_q
  -- address bridges
  have hspN : (vsp - 64#64).toNat = vsp.toNat - 64 := sp_sub64_toNat vsp (by omega)
  have hq8 : ((q : BitVec 64) + sign_extend (m := 64) (0x008#12)).toNat = q.toNat + 8 :=
    ptr_addoff q _ 8 (by decide) (by omega)
  have hq16 : ((q : BitVec 64) + sign_extend (m := 64) (0x010#12)).toNat = q.toNat + 16 :=
    ptr_addoff q _ 16 (by decide) (by omega)
  have hv0 : ((viov : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = viov.toNat :=
    off_ed_00 viov
  have hv8 : ((viov : BitVec 64) + sign_extend (m := 64) (0x008#12)).toNat = viov.toNat + 8 :=
    ptr_addoff viov _ 8 (by decide) (by omega)
  -- pin list L0: [x9, x2, x14, x8, x19, x20, x21]
  have hp0 : PinsHold c.σ [⟨Register.x9, q⟩, ⟨Register.x2, vsp - 64#64⟩,
      ⟨Register.x14, BitVec.ofNat 64 (n1 + n2)⟩, ⟨Register.x8, viov⟩, ⟨Register.x19, va0⟩,
      ⟨Register.x20, p⟩, ⟨Register.x21, (0xffffffffffffffff#64 : BitVec 64)⟩] :=
    ⟨hs1r, hsp, ha4r, hs0r, hs3r, hs4r, hs5r, trivial⟩
  -- === e950: lw a5,8(s1)  (count = 2) ===
  have hpinC : Pin4 c.σ.mem ((q + sign_extend (m := 64) (0x008#12)).toNat) (2#32) := by
    rw [hq8, hmemeq]
    exact Pin4_frame (fun k hk1 hk2 =>
      srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hcount
  obtain ⟨σ1, i1, hstp1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000e950_sr c.σ c.tick c.steps _ vmi q _ _ _ _
      hgood hpc hmi hp0.1 hload rfl
      (by rw [hq8]; omega) (by rw [hq8]; omega) (Or.inr (by rw [hq8]; omega))
      (by rw [hq8]; omega)
      hpinC.1 hpinC.2.1 hpinC.2.2.1 hpinC.2.2.2 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000e954#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000e950#64) 4 = (0x8000e954#64 : BitVec 64) from by decide] at this
  have ha15_1 : σ1.regs.get? Register.x15 = some (2#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [lw_count2_sr] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hp1 := pins_alu hobs1 (by rfl) hp0
  have hload1 : __ssprint_rLoaded σ1.mem := hmem1 ▸ hload
  -- === e954: mv a3,a4 ===
  obtain ⟨σ2, i2, hstp2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000e954_sr σ1 i1 (c.steps + 1) _ vmi1 (BitVec.ofNat 64 (n1 + n2))
      hG1 hpc1 hmi1 hp1.2.2.1 hload1 rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000e958#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000e954#64) 4 = (0x8000e958#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have ha15_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha15_1
  have hp2 := pins_alu hobs2 (by rfl) hp1
  have hload2 : __ssprint_rLoaded σ2.mem := hmem2 ▸ hload1
  -- === e958: addiw a2,a5,-1  (a2 := 1) ===
  obtain ⟨σ3, i3, hstp3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000e958_sr σ2 i2 (c.steps + 1 + 1) _ vmi2 (2#64)
      hG2 hpc2 hmi2 ha15_2 hload2 rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000e95c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x8000e958#64) 4 = (0x8000e95c#64 : BitVec 64) from by decide] at this
  have ha12_3 : σ3.regs.get? Register.x12 = some (BitVec.ofNat 64 1) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addiw_cnt2_sr] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have ha15_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha15_2
  have hp3 := pins_alu hobs3 (by rfl) hp2
  have hload3 : __ssprint_rLoaded σ3.mem := hmem3 ▸ hload2
  -- === e95c: sw a2,8(s1)  (count := 1) ===
  obtain ⟨σ4, i4, hstp4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000e95c_sr σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 q (BitVec.ofNat 64 1)
      hG3 hpc3 hmi3 hp3.1 ha12_3 hload3 rfl
      (by rw [hq8]; omega) (by rw [hq8]; omega) (by rw [hq8]; omega) (by rw [hq8]; omega) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000e960#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x8000e95c#64) 4 = (0x8000e960#64 : BitVec 64) from by decide] at this
  have hm4 : σ4.mem = writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32) := by
    rw [hmem4, mem_afterNextPC, hmem3, hmem2, hmem1, hmemeq, hq8, swData_one_sr]
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have ha15_4 := obs_store_other' hobs4 Register.x15 (by decide) ha15_3
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hloadM2 : __ssprint_rLoaded (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32)) :=
    ssprint_writeMap4_ss _ _ _ (by omega) (hmemeq ▸ hload)
  have hload4 : __ssprint_rLoaded σ4.mem := by rw [hm4]; exact hloadM2
  -- === e960: blez a5 NOT taken (count 2 > 0) ===
  obtain ⟨σ5, i5, hstp5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000e960_nottaken_sr σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 (2#64)
      hG4 hpc4 hmi4 ha15_4 hload4 rfl (by decide) hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000e964#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs5
    rwa [show BitVec.addInt (0x8000e960#64) 4 = (0x8000e964#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_bnottaken_minstret hobs5
  have hp5 := pins_bnottaken hobs5 (by rfl) hp4
  have hload5 : __ssprint_rLoaded σ5.mem := hmem5 ▸ hload4
  have hm5 : σ5.mem = writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32) := by rw [hmem5, hm4]
  -- === e964: ld s2,8(s0)  (s2 := len1 = n1) ===
  have hpinL1 : Pin8 σ5.mem ((viov + sign_extend (m := 64) (0x008#12)).toNat)
      (BitVec.ofNat 64 n1) := by
    rw [hv8, hm5]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
      exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hiov0l
  obtain ⟨σ6, i6, hstp6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000e964_sr σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5 viov _ _ _ _ _ _ _ _
      hG5 hpc5 hmi5 hp5.2.2.2.1 hload5 rfl
      (by rw [hv8]; omega) (by rw [hv8]; omega) (Or.inr (by rw [hv8]; omega))
      (by rw [hv8]; omega)
      hpinL1.1 hpinL1.2.1 hpinL1.2.2.1 hpinL1.2.2.2.1 hpinL1.2.2.2.2.1 hpinL1.2.2.2.2.2.1
      hpinL1.2.2.2.2.2.2.1 hpinL1.2.2.2.2.2.2.2 hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000e968#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000e964#64) 4 = (0x8000e968#64 : BitVec 64) from by decide] at this
  have ha18_6 : σ6.regs.get? Register.x18 = some (BitVec.ofNat 64 n1) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- L6: [x18, x9, x2, x14, x8, x19, x20, x21]
  have hp6 := pins_cons Register.x18 (BitVec.ofNat 64 n1) ha18_6 (pins_alu hobs6 (by rfl) hp5)
  have hload6 : __ssprint_rLoaded σ6.mem := hmem6 ▸ hload5
  -- === e968: beqz s2 NOT taken (n1 ≥ 1) ===
  obtain ⟨σ7, i7, hstp7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000e968_nottaken_sr σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi6
      (BitVec.ofNat 64 n1)
      hG6 hpc6 hmi6 hp6.1 hload6 rfl
      (beq64_false_of_toNat_ne _ _ (by simp only [BitVec.toNat_ofNat]; omega)) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x8000e96c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs7
    rwa [show BitVec.addInt (0x8000e968#64) 4 = (0x8000e96c#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_bnottaken_minstret hobs7
  have hp7 := pins_bnottaken hobs7 (by rfl) hp6
  have hload7 : __ssprint_rLoaded σ7.mem := hmem7 ▸ hload6
  have hm7 : σ7.mem = writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32) := by rw [hmem7, hmem6, hm5]
  -- === e96c: ld a2,0(s0)  (a2 := base1 = s1) ===
  have hpinB1 : Pin8 σ7.mem ((viov + sign_extend (m := 64) (0x000#12)).toNat) s1 := by
    rw [hv0, hm7]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
      exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hiov0b
  obtain ⟨σ8, i8, hstp8, hi8, hG8, hmem8, hobs8⟩ :=
    site_8000e96c_sr σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi7 viov _ _ _ _ _ _ _ _
      hG7 hpc7 hmi7 hp7.2.2.2.2.1 hload7 rfl
      (by rw [hv0]; omega) (by rw [hv0]; omega) (Or.inr (by rw [hv0]; omega))
      (by rw [hv0]; omega)
      hpinB1.1 hpinB1.2.1 hpinB1.2.2.1 hpinB1.2.2.2.1 hpinB1.2.2.2.2.1 hpinB1.2.2.2.2.2.1
      hpinB1.2.2.2.2.2.2.1 hpinB1.2.2.2.2.2.2.2 hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000e970#64 : BitVec 64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x8000e96c#64) 4 = (0x8000e970#64 : BitVec 64) from by decide] at this
  have ha12_8 : σ8.regs.get? Register.x12 = some s1 := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hp8 := pins_alu hobs8 (by rfl) hp7
  have hload8 : __ssprint_rLoaded σ8.mem := hmem8 ▸ hload7
  -- === e970: mv a3,s2  (a3 := n1) ===
  obtain ⟨σ9, i9, hstp9, hi9, hG9, hmem9, hobs9⟩ :=
    site_8000e970_sr σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi8
      (BitVec.ofNat 64 n1)
      hG8 hpc8 hmi8 hp8.1 hload8 rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000e974#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000e970#64) 4 = (0x8000e974#64 : BitVec 64) from by decide] at this
  have ha13_9 : σ9.regs.get? Register.x13 = some (BitVec.ofNat 64 n1) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (BitVec.ofNat 64 n1)] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have ha12_9 := obs_alu_other' hobs9 Register.x12 (by decide) ha12_8
  have hp9 := pins_alu hobs9 (by rfl) hp8
  have hload9 : __ssprint_rLoaded σ9.mem := hmem9 ▸ hload8
  -- === e974: mv a1,s4  (a1 := p) ===
  obtain ⟨σ10, i10, hstp10, hi10, hG10, hmem10, hobs10⟩ :=
    site_8000e974_sr σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi9 p
      hG9 hpc9 hmi9 hp9.2.2.2.2.2.2.1 hload9 rfl hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000e978#64 : BitVec 64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x8000e974#64) 4 = (0x8000e978#64 : BitVec 64) from by decide] at this
  have ha11_10 : σ10.regs.get? Register.x11 = some p := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add p] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have ha12_10 := obs_alu_other' hobs10 Register.x12 (by decide) ha12_9
  have ha13_10 := obs_alu_other' hobs10 Register.x13 (by decide) ha13_9
  have hp10 := pins_alu hobs10 (by rfl) hp9
  have hload10 : __ssprint_rLoaded σ10.mem := hmem10 ▸ hload9
  -- === e978: mv a0,s3  (a0 := va0) ===
  obtain ⟨σ11, i11, hstp11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000e978_sr σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi10 va0
      hG10 hpc10 hmi10 hp10.2.2.2.2.2.1 hload10 rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000e97c#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x8000e978#64) 4 = (0x8000e97c#64 : BitVec 64) from by decide] at this
  have ha10_11 : σ11.regs.get? Register.x10 = some va0 := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add va0] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have ha11_11 := obs_alu_other' hobs11 Register.x11 (by decide) ha11_10
  have ha12_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha12_10
  have ha13_11 := obs_alu_other' hobs11 Register.x13 (by decide) ha13_10
  have hp11 := pins_alu hobs11 (by rfl) hp10
  have hload11 : __ssprint_rLoaded σ11.mem := hmem11 ▸ hload10
  -- === e97c: jal ra,__ssputs_r ===
  obtain ⟨σ12, i12, hstp12, hi12, hG12, hmem12, hobs12⟩ :=
    site_8000e97c_sr σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi11
      hG11 hpc11 hmi11 hload11 rfl hi11
  have hpcJ : σ12.regs.get? Register.PC = some (0x8001438c#64 : BitVec 64) := by
    have := obs_jal_pc hobs12
    rwa [show (0x8000e97c#64 : BitVec 64) + sign_extend (m := 64) (0x005a10#21)
        = (0x8001438c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hraJ : σ12.regs.get? Register.x1 = some (0x8000e980#64 : BitVec 64) := by
    have := obs_jal_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000e97c#64) 4 = (0x8000e980#64 : BitVec 64) from by decide] at this
  have ha10_12 := obs_jal_other' hobs12 Register.x10 (by decide) ha10_11
  have ha11_12 := obs_jal_other' hobs12 Register.x11 (by decide) ha11_11
  have ha12_12 := obs_jal_other' hobs12 Register.x12 (by decide) ha12_11
  have ha13_12 := obs_jal_other' hobs12 Register.x13 (by decide) ha13_11
  have hp12 := pins_jal hobs12 (by rfl) hp11
  have hm12eq : σ12.mem = writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32) := by
    rw [hmem12, hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hm5]
  -- === call 1: __ssputs_r fast path on iov[0] ===
  have hsloadM2 : Vsa.Sim.Code.__ssputs_rLoaded
      (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (q.toNat + 8) (1#32)) :=
    ssputs_writeMap4_ss _ _ _ (by omega) (hmemeq ▸ hsload)
  have hmvloadM2 : MemmoveLoaded
      (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (q.toNat + 8) (1#32)) :=
    memmove_writeMap4_sr _ _ _ (by omega) (hmemeq ▸ hmvload)
  have hcursorM2 : Pin8 (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32)) p.toNat d :=
    Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
      exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hcursor
  have hcapM2 : Pin4 (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32)) (p.toNat + 12) cap32 :=
    Pin4_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
      exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hcap
  have hbsM2 : MvBytes (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32)) s1 n1 bs1 := fun k hk => by
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega),
      srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) _ (by omega)]
    exact hbs1 k hk
  have hregions_sp1 : SpRegions p d s1 (vsp - 64#64) n1 :=
    ⟨⟨hn11, hn131, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩,
     by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
     by omega, by omega, by omega, by omega⟩
  obtain ⟨c1, hsteps_call1, hpost1⟩ :=
    ssputs_fast_spec (fun R => σ12.regs.get? R) (0x8000e980#64) p d s1 (vsp - 64#64) viov q
      n1 cap32 (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (q.toNat + 8) (1#32))
      bs1 (by decide)
      ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG12, (by rw [hm12eq]; exact hsloadM2), (by rw [hm12eq]; exact hmvloadM2), hpcJ,
       ⟨va0, ha10_12⟩, ha11_12, ha12_12, ha13_12, hraJ, hp12.2.2.1, hp12.2.2.2.2.1, hp12.2.1,
       obs_jal_minstret hobs12, hi12, hregions_sp1, hcursorM2, hcapM2, hbsM2,
       (by rw [sext32_toNat_small cap32 (by omega)]; omega), hm12eq, fun R _ => rfl⟩
  obtain ⟨hG', hpc', ha0', hra', hsp', hs0', hs1', hcopied1, hcursor', hcap', hmframe1,
    htick', hregframe1⟩ := hpost1
  obtain ⟨vmi', hmi'⟩ := hG'.minstret
  -- registers surviving the call
  have hp13 : PinsHold σ12 [⟨Register.x18, BitVec.ofNat 64 n1⟩, ⟨Register.x19, va0⟩,
      ⟨Register.x20, p⟩, ⟨Register.x21, (0xffffffffffffffff#64 : BitVec 64)⟩] :=
    ⟨hp12.1, hp12.2.2.2.2.2⟩
  have hp14 := pins_of_frame
    (fun R hl => hregframe1 R (notWrittenSp_of_avoid hl)) (by rfl) hp13
  -- L': [x9, x2, x8, x18, x19, x20, x21]
  have hpA := pins_cons Register.x9 q hs1'
    (pins_cons Register.x2 (vsp - 64#64) hsp' (pins_cons Register.x8 viov hs0' hp14))
  -- ssprint code survives the call
  have hload_c1 : __ssprint_rLoaded c1.σ.mem :=
    ssprint_frame_sr _ _ (fun a ha =>
      hmframe1 a (by omega) (by omega) (by omega) (by omega)) hloadM2
  -- === e980: beq a0,s5 NOT taken (0 ≠ -1) ===
  obtain ⟨σ13, i13, hstp13, hi13, hG13, hmem13, hobs13⟩ :=
    site_8000e980_nottaken_sr c1.σ c1.tick c1.steps _ vmi' (0#64)
      (0xffffffffffffffff#64 : BitVec 64)
      hG' hpc' hmi' ha0' hpA.2.2.2.2.2.2.1 hload_c1 rfl (by decide) htick'
  have hpc13 : σ13.regs.get? Register.PC = some (0x8000e984#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs13
    rwa [show BitVec.addInt (0x8000e980#64) 4 = (0x8000e984#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_bnottaken_minstret hobs13
  have hp15 := pins_bnottaken hobs13 (by rfl) hpA
  have hload13 : __ssprint_rLoaded σ13.mem := hmem13 ▸ hload_c1
  -- === e984: ld a4,16(s1)  (a4 := resid = n1+n2) ===
  have hpinR2 : Pin8 σ13.mem ((q + sign_extend (m := 64) (0x010#12)).toNat)
      (BitVec.ofNat 64 (n1 + n2)) := by
    rw [hq16, hmem13]
    exact Pin8_frame (fun k hk1 hk2 =>
      (hmframe1 k (by omega) (by omega) (by omega) (by omega)).trans (by
        rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
        exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega))) hresid
  obtain ⟨σ14, i14, hstp14, hi14, hG14, hmem14, hobs14⟩ :=
    site_8000e984_sr σ13 i13 (c1.steps + 1) _ vmi13 q _ _ _ _ _ _ _ _
      hG13 hpc13 hmi13 hp15.1 hload13 rfl
      (by rw [hq16]; omega) (by rw [hq16]; omega) (Or.inr (by rw [hq16]; omega))
      (by rw [hq16]; omega)
      hpinR2.1 hpinR2.2.1 hpinR2.2.2.1 hpinR2.2.2.2.1 hpinR2.2.2.2.2.1 hpinR2.2.2.2.2.2.1
      hpinR2.2.2.2.2.2.2.1 hpinR2.2.2.2.2.2.2.2 hi13
  have hpc14 : σ14.regs.get? Register.PC = some (0x8000e988#64 : BitVec 64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x8000e984#64) 4 = (0x8000e988#64 : BitVec 64) from by decide] at this
  have ha14_14 : σ14.regs.get? Register.x14 = some (BitVec.ofNat 64 (n1 + n2)) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  -- L: [x14, x9, x2, x8, x18, x19, x20, x21]
  have hp16 := pins_cons Register.x14 (BitVec.ofNat 64 (n1 + n2)) ha14_14
    (pins_alu hobs14 (by rfl) hp15)
  have hload14 : __ssprint_rLoaded σ14.mem := hmem14 ▸ hload13
  -- === e988: addi s0,s0,16  (s0 := viov+16) ===
  obtain ⟨σ15, i15, hstp15, hi15, hG15, hmem15, hobs15⟩ :=
    site_8000e988_sr σ14 i14 (c1.steps + 1 + 1) _ vmi14 viov
      hG14 hpc14 hmi14 hp16.2.2.2.1 hload14 rfl hi14
  have hpc15 : σ15.regs.get? Register.PC = some (0x8000e98c#64 : BitVec 64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x8000e988#64) 4 = (0x8000e98c#64 : BitVec 64) from by decide] at this
  have ha8_15 : σ15.regs.get? Register.x8
      = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  -- L: [x8, x14, x9, x2, x18, x19, x20, x21]
  have hp17 := pins_cons Register.x8 (viov + sign_extend (m := 64) (0x010#12)) ha8_15
    (pins_alu hobs15 (by rfl) (pins_drop4 hp16))
  have hload15 : __ssprint_rLoaded σ15.mem := hmem15 ▸ hload14
  -- === e98c: sub a4,a4,s2  (a4 := n2) ===
  obtain ⟨σ16, i16, hstp16, hi16, hG16, hmem16, hobs16⟩ :=
    site_8000e98c_sr σ15 i15 (c1.steps + 1 + 1 + 1) _ vmi15
      (BitVec.ofNat 64 (n1 + n2)) (BitVec.ofNat 64 n1)
      hG15 hpc15 hmi15 hp17.2.1 hp17.2.2.2.2.1 hload15 rfl hi15
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000e990#64 : BitVec 64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x8000e98c#64) 4 = (0x8000e990#64 : BitVec 64) from by decide] at this
  have ha14_16 : σ16.regs.get? Register.x14 = some (BitVec.ofNat 64 n2) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ofNat_sub_left n1 n2 (by omega)] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  -- L: [x14, x8, x9, x2, x18, x19, x20, x21]
  have hp18 := pins_cons Register.x14 (BitVec.ofNat 64 n2) ha14_16
    (pins_alu hobs16 (by rfl) (pins_drop2 hp17))
  have hload16 : __ssprint_rLoaded σ16.mem := hmem16 ▸ hload15
  -- === e990: sd a4,16(s1)  (resid := n2) ===
  obtain ⟨σ17, i17, hstp17, hi17, hG17, hmem17, hobs17⟩ :=
    site_8000e990_sr σ16 i16 (c1.steps + 1 + 1 + 1 + 1) _ vmi16 q (BitVec.ofNat 64 n2)
      hG16 hpc16 hmi16 hp18.2.2.1 hp18.1 hload16 rfl
      (by rw [hq16]; omega) (by rw [hq16]; omega) (by rw [hq16]; omega)
      (by rw [hq16]; omega) hi16
  have hpc17 : σ17.regs.get? Register.PC = some (0x8000e994#64 : BitVec 64) := by
    have := obs_store_pc hobs17
    rwa [show BitVec.addInt (0x8000e990#64) 4 = (0x8000e994#64 : BitVec 64) from by decide] at this
  have hm17 : σ17.mem = writeMap8 c1.σ.mem (q.toNat + 16)
      (sdData_val (BitVec.ofNat 64 n2)) := by
    rw [hmem17, mem_afterNextPC, hmem16, hmem15, hmem14, hmem13, hq16]
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret hobs17
  have hp19 := pins_store hobs17 (by rfl) hp18
  have hload17 : __ssprint_rLoaded σ17.mem := by
    rw [hm17]; exact ssprint_writeMap8_ss _ _ _ (by omega) hload_c1
  -- === e994: mv a3,a4  (a3 := n2) ===
  obtain ⟨σ18, i18, hstp18, hi18, hG18, hmem18, hobs18⟩ :=
    site_8000e994_sr σ17 i17 (c1.steps + 1 + 1 + 1 + 1 + 1) _ vmi17 (BitVec.ofNat 64 n2)
      hG17 hpc17 hmi17 hp19.1 hload17 rfl hi17
  have hpc18 : σ18.regs.get? Register.PC = some (0x8000e998#64 : BitVec 64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x8000e994#64) 4 = (0x8000e998#64 : BitVec 64) from by decide] at this
  have ha13_18 : σ18.regs.get? Register.x13 = some (BitVec.ofNat 64 n2) := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (BitVec.ofNat 64 n2)] at this
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hp20 := pins_alu hobs18 (by rfl) hp19
  have hload18 : __ssprint_rLoaded σ18.mem := hmem18 ▸ hload17
  -- === e998: bnez a3 TAKEN (resid = n2 ≠ 0) → 0x8000e950 ===
  obtain ⟨σ19, i19, hstp19, hi19, hG19, hmem19, hobs19⟩ :=
    site_8000e998_taken_sr σ18 i18 (c1.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi18
      (BitVec.ofNat 64 n2)
      hG18 hpc18 hmi18 ha13_18 hload18 rfl
      (bne64_true_of_toNat_ne _ _ (by simp only [BitVec.toNat_ofNat]; omega)) hi18
  have hpc19 : σ19.regs.get? Register.PC = some (0x8000e950#64 : BitVec 64) := by
    have := obs_btaken_pc hobs19
    rwa [site_8000e998_taken_sr_tgt] at this
  have hp21 := pins_btaken hobs19 (by rfl) hp20
  have hload19 : __ssprint_rLoaded σ19.mem := hmem19 ▸ hload18
  have hm19 : σ19.mem = writeMap8 c1.σ.mem (q.toNat + 16)
      (sdData_val (BitVec.ofNat 64 n2)) := by
    rw [hmem19, hmem18, hm17]
  -- === St2 memory facts ===
  have hcountC1 : Pin4 c1.σ.mem (q.toNat + 8) (1#32) :=
    Pin4_frame (fun k hk1 hk2 =>
      hmframe1 k (by omega) (by omega) (by omega) (by omega)) (Pin4_writeMap4 _ _ _)
  have hiovbM2 : Pin8 (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32)) (viov.toNat + 16) s2 :=
    Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
      exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hiov1b
  have hiovlM2 : Pin8 (writeMap4 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21)
      (q.toNat + 8) (1#32)) (viov.toNat + 24) (BitVec.ofNat 64 n2) :=
    Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
      exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) k (by omega)) hiov1l
  have hiovbC1 : Pin8 c1.σ.mem (viov.toNat + 16) s2 :=
    Pin8_frame (fun k hk1 hk2 =>
      hmframe1 k (by omega) (by omega) (by omega) (by omega)) hiovbM2
  have hiovlC1 : Pin8 c1.σ.mem (viov.toNat + 24) (BitVec.ofNat 64 n2) :=
    Pin8_frame (fun k hk1 hk2 =>
      hmframe1 k (by omega) (by omega) (by omega) (by omega)) hiovlM2
  have hslot : ∀ (K : Nat) (v : BitVec 64), 8 ≤ K → K ≤ 56 →
      Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - K) v →
      Pin8 σ19.mem (vsp.toNat - K) v := by
    intro K v hK1 hK2 hpin
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (Pin8_frame (fun k hk1 hk2 =>
        hmframe1 k (by omega) (by omega) (by omega) (by omega))
        (Pin8_frame (fun k hk1 hk2 =>
          getElem_writeMap4_disjoint _ _ _ _ (by omega)) hpin))
  -- assemble St2
  refine ⟨⟨σ19, i19, c1.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG19, hload19, ?_, ?_, hpc19,
    hp21.2.2.2.1, hp21.2.1, hp21.2.2.1, hp21.1, hp21.2.2.2.2.2.1, hp21.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.1, hi19, hreg, hcaplt, hcap31, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hslot 8 r (by omega) (by omega) (srStackMem_ra m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 16 v8 (by omega) (by omega) (srStackMem_s0 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 24 v9 (by omega) (by omega) (srStackMem_s1 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 32 v18 (by omega) (by omega) (srStackMem_s2 m0 vsp r v8 v9 v18 v19 v20 v21),
    hslot 40 v19 (by omega) (by omega) (srStackMem_s3 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 48 v20 (by omega) (by omega) (srStackMem_s4 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 56 v21 (by omega) (by omega) (srStackMem_s5 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    ?_, ?_⟩
  · -- Steps chain
    exact ((((((((((((((((((Steps.single hstp1).trans (Steps.single hstp2)).trans
      (Steps.single hstp3)).trans (Steps.single hstp4)).trans (Steps.single hstp5)).trans
      (Steps.single hstp6)).trans (Steps.single hstp7)).trans (Steps.single hstp8)).trans
      (Steps.single hstp9)).trans (Steps.single hstp10)).trans (Steps.single hstp11)).trans
      (Steps.single hstp12)).trans hsteps_call1).trans (Steps.single hstp13)).trans
      (Steps.single hstp14)).trans (Steps.single hstp15)).trans (Steps.single hstp16)).trans
      (Steps.single hstp17)).trans ((Steps.single hstp18).trans (Steps.single hstp19))
  · -- __ssputs_rLoaded
    rw [hm19]
    exact ssputs_writeMap8_ss _ _ _ (by omega)
      (ssputs_frame_ss _ _ (fun a ha =>
        hmframe1 a (by omega) (by omega) (by omega) (by omega)) hsloadM2)
  · -- MemmoveLoaded
    rw [hm19]
    exact memmove_writeMap8_ss _ _ _ (by omega)
      (memmove_frame_sr _ _ (fun a ha =>
        hmframe1 a (by omega) (by omega) (by omega) (by omega)) hmvloadM2)
  · -- count1
    rw [hm19]
    exact Pin4_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega)) hcountC1
  · -- resid1
    rw [hm19]
    exact Pin8_writeMap8 _ _ _
  · -- hiov1b
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega)) hiovbC1
  · -- hiov1l
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega)) hiovlC1
  · -- cursor1
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega)) hcursor'
  · -- cap1
    rw [hm19]
    exact Pin4_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (swData_spNewCap cap32 n1 ▸ hcap')
  · -- copied1
    intro k hk
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact hcopied1 k hk
  · -- hsrc2
    intro k hk
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    refine (hmframe1 _ (by omega) (by omega) (by omega) (by omega)).trans ?_
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega),
      srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) _ (by omega)]
    exact hbs2 k hk
  · -- mframe
    intro a h1 h2 h3 h4 h5 h6
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    refine (hmframe1 a (by omega) (by omega) (by omega) (by omega)).trans ?_
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) a (by omega)
  · -- register ghost frame
    intro R hR
    have hmv := hR.sp.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.sp.x15 hmv
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.sp.x13 hmv
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.sp.x12 hmv
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_mv hobs4 R hmv
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_bnottaken_mv hobs5 R hmv
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_mv hobs6 R hR.x18 hmv
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_bnottaken_mv hobs7 R hmv
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_alu_mv hobs8 R hR.sp.x12 hmv
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_mv hobs9 R hR.sp.x13 hmv
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_mv hobs10 R hR.sp.x11 hmv
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.sp.x10 hmv
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_jal_sp hobs12 R hR.sp.x1 hmv
    have ec : c1.σ.regs.get? R = σ12.regs.get? R := hregframe1 R hR.sp
    have e13 : σ13.regs.get? R = c1.σ.regs.get? R := frame_bnottaken_mv hobs13 R hmv
    have e14 : σ14.regs.get? R = σ13.regs.get? R := frame_alu_mv hobs14 R hR.sp.x14 hmv
    have e15 : σ15.regs.get? R = σ14.regs.get? R := frame_alu_mv hobs15 R hR.sp.x8 hmv
    have e16 : σ16.regs.get? R = σ15.regs.get? R := frame_alu_mv hobs16 R hR.sp.x14 hmv
    have e17 : σ17.regs.get? R = σ16.regs.get? R := frame_store_mv hobs17 R hmv
    have e18 : σ18.regs.get? R = σ17.regs.get? R := frame_alu_mv hobs18 R hR.sp.x13 hmv
    have e19 : σ19.regs.get? R = σ18.regs.get? R := frame_btaken_mv hobs19 R hmv
    rw [e19, e18, e17, e16, e15, e14, e13, ec, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3,
      e2, e1]
    exact hgframe R hR

/-! ## Iteration 2: `0x8000e950 → … → jal __ssputs_r (iov[1]) → … → 0x8000e99c` -/

theorem tr_ssprint_iter2 (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) :
    Triple (St2Sr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2)
      (St3Sr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2) := by
  intro c hSt
  obtain ⟨hgood, hload, hsload, hmvload, hpc, hsp, hs0i, hs1r, ha4r, hs3r, hs4r, hs5r, htick,
    hreg, hcaplt, hcap31, hcount1, hresid1, hiov1b, hiov1l, hcursor1, hcap1, hcopied1S, hsrc2,
    hsave_ra, hsave_s0, hsave_s1, hsave_s2, hsave_s3, hsave_s4, hsave_s5, hmframeS,
    hgframe⟩ := hSt
  obtain ⟨vmi, hmi⟩ := hgood.minstret
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hn11 := hreg.n1_1; have hn131 := hreg.n1_31
  have hn21 := hreg.n2_1; have hn231 := hreg.n2_31
  have hqlo := hreg.q_lo; have hqhi := hreg.q_hi
  have hqwin := hreg.q_win; have hqal := hreg.q_align
  have hvlo := hreg.v_lo; have hvhi := hreg.v_hi
  have hvwin := hreg.v_win; have hval := hreg.v_align
  have hplo := hreg.p_lo; have hphi := hreg.p_hi
  have hpwin := hreg.p_win; have hpal := hreg.p_align
  have hdlo := hreg.d_lo; have hdhi := hreg.d_hi; have hdwin := hreg.d_win
  have hs2lo := hreg.s2_lo; have hs2hi := hreg.s2_hi; have hs2win := hreg.s2_win
  have hsplo := hreg.sp_lo; have hsphi := hreg.sp_hi
  have hspwin := hreg.sp_win; have hspal := hreg.sp_align
  have hds2 := hreg.dst_src2
  have hsd := hreg.sink_dst; have hsstk := hreg.sink_stack; have hss2 := hreg.sink_src2
  have hstkd := hreg.stack_dst; have hstks2 := hreg.stack_src2
  have hqd := hreg.q_dst; have hqsink := hreg.q_sink; have hqstk := hreg.q_stack
  have hqs2 := hreg.q_src2
  have hvd := hreg.v_dst; have hvsink := hreg.v_sink; have hvstk := hreg.v_stack
  have hvq := hreg.v_q
  -- address bridges
  have hspN : (vsp - 64#64).toNat = vsp.toNat - 64 := sp_sub64_toNat vsp (by omega)
  have hq8 : ((q : BitVec 64) + sign_extend (m := 64) (0x008#12)).toNat = q.toNat + 8 :=
    ptr_addoff q _ 8 (by decide) (by omega)
  have hq16 : ((q : BitVec 64) + sign_extend (m := 64) (0x010#12)).toNat = q.toNat + 16 :=
    ptr_addoff q _ 16 (by decide) (by omega)
  have hv16 : ((viov : BitVec 64) + sign_extend (m := 64) (0x010#12)).toNat = viov.toNat + 16 :=
    ptr_addoff viov _ 16 (by decide) (by omega)
  have hv24 : (((viov : BitVec 64) + sign_extend (m := 64) (0x010#12))
      + sign_extend (m := 64) (0x008#12)).toNat = viov.toNat + 24 := by
    rw [ptr_addoff _ _ 8 (by decide) (by rw [hv16]; omega), hv16]
  have hv16z : (((viov : BitVec 64) + sign_extend (m := 64) (0x010#12))
      + sign_extend (m := 64) (0x000#12)).toNat = viov.toNat + 16 := by
    rw [off_ed_00, hv16]
  have hdn1 : (d + BitVec.ofNat 64 n1).toNat = d.toNat + n1 :=
    add_ofNat_toNat d n1 (by omega)
  -- pin list L0: [x9, x2, x14, x8, x19, x20, x21]
  have hp0 : PinsHold c.σ [⟨Register.x9, q⟩, ⟨Register.x2, vsp - 64#64⟩,
      ⟨Register.x14, BitVec.ofNat 64 n2⟩,
      ⟨Register.x8, viov + sign_extend (m := 64) (0x010#12)⟩, ⟨Register.x19, va0⟩,
      ⟨Register.x20, p⟩, ⟨Register.x21, (0xffffffffffffffff#64 : BitVec 64)⟩] :=
    ⟨hs1r, hsp, ha4r, hs0i, hs3r, hs4r, hs5r, trivial⟩
  -- === e950: lw a5,8(s1)  (count = 1) ===
  have hpinC : Pin4 c.σ.mem ((q + sign_extend (m := 64) (0x008#12)).toNat) (1#32) := by
    rw [hq8]; exact hcount1
  obtain ⟨σ1, i1, hstp1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000e950_sr c.σ c.tick c.steps _ vmi q _ _ _ _
      hgood hpc hmi hp0.1 hload rfl
      (by rw [hq8]; omega) (by rw [hq8]; omega) (Or.inr (by rw [hq8]; omega))
      (by rw [hq8]; omega)
      hpinC.1 hpinC.2.1 hpinC.2.2.1 hpinC.2.2.2 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000e954#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000e950#64) 4 = (0x8000e954#64 : BitVec 64) from by decide] at this
  have ha15_1 : σ1.regs.get? Register.x15 = some (1#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [lw_count1_sr] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hp1 := pins_alu hobs1 (by rfl) hp0
  have hload1 : __ssprint_rLoaded σ1.mem := hmem1 ▸ hload
  -- === e954: mv a3,a4 ===
  obtain ⟨σ2, i2, hstp2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000e954_sr σ1 i1 (c.steps + 1) _ vmi1 (BitVec.ofNat 64 n2)
      hG1 hpc1 hmi1 hp1.2.2.1 hload1 rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000e958#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000e954#64) 4 = (0x8000e958#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have ha15_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha15_1
  have hp2 := pins_alu hobs2 (by rfl) hp1
  have hload2 : __ssprint_rLoaded σ2.mem := hmem2 ▸ hload1
  -- === e958: addiw a2,a5,-1  (a2 := 0) ===
  obtain ⟨σ3, i3, hstp3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000e958_sr σ2 i2 (c.steps + 1 + 1) _ vmi2 (1#64)
      hG2 hpc2 hmi2 ha15_2 hload2 rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000e95c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x8000e958#64) 4 = (0x8000e95c#64 : BitVec 64) from by decide] at this
  have ha12_3 : σ3.regs.get? Register.x12 = some (BitVec.ofNat 64 0) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addiw_cnt1_sr] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have ha15_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha15_2
  have hp3 := pins_alu hobs3 (by rfl) hp2
  have hload3 : __ssprint_rLoaded σ3.mem := hmem3 ▸ hload2
  -- === e95c: sw a2,8(s1)  (count := 0) ===
  obtain ⟨σ4, i4, hstp4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000e95c_sr σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 q (BitVec.ofNat 64 0)
      hG3 hpc3 hmi3 hp3.1 ha12_3 hload3 rfl
      (by rw [hq8]; omega) (by rw [hq8]; omega) (by rw [hq8]; omega) (by rw [hq8]; omega) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000e960#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x8000e95c#64) 4 = (0x8000e960#64 : BitVec 64) from by decide] at this
  have hm4 : σ4.mem = writeMap4 c.σ.mem (q.toNat + 8) (0#32) := by
    rw [hmem4, mem_afterNextPC, hmem3, hmem2, hmem1, hq8, swData_zero_sr]
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have ha15_4 := obs_store_other' hobs4 Register.x15 (by decide) ha15_3
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hloadM5 : __ssprint_rLoaded (writeMap4 c.σ.mem (q.toNat + 8) (0#32)) :=
    ssprint_writeMap4_ss _ _ _ (by omega) hload
  have hload4 : __ssprint_rLoaded σ4.mem := by rw [hm4]; exact hloadM5
  -- === e960: blez a5 NOT taken (count 1 > 0) ===
  obtain ⟨σ5, i5, hstp5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000e960_nottaken_sr σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 (1#64)
      hG4 hpc4 hmi4 ha15_4 hload4 rfl (by decide) hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000e964#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs5
    rwa [show BitVec.addInt (0x8000e960#64) 4 = (0x8000e964#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_bnottaken_minstret hobs5
  have hp5 := pins_bnottaken hobs5 (by rfl) hp4
  have hload5 : __ssprint_rLoaded σ5.mem := hmem5 ▸ hload4
  have hm5 : σ5.mem = writeMap4 c.σ.mem (q.toNat + 8) (0#32) := by rw [hmem5, hm4]
  -- === e964: ld s2,8(s0)  (s2 := len2 = n2) ===
  have hpinL2 : Pin8 σ5.mem (((viov + sign_extend (m := 64) (0x010#12))
      + sign_extend (m := 64) (0x008#12)).toNat) (BitVec.ofNat 64 n2) := by
    rw [hv24, hm5]
    exact Pin8_frame (fun k hk1 hk2 =>
      getElem_writeMap4_disjoint _ _ _ _ (by omega)) hiov1l
  obtain ⟨σ6, i6, hstp6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000e964_sr σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5
      (viov + sign_extend (m := 64) (0x010#12)) _ _ _ _ _ _ _ _
      hG5 hpc5 hmi5 hp5.2.2.2.1 hload5 rfl
      (by rw [hv24]; omega) (by rw [hv24]; omega) (Or.inr (by rw [hv24]; omega))
      (by rw [hv24]; omega)
      hpinL2.1 hpinL2.2.1 hpinL2.2.2.1 hpinL2.2.2.2.1 hpinL2.2.2.2.2.1 hpinL2.2.2.2.2.2.1
      hpinL2.2.2.2.2.2.2.1 hpinL2.2.2.2.2.2.2.2 hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000e968#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000e964#64) 4 = (0x8000e968#64 : BitVec 64) from by decide] at this
  have ha18_6 : σ6.regs.get? Register.x18 = some (BitVec.ofNat 64 n2) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- L6: [x18, x9, x2, x14, x8, x19, x20, x21]
  have hp6 := pins_cons Register.x18 (BitVec.ofNat 64 n2) ha18_6 (pins_alu hobs6 (by rfl) hp5)
  have hload6 : __ssprint_rLoaded σ6.mem := hmem6 ▸ hload5
  -- === e968: beqz s2 NOT taken (n2 ≥ 1) ===
  obtain ⟨σ7, i7, hstp7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000e968_nottaken_sr σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi6
      (BitVec.ofNat 64 n2)
      hG6 hpc6 hmi6 hp6.1 hload6 rfl
      (beq64_false_of_toNat_ne _ _ (by simp only [BitVec.toNat_ofNat]; omega)) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x8000e96c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs7
    rwa [show BitVec.addInt (0x8000e968#64) 4 = (0x8000e96c#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_bnottaken_minstret hobs7
  have hp7 := pins_bnottaken hobs7 (by rfl) hp6
  have hload7 : __ssprint_rLoaded σ7.mem := hmem7 ▸ hload6
  have hm7 : σ7.mem = writeMap4 c.σ.mem (q.toNat + 8) (0#32) := by rw [hmem7, hmem6, hm5]
  -- === e96c: ld a2,0(s0)  (a2 := base2 = s2) ===
  have hpinB2 : Pin8 σ7.mem (((viov + sign_extend (m := 64) (0x010#12))
      + sign_extend (m := 64) (0x000#12)).toNat) s2 := by
    rw [hv16z, hm7]
    exact Pin8_frame (fun k hk1 hk2 =>
      getElem_writeMap4_disjoint _ _ _ _ (by omega)) hiov1b
  obtain ⟨σ8, i8, hstp8, hi8, hG8, hmem8, hobs8⟩ :=
    site_8000e96c_sr σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi7
      (viov + sign_extend (m := 64) (0x010#12)) _ _ _ _ _ _ _ _
      hG7 hpc7 hmi7 hp7.2.2.2.2.1 hload7 rfl
      (by rw [hv16z]; omega) (by rw [hv16z]; omega) (Or.inr (by rw [hv16z]; omega))
      (by rw [hv16z]; omega)
      hpinB2.1 hpinB2.2.1 hpinB2.2.2.1 hpinB2.2.2.2.1 hpinB2.2.2.2.2.1 hpinB2.2.2.2.2.2.1
      hpinB2.2.2.2.2.2.2.1 hpinB2.2.2.2.2.2.2.2 hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000e970#64 : BitVec 64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x8000e96c#64) 4 = (0x8000e970#64 : BitVec 64) from by decide] at this
  have ha12_8 : σ8.regs.get? Register.x12 = some s2 := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hp8 := pins_alu hobs8 (by rfl) hp7
  have hload8 : __ssprint_rLoaded σ8.mem := hmem8 ▸ hload7
  -- === e970: mv a3,s2  (a3 := n2) ===
  obtain ⟨σ9, i9, hstp9, hi9, hG9, hmem9, hobs9⟩ :=
    site_8000e970_sr σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi8
      (BitVec.ofNat 64 n2)
      hG8 hpc8 hmi8 hp8.1 hload8 rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000e974#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000e970#64) 4 = (0x8000e974#64 : BitVec 64) from by decide] at this
  have ha13_9 : σ9.regs.get? Register.x13 = some (BitVec.ofNat 64 n2) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (BitVec.ofNat 64 n2)] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have ha12_9 := obs_alu_other' hobs9 Register.x12 (by decide) ha12_8
  have hp9 := pins_alu hobs9 (by rfl) hp8
  have hload9 : __ssprint_rLoaded σ9.mem := hmem9 ▸ hload8
  -- === e974: mv a1,s4  (a1 := p) ===
  obtain ⟨σ10, i10, hstp10, hi10, hG10, hmem10, hobs10⟩ :=
    site_8000e974_sr σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi9 p
      hG9 hpc9 hmi9 hp9.2.2.2.2.2.2.1 hload9 rfl hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000e978#64 : BitVec 64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x8000e974#64) 4 = (0x8000e978#64 : BitVec 64) from by decide] at this
  have ha11_10 : σ10.regs.get? Register.x11 = some p := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add p] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have ha12_10 := obs_alu_other' hobs10 Register.x12 (by decide) ha12_9
  have ha13_10 := obs_alu_other' hobs10 Register.x13 (by decide) ha13_9
  have hp10 := pins_alu hobs10 (by rfl) hp9
  have hload10 : __ssprint_rLoaded σ10.mem := hmem10 ▸ hload9
  -- === e978: mv a0,s3  (a0 := va0) ===
  obtain ⟨σ11, i11, hstp11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000e978_sr σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi10 va0
      hG10 hpc10 hmi10 hp10.2.2.2.2.2.1 hload10 rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000e97c#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x8000e978#64) 4 = (0x8000e97c#64 : BitVec 64) from by decide] at this
  have ha10_11 : σ11.regs.get? Register.x10 = some va0 := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add va0] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have ha11_11 := obs_alu_other' hobs11 Register.x11 (by decide) ha11_10
  have ha12_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha12_10
  have ha13_11 := obs_alu_other' hobs11 Register.x13 (by decide) ha13_10
  have hp11 := pins_alu hobs11 (by rfl) hp10
  have hload11 : __ssprint_rLoaded σ11.mem := hmem11 ▸ hload10
  -- === e97c: jal ra,__ssputs_r ===
  obtain ⟨σ12, i12, hstp12, hi12, hG12, hmem12, hobs12⟩ :=
    site_8000e97c_sr σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi11
      hG11 hpc11 hmi11 hload11 rfl hi11
  have hpcJ : σ12.regs.get? Register.PC = some (0x8001438c#64 : BitVec 64) := by
    have := obs_jal_pc hobs12
    rwa [show (0x8000e97c#64 : BitVec 64) + sign_extend (m := 64) (0x005a10#21)
        = (0x8001438c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hraJ : σ12.regs.get? Register.x1 = some (0x8000e980#64 : BitVec 64) := by
    have := obs_jal_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000e97c#64) 4 = (0x8000e980#64 : BitVec 64) from by decide] at this
  have ha10_12 := obs_jal_other' hobs12 Register.x10 (by decide) ha10_11
  have ha11_12 := obs_jal_other' hobs12 Register.x11 (by decide) ha11_11
  have ha12_12 := obs_jal_other' hobs12 Register.x12 (by decide) ha12_11
  have ha13_12 := obs_jal_other' hobs12 Register.x13 (by decide) ha13_11
  have hp12 := pins_jal hobs12 (by rfl) hp11
  have hm12eq : σ12.mem = writeMap4 c.σ.mem (q.toNat + 8) (0#32) := by
    rw [hmem12, hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hm5]
  -- === call 2: __ssputs_r fast path on iov[1] ===
  have hsloadM5 : Vsa.Sim.Code.__ssputs_rLoaded (writeMap4 c.σ.mem (q.toNat + 8) (0#32)) :=
    ssputs_writeMap4_ss _ _ _ (by omega) hsload
  have hmvloadM5 : MemmoveLoaded (writeMap4 c.σ.mem (q.toNat + 8) (0#32)) :=
    memmove_writeMap4_sr _ _ _ (by omega) hmvload
  have hcursorM5 : Pin8 (writeMap4 c.σ.mem (q.toNat + 8) (0#32)) p.toNat
      (d + BitVec.ofNat 64 n1) :=
    Pin8_frame (fun k hk1 hk2 => getElem_writeMap4_disjoint _ _ _ _ (by omega)) hcursor1
  have hcapM5 : Pin4 (writeMap4 c.σ.mem (q.toNat + 8) (0#32)) (p.toNat + 12)
      (cap32 - BitVec.ofNat 32 n1) :=
    Pin4_frame (fun k hk1 hk2 => getElem_writeMap4_disjoint _ _ _ _ (by omega)) hcap1
  have hbsM5 : MvBytes (writeMap4 c.σ.mem (q.toNat + 8) (0#32)) s2 n2 bs2 := fun k hk => by
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact hsrc2 k hk
  have hcap2toNat : (cap32 - BitVec.ofNat 32 n1).toNat = cap32.toNat - n1 :=
    sub32_toNat cap32 n1 (by omega) (by omega)
  have hregions_sp2 : SpRegions p (d + BitVec.ofNat 64 n1) s2 (vsp - 64#64) n2 :=
    ⟨⟨hn21, hn231, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩,
     by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
     by omega, by omega, by omega, by omega⟩
  obtain ⟨c1, hsteps_call2, hpost2⟩ :=
    ssputs_fast_spec (fun R => σ12.regs.get? R) (0x8000e980#64) p (d + BitVec.ofNat 64 n1) s2
      (vsp - 64#64) (viov + sign_extend (m := 64) (0x010#12)) q n2
      (cap32 - BitVec.ofNat 32 n1) (writeMap4 c.σ.mem (q.toNat + 8) (0#32))
      bs2 (by decide)
      ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG12, (by rw [hm12eq]; exact hsloadM5), (by rw [hm12eq]; exact hmvloadM5), hpcJ,
       ⟨va0, ha10_12⟩, ha11_12, ha12_12, ha13_12, hraJ, hp12.2.2.1, hp12.2.2.2.2.1, hp12.2.1,
       obs_jal_minstret hobs12, hi12, hregions_sp2, hcursorM5, hcapM5, hbsM5,
       (by rw [sext32_toNat_small _ (by rw [hcap2toNat]; omega), hcap2toNat]; omega),
       hm12eq, fun R _ => rfl⟩
  obtain ⟨hG', hpc', ha0', hra', hsp', hs0', hs1', hcopied2, hcursor', hcap', hmframe2,
    htick', hregframe2⟩ := hpost2
  obtain ⟨vmi', hmi'⟩ := hG'.minstret
  -- registers surviving the call
  have hp13 : PinsHold σ12 [⟨Register.x18, BitVec.ofNat 64 n2⟩, ⟨Register.x19, va0⟩,
      ⟨Register.x20, p⟩, ⟨Register.x21, (0xffffffffffffffff#64 : BitVec 64)⟩] :=
    ⟨hp12.1, hp12.2.2.2.2.2⟩
  have hp14 := pins_of_frame
    (fun R hl => hregframe2 R (notWrittenSp_of_avoid hl)) (by rfl) hp13
  -- L': [x9, x2, x18, x19, x20, x21]
  have hpA := pins_cons Register.x9 q hs1' (pins_cons Register.x2 (vsp - 64#64) hsp' hp14)
  have hload_c1 : __ssprint_rLoaded c1.σ.mem :=
    ssprint_frame_sr _ _ (fun a ha =>
      hmframe2 a (by omega) (by omega) (by omega) (by omega)) hloadM5
  -- === e980: beq a0,s5 NOT taken (0 ≠ -1) ===
  obtain ⟨σ13, i13, hstp13, hi13, hG13, hmem13, hobs13⟩ :=
    site_8000e980_nottaken_sr c1.σ c1.tick c1.steps _ vmi' (0#64)
      (0xffffffffffffffff#64 : BitVec 64)
      hG' hpc' hmi' ha0' hpA.2.2.2.2.2.1 hload_c1 rfl (by decide) htick'
  have hpc13 : σ13.regs.get? Register.PC = some (0x8000e984#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs13
    rwa [show BitVec.addInt (0x8000e980#64) 4 = (0x8000e984#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_bnottaken_minstret hobs13
  have hp15 := pins_bnottaken hobs13 (by rfl) hpA
  have hload13 : __ssprint_rLoaded σ13.mem := hmem13 ▸ hload_c1
  have hs0'_13 := obs_bnottaken_other' hobs13 Register.x8 (by decide) hs0'
  -- === e984: ld a4,16(s1)  (a4 := resid = n2) ===
  have hpinR2 : Pin8 σ13.mem ((q + sign_extend (m := 64) (0x010#12)).toNat)
      (BitVec.ofNat 64 n2) := by
    rw [hq16, hmem13]
    exact Pin8_frame (fun k hk1 hk2 =>
      (hmframe2 k (by omega) (by omega) (by omega) (by omega)).trans (by
        rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)])) hresid1
  obtain ⟨σ14, i14, hstp14, hi14, hG14, hmem14, hobs14⟩ :=
    site_8000e984_sr σ13 i13 (c1.steps + 1) _ vmi13 q _ _ _ _ _ _ _ _
      hG13 hpc13 hmi13 hp15.1 hload13 rfl
      (by rw [hq16]; omega) (by rw [hq16]; omega) (Or.inr (by rw [hq16]; omega))
      (by rw [hq16]; omega)
      hpinR2.1 hpinR2.2.1 hpinR2.2.2.1 hpinR2.2.2.2.1 hpinR2.2.2.2.2.1 hpinR2.2.2.2.2.2.1
      hpinR2.2.2.2.2.2.2.1 hpinR2.2.2.2.2.2.2.2 hi13
  have hpc14 : σ14.regs.get? Register.PC = some (0x8000e988#64 : BitVec 64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x8000e984#64) 4 = (0x8000e988#64 : BitVec 64) from by decide] at this
  have ha14_14 : σ14.regs.get? Register.x14 = some (BitVec.ofNat 64 n2) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  -- L: [x14, x9, x2, x18, x19, x20, x21]
  have hp16 := pins_cons Register.x14 (BitVec.ofNat 64 n2) ha14_14
    (pins_alu hobs14 (by rfl) hp15)
  have hload14 : __ssprint_rLoaded σ14.mem := hmem14 ▸ hload13
  have hs0'_14 := obs_alu_other' hobs14 Register.x8 (by decide) hs0'_13
  -- === e988: addi s0,s0,16 ===
  obtain ⟨σ15, i15, hstp15, hi15, hG15, hmem15, hobs15⟩ :=
    site_8000e988_sr σ14 i14 (c1.steps + 1 + 1) _ vmi14
      (viov + sign_extend (m := 64) (0x010#12))
      hG14 hpc14 hmi14 hs0'_14 hload14 rfl hi14
  have hpc15 : σ15.regs.get? Register.PC = some (0x8000e98c#64 : BitVec 64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x8000e988#64) 4 = (0x8000e98c#64 : BitVec 64) from by decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hp17 := pins_alu hobs15 (by rfl) hp16
  have hload15 : __ssprint_rLoaded σ15.mem := hmem15 ▸ hload14
  -- === e98c: sub a4,a4,s2  (a4 := 0) ===
  obtain ⟨σ16, i16, hstp16, hi16, hG16, hmem16, hobs16⟩ :=
    site_8000e98c_sr σ15 i15 (c1.steps + 1 + 1 + 1) _ vmi15
      (BitVec.ofNat 64 n2) (BitVec.ofNat 64 n2)
      hG15 hpc15 hmi15 hp17.1 hp17.2.2.2.1 hload15 rfl hi15
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000e990#64 : BitVec 64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x8000e98c#64) 4 = (0x8000e990#64 : BitVec 64) from by decide] at this
  have ha14_16 : σ16.regs.get? Register.x14 = some (0#64) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [BitVec.sub_self] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  -- L: [x14(0), x9, x2, x18, x19, x20, x21]
  have hp18 := pins_cons Register.x14 (0#64) ha14_16 (pins_alu hobs16 (by rfl) hp17.2)
  have hload16 : __ssprint_rLoaded σ16.mem := hmem16 ▸ hload15
  -- === e990: sd a4,16(s1)  (resid := 0) ===
  obtain ⟨σ17, i17, hstp17, hi17, hG17, hmem17, hobs17⟩ :=
    site_8000e990_sr σ16 i16 (c1.steps + 1 + 1 + 1 + 1) _ vmi16 q (0#64)
      hG16 hpc16 hmi16 hp18.2.1 hp18.1 hload16 rfl
      (by rw [hq16]; omega) (by rw [hq16]; omega) (by rw [hq16]; omega)
      (by rw [hq16]; omega) hi16
  have hpc17 : σ17.regs.get? Register.PC = some (0x8000e994#64 : BitVec 64) := by
    have := obs_store_pc hobs17
    rwa [show BitVec.addInt (0x8000e990#64) 4 = (0x8000e994#64 : BitVec 64) from by decide] at this
  have hm17 : σ17.mem = writeMap8 c1.σ.mem (q.toNat + 16) (sdData_val (0#64)) := by
    rw [hmem17, mem_afterNextPC, hmem16, hmem15, hmem14, hmem13, hq16]
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret hobs17
  have hp19 := pins_store hobs17 (by rfl) hp18
  have hload17 : __ssprint_rLoaded σ17.mem := by
    rw [hm17]; exact ssprint_writeMap8_ss _ _ _ (by omega) hload_c1
  -- === e994: mv a3,a4  (a3 := 0) ===
  obtain ⟨σ18, i18, hstp18, hi18, hG18, hmem18, hobs18⟩ :=
    site_8000e994_sr σ17 i17 (c1.steps + 1 + 1 + 1 + 1 + 1) _ vmi17 (0#64)
      hG17 hpc17 hmi17 hp19.1 hload17 rfl hi17
  have hpc18 : σ18.regs.get? Register.PC = some (0x8000e998#64 : BitVec 64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x8000e994#64) 4 = (0x8000e998#64 : BitVec 64) from by decide] at this
  have ha13_18 : σ18.regs.get? Register.x13 = some (0#64) := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (0#64)] at this
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hp20 := pins_alu hobs18 (by rfl) hp19
  have hload18 : __ssprint_rLoaded σ18.mem := hmem18 ▸ hload17
  -- === e998: bnez a3 NOT taken (resid = 0) → fall through to 0x8000e99c ===
  obtain ⟨σ19, i19, hstp19, hi19, hG19, hmem19, hobs19⟩ :=
    site_8000e998_nottaken_sr σ18 i18 (c1.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi18 (0#64)
      hG18 hpc18 hmi18 ha13_18 hload18 rfl (by decide) hi18
  have hpc19 : σ19.regs.get? Register.PC = some (0x8000e99c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs19
    rwa [show BitVec.addInt (0x8000e998#64) 4 = (0x8000e99c#64 : BitVec 64) from by decide] at this
  have hp21 := pins_bnottaken hobs19 (by rfl) hp20
  have hload19 : __ssprint_rLoaded σ19.mem := hmem19 ▸ hload18
  have hm19 : σ19.mem = writeMap8 c1.σ.mem (q.toNat + 16) (sdData_val (0#64)) := by
    rw [hmem19, hmem18, hm17]
  -- === St3 memory facts ===
  have hslot2 : ∀ (K : Nat) (v : BitVec 64), 8 ≤ K → K ≤ 56 →
      Pin8 c.σ.mem (vsp.toNat - K) v → Pin8 σ19.mem (vsp.toNat - K) v := by
    intro K v hK1 hK2 hpin
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (Pin8_frame (fun k hk1 hk2 =>
        hmframe2 k (by omega) (by omega) (by omega) (by omega))
        (Pin8_frame (fun k hk1 hk2 =>
          getElem_writeMap4_disjoint _ _ _ _ (by omega)) hpin))
  -- assemble St3
  refine ⟨⟨σ19, i19, c1.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG19, hload19, hpc19,
    hp21.2.2.1, hp21.2.1, hi19, hreg, ?_, ?_, ?_, ?_,
    hslot2 8 r (by omega) (by omega) hsave_ra,
    hslot2 16 v8 (by omega) (by omega) hsave_s0,
    hslot2 24 v9 (by omega) (by omega) hsave_s1,
    hslot2 32 v18 (by omega) (by omega) hsave_s2,
    hslot2 40 v19 (by omega) (by omega) hsave_s3,
    hslot2 48 v20 (by omega) (by omega) hsave_s4,
    hslot2 56 v21 (by omega) (by omega) hsave_s5,
    ?_, ?_⟩
  · -- Steps chain
    exact ((((((((((((((((((Steps.single hstp1).trans (Steps.single hstp2)).trans
      (Steps.single hstp3)).trans (Steps.single hstp4)).trans (Steps.single hstp5)).trans
      (Steps.single hstp6)).trans (Steps.single hstp7)).trans (Steps.single hstp8)).trans
      (Steps.single hstp9)).trans (Steps.single hstp10)).trans (Steps.single hstp11)).trans
      (Steps.single hstp12)).trans hsteps_call2).trans (Steps.single hstp13)).trans
      (Steps.single hstp14)).trans (Steps.single hstp15)).trans (Steps.single hstp16)).trans
      (Steps.single hstp17)).trans ((Steps.single hstp18).trans (Steps.single hstp19))
  · -- copied1: [d, d+n1) still bs1
    intro k hk
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    refine (hmframe2 _ (by rw [hdn1]; omega) (by omega) (by omega) (by omega)).trans ?_
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact hcopied1S k hk
  · -- copied2: [d+n1, d+n1+n2) = bs2
    intro k hk
    have := hcopied2 k hk
    rw [hdn1] at this
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact this
  · -- cursorF
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (add_ofNat_ofNat d n1 n2 ▸ hcursor')
  · -- capF
    rw [hm19]
    exact Pin4_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (swData_spNewCap (cap32 - BitVec.ofNat 32 n1) n2 ▸ hcap')
  · -- mframe
    intro a h1 h2 h3 h4 h5 h6
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    refine (hmframe2 a (by rw [hdn1]; omega) (by omega) (by omega) (by omega)).trans ?_
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact hmframeS a h1 h2 h3 h4 h5 h6
  · -- register ghost frame
    intro R hR
    have hmv := hR.sp.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.sp.x15 hmv
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.sp.x13 hmv
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.sp.x12 hmv
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_mv hobs4 R hmv
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_bnottaken_mv hobs5 R hmv
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_mv hobs6 R hR.x18 hmv
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_bnottaken_mv hobs7 R hmv
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_alu_mv hobs8 R hR.sp.x12 hmv
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_mv hobs9 R hR.sp.x13 hmv
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_mv hobs10 R hR.sp.x11 hmv
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.sp.x10 hmv
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_jal_sp hobs12 R hR.sp.x1 hmv
    have ec : c1.σ.regs.get? R = σ12.regs.get? R := hregframe2 R hR.sp
    have e13 : σ13.regs.get? R = c1.σ.regs.get? R := frame_bnottaken_mv hobs13 R hmv
    have e14 : σ14.regs.get? R = σ13.regs.get? R := frame_alu_mv hobs14 R hR.sp.x14 hmv
    have e15 : σ15.regs.get? R = σ14.regs.get? R := frame_alu_mv hobs15 R hR.sp.x8 hmv
    have e16 : σ16.regs.get? R = σ15.regs.get? R := frame_alu_mv hobs16 R hR.sp.x14 hmv
    have e17 : σ17.regs.get? R = σ16.regs.get? R := frame_store_mv hobs17 R hmv
    have e18 : σ18.regs.get? R = σ17.regs.get? R := frame_alu_mv hobs18 R hR.sp.x13 hmv
    have e19 : σ19.regs.get? R = σ18.regs.get? R := frame_bnottaken_mv hobs19 R hmv
    rw [e19, e18, e17, e16, e15, e14, e13, ec, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3,
      e2, e1]
    exact hgframe R hR

/-! ## Postcondition and the tail: `0x8000e99c → ret` -/

/-- Final postcondition at `PC = r`: success return, both iovecs flushed to
`[d, d+n1+n2)`, cursor advanced, capacity decremented twice, the `q` struct's
resid/count cleared, callee-saves and `sp` restored, and every byte outside
the six written windows equal to the entry memory `m0`. -/
def ssprint_iov2_post (g : (R : Register) → Option (RegisterType R))
    (r q _viov p d _s1 _s2 vsp v8 v9 v18 v19 v20 v21 _va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  c.σ.regs.get? Register.x2 = some vsp ∧
  c.σ.regs.get? Register.x8 = some v8 ∧
  c.σ.regs.get? Register.x9 = some v9 ∧
  c.σ.regs.get? Register.x18 = some v18 ∧
  c.σ.regs.get? Register.x19 = some v19 ∧
  c.σ.regs.get? Register.x20 = some v20 ∧
  c.σ.regs.get? Register.x21 = some v21 ∧
  (∀ k, k < n1 → c.σ.mem[(d.toNat + k)]? = some (bs1 k)) ∧
  (∀ k, k < n2 → c.σ.mem[(d.toNat + n1 + k)]? = some (bs2 k)) ∧
  Pin8 c.σ.mem p.toNat (d + BitVec.ofNat 64 (n1 + n2)) ∧
  Pin4 c.σ.mem (p.toNat + 12) (cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2) ∧
  Pin8 c.σ.mem (q.toNat + 16) (0#64 : BitVec 64) ∧
  Pin4 c.σ.mem (q.toNat + 8) (0#32 : BitVec 32) ∧
  (∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n1 + n2) →
    ¬(p.toNat ≤ a ∧ a < p.toNat + 8) → ¬(p.toNat + 12 ≤ a ∧ a < p.toNat + 16) →
    ¬(q.toNat + 8 ≤ a ∧ a < q.toNat + 12) → ¬(q.toNat + 16 ≤ a ∧ a < q.toNat + 24) →
    ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat) →
    c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenSr R → c.σ.regs.get? R = g R)

theorem tr_ssprint_tail (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (St3Sr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2)
      (ssprint_iov2_post g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0
        bs1 bs2) := by
  intro c hSt
  obtain ⟨hgood, hload, hpc, hsp, hs1r, htick, hreg, hcopied1, hcopied2, hcursorF, hcapF,
    hsave_ra, hsave_s0, hsave_s1, hsave_s2, hsave_s3, hsave_s4, hsave_s5, hmframeS,
    hgframe⟩ := hSt
  obtain ⟨vmi, hmi⟩ := hgood.minstret
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hn11 := hreg.n1_1; have hn131 := hreg.n1_31
  have hn21 := hreg.n2_1; have hn231 := hreg.n2_31
  have hqlo := hreg.q_lo; have hqhi := hreg.q_hi
  have hqwin := hreg.q_win; have hqal := hreg.q_align
  have hplo := hreg.p_lo; have hphi := hreg.p_hi
  have hpwin := hreg.p_win; have hpal := hreg.p_align
  have hdlo := hreg.d_lo; have hdhi := hreg.d_hi; have hdwin := hreg.d_win
  have hsplo := hreg.sp_lo; have hsphi := hreg.sp_hi
  have hspwin := hreg.sp_win; have hspal := hreg.sp_align
  have hsd := hreg.sink_dst; have hsstk := hreg.sink_stack
  have hstkd := hreg.stack_dst
  have hqd := hreg.q_dst; have hqsink := hreg.q_sink; have hqstk := hreg.q_stack
  -- address bridges
  have hspN : (vsp - 64#64).toNat = vsp.toNat - 64 := sp_sub64_toNat vsp (by omega)
  have hq8 : ((q : BitVec 64) + sign_extend (m := 64) (0x008#12)).toNat = q.toNat + 8 :=
    ptr_addoff q _ 8 (by decide) (by omega)
  have hq16 : ((q : BitVec 64) + sign_extend (m := 64) (0x010#12)).toNat = q.toNat + 16 :=
    ptr_addoff q _ 16 (by decide) (by omega)
  have ha24 : ((vsp - 64#64) + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat - 24 := by
    rw [ptr_addoff _ _ 40 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha8 : ((vsp - 64#64) + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat - 8 := by
    rw [ptr_addoff _ _ 56 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha16 : ((vsp - 64#64) + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat - 16 := by
    rw [ptr_addoff _ _ 48 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha40 : ((vsp - 64#64) + sign_extend (m := 64) (0x018#12)).toNat = vsp.toNat - 40 := by
    rw [ptr_addoff _ _ 24 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha48 : ((vsp - 64#64) + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat - 48 := by
    rw [ptr_addoff _ _ 16 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha56 : ((vsp - 64#64) + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat - 56 := by
    rw [ptr_addoff _ _ 8 (by decide) (by rw [hspN]; omega), hspN]; omega
  have ha32 : ((vsp - 64#64) + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat - 32 := by
    rw [ptr_addoff _ _ 32 (by decide) (by rw [hspN]; omega), hspN]; omega
  -- pin list L0: [x2, x9]
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp - 64#64⟩, ⟨Register.x9, q⟩] :=
    ⟨hsp, hs1r, trivial⟩
  -- === e99c: ld s0,48(sp)  (s0 := v8) ===
  have hpin1 : Pin8 c.σ.mem (((vsp - 64#64) + sign_extend (m := 64) (0x030#12)).toNat) v8 := by
    rw [ha16]; exact hsave_s0
  obtain ⟨σ1, i1, hstp1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000e99c_sr c.σ c.tick c.steps _ vmi (vsp - 64#64) _ _ _ _ _ _ _ _
      hgood hpc hmi hp0.1 hload rfl
      (by rw [ha16]; omega) (by rw [ha16]; omega) (Or.inr (by rw [ha16]; omega))
      (by rw [ha16]; omega)
      hpin1.1 hpin1.2.1 hpin1.2.2.1 hpin1.2.2.2.1 hpin1.2.2.2.2.1 hpin1.2.2.2.2.2.1
      hpin1.2.2.2.2.2.2.1 hpin1.2.2.2.2.2.2.2 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000e9a0#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000e99c#64) 4 = (0x8000e9a0#64 : BitVec 64) from by decide] at this
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- L1: [x8, x2, x9]
  have hp1 := pins_cons Register.x8 v8 hx8_1 (pins_alu hobs1 (by rfl) hp0)
  have hload1 : __ssprint_rLoaded σ1.mem := hmem1 ▸ hload
  -- === e9a0: ld s2,32(sp)  (s2 := v18) ===
  have hpin2 : Pin8 σ1.mem (((vsp - 64#64) + sign_extend (m := 64) (0x020#12)).toNat) v18 := by
    rw [ha32, hmem1]; exact hsave_s2
  obtain ⟨σ2, i2, hstp2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000e9a0_sr σ1 i1 (c.steps + 1) _ vmi1 (vsp - 64#64) _ _ _ _ _ _ _ _
      hG1 hpc1 hmi1 hp1.2.1 hload1 rfl
      (by rw [ha32]; omega) (by rw [ha32]; omega) (Or.inr (by rw [ha32]; omega))
      (by rw [ha32]; omega)
      hpin2.1 hpin2.2.1 hpin2.2.2.1 hpin2.2.2.2.1 hpin2.2.2.2.2.1 hpin2.2.2.2.2.2.1
      hpin2.2.2.2.2.2.2.1 hpin2.2.2.2.2.2.2.2 hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000e9a4#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000e9a0#64) 4 = (0x8000e9a4#64 : BitVec 64) from by decide] at this
  have hx18_2 : σ2.regs.get? Register.x18 = some v18 := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- L2: [x18, x8, x2, x9]
  have hp2 := pins_cons Register.x18 v18 hx18_2 (pins_alu hobs2 (by rfl) hp1)
  have hload2 : __ssprint_rLoaded σ2.mem := hmem2 ▸ hload1
  -- === e9a4: ld s3,24(sp)  (s3 := v19) ===
  have hpin3 : Pin8 σ2.mem (((vsp - 64#64) + sign_extend (m := 64) (0x018#12)).toNat) v19 := by
    rw [ha40, hmem2, hmem1]; exact hsave_s3
  obtain ⟨σ3, i3, hstp3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000e9a4_sr σ2 i2 (c.steps + 1 + 1) _ vmi2 (vsp - 64#64) _ _ _ _ _ _ _ _
      hG2 hpc2 hmi2 hp2.2.2.1 hload2 rfl
      (by rw [ha40]; omega) (by rw [ha40]; omega) (Or.inr (by rw [ha40]; omega))
      (by rw [ha40]; omega)
      hpin3.1 hpin3.2.1 hpin3.2.2.1 hpin3.2.2.2.1 hpin3.2.2.2.2.1 hpin3.2.2.2.2.2.1
      hpin3.2.2.2.2.2.2.1 hpin3.2.2.2.2.2.2.2 hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000e9a8#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x8000e9a4#64) 4 = (0x8000e9a8#64 : BitVec 64) from by decide] at this
  have hx19_3 : σ3.regs.get? Register.x19 = some v19 := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  -- L3: [x19, x18, x8, x2, x9]
  have hp3 := pins_cons Register.x19 v19 hx19_3 (pins_alu hobs3 (by rfl) hp2)
  have hload3 : __ssprint_rLoaded σ3.mem := hmem3 ▸ hload2
  -- === e9a8: ld s4,16(sp)  (s4 := v20) ===
  have hpin4 : Pin8 σ3.mem (((vsp - 64#64) + sign_extend (m := 64) (0x010#12)).toNat) v20 := by
    rw [ha48, hmem3, hmem2, hmem1]; exact hsave_s4
  obtain ⟨σ4, i4, hstp4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000e9a8_sr σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 (vsp - 64#64) _ _ _ _ _ _ _ _
      hG3 hpc3 hmi3 hp3.2.2.2.1 hload3 rfl
      (by rw [ha48]; omega) (by rw [ha48]; omega) (Or.inr (by rw [ha48]; omega))
      (by rw [ha48]; omega)
      hpin4.1 hpin4.2.1 hpin4.2.2.1 hpin4.2.2.2.1 hpin4.2.2.2.2.1 hpin4.2.2.2.2.2.1
      hpin4.2.2.2.2.2.2.1 hpin4.2.2.2.2.2.2.2 hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000e9ac#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x8000e9a8#64) 4 = (0x8000e9ac#64 : BitVec 64) from by decide] at this
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  -- L4: [x20, x19, x18, x8, x2, x9]
  have hp4 := pins_cons Register.x20 v20 hx20_4 (pins_alu hobs4 (by rfl) hp3)
  have hload4 : __ssprint_rLoaded σ4.mem := hmem4 ▸ hload3
  -- === e9ac: ld s5,8(sp)  (s5 := v21) ===
  have hpin5 : Pin8 σ4.mem (((vsp - 64#64) + sign_extend (m := 64) (0x008#12)).toNat) v21 := by
    rw [ha56, hmem4, hmem3, hmem2, hmem1]; exact hsave_s5
  obtain ⟨σ5, i5, hstp5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000e9ac_sr σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 (vsp - 64#64) _ _ _ _ _ _ _ _
      hG4 hpc4 hmi4 hp4.2.2.2.2.1 hload4 rfl
      (by rw [ha56]; omega) (by rw [ha56]; omega) (Or.inr (by rw [ha56]; omega))
      (by rw [ha56]; omega)
      hpin5.1 hpin5.2.1 hpin5.2.2.1 hpin5.2.2.2.1 hpin5.2.2.2.2.1 hpin5.2.2.2.2.2.1
      hpin5.2.2.2.2.2.2.1 hpin5.2.2.2.2.2.2.2 hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000e9b0#64 : BitVec 64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000e9ac#64) 4 = (0x8000e9b0#64 : BitVec 64) from by decide] at this
  have hx21_5 : σ5.regs.get? Register.x21 = some v21 := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  -- L5: [x21, x20, x19, x18, x8, x2, x9]
  have hp5 := pins_cons Register.x21 v21 hx21_5 (pins_alu hobs5 (by rfl) hp4)
  have hload5 : __ssprint_rLoaded σ5.mem := hmem5 ▸ hload4
  -- === e9b0: ld ra,56(sp)  (ra := r) ===
  have hpin6 : Pin8 σ5.mem (((vsp - 64#64) + sign_extend (m := 64) (0x038#12)).toNat) r := by
    rw [ha8, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hsave_ra
  obtain ⟨σ6, i6, hstp6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000e9b0_sr σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5 (vsp - 64#64) _ _ _ _ _ _ _ _
      hG5 hpc5 hmi5 hp5.2.2.2.2.2.1 hload5 rfl
      (by rw [ha8]; omega) (by rw [ha8]; omega) (Or.inr (by rw [ha8]; omega))
      (by rw [ha8]; omega)
      hpin6.1 hpin6.2.1 hpin6.2.2.1 hpin6.2.2.2.1 hpin6.2.2.2.2.1 hpin6.2.2.2.2.2.1
      hpin6.2.2.2.2.2.2.1 hpin6.2.2.2.2.2.2.2 hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000e9b4#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000e9b0#64) 4 = (0x8000e9b4#64 : BitVec 64) from by decide] at this
  have hx1_6 : σ6.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- L6: [x1, x21, x20, x19, x18, x8, x2, x9]
  have hp6 := pins_cons Register.x1 r hx1_6 (pins_alu hobs6 (by rfl) hp5)
  have hload6 : __ssprint_rLoaded σ6.mem := hmem6 ▸ hload5
  have hm6 : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  -- === e9b4: sd zero,16(s1)  (resid := 0) ===
  obtain ⟨σ7, i7, hstp7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000e9b4_sr σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi6 q
      hG6 hpc6 hmi6 hp6.2.2.2.2.2.2.2.1 hload6 rfl
      (by rw [hq16]; omega) (by rw [hq16]; omega) (by rw [hq16]; omega)
      (by rw [hq16]; omega) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x8000e9b8#64 : BitVec 64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x8000e9b4#64) 4 = (0x8000e9b8#64 : BitVec 64) from by decide] at this
  have hm7 : σ7.mem = writeMap8 c.σ.mem (q.toNat + 16) (sdData_val (0#64)) := by
    rw [hmem7, mem_afterNextPC, hm6, hq16]
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hload7 : __ssprint_rLoaded σ7.mem := by
    rw [hm7]; exact ssprint_writeMap8_ss _ _ _ (by omega) hload
  -- === e9b8: sw zero,8(s1)  (count := 0) ===
  obtain ⟨σ8, i8, hstp8, hi8, hG8, hmem8, hobs8⟩ :=
    site_8000e9b8_sr σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi7 q
      hG7 hpc7 hmi7 hp7.2.2.2.2.2.2.2.1 hload7 rfl
      (by rw [hq8]; omega) (by rw [hq8]; omega) (by rw [hq8]; omega)
      (by rw [hq8]; omega) hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000e9bc#64 : BitVec 64) := by
    have := obs_store_pc hobs8
    rwa [show BitVec.addInt (0x8000e9b8#64) 4 = (0x8000e9bc#64 : BitVec 64) from by decide] at this
  have hm8 : σ8.mem = writeMap4 (writeMap8 c.σ.mem (q.toNat + 16) (sdData_val (0#64)))
      (q.toNat + 8) (0#32) := by
    rw [hmem8, mem_afterNextPC, hm7, hq8, swData_zero_sr']
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hp8 := pins_store hobs8 (by rfl) hp7
  have hload8 : __ssprint_rLoaded σ8.mem := by
    rw [hm8]
    exact ssprint_writeMap4_ss _ _ _ (by omega)
      (ssprint_writeMap8_ss _ _ _ (by omega) hload)
  -- === e9bc: li a0,0 ===
  obtain ⟨σ9, i9, hstp9, hi9, hG9, hmem9, hobs9⟩ :=
    site_8000e9bc_sr σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi8
      hG8 hpc8 hmi8 hload8 rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000e9c0#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000e9bc#64) 4 = (0x8000e9c0#64 : BitVec 64) from by decide] at this
  have hx10_9 : σ9.regs.get? Register.x10 = some (0#64) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add (0#64)] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  -- L9: [x10, x1, x21, x20, x19, x18, x8, x2, x9]
  have hp9 := pins_cons Register.x10 (0#64) hx10_9 (pins_alu hobs9 (by rfl) hp8)
  have hload9 : __ssprint_rLoaded σ9.mem := hmem9 ▸ hload8
  -- === e9c0: ld s1,40(sp)  (s1 := v9) ===
  have hpin10 : Pin8 σ9.mem (((vsp - 64#64) + sign_extend (m := 64) (0x028#12)).toNat) v9 := by
    rw [ha24, hmem9, hm8]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]) hsave_s1
  obtain ⟨σ10, i10, hstp10, hi10, hG10, hmem10, hobs10⟩ :=
    site_8000e9c0_sr σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi9
      (vsp - 64#64) _ _ _ _ _ _ _ _
      hG9 hpc9 hmi9 hp9.2.2.2.2.2.2.2.1 hload9 rfl
      (by rw [ha24]; omega) (by rw [ha24]; omega) (Or.inr (by rw [ha24]; omega))
      (by rw [ha24]; omega)
      hpin10.1 hpin10.2.1 hpin10.2.2.1 hpin10.2.2.2.1 hpin10.2.2.2.2.1 hpin10.2.2.2.2.2.1
      hpin10.2.2.2.2.2.2.1 hpin10.2.2.2.2.2.2.2 hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000e9c4#64 : BitVec 64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x8000e9c0#64) 4 = (0x8000e9c4#64 : BitVec 64) from by decide] at this
  have hx9_10 : σ10.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  -- L10: [x9, x10, x1, x21, x20, x19, x18, x8, x2]
  have hp10 := pins_cons Register.x9 v9 hx9_10 (pins_alu hobs10 (by rfl) (pins_drop9 hp9))
  have hload10 : __ssprint_rLoaded σ10.mem := hmem10 ▸ hload9
  -- === e9c4: addi sp,sp,64  (sp := vsp) ===
  obtain ⟨σ11, i11, hstp11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000e9c4_sr σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi10
      (vsp - 64#64)
      hG10 hpc10 hmi10 hp10.2.2.2.2.2.2.2.2.1 hload10 rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000e9c8#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x8000e9c4#64) 4 = (0x8000e9c8#64 : BitVec 64) from by decide] at this
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_restore64 vsp] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  -- L11: [x2, x9, x10, x1, x21, x20, x19, x18, x8]
  have hp11 := pins_cons Register.x2 vsp hx2_11 (pins_alu hobs11 (by rfl) (pins_drop9 hp10))
  have hload11 : __ssprint_rLoaded σ11.mem := hmem11 ▸ hload10
  -- === e9c8: ret ===
  obtain ⟨σ12, i12, hstp12, hi12, hG12, hmem12, hobs12⟩ :=
    site_8000e9c8_sr σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ vmi11 r
      hG11 hpc11 hmi11 hp11.2.2.2.1 hload11 rfl
      (by rw [ret_tgt r halign]; exact halign) hi11
  have hpcF : σ12.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs12, ret_tgt r halign]
  have hp12 := pins_jr hobs12 (by rfl) hp11
  have hmF : σ12.mem = writeMap4 (writeMap8 c.σ.mem (q.toNat + 16) (sdData_val (0#64)))
      (q.toNat + 8) (0#32) := by
    rw [hmem12, hmem11, hmem10, hmem9, hm8]
  -- assemble the postcondition
  refine ⟨⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((((((((Steps.single hstp1).trans (Steps.single hstp2)).trans
      (Steps.single hstp3)).trans (Steps.single hstp4)).trans (Steps.single hstp5)).trans
      (Steps.single hstp6)).trans (Steps.single hstp7)).trans (Steps.single hstp8)).trans
      (Steps.single hstp9)).trans (Steps.single hstp10)).trans (Steps.single hstp11)).trans
      (Steps.single hstp12),
    hG12, hpcF, hp12.2.2.1, hp12.2.2.2.1, hp12.1, hp12.2.2.2.2.2.2.2.2.1, hp12.2.1,
    hp12.2.2.2.2.2.2.2.1, hp12.2.2.2.2.2.2.1, hp12.2.2.2.2.2.1, hp12.2.2.2.2.1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi12, ?_⟩
  · -- copied1
    intro k hk
    rw [hmF, getElem_writeMap4_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact hcopied1 k hk
  · -- copied2
    intro k hk
    rw [hmF, getElem_writeMap4_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact hcopied2 k hk
  · -- cursor
    rw [hmF]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]) hcursorF
  · -- capacity
    rw [hmF]
    exact Pin4_frame (fun k hk1 hk2 => by
      rw [getElem_writeMap4_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]) hcapF
  · -- resid cleared
    rw [hmF]
    exact Pin8_frame (fun k hk1 hk2 =>
      getElem_writeMap4_disjoint _ _ _ _ (by omega)) (Pin8_writeMap8 _ _ _)
  · -- count cleared
    rw [hmF]
    exact Pin4_writeMap4 _ _ _
  · -- memory frame
    intro a h1 h2 h3 h4 h5 h6
    rw [hmF, getElem_writeMap4_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact hmframeS a h1 h2 h3 h4 h5 h6
  · -- register ghost frame
    intro R hR
    have hmv := hR.sp.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.sp.x8 hmv
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.x18 hmv
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.x19 hmv
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_alu_mv hobs4 R hR.x20 hmv
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_alu_mv hobs5 R hR.x21 hmv
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_mv hobs6 R hR.sp.x1 hmv
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_store_mv hobs7 R hmv
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_store_mv hobs8 R hmv
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_mv hobs9 R hR.sp.x10 hmv
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_mv hobs10 R hR.sp.x9 hmv
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.sp.x2 hmv
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_jr_mv hobs12 R hmv
    rw [e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
    exact hgframe R hR

/-! ## The composed 2-iovec flush spec -/

/-- **`__ssprint_r` 2-iovec flush** (`0x8000e908 → ret`), composed twice with
the verified `__ssputs_r` fast path: flushes the sign iovec `(s1, n1, bs1)`
and the digit iovec `(s2, n2, bs2)` into the sink cursor buffer at `d`,
advances the cursor to `d + (n1+n2)`, decrements the capacity word twice,
clears the `q` struct's resid/count, returns `0` with all callee-saves and
`sp` restored and a pointwise frame outside the six written windows. -/
theorem ssprint_iov2_spec (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 n2 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 bs2 : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (PreSr g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2)
      (ssprint_iov2_post g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0
        bs1 bs2) :=
  ((tr_ssprint_entry g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0
      bs1 bs2).seq
    ((tr_ssprint_iter1 g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0
        bs1 bs2).seq
      (tr_ssprint_iter2 g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0
        bs1 bs2))).seq
    (tr_ssprint_tail g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0
      bs1 bs2 halign)

end Vsa.Sim
