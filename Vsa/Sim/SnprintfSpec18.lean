import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.SnprintfSpec17
import Vsa.Sim.StrcpySpec
import Vsa.Sim.Code.Memmove
import Vsa.Sim.DecodeTable.Batch07Part26
import Vsa.Sim.DecodeTable.Batch07Part05
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch06Part32
import Vsa.Sim.DecodeTable.Batch06Part15
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch09Part23
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part14
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec18` : `memmove` fast path (`_mv`) — forward byte loop

The `__ssputs_r` fast path (`0x8001438c`, next file) calls newlib `memmove`
(`0x800069c4 <memmove>`) to copy an iovec into the string sink's cursor buffer.
For the `%lld` flush the arguments are always **disjoint** regions (`dst` in the
caller's destination buffer, `src` on the `svfprintf` C stack) with `1 ≤ n ≤ 31`
(a sign byte or ≤ 20 digits), so the executed path is:

```
  69c4: bgeu a1,a0,69f0     taken when src ≥ dst        ┐ dispatch
  69c8: add  a5,a1,a2       a5 := src + n               │ (disjoint ⇒ one of
  69cc: bgeu a0,a5,69f0     taken when dst ≥ src + n     ┘  the two fires)
  69f0: li   a5,31
  69f4: bltu a5,a2,6a24     NOT taken (n ≤ 31 ⇒ byte path)
  69f8: mv   a5,a0           a5 := dst
  69fc: addi a3,a2,-1        a3 := n - 1
  6a00: beqz a2,6ae0         NOT taken (1 ≤ n)
  6a04: addi a3,a3,1         a3 := n
  6a08: add  a3,a5,a3        a3 := dst + n (end pointer)
  6a0c: lbu  a4,0(a1)        ┐ loop body (5 instrs, back-edge 6a1c → 6a0c
  6a10: addi a5,a5,1         │ while a5 ≠ a3): copy one byte
  6a14: addi a1,a1,1         │ src → dst
  6a18: sb   a4,-1(a5)       ┘
  6a1c: bne  a5,a3,6a0c
  6a20: ret
```

`memmove_fwd_spec` is the total-correctness segment for this path: from the
`memmove` entry with `dst/src/n` in place, regions disjoint (`dst+n ≤ src` or
`src+n ≤ dst`, unsigned), `1 ≤ n ≤ 31`, and the source bytes `bs` pinned in
`m0`, it returns to `ra = r` with

* `[dst, dst+n)` holding exactly the source bytes (`∀ i < n`,
  `mem[dst+i]? = some (bs i)`), and
* every other address still reading `m0` (frame).

Memory bookkeeping reuses the strcpy machinery (`CpyRegions`/`CpyInv`/
`cpyinv_store`, with `len := n-1` so the written window is exactly
`[dst, dst+n)`); the `MemmoveLoaded` code pins survive byte inserts above
`0x80006b00` (the function spans `[0x800069c4, 0x80006aec)`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemmoveLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Guard / pointer bridges -/

/-- Unsigned `≥` introduction: `dst.toNat ≤ src.toNat ⇒ (src ≥ᵤ dst) = true`. -/
theorem bgeu_of_le (a b : BitVec 64) (h : b.toNat ≤ a.toNat) : zopz0zKzJ_u a b = true := by
  unfold zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_true (Int.ofNat_le.mpr h)

/-- Unsigned `≥` refutation: `a.toNat < b.toNat ⇒ (a ≥ᵤ b) = false`. -/
theorem bgeu_false_of_lt (a b : BitVec 64) (h : a.toNat < b.toNat) : zopz0zKzJ_u a b = false := by
  unfold zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (by intro hc; exact absurd (Int.ofNat_le.mp hc) (by omega))

/-- Unsigned `<` refutation: `b.toNat ≤ a.toNat ⇒ (a <ᵤ b) = false`. -/
theorem bltu_false_of_ge (a b : BitVec 64) (h : b.toNat ≤ a.toNat) : zopz0zI_u a b = false := by
  unfold zopz0zI_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (by intro hc; exact absurd (Int.ofNat_lt.mp hc) (by omega))

theorem sext1_toNat : (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 := by decide

theorem bne_not_beq (a b : BitVec 64) : (a != b) = !(a == b) := rfl

theorem beq_false_of_toNat_ne (a b : BitVec 64) (h : a.toNat ≠ b.toNat) : (a == b) = false := by
  cases hb : (a == b) with
  | false => rfl
  | true => rw [beq_iff_eq] at hb; exact absurd (congrArg BitVec.toNat hb) h

theorem bne_true_of_toNat_ne (a b : BitVec 64) (h : a.toNat ≠ b.toNat) : (a != b) = true := by
  rw [bne_not_beq, beq_false_of_toNat_ne a b h]; rfl

/-- `(base + k) + 1 = base + (k+1)` as BitVecs under no-wrap. -/
theorem ptrS (base : BitVec 64) (k : Nat) (h : base.toNat + k + 1 < 2^64) :
    (base + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x001#12)
      = base + BitVec.ofNat 64 (k+1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [sext1_toNat]
  omega

/-- `(base + (k+1)) - 1 = base + k` as BitVecs (the `sb a4,-1(a5)` EA).
Routed through `sub1_bv_sn5`: the naive `toNat`+`omega` proof term blows the
kernel recursion limit on the `2^64 - 1` literal. -/
theorem ptrSB (base : BitVec 64) (k : Nat) (h : base.toNat + k + 1 < 2^64) :
    (base + BitVec.ofNat 64 (k+1)) + sign_extend (m := 64) (0xfff#12)
      = base + BitVec.ofNat 64 k := by
  have h1 : (base + BitVec.ofNat 64 (k+1)).toNat = base.toNat + (k+1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [sub1_bv_sn5 _ (by rw [h1]; omega), h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_ofNat_zero (v : BitVec 64) : v + BitVec.ofNat 64 0 = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `n - 1 + 1 = n` for the `a3` bookkeeping (`1 ≤ n`, `n` small). -/
theorem dec1_back (n : Nat) (hn : 1 ≤ n) (hlt : n < 2^63) :
    (BitVec.ofNat 64 (n-1) + sign_extend (m := 64) (0x001#12)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [sext1_toNat]
  omega

/-- `(ofNat n) - 1 = ofNat (n-1)` for the `addi a3,a2,-1` (via `sub1_bv_sn5`,
same kernel-recursion workaround as `ptrSB`). -/
theorem dec1_fwd (n : Nat) (hn : 1 ≤ n) (hlt : n < 2^63) :
    (BitVec.ofNat 64 n + sign_extend (m := 64) (0xfff#12)) = BitVec.ofNat 64 (n-1) := by
  have h1 : (BitVec.ofNat 64 n : BitVec 64).toNat = n :=
    BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (by omega)
  rw [sub1_bv_sn5 _ (by rw [h1]; omega), h1]

/-- The loop back-edge target: `0x80006a1c + sext(0x1ff0#13) = 0x80006a0c`. -/
theorem bne_target_mv :
    (0x80006a1c#64 + sign_extend (m := 64) (0x1ff0#13)) = (0x80006a0c#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem li31_val : ((0#64) + sign_extend (m := 64) (0x01f#12) : BitVec 64) = (0x1f#64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## `MemmoveLoaded` survival above the code region -/

/-- Read-over-write for the memmove code region: writes land above `0x80006b00`
(the function spans `[0x800069c4, 0x80006aec)`). -/
theorem getElem?_insert_aboveB_mv (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80006b00 ≤ k) (a : Nat) (ha : a < 0x80006b00) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem memmove_insert_mv (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80006b00 ≤ k) (h : MemmoveLoaded mem) : MemmoveLoaded (mem.insert k v) := by
  unfold MemmoveLoaded Vsa.Sim.Code.memmoveChunk0 Vsa.Sim.Code.memmoveChunk1
    Vsa.Sim.Code.memmoveChunk2 Vsa.Sim.Code.memmoveChunk3 Vsa.Sim.Code.memmoveChunk4 at h ⊢
  simp (disch := omega) only [getElem?_insert_aboveB_mv mem k v hk]
  exact h

/-! ## Per-site observational steps -/

/-- 0x800069c4: `bgeu a1,a0 → 0x800069f0` (TAKEN: `src ≥ᵤ dst`). -/
theorem site_69c4_taken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsrc vdst : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vsrc)
    (hx10 : σ.regs.get? Register.x10 = some vdst)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069c4#64 : BitVec 64))
    (hv : zopz0zKzJ_u vsrc vdst = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x002c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069c4 hmem
  refine stepObs_branch_taken σ i u (0x800069c4#64) vminstret (0x002c#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) bop.BGEU (0x02a5f663#32)
    (0x63#8) (0xf6#8) (0xa5#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02a5f663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    ?_ hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi
  exact execute_btype_bgeu_taken (0x002c#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
    vsrc vdst (0x800069c4#64) initMisa (afterNextPC (afterPrelude σ) (0x800069c4#64))
    (rX_bits_x11 _ vsrc
      (by rw [get?_afterNextPC σ (0x800069c4#64) _ (by decide) (by decide)]; exact hx11))
    (rX_bits_x10 _ vdst
      (by rw [get?_afterNextPC σ (0x800069c4#64) _ (by decide) (by decide)]; exact hx10))
    (by rw [get?_afterNextPC σ (0x800069c4#64) _ (by decide) (by decide)]; exact hpc)
    (by rw [get?_afterNextPC σ (0x800069c4#64) _ (by decide) (by decide)]; exact hG.misa)
    (by decide) hv

/-- 0x800069c4: `bgeu a1,a0 → 0x800069c8` (NOT taken: `src <ᵤ dst`). -/
theorem site_69c4_nottaken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsrc vdst : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vsrc)
    (hx10 : σ.regs.get? Register.x10 = some vdst)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069c4#64 : BitVec 64))
    (hv : zopz0zKzJ_u vsrc vdst = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069c4 hmem
  exact stepObs_branch_nottaken σ i u (0x800069c4#64) vminstret (0x002c#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) bop.BGEU (0x02a5f663#32)
    (0x63#8) (0xf6#8) (0xa5#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02a5f663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bgeu_nottaken (0x002c#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
      vsrc vdst (afterNextPC (afterPrelude σ) (0x800069c4#64))
      (rX_bits_x11 _ vsrc
        (by rw [get?_afterNextPC σ (0x800069c4#64) _ (by decide) (by decide)]; exact hx11))
      (rX_bits_x10 _ vdst
        (by rw [get?_afterNextPC σ (0x800069c4#64) _ (by decide) (by decide)]; exact hx10))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800069c8: `add a5,a1,a2` (`a5 := src + n`). -/
theorem site_69c8 (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vsrc vn : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vsrc)
    (hx12 : σ.regs.get? Register.x12 = some vn)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069c8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (vsrc + vn)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069c8 hmem
  exact stepObs_alu σ i u (0x800069c8#64) vminstret (0x00c587b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (vsrc + vn)
    (0xb3#8) (0x87#8) (0xc5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c587b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      vsrc vn (afterNextPC (afterPrelude σ) (0x800069c8#64))
      (sigma3_alu σ (0x800069c8#64) Register.x15 (vsrc + vn))
      (rX_bits_x11 _ vsrc
        (by rw [get?_afterNextPC σ (0x800069c8#64) _ (by decide) (by decide)]; exact hx11))
      (rX_bits_x12 _ vn
        (by rw [get?_afterNextPC σ (0x800069c8#64) _ (by decide) (by decide)]; exact hx12))
      (wX_bits_x15 _ (vsrc + vn)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800069cc: `bgeu a0,a5 → 0x800069f0` (TAKEN: `dst ≥ᵤ src + n`). -/
theorem site_69cc_taken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vdst vsrcn : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vdst)
    (hx15 : σ.regs.get? Register.x15 = some vsrcn)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069cc#64 : BitVec 64))
    (hv : zopz0zKzJ_u vdst vsrcn = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0024#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069cc hmem
  refine stepObs_branch_taken σ i u (0x800069cc#64) vminstret (0x0024#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5) bop.BGEU (0x02f57263#32)
    (0x63#8) (0x72#8) (0xf5#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02f57263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    ?_ hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi
  exact execute_btype_bgeu_taken (0x0024#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5)
    vdst vsrcn (0x800069cc#64) initMisa (afterNextPC (afterPrelude σ) (0x800069cc#64))
    (rX_bits_x10 _ vdst
      (by rw [get?_afterNextPC σ (0x800069cc#64) _ (by decide) (by decide)]; exact hx10))
    (rX_bits_x15 _ vsrcn
      (by rw [get?_afterNextPC σ (0x800069cc#64) _ (by decide) (by decide)]; exact hx15))
    (by rw [get?_afterNextPC σ (0x800069cc#64) _ (by decide) (by decide)]; exact hpc)
    (by rw [get?_afterNextPC σ (0x800069cc#64) _ (by decide) (by decide)]; exact hG.misa)
    (by decide) hv

/-- 0x800069f0: `li a5,31`. -/
theorem site_69f0 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069f0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        ((0#64) + sign_extend (m := 64) (0x01f#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069f0 hmem
  exact stepObs_alu σ i u (0x800069f0#64) vminstret (0x01f00793#32)
    (instruction.ITYPE (0x01f#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x01f#12))
    (0x93#8) (0x07#8) (0xf0#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01f00793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x01f#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x800069f0#64))
      (sigma3_alu σ (0x800069f0#64) Register.x15 ((0#64) + sign_extend (m := 64) (0x01f#12)))
      (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x01f#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800069f4: `bltu a5,a2 → 0x800069f8` (NOT taken: `n ≤ᵤ 31`). -/
theorem site_69f4_nottaken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vn : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some (0x1f#64))
    (hx12 : σ.regs.get? Register.x12 = some vn)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069f4#64 : BitVec 64))
    (hv : zopz0zI_u (0x1f#64) vn = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069f4 hmem
  exact stepObs_branch_nottaken σ i u (0x800069f4#64) vminstret (0x0030#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) bop.BLTU (0x02c7e863#32)
    (0x63#8) (0xe8#8) (0xc7#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02c7e863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bltu_nottaken (0x0030#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5)
      (0x1f#64) vn (afterNextPC (afterPrelude σ) (0x800069f4#64))
      (rX_bits_x15 _ (0x1f#64)
        (by rw [get?_afterNextPC σ (0x800069f4#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x12 _ vn
        (by rw [get?_afterNextPC σ (0x800069f4#64) _ (by decide) (by decide)]; exact hx12))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800069f8: `mv a5,a0` (`a5 := dst`). -/
theorem site_69f8 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vdst : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vdst)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069f8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (vdst + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069f8 hmem
  exact stepObs_alu σ i u (0x800069f8#64) vminstret (0x00050793#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (vdst + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x07#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00050793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5) vdst
      (afterNextPC (afterPrelude σ) (0x800069f8#64))
      (sigma3_alu σ (0x800069f8#64) Register.x15 (vdst + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ vdst
        (by rw [get?_afterNextPC σ (0x800069f8#64) _ (by decide) (by decide)]; exact hx10))
      (wX_bits_x15 _ (vdst + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800069fc: `addi a3,a2,-1` (`a3 := n − 1`). -/
theorem site_69fc (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vn vnm1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vn)
    (hval : vn + sign_extend (m := 64) (0xfff#12) = vnm1)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x800069fc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13
        (vn + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_800069fc hmem
  exact stepObs_alu σ i u (0x800069fc#64) vminstret (0xfff60693#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (vn + sign_extend (m := 64) (0xfff#12))
    (0x93#8) (0x06#8) (0xf6#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fff60693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) vn
      (afterNextPC (afterPrelude σ) (0x800069fc#64))
      (sigma3_alu σ (0x800069fc#64) Register.x13 (vn + sign_extend (m := 64) (0xfff#12)))
      (rX_bits_x12 _ vn
        (by rw [get?_afterNextPC σ (0x800069fc#64) _ (by decide) (by decide)]; exact hx12))
      (wX_bits_x13 _ (vn + sign_extend (m := 64) (0xfff#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a00: `beqz a2 → 0x80006a04` (NOT taken: `n ≠ 0`). -/
theorem site_6a00_nottaken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vn : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vn)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a00#64 : BitVec 64))
    (hv : (vn == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a00 hmem
  exact stepObs_branch_nottaken σ i u (0x80006a00#64) vminstret (0x00e0#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BEQ (0x0e060063#32)
    (0x63#8) (0x00#8) (0x06#8) (0x0e#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0e060063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x00e0#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
      vn (0#64) (afterNextPC (afterPrelude σ) (0x80006a00#64))
      (rX_bits_x12 _ vn
        (by rw [get?_afterNextPC σ (0x80006a00#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a04: `addi a3,a3,1`. -/
theorem site_6a04 (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vin vout : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some vin)
    (hval : vin + sign_extend (m := 64) (0x001#12) = vout)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a04#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13
        (vin + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a04 hmem
  exact stepObs_alu σ i u (0x80006a04#64) vminstret (0x00168693#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (vin + sign_extend (m := 64) (0x001#12))
    (0x93#8) (0x86#8) (0x16#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00168693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5) vin
      (afterNextPC (afterPrelude σ) (0x80006a04#64))
      (sigma3_alu σ (0x80006a04#64) Register.x13 (vin + sign_extend (m := 64) (0x001#12)))
      (rX_bits_x13 _ vin
        (by rw [get?_afterNextPC σ (0x80006a04#64) _ (by decide) (by decide)]; exact hx13))
      (wX_bits_x13 _ (vin + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a08: `add a3,a5,a3` (`a3 := a5 + a3`). -/
theorem site_6a08 (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v5 v3 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v5)
    (hx13 : σ.regs.get? Register.x13 = some v3)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a08#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (v5 + v3)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a08 hmem
  exact stepObs_alu σ i u (0x80006a08#64) vminstret (0x00d786b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, rop.ADD))
    Register.x13 (v5 + v3)
    (0xb3#8) (0x86#8) (0xd7#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00d786b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5)
      v5 v3 (afterNextPC (afterPrelude σ) (0x80006a08#64))
      (sigma3_alu σ (0x80006a08#64) Register.x13 (v5 + v3))
      (rX_bits_x15 _ v5
        (by rw [get?_afterNextPC σ (0x80006a08#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x13 _ v3
        (by rw [get?_afterNextPC σ (0x80006a08#64) _ (by decide) (by decide)]; exact hx13))
      (wX_bits_x13 _ (v5 + v3)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a0c: `lbu a4,0(a1)` (`a4 := mem[src + k]`). -/
theorem site_6a0c (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret va1 : BitVec 64) (b : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some va1)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a0c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ va1.toNat)
    (hhi : va1.toNat + 1 ≤ 0x100000000)
    (hhtif : va1.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ va1.toNat)
    (hb : σ.mem[va1.toNat]? = some b) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (zero_extend (m := 64) b)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a0c hmem
  have hEA : (va1 + sign_extend (m := 64) (0x000#12)) = va1 := sext0_add va1
  exact stepObs_alu σ i u (0x80006a0c#64) vminstret (0x0005c703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, true, 1))
    Register.x14 (zero_extend (m := 64) b)
    (0x03#8) (0xc7#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0005c703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006a0c#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5)
      va1 b (sigma3_alu σ (0x80006a0c#64) Register.x14 (zero_extend (m := 64) b)) hG
      (rX_bits_x11 _ va1
        (by rw [get?_afterNextPC σ (0x80006a0c#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (zero_extend (m := 64) b))
      (by rw [hEA]; simpa using hlo) (by rw [hEA]; simpa using hhi)
      (by rw [hEA]; simpa using hhtif) (by rw [hEA]; exact hb))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a10: `addi a5,a5,1`. -/
theorem site_6a10 (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vin vout : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some vin)
    (hval : vin + sign_extend (m := 64) (0x001#12) = vout)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a10#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (vin + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a10 hmem
  exact stepObs_alu σ i u (0x80006a10#64) vminstret (0x00178793#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (vin + sign_extend (m := 64) (0x001#12))
    (0x93#8) (0x87#8) (0x17#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00178793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) vin
      (afterNextPC (afterPrelude σ) (0x80006a10#64))
      (sigma3_alu σ (0x80006a10#64) Register.x15 (vin + sign_extend (m := 64) (0x001#12)))
      (rX_bits_x15 _ vin
        (by rw [get?_afterNextPC σ (0x80006a10#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x15 _ (vin + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a14: `addi a1,a1,1`. -/
theorem site_6a14 (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vin vout : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vin)
    (hval : vin + sign_extend (m := 64) (0x001#12) = vout)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a14#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11
        (vin + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a14 hmem
  exact stepObs_alu σ i u (0x80006a14#64) vminstret (0x00158593#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (vin + sign_extend (m := 64) (0x001#12))
    (0x93#8) (0x85#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00158593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) vin
      (afterNextPC (afterPrelude σ) (0x80006a14#64))
      (sigma3_alu σ (0x80006a14#64) Register.x11 (vin + sign_extend (m := 64) (0x001#12)))
      (rX_bits_x11 _ vin
        (by rw [get?_afterNextPC σ (0x80006a14#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x11 _ (vin + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a18: `sb a4,-1(a5)` (store the byte at `dst + k`). -/
theorem site_6a18 (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret va5 : BitVec 64) (b : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some va5)
    (hx14 : σ.regs.get? Register.x14 = some (zero_extend (m := 64) b))
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a18#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (va5 + sign_extend (m := 64) (0xfff#12)).toNat)
    (hhiram : (va5 + sign_extend (m := 64) (0xfff#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (va5 + sign_extend (m := 64) (0xfff#12)).toNat)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006a18#64)).mem.insert
        (va5 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 (zero_extend (m := 64) b))) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        ((afterNextPC (afterPrelude σ) (0x80006a18#64)).mem.insert
          (va5 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 (zero_extend (m := 64) b)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a18 hmem
  exact stepObs_store σ i u (0x80006a18#64) vminstret (0xfee78fa3#32)
    (instruction.STORE (0xfff#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006a18#64)).mem.insert
      (va5 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 (zero_extend (m := 64) b)))
    (0xa3#8) (0x8f#8) (0xe7#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fee78fa3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006a18#64) (0xfff#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
      va5 (zero_extend (m := 64) b) hG
      (rX_bits_x15 _ va5
        (by rw [get?_afterNextPC σ (0x80006a18#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x14 _ (zero_extend (m := 64) b)
        (by rw [get?_afterNextPC σ (0x80006a18#64) _ (by decide) (by decide)]; exact hx14))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a1c: `bne a5,a3 → 0x80006a0c` (TAKEN: `a5 ≠ a3`). -/
theorem site_6a1c_taken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v5 v3 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v5)
    (hx13 : σ.regs.get? Register.x13 = some v3)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a1c#64 : BitVec 64))
    (hv : (v5 != v3) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a1c hmem
  exact stepObs_branch_taken σ i u (0x80006a1c#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) bop.BNE (0xfed798e3#32)
    (0xe3#8) (0x98#8) (0xd7#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fed798e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_taken (0x1ff0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5)
      v5 v3 (0x80006a1c#64) initMisa (afterNextPC (afterPrelude σ) (0x80006a1c#64))
      (rX_bits_x15 _ v5
        (by rw [get?_afterNextPC σ (0x80006a1c#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x13 _ v3
        (by rw [get?_afterNextPC σ (0x80006a1c#64) _ (by decide) (by decide)]; exact hx13))
      (by rw [get?_afterNextPC σ (0x80006a1c#64) _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ (0x80006a1c#64) _ (by decide) (by decide)]; exact hG.misa)
      (by rw [bne_target_mv]; decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a1c: `bne a5,a3 → 0x80006a20` (NOT taken: `a5 = a3`). -/
theorem site_6a1c_nottaken (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret v5 v3 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v5)
    (hx13 : σ.regs.get? Register.x13 = some v3)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a1c#64 : BitVec 64))
    (hv : (v5 != v3) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a1c hmem
  exact stepObs_branch_nottaken σ i u (0x80006a1c#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) bop.BNE (0xfed798e3#32)
    (0xe3#8) (0x98#8) (0xd7#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fed798e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_nottaken (0x1ff0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5)
      v5 v3 (afterNextPC (afterPrelude σ) (0x80006a1c#64))
      (rX_bits_x15 _ v5
        (by rw [get?_afterNextPC σ (0x80006a1c#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x13 _ v3
        (by rw [get?_afterNextPC σ (0x80006a1c#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006a20: `ret`. -/
theorem site_6a20 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vr : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vr)
    (hmem : MemmoveLoaded σ.mem) (hpcv : pc = (0x80006a20#64 : BitVec 64))
    (halign : vr.toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (Sail.BitVec.update (vr + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memmove_at_80006a20 hmem
  have htgt : (Sail.BitVec.update (vr + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt vr halign]; exact halign
  exact stepObs_jr σ i u (0x80006a20#64) vminstret vr (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x1 _ vr
      (by rw [get?_afterNextPC σ (0x80006a20#64) _ (by decide) (by decide)]; exact hx1))
    htgt hi

/-! ## Region / no-wrap side conditions for the forward byte path

`MvRegions dst src n` bundles the disjointness / no-wrap facts for an `n`-byte
copy (`1 ≤ n ≤ 31` — the small-`n` byte path).  The written window is
`[dst, dst+n)`, the read window `[src, src+n)`; both in RAM above the HTIF
window (hence above the `memmove` code, `tohostAddr > 0x80006b00`). -/
structure MvRegions (dst src : BitVec 64) (n : Nat) : Prop where
  n1 : 1 ≤ n
  n31 : n ≤ 31
  dst_nowrap : dst.toNat + n < 2^64
  src_nowrap : src.toNat + n < 2^64
  disjoint : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat
  dst_lo : 0x80000000 ≤ dst.toNat
  dst_hi : dst.toNat + n ≤ 0x100000000
  src_lo : 0x80000000 ≤ src.toNat
  src_hi : src.toNat + n ≤ 0x100000000
  dst_win : tohostAddr + 16 ≤ dst.toNat
  src_win : tohostAddr + 16 ≤ src.toNat

/-- The source-window ghost: `bs` pins the `n` source bytes in `m0`. -/
def MvBytes (m0 : Std.ExtHashMap Nat (BitVec 8)) (src : BitVec 64) (n : Nat)
    (bs : Nat → BitVec 8) : Prop :=
  ∀ k, k < n → m0[(src.toNat + k)]? = some (bs k)

/-- `MvRegions` gives the `CpyInv`-shaped disjointness at `len := n-1`. -/
theorem mv_disjoint (dst src : BitVec 64) (n : Nat) (hreg : MvRegions dst src n) :
    dst.toNat + (n-1) + 1 ≤ src.toNat ∨ src.toNat + (n-1) + 1 ≤ dst.toNat := by
  have h1 := hreg.n1
  rcases hreg.disjoint with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## Blanket ghost-frame predicate (`NotWrittenMv`) + per-class helpers

The forward path writes GPRs `x11` (`a1`), `x13` (`a3`), `x14` (`a4`), `x15`
(`a5`).  `x10` (`a0 = dst`), `x12` (`a2 = n`) and `x1` (`ra`) are preserved. -/
abbrev NotWrittenMv (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenMv.x11 {R : Register} (h : NotWrittenMv R) : (Register.x11 == R) = false := h.1
theorem NotWrittenMv.x13 {R : Register} (h : NotWrittenMv R) : (Register.x13 == R) = false := h.2.1
theorem NotWrittenMv.x14 {R : Register} (h : NotWrittenMv R) : (Register.x14 == R) = false := h.2.2.1
theorem NotWrittenMv.x15 {R : Register} (h : NotWrittenMv R) : (Register.x15 == R) = false := h.2.2.2.1

theorem frame_alu_mv {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenMv R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frame_store_mv {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenMv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

theorem frame_btaken_mv {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenMv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frame_bnottaken_mv {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenMv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

theorem frame_jr_mv {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenMv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## Pointer/window bounds for iteration `i` -/

theorem mv_src_bounds (dst src : BitVec 64) (n : Nat) (hreg : MvRegions dst src n)
    (i : Nat) (hi : i < n) :
    (src + BitVec.ofNat 64 i).toNat = src.toNat + i ∧
    0x80000000 ≤ (src + BitVec.ofNat 64 i).toNat ∧
    (src + BitVec.ofNat 64 i).toNat + 1 ≤ 0x100000000 ∧
    ((src + BitVec.ofNat 64 i).toNat + 1 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (src + BitVec.ofNat 64 i).toNat) := by
  have htn : (src + BitVec.ofNat 64 i).toNat = src.toNat + i :=
    ptr_toNat src i (by have := hreg.src_nowrap; omega)
  have hlo := hreg.src_lo; have hhi := hreg.src_hi; have hwin := hreg.src_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, by rw [htn]; omega, by rw [htn]; omega, Or.inr (by rw [htn]; omega)⟩

theorem mv_dst_bounds (dst src : BitVec 64) (n : Nat) (hreg : MvRegions dst src n)
    (i : Nat) (hi : i < n) :
    0x80000000 ≤ ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat ∧
    ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat + 1 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat ∧
    ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat = dst.toNat + i := by
  have hsb : ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat
      = dst.toNat + i := by
    rw [sbAddr_succ_raw dst i]; exact ptr_toNat dst i (by have := hreg.dst_nowrap; omega)
  have hlo := hreg.dst_lo; have hhi := hreg.dst_hi; have hwin := hreg.dst_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by rw [hsb]; omega, by rw [hsb]; omega, by rw [hsb]; omega, hsb⟩

/-- The write key `dst.toNat + i` is above the `memmove` code (dst is above the
HTIF window, which sits above `0x80006b00`). -/
theorem mv_key_above (dst src : BitVec 64) (n : Nat) (hreg : MvRegions dst src n) (i : Nat) :
    0x80006b00 ≤ dst.toNat + i := by
  have := hreg.dst_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  omega

/-! ## The config-level state predicate at the loop head `0x80006a0c`

`StMv g i r dst src n m0 bs c` holds at byte-loop iteration `i` (`i < n`):
`a0 = dst`, `a1 = src+i`, `a3 = dst+n` (end pointer), `a5 = dst+i`, `x1 = r`,
`CpyInv` at `len := n-1` (window `[dst, dst+n)`). -/
structure StMv (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006a0c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 i)
  a3 : c.σ.regs.get? Register.x13 = some (dst + BitVec.ofNat 64 n)
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 i)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : MvRegions dst src n
  hbs : MvBytes m0 src n bs
  ilt : i < n
  cpyinv : CpyInv dst src (n-1) bs i m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenMv R → c.σ.regs.get? R = g R

/-- State at `0x80006a1c` (pre-`bne`) after body iteration `i`: pointers advanced
to `i+1`, prefix copied to `i+1`. -/
structure StMv1c (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006a1c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (i + 1))
  a3 : c.σ.regs.get? Register.x13 = some (dst + BitVec.ofNat 64 n)
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (i + 1))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : MvRegions dst src n
  hbs : MvBytes m0 src n bs
  ilt : i < n
  cpyinv : CpyInv dst src (n-1) bs (i + 1) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenMv R → c.σ.regs.get? R = g R

/-- The "done" configuration at `0x80006a20` (ret entry): full window copied. -/
structure StMvDone (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006a20#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : MvRegions dst src n
  cpyinv : CpyInv dst src (n-1) bs n m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenMv R → c.σ.regs.get? R = g R

/-! ## One loop body iteration (`0x80006a0c → 0x80006a1c`)

Chains `lbu a4,0(a1) → addi a5,a5,1 → addi a1,a1,1 → sb a4,-1(a5)`. -/
theorem iterMv (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (StMv g i r dst src n m0 bs) (StMv1c g i r dst src n m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha3, ha5, hra, ⟨vmi, hmi⟩, htick,
    hreg, hbs, hilt, hcinv, hframe⟩ := hSt
  obtain ⟨htn_src, hslo, hshi, hshtif⟩ := mv_src_bounds dst src n hreg i hilt
  obtain ⟨hdlo, hdhi, hdwin, hsbeq⟩ := mv_dst_bounds dst src n hreg i hilt
  -- the loaded byte is bs i (src_intact at index i, then the m0 pin)
  have hbyte : c.σ.mem[(src + BitVec.ofNat 64 i).toNat]? = some (bs i) := by
    rw [htn_src, hcinv.src_intact i (Nat.le_refl i) (by have := hreg.n1; omega)]
    exact hbs i hilt
  -- === 6a0c: lbu a4,0(a1) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_6a0c c.σ c.tick c.steps (0x80006a0c#64) vmi (src + BitVec.ofNat 64 i) (bs i)
      hgood hpc hmi ha1 hloaded rfl hslo hshi hshtif hbyte htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006a10#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80006a0c#64) 4 = (0x80006a10#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have ha5_1 := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha4_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 6a10: addi a5,a5,1 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_6a10 σ1 i1 (c.steps + 1) (0x80006a10#64) vmi1 (dst + BitVec.ofNat 64 i)
      (dst + BitVec.ofNat 64 (i + 1))
      hG1 hpc1 hmi1 ha5_1 (ptr_succ dst i) (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006a14#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80006a10#64) 4 = (0x80006a14#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (i + 1)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_succ dst i] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- === 6a14: addi a1,a1,1 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_6a14 σ2 i2 (c.steps + 1 + 1) (0x80006a14#64) vmi2 (src + BitVec.ofNat 64 i)
      (src + BitVec.ofNat 64 (i + 1))
      hG2 hpc2 hmi2 ha1_2 (ptr_succ src i) (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006a18#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80006a14#64) 4 = (0x80006a18#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha1_3 : σ3.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (i + 1)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_succ src i] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  -- === 6a18: sb a4,-1(a5) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_6a18 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006a18#64) vmi3
      (dst + BitVec.ofNat 64 (i + 1)) (bs i)
      hG3 hpc3 hmi3 ha5_3 ha4_3 (by rw [hmem3eq]; exact hloaded) rfl
      hdlo hdhi hdwin hi3
  have hstore_mem : σ4.mem = c.σ.mem.insert (dst.toNat + i) (bs i) := by
    rw [hmem4, mem_afterNextPC, hmem3eq, stData_zext, hsbeq]
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, ?_⟩
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006a1c#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80006a18#64) 4 = (0x80006a1c#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_store_other' hobs4 Register.x11 (by decide) ha1_3
  have ha3_4 := obs_store_other' hobs4 Register.x13 (by decide) ha3_3
  have ha5_4 := obs_store_other' hobs4 Register.x15 (by decide) ha5_3
  have hra_4 := obs_store_other' hobs4 Register.x1 (by decide) hra_3
  refine ⟨hG4,
    by rw [hstore_mem]
       exact memmove_insert_mv c.σ.mem (dst.toNat + i) (bs i)
         (mv_key_above dst src n hreg i) hloaded,
    hpc4, ha0_4, ha1_4, ha3_4, ha5_4, hra_4, obs_store_minstret hobs4, hi4, hreg, hbs, hilt, ?_, ?_⟩
  · rw [hstore_mem]
    exact cpyinv_store' dst src (n-1) bs i m0 c.σ.mem
      (mv_disjoint dst src n hreg) (by have := hreg.n1; omega) hcinv
  · intro R hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.x14 hR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.x15 hR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.x11 hR
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_mv hobs4 R hR
    rw [e4, e3, e2, e1]; exact hframe R hR

/-! ## The `bne a5,a3` at `0x80006a1c` (loop back-edge / exit to ret) -/

/-- `bne` taken (`i+1 < n`): `dst+(i+1) ≠ dst+n`, loop back to iteration `i+1`. -/
theorem tr_bne_back_mv (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (hlt : i + 1 < n) :
    Triple (StMv1c g i r dst src n m0 bs) (StMv g (i+1) r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha3, ha5, hra, ⟨vmi, hmi⟩, htick,
    hreg, hbs, hilt, hcinv, hframe⟩ := hSt
  have hnw := hreg.dst_nowrap
  have hv : ((dst + BitVec.ofNat 64 (i+1)) != (dst + BitVec.ofNat 64 n)) = true := by
    apply bne_true_of_toNat_ne
    rw [ptr_toNat dst (i+1) (by omega), ptr_toNat dst n (by omega)]
    omega
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_6a1c_taken c.σ c.tick c.steps (0x80006a1c#64) vmi
      (dst + BitVec.ofNat 64 (i+1)) (dst + BitVec.ofNat 64 n)
      hgood hpc hmi ha5 ha3 hloaded rfl hv htick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, ?_,
    obs_btaken_other' hobs Register.x10 (by decide) ha0,
    obs_btaken_other' hobs Register.x11 (by decide) ha1,
    obs_btaken_other' hobs Register.x13 (by decide) ha3,
    obs_btaken_other' hobs Register.x15 (by decide) ha5,
    obs_btaken_other' hobs Register.x1 (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, hbs, hlt, by rw [hmem']; exact hcinv,
    fun R hR => (frame_btaken_mv hobs R hR).trans (hframe R hR)⟩
  rw [obs_btaken_pc hobs, bne_target_mv]

/-- `bne` not taken (`i+1 = n`): fall through to `ret` with the window fully copied. -/
theorem tr_bne_done_mv (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (heq : i + 1 = n) :
    Triple (StMv1c g i r dst src n m0 bs) (StMvDone g r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha3, ha5, hra, ⟨vmi, hmi⟩, htick,
    hreg, hbs, hilt, hcinv, hframe⟩ := hSt
  rw [heq] at ha5 hcinv
  have hv : ((dst + BitVec.ofNat 64 n) != (dst + BitVec.ofNat 64 n)) = false := by
    rw [bne_not_beq, beq_self_eq_true]; rfl
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_6a1c_nottaken c.σ c.tick c.steps (0x80006a1c#64) vmi
      (dst + BitVec.ofNat 64 n) (dst + BitVec.ofNat 64 n)
      hgood hpc hmi ha5 ha3 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006a20#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006a1c#64) 4 = (0x80006a20#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, hpc',
    obs_bnottaken_other' hobs Register.x10 (by decide) ha0,
    obs_bnottaken_other' hobs Register.x15 (by decide) ha5,
    obs_bnottaken_other' hobs Register.x1 (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, by rw [hmem']; exact hcinv,
    fun R hR => (frame_bnottaken_mv hobs R hR).trans (hframe R hR)⟩

/-! ## Loop invariant, guard, measure -/

def AtHeadMv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  ∃ i, i < n ∧ StMv g i r dst src n m0 bs c

def LoopIMv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadMv g r dst src n m0 bs c ∨ StMvDone g r dst src n m0 bs c

def LoopMuMv (c : Config) : Nat :=
  2^64 - ((c.σ.regs.get? Register.x15).getD (0#64)).toNat

theorem loopmu_head_mv (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config)
    (hSt : StMv g i r dst src n m0 bs c) : LoopMuMv c = 2^64 - (dst.toNat + i) := by
  simp only [LoopMuMv, hSt.a5, Option.getD_some]
  rw [ptr_toNat dst i (by have := hSt.regions.dst_nowrap; have := hSt.ilt; omega)]

/-- **Loop body**: one iteration re-establishes `LoopIMv` strictly decreasing the measure. -/
theorem loop_body_mv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (k : Nat) :
    Triple (fun c => LoopIMv g r dst src n m0 bs c ∧ AtHeadMv g r dst src n m0 bs c ∧ LoopMuMv c = k)
           (fun c => LoopIMv g r dst src n m0 bs c ∧ LoopMuMv c < k) := by
  intro c hc
  obtain ⟨_, ⟨i, hilt, hSt⟩, hmu⟩ := hc
  have hmu_eq : LoopMuMv c = 2^64 - (dst.toNat + i) := loopmu_head_mv g i r dst src n m0 bs c hSt
  rw [hmu_eq] at hmu
  have hnw := hSt.regions.dst_nowrap
  obtain ⟨c1, hs1, hSt1c⟩ := iterMv g i r dst src n m0 bs c hSt
  by_cases hdone : i + 1 = n
  · -- exit: bne not taken → StMvDone
    obtain ⟨c2, hs2, hD⟩ := tr_bne_done_mv g i r dst src n m0 bs hdone c1 hSt1c
    refine ⟨c2, hs1.trans hs2, Or.inr hD, ?_⟩
    have hmu2 : LoopMuMv c2 = 2^64 - (dst.toNat + n) := by
      simp only [LoopMuMv, hD.a5, Option.getD_some]
      rw [ptr_toNat dst n (by omega)]
    rw [hmu2, ← hmu]; omega
  · -- back-edge: bne taken → head (i+1)
    have hlt : i + 1 < n := by have := hSt.ilt; omega
    obtain ⟨c2, hs2, hSt2⟩ := tr_bne_back_mv g i r dst src n m0 bs hlt c1 hSt1c
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨i + 1, hlt, hSt2⟩, ?_⟩
    have hmu2 : LoopMuMv c2 = 2^64 - (dst.toNat + (i + 1)) :=
      loopmu_head_mv g (i+1) r dst src n m0 bs c2 hSt2
    rw [hmu2, ← hmu]; omega

/-- The loop runs to `StMvDone` (`0x80006a20`, full window copied). -/
theorem loop_to_done_mv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (LoopIMv g r dst src n m0 bs) (StMvDone g r dst src n m0 bs) := by
  have hloop := Triple.loop (I := LoopIMv g r dst src n m0 bs)
    (B := AtHeadMv g r dst src n m0 bs) LoopMuMv (loop_body_mv g r dst src n m0 bs)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hDone⟩

/-! ## `ret` (`0x80006a20 → r`) and the described-update postcondition -/

/-- Described update: `[dst, dst+n)` holds the source bytes, everything else reads
`m0`; `a0 = dst` (memmove returns dst), PC back at `r`. -/
def memmove_fwd_post (g : (R : Register) → Option (RegisterType R)) (r dst _src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∀ k, k < n → c.σ.mem[(dst.toNat + k)]? = some (bs k)) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + n ≤ a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenMv R → c.σ.regs.get? R = g R)

/-- `ret` transition: from `StMvDone` to the postcondition (`r` 4-aligned). -/
theorem tr_ret_mv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) :
    Triple (StMvDone g r dst src n m0 bs) (memmove_fwd_post g r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha5, hra, ⟨vmi, hmi⟩, htick, hreg, hcinv, hframe⟩ := hSt
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_6a20 c.σ c.tick c.steps (0x80006a20#64) vmi r hgood hpc hmi hra hloaded rfl halign htick
  have hpc' : σ'.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs, ret_tgt r halign]
  have ha0' := obs_jr_other' hobs Register.x10 (by decide) ha0
  have hra' := obs_jr_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG', hpc', ha0', hra', ?_, ?_, hi',
    fun R hR => (frame_jr_mv hobs R hR).trans (hframe R hR)⟩
  · intro k hk; rw [hmem']; exact hcinv.copied k hk
  · intro a ha; rw [hmem']
    exact hcinv.outside a (by have := hreg.n1; omega)

/-! ## Entry dispatch (`0x800069c4 → 0x80006a0c`)

Both disjointness arms funnel to `0x800069f0`:
* `dst+n ≤ src`: `src ≥ᵤ dst`, so the `bgeu a1,a0` at `0x69c4` is taken.
* `src+n ≤ dst`: `src <ᵤ dst` (not taken), then `a5 := src+n` and the
  `bgeu a0,a5` at `0x69cc` is taken.
Then `li a5,31` / `bltu` (byte path, `n ≤ 31`) / `mv a5,a0` / `addi a3,a2,-1` /
`beqz a2` (not taken, `1 ≤ n`) / `addi a3,a3,1` / `add a3,a5,a3` set up the loop. -/

/-- Entry configuration at `0x800069c4`: ABI arguments in place, `mem = m0`. -/
structure PreMv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x800069c4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : MvRegions dst src n
  hbs : MvBytes m0 src n bs
  memeq : c.σ.mem = m0
  hframe : ∀ R : Register, NotWrittenMv R → c.σ.regs.get? R = g R

/-- Mid-dispatch configuration at `0x800069f0` (both arms land here). -/
structure StMvF0 (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemmoveLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x800069f0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : MvRegions dst src n
  hbs : MvBytes m0 src n bs
  memeq : c.σ.mem = m0
  hframe : ∀ R : Register, NotWrittenMv R → c.σ.regs.get? R = g R

/-- Dispatch head: `0x69c4 → 0x69f0` (one or three steps, by disjointness arm). -/
theorem tr_dispatch_mv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreMv g r dst src n m0 bs) (StMvF0 g r dst src n m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, hra, ⟨vmi, hmi⟩, htick,
    hreg, hbs, hmemeq, hframe⟩ := hPre
  have hn1 := hreg.n1
  have hdnw := hreg.dst_nowrap
  have hsnw := hreg.src_nowrap
  rcases hreg.disjoint with hd | hd
  · -- dst+n ≤ src: bgeu a1,a0 taken straight to 0x69f0
    have hv : zopz0zKzJ_u src dst = true := bgeu_of_le src dst (by omega)
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_69c4_taken c.σ c.tick c.steps (0x800069c4#64) vmi src dst
        hgood hpc hmi ha1 ha0 hloaded rfl hv htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x800069f0#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs1,
        show (0x800069c4#64 : BitVec 64) + sign_extend (m := 64) (0x002c#13) = (0x800069f0#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide]
    refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1,
      hG1, by rw [hmem1]; exact hloaded, hpc1,
      obs_btaken_other' hobs1 Register.x10 (by decide) ha0,
      obs_btaken_other' hobs1 Register.x11 (by decide) ha1,
      obs_btaken_other' hobs1 Register.x12 (by decide) ha2,
      obs_btaken_other' hobs1 Register.x1 (by decide) hra,
      obs_btaken_minstret hobs1, hi1, hreg, hbs, by rw [hmem1]; exact hmemeq,
      fun R hR => (frame_btaken_mv hobs1 R hR).trans (hframe R hR)⟩
  · -- src+n ≤ dst: not taken, a5 := src+n, bgeu a0,a5 taken
    have hv : zopz0zKzJ_u src dst = false := bgeu_false_of_lt src dst (by omega)
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_69c4_nottaken c.σ c.tick c.steps (0x800069c4#64) vmi src dst
        hgood hpc hmi ha1 ha0 hloaded rfl hv htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x800069c8#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1
      rwa [show BitVec.addInt (0x800069c4#64) 4 = (0x800069c8#64 : BitVec 64) from by decide] at this
    have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
    have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
    obtain ⟨vmi1, hmi1⟩ := obs_bnottaken_minstret hobs1
    -- 69c8: add a5,a1,a2
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_69c8 σ1 i1 (c.steps + 1) (0x800069c8#64) vmi1 src (BitVec.ofNat 64 n)
        hG1 hpc1 hmi1 ha1_1 ha2_1 (by rw [hmem1]; exact hloaded) rfl hi1
    have hpc2 : σ2.regs.get? Register.PC = some (0x800069cc#64 : BitVec 64) := by
      have := obs_alu_pc hobs2
      rwa [show BitVec.addInt (0x800069c8#64) 4 = (0x800069cc#64 : BitVec 64) from by decide] at this
    have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
    have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
    have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
    have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
    have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
    -- 69cc: bgeu a0,a5 taken (dst ≥ src+n)
    have hsn : (src + BitVec.ofNat 64 n).toNat = src.toNat + n := ptr_toNat src n (by omega)
    have hv2 : zopz0zKzJ_u dst (src + BitVec.ofNat 64 n) = true :=
      bgeu_of_le dst (src + BitVec.ofNat 64 n) (by rw [hsn]; omega)
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_69cc_taken σ2 i2 (c.steps + 1 + 1) (0x800069cc#64) vmi2 dst (src + BitVec.ofNat 64 n)
        hG2 hpc2 hmi2 ha0_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hv2 hi2
    have hpc3 : σ3.regs.get? Register.PC = some (0x800069f0#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs3,
        show (0x800069cc#64 : BitVec 64) + sign_extend (m := 64) (0x0024#13) = (0x800069f0#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide]
    refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
      ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3),
      hG3, by rw [hmem3, hmem2, hmem1]; exact hloaded, hpc3,
      obs_btaken_other' hobs3 Register.x10 (by decide) ha0_2,
      obs_btaken_other' hobs3 Register.x11 (by decide) ha1_2,
      obs_btaken_other' hobs3 Register.x12 (by decide) ha2_2,
      obs_btaken_other' hobs3 Register.x1 (by decide) hra_2,
      obs_btaken_minstret hobs3, hi3, hreg, hbs, by rw [hmem3, hmem2, hmem1]; exact hmemeq, ?_⟩
    intro R hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_bnottaken_mv hobs1 R hR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.x15 hR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_btaken_mv hobs3 R hR
    rw [e3, e2, e1]; exact hframe R hR

/-- Setup tail: `0x69f0 → 0x6a0c` (seven straight-line/fall-through steps),
establishing the loop head at iteration `0`. -/
theorem tr_setup_mv (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (StMvF0 g r dst src n m0 bs) (AtHeadMv g r dst src n m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, hra, ⟨vmi, hmi⟩, htick,
    hreg, hbs, hmemeq, hframe⟩ := hSt
  have hn1 := hreg.n1
  have hn31 := hreg.n31
  have hntn : (BitVec.ofNat 64 n : BitVec 64).toNat = n :=
    BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (by omega)
  -- === 69f0: li a5,31 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_69f0 c.σ c.tick c.steps (0x800069f0#64) vmi hgood hpc hmi hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x800069f4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800069f0#64) 4 = (0x800069f4#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some (0x1f#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li31_val] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 69f4: bltu a5,a2 not taken (n ≤ 31) ===
  have hv1 : zopz0zI_u (0x1f#64) (BitVec.ofNat 64 n) = false :=
    bltu_false_of_ge (0x1f#64) (BitVec.ofNat 64 n)
      (by rw [hntn, show (0x1f#64 : BitVec 64).toNat = 31 from by decide]; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_69f4_nottaken σ1 i1 (c.steps + 1) (0x800069f4#64) vmi1 (BitVec.ofNat 64 n)
      hG1 hpc1 hmi1 ha5_1 ha2_1 (by rw [hmem1]; exact hloaded) rfl hv1 hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x800069f8#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs2
    rwa [show BitVec.addInt (0x800069f4#64) 4 = (0x800069f8#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_bnottaken_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_bnottaken_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_bnottaken_other' hobs2 Register.x12 (by decide) ha2_1
  have hra_2 := obs_bnottaken_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_bnottaken_minstret hobs2
  -- === 69f8: mv a5,a0 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_69f8 σ2 i2 (c.steps + 1 + 1) (0x800069f8#64) vmi2 dst
      hG2 hpc2 hmi2 ha0_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x800069fc#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800069f8#64) 4 = (0x800069fc#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha5_3 : σ3.regs.get? Register.x15 = some dst := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add dst] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  -- === 69fc: addi a3,a2,-1 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_69fc σ3 i3 (c.steps + 1 + 1 + 1) (0x800069fc#64) vmi3 (BitVec.ofNat 64 n)
      (BitVec.ofNat 64 (n-1))
      hG3 hpc3 hmi3 ha2_3 (dec1_fwd n hn1 (by omega))
      (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006a00#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x800069fc#64) 4 = (0x80006a00#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_alu_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
  have ha5_4 := obs_alu_other' hobs4 Register.x15 (by decide) ha5_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha3_4 : σ4.regs.get? Register.x13 = some (BitVec.ofNat 64 (n-1)) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [dec1_fwd n hn1 (by omega)] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  -- === 6a00: beqz a2 not taken (n ≠ 0) ===
  have hv2 : ((BitVec.ofNat 64 n : BitVec 64) == (0#64)) = false :=
    beq_false_of_toNat_ne _ _ (by rw [hntn, show (0#64 : BitVec 64).toNat = 0 from by decide]; omega)
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_6a00_nottaken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006a00#64) vmi4 (BitVec.ofNat 64 n)
      hG4 hpc4 hmi4 ha2_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hv2 hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006a04#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs5
    rwa [show BitVec.addInt (0x80006a00#64) 4 = (0x80006a04#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_bnottaken_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_bnottaken_other' hobs5 Register.x11 (by decide) ha1_4
  have ha3_5 := obs_bnottaken_other' hobs5 Register.x13 (by decide) ha3_4
  have ha5_5 := obs_bnottaken_other' hobs5 Register.x15 (by decide) ha5_4
  have hra_5 := obs_bnottaken_other' hobs5 Register.x1 (by decide) hra_4
  obtain ⟨vmi5, hmi5⟩ := obs_bnottaken_minstret hobs5
  -- === 6a04: addi a3,a3,1 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_6a04 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006a04#64) vmi5
      (BitVec.ofNat 64 (n-1)) (BitVec.ofNat 64 n)
      hG5 hpc5 hmi5 ha3_5 (dec1_back n hn1 (by omega))
      (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006a08#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80006a04#64) 4 = (0x80006a08#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_alu_other' hobs6 Register.x11 (by decide) ha1_5
  have ha5_6 := obs_alu_other' hobs6 Register.x15 (by decide) ha5_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha3_6 : σ6.regs.get? Register.x13 = some (BitVec.ofNat 64 n) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [dec1_back n hn1 (by omega)] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- === 6a08: add a3,a5,a3 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_6a08 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006a08#64) vmi6
      dst (BitVec.ofNat 64 n)
      hG6 hpc6 hmi6 ha5_6 ha3_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded)
      rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006a0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80006a08#64) 4 = (0x80006a0c#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 := obs_alu_other' hobs7 Register.x11 (by decide) ha1_6
  have ha5_7 := obs_alu_other' hobs7 Register.x15 (by decide) ha5_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha3_7 := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmem7eq : σ7.mem = c.σ.mem := by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  refine ⟨⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩,
    ((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7),
    0, hn1, ?_⟩
  refine ⟨hG7, by rw [hmem7eq]; exact hloaded, hpc7, ha0_7, ?_, ha3_7, ?_, hra_7,
    obs_alu_minstret hobs7, hi7, hreg, hbs, hn1, ?_, ?_⟩
  · rwa [show src = src + BitVec.ofNat 64 0 from (add_ofNat_zero src).symm] at ha1_7
  · rwa [show dst = dst + BitVec.ofNat 64 0 from (add_ofNat_zero dst).symm] at ha5_7
  · rw [hmem7eq, hmemeq]
    exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun a _ => rfl, fun k _ _ => rfl⟩
  · intro R hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.x15 hR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_bnottaken_mv hobs2 R hR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.x15 hR
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_alu_mv hobs4 R hR.x13 hR
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_bnottaken_mv hobs5 R hR
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_mv hobs6 R hR.x13 hR
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_alu_mv hobs7 R hR.x13 hR
    rw [e7, e6, e5, e4, e3, e2, e1]; exact hframe R hR

/-! ## The composed forward-path spec -/

/-- **`memmove` forward byte path** (`0x800069c4 → ret`): for disjoint regions
with `1 ≤ n ≤ 31`, the machine runs from the entry to `r` with `a0 = dst`,
`[dst, dst+n)` holding exactly the source bytes and all other memory unchanged. -/
theorem memmove_fwd_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) :
    Triple (PreMv g r dst src n m0 bs) (memmove_fwd_post g r dst src n m0 bs) :=
  ((tr_dispatch_mv g r dst src n m0 bs).seq
    ((tr_setup_mv g r dst src n m0 bs).seq
      ((fun c hc => loop_to_done_mv g r dst src n m0 bs c (Or.inl hc)) :
        Triple (AtHeadMv g r dst src n m0 bs) (StMvDone g r dst src n m0 bs)))).seq
    (tr_ret_mv g r dst src n m0 bs halign)

end Vsa.Sim
