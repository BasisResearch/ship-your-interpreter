import Vsa.Sim.SnprintfSites

/-!
# M3 Layer-3 — `SnprintfSites2` : the sign-block + indirect-dispatch step battery

Session-4 file (`_sn4` suffix on all new names).  Extends the loop-body site
battery of `SnprintfSites.lean` with:

* the **sign block** of the `%lld` path (`experiments/M3-snprintf-lld.md` §1.3(c),
  disasm `[0x800080dc, 0x800080f4]`): the `bgez` split on the signed argument, the
  `'-'` sign-byte handling, and the `neg` producing the unsigned magnitude;
* the **conversion-char dispatch** `jr a5` at `0x800077bc` — the computed-goto
  jump table whose slot resolves the `%lld`→`d` handler.

## Sign-byte placement finding (buffer vs flush)

The disassembly is unambiguous: the `'-'` byte is stored by
`0x800080f0 sb a5,167(sp)` into a **dedicated stack slot** `167(sp)` — *not* into
the descending digit buffer (which starts at `sp+348` and grows downward, written
by `0x8000832c sb a0,-1(s9)`).  The sign byte is later **read back** at
`0x80008388 lbu t5,167(sp)` by the pad/emit machinery and prepended into the iov
that `__ssprint_r` flushes.  So: **the `'-'` is prepended at flush, never written
into the digit buffer.**  This is exactly `intToString (.negSucc m) = "-" ++
natToString (m+1)`: the sign and the magnitude digits are produced independently
and concatenated, the sign first.

## What is a step here vs a boundary hypothesis

There is no `stepObs_load` primitive in the current Sail-model step layer (LOADs
have no observational-step lemma; only ALU/branch/store/jump do).  The two loads
of the sign block —`0x800080dc ld a3,0(a4)` (fetch the 64-bit va_list arg) and
the preceding `ld a4,24(sp)`— are therefore modelled as a **boundary**: the site
lemmas below take the loaded argument value `v` as a hypothesis (`x13 = v` after
the load), and step the ALU/branch/store instructions that consume it.  The same
convention is used for the interleaved `0x800080e0 sd a5,24(sp)` (va_list bump,
an 8-byte stack store off the live path) and `0x800080f8 bltz s4` (the
already-set-flag guard): they are not on the value-producing path and are elided
from the linear trace, documented at the composition in `SnprintfSpec4.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word helpers for the new sign-block / dispatch words

Mirror the `w_*_sn` / `nr_*_sn` shape of `SnprintfSites.lean`.  `_sn4` suffix. -/

theorem w_00078067_sn4 : (((0x00#8).append (0x07#8)).append (0x80#8)).append (0x67#8) = (0x00078067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00078067_sn4 : Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x80#8)).append (0x67#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Shared decode-prelude helper (same as `SnprintfSites`). -/

private theorem misa_pre4 (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa
private theorem priv_pre4 (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege
private theorem sec_pre4 (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg

/-! ## Sign-block sites -/

/-! ### 0x800080e4 — `mv a4,a3` = `addi x14,x13,0` (x14 := x13 = the arg value) -/
theorem site_800080e4_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080e4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v13 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800080e4 hmem
  have hx13₂ : (afterNextPC (afterPrelude σ) (0x800080e4#64)).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ (0x800080e4#64) _ (by decide) (by decide)]; exact hx13
  exact stepObs_alu σ i u (0x800080e4#64) vminstret (0x00068713#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v13 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x87#8) (0x06#8) (0x00#8)
    hG hpc hminstret w_00068713_sn nr_00068713_sn
    (Vsa.Sim.DecodeTable.decode_00068713 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0e#5) v13
      (afterNextPC (afterPrelude σ) (0x800080e4#64))
      (sigma3_alu σ (0x800080e4#64) Register.x14 (v13 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x13 _ v13 hx13₂) (wX_bits_x14 _ (v13 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800080e8 — `bgez a3` = `BTYPE(imm,x0,x13,BGE)` : taken iff `a3 ≥s 0`

Taken (`a3 ≥ 0`, non-negative) jumps to `0x80008050` (skip the sign block).
Not-taken (`a3 < 0`, negative) falls through to `0x800080ec` (emit `'-'`, `neg`). -/
theorem site_800080e8_taken_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080e8#64 : BitVec 64))
    (hv : zopz0zKzJ_s v13 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1f68#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800080e8 hmem
  have hx13₂ : (afterNextPC (afterPrelude σ) (0x800080e8#64)).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ (0x800080e8#64) _ (by decide) (by decide)]; exact hx13
  exact stepObs_branch_taken σ i u (0x800080e8#64) vminstret (0x1f68#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BGE (0xf606d4e3#32) (0xe3#8) (0xd4#8) (0x06#8) (0xf6#8)
    hG hpc hminstret w_f606d4e3_sn nr_f606d4e3_sn
    (Vsa.Sim.DecodeTable.decode_f606d4e3 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    (execute_btype_bge_taken (0x1f68#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) v13 (0#64)
      (0x800080e8#64) (Vsa.Sim.initMisa) (afterNextPC (afterPrelude σ) (0x800080e8#64))
      (rX_bits_x13 _ v13 hx13₂) (rX_bits_zero _)
      (by rw [get?_afterNextPC σ (0x800080e8#64) _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ (0x800080e8#64) _ (by decide) (by decide)]; exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Not-taken arm: `a3 < 0` (negative) ⇒ fall through to `0x800080ec`. -/
theorem site_800080e8_nottaken_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080e8#64 : BitVec 64))
    (hv : zopz0zKzJ_s v13 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800080e8 hmem
  have hx13₂ : (afterNextPC (afterPrelude σ) (0x800080e8#64)).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ (0x800080e8#64) _ (by decide) (by decide)]; exact hx13
  exact stepObs_branch_nottaken σ i u (0x800080e8#64) vminstret (0x1f68#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BGE (0xf606d4e3#32) (0xe3#8) (0xd4#8) (0x06#8) (0xf6#8)
    hG hpc hminstret w_f606d4e3_sn nr_f606d4e3_sn
    (Vsa.Sim.DecodeTable.decode_f606d4e3 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    (execute_btype_bge_nottaken (0x1f68#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) v13 (0#64)
      (afterNextPC (afterPrelude σ) (0x800080e8#64))
      (rX_bits_x13 _ v13 hx13₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800080ec — `li a5,45` = `addi x15,x0,45` (x15 := '-') -/
theorem site_800080ec_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080ec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x02d#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800080ec hmem
  exact stepObs_alu σ i u (0x800080ec#64) vminstret (0x02d00793#32)
    (instruction.ITYPE (0x02d#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x02d#12)) (0x93#8) (0x07#8) (0xd0#8) (0x02#8)
    hG hpc hminstret w_02d00793_sn nr_02d00793_sn
    (Vsa.Sim.DecodeTable.decode_02d00793 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    (execute_itype_addi_char (0x02d#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x800080ec#64))
      (sigma3_alu σ (0x800080ec#64) Register.x15 ((0#64) + sign_extend (m := 64) (0x02d#12)))
      (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x02d#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800080f0 — `sb a5,167(sp)` = `STORE(0x0a7,x15,x2,1)` : sign byte → 167(sp)

The load-bearing placement site: `'-'` (`x15`) is stored at `sp+167`, a dedicated
stack slot *disjoint* from the digit buffer at `sp+348 …`.  `v2 = sp`, `vdata =
x15`. -/
theorem site_800080f0_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080f0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hhiram : (v2 + sign_extend (m := 64) (0x0a7#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x0a7#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x800080f0#64)).mem.insert
        (v2 + sign_extend (m := 64) (0x0a7#12)).toNat (stData 1 v15)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        ((afterNextPC (afterPrelude σ) (0x800080f0#64)).mem.insert
          (v2 + sign_extend (m := 64) (0x0a7#12)).toNat (stData 1 v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800080f0 hmem
  exact stepObs_store σ i u (0x800080f0#64) vminstret (0x0af103a3#32)
    (instruction.STORE (0x0a7#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x02#5, 1))
    ((afterNextPC (afterPrelude σ) (0x800080f0#64)).mem.insert
      (v2 + sign_extend (m := 64) (0x0a7#12)).toNat (stData 1 v15))
    (0xa3#8) (0x03#8) (0xf1#8) (0x0a#8)
    hG hpc hminstret w_0af103a3_sn nr_0af103a3_sn
    (Vsa.Sim.DecodeTable.decode_0af103a3 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    (exec_sb σ (0x800080f0#64) (0x0a7#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x02#5) v2 v15 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800080f0#64) _ (by decide) (by decide)]; exact hx2))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800080f0#64) _ (by decide) (by decide)]; exact hx15))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800080f4 — `neg a4,a4` = `RTYPE(x14,x0,x14,SUB)` : x14 := 0 - x14 (magnitude)

The two's-complement negation.  For a negative signed argument `v`, the result
`0 - v = BitVec.neg v` read as unsigned is `|v|` — including `INT64_MIN`, where
`neg` wraps to the same bit pattern but is consumed as unsigned `2^63` by the
loop (the arithmetic-core `neg_magnitude` lemma, `SnprintfSpec.lean`). -/
theorem site_800080f4_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080f4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 ((0#64) - v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800080f4 hmem
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x800080f4#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x800080f4#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_alu σ i u (0x800080f4#64) vminstret (0x40e00733#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0e#5, rop.SUB))
    Register.x14 ((0#64) - v14) (0x33#8) (0x07#8) (0xe0#8) (0x40#8)
    hG hpc hminstret w_40e00733_sn nr_40e00733_sn
    (Vsa.Sim.DecodeTable.decode_40e00733 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    (execute_rtype_sub_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) (0#64) v14
      (afterNextPC (afterPrelude σ) (0x800080f4#64))
      (sigma3_alu σ (0x800080f4#64) Register.x14 ((0#64) - v14))
      (rX_bits_zero _) (rX_bits_x14 _ v14 hx14₂) (wX_bits_x14 _ ((0#64) - v14)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## The conversion-char dispatch — `jr a5` at `0x800077bc`

`jr a5` = `JALR(0x000, x15, x0)` (link `x0`, no return address written): an
indirect jump to `x15 = a5`.  On the `%lld` path, `a5` was computed by the
preceding table lookup

```
800077b0  add  a5,a5,s6      ; a5 = table_base + (char-32)*4
800077b4  lw   a5,0(a5)      ; a5 = table[char-32]   (a relative offset word)
800077b8  add  a5,a5,s6      ; a5 = table_base + offset  (the concrete handler PC)
800077bc  jr   a5            ; → handler
```

so `a5` holds a *concrete* address once the rodata table slot is pinned (the
`MaskPinned`/jump-table precedent — a data byte-pin makes the loaded offset a
literal).  This site takes that resolved target `tgt = a5` as a hypothesis and
steps to `PC := tgt`; the dispatch composition (future) supplies `tgt` = the
`d`-conversion handler `0x800080c4` by pinning `table[0x64-0x20]` and the base
`s6 = 0x8001a0fc`.  Target alignment (`tgt.toNat % 4 = 0`) is a hypothesis
(handler PCs are word-aligned). -/
theorem site_800077bc_jr_sn4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800077bc#64 : BitVec 64))
    (htgt : (BitVec.update (v15 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (v15 + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800077bc hmem
  have hx15₂ : (rX_bits (regidx.Regidx 0x0f#5)).run
      (afterNextPC (afterPrelude σ) (0x800077bc#64))
      = .ok v15 (afterNextPC (afterPrelude σ) (0x800077bc#64)) :=
    rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x800077bc#64) _ (by decide) (by decide)]; exact hx15)
  exact stepObs_jr σ i u (0x800077bc#64) vminstret v15 (0x00078067#32) (0x000#12)
    (regidx.Regidx 0x0f#5) (0x67#8) (0x80#8) (0x07#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00078067_sn4 w_00078067_sn4
    (Vsa.Sim.DecodeTable.decode_00078067 (afterPrelude σ) (misa_pre4 σ hG) (priv_pre4 σ hG) (sec_pre4 σ hG))
    hx15₂ htgt hi

end Vsa.Sim
