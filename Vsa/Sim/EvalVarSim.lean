import Vsa.Sim.EvalStrSim
import Vsa.Sim.EnvGetSpec4
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4: the `EvalE.var` simulation Triple (`evalVarSim`)

The `EvalE.var` leaf case (`ExprKind` tag `k = 4`, arm PC `0x80003434`). This is the
first non-leaf-shaped case: the arm calls `env_get` and copies the found `Value`
into the sret buffer. It does NOT use the shared `blockD_v` epilogue — the var arm
carries its OWN inlined epilogue (interleaved with the value copy), so `blockC_var`
reaches `EvalExit` directly.

## The full var arm disassembly (all 18 words decoded/verified against the ELF)

    0x80003434: 00863583  ld   a1, 8(a2)       -- a1 := *(a2+8) = var-name CString ptr
    0x80003438: 00068513  addi a0, a3, 0        -- a0 := a3   (the interp/env arg → env_get arg0)
    0x8000343c: 0f010613  addi a2, sp, 240      -- a2 := sp+0xf0  (24-byte result buffer)
    0x80003440: fd0ff0ef  jal  ra, 0x80002c10   -- call env_get   (link 0x80003444)
    0x80003444: 32050ee3  beq  a0, x0, 0x80003f80 -- NOT taken (found ⇒ a0≠0)
    0x80003448: 0f013683  ld   a3, 0xf0(sp)     -- a3 := *(sp+0xf0)   Value bytes 0..7
    0x8000344c: 0f813703  ld   a4, 0xf8(sp)     -- a4 :=                    bytes 8..15
    0x80003450: 10013783  ld   a5, 0x100(sp)    -- a5 :=                    bytes 16..23
    0x80003454: 43813083  ld   ra, 1080(sp)     -- inlined epilogue: restore ra   (= r)
    0x80003458: 43013403  ld   s0, 1072(sp)     --   restore s0
    0x8000345c: 00d4b023  sd   a3, 0(s1)        -- copy Value into sret (s1): bytes 0..7
    0x80003460: 00e4b423  sd   a4, 8(s1)        --   bytes 8..15
    0x80003464: 00f4b823  sd   a5, 16(s1)       --   bytes 16..23
    0x80003468: 42013903  ld   s2, 1056(sp)     --   restore s2
    0x8000346c: 00048513  addi a0, s1, 0        --   a0 := s1 = sret (return value)
    0x80003470: 42813483  ld   s1, 1064(sp)     --   restore s1
    0x80003474: 44010113  addi sp, sp, 1088     --   restore sp
    0x80003478: 00008067  ret                   --   PC := r

## Structure (mirrors `EvalStrSim.lean`)

* `blockA_k` (k=4, armPC 0x80003434, `Env_getLoaded`, `.var x`) delivers `ArmEntryK`.
* **`blockC_var`** — the whole arm `ArmEntryK … 0x80003434 Env_getLoaded (.var x) →
  EvalExit … v`, taking `env_get`'s FOUND-case contract as an explicit hypothesis
  (`henv_get`, see below) and proving the remainder (beq-not-taken, 3-word result
  load, 3-word store into sret, and the inlined-epilogue restores) concretely,
  establishing `EvalExit` directly.
* **`VarSlotPinned` / `var_slot_kindPinned`** — the jump-table slot pin for tag 4.
* **`EvalVarEntry` / `evalVarSim`** — the `EvalE.var` Triple.

## HONEST DEPENDENCY: `env_get`'s FOUND-case contract (`henv_get`)

The `env_get` Layer-3 spec suite (`EnvGetSpec*.lean`) is, per its own docstring, a
"WORK IN PROGRESS FOUNDATION": every one of the 51 instructions has a `stepObs`
lemma, and the SCAN LOOP is verified up to `ScanExit` (hit @0x80002c70 / miss
@0x80002cc4). But the full end-to-end contract — prologue (0x80002c10 → scan entry),
the FOUND-value copy tail (0x80002c70–0x80002cc0: `a0 := 1`; copy the 24-byte
`values[i]` into `*out`; restore; `addi sp,64`; `ret`), the parent chain-walk loop,
and the `Store.lookup ↔ ValueRepr` bridge — is DESIGNED but NOT PROVEN. Composing
the existing lemmas the way `blockC_str` composes `value_str_spec_full` is therefore
not possible today.

So `blockC_var` threads `env_get`'s found-case as a single, clearly-scoped
`Triple`-shaped hypothesis on `EvalVarEntry` (`env_get_found`): from the machine
config at the call site (PC 0x80002c10, args set) it reaches the link return
(PC 0x80003444) with `a0 = 1`, the 24-byte result buffer at `sp+0xf0` holding
`ValueRepr … v` (the found value from the `EvalE.var` derivation), and all the
frame/store/geometry invariants preserved. Everything ELSE in the var arm — the
argument setup, the not-taken branch, the value copy into sret (preserving
`ValueRepr` via `valueRepr_agreeP`), and the inlined epilogue restores → `EvalExit`
— is proven here for real. When `env_get`'s full contract lands, this one hypothesis
is discharged by it and `blockC_var` closes unconditionally.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `EX_VAR` arm sites (@0x80003434 … @0x80003478) -/

/-- 0x80003434: `ld a1,8(a2)` → `x11 := *(a2+8)` (the var-name CString pointer;
word `0x00863583`, identical form to str's `site_80003414_ee`). -/
theorem site_80003434_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003434#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003434 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80003434#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x80003434#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80003434#64) vminstret (0x00863583#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, false, 8))
    Register.x11 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x35#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00863583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003434#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x80003434#64) Register.x11
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vexpr b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x12 _ vexpr hx12₂)
      (wX_bits_x11 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003438: `addi a0,a3,0` (mv a0,a3) → `x10 := x13` (word `0x00068513`). -/
theorem site_80003438_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003438#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003438 hmem
  have hx13₂ : (afterNextPC (afterPrelude σ) (0x80003438#64)).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ (0x80003438#64) _ (by decide) (by decide)]; exact hx13
  exact stepObs_alu σ i u (0x80003438#64) vminstret (0x00068513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x85#8) (0x06#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00068513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0a#5) v13
      (afterNextPC (afterPrelude σ) (0x80003438#64))
      (sigma3_alu σ (0x80003438#64) Register.x10 (v13 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x13 _ v13 hx13₂) (wX_bits_x10 _ (v13 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000343c: `addi a2,sp,240` → `x12 := sp + 0xf0` (word `0x0f010613`). -/
theorem site_8000343c_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000343c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (vsp + sign_extend (m := 64) (0x0f0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000343c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000343c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000343c#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x8000343c#64) vminstret (0x0f010613#32)
    (instruction.ITYPE (0x0f0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (vsp + sign_extend (m := 64) (0x0f0#12)) (0x13#8) (0x06#8) (0x01#8) (0x0f#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0f010613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x0f0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0c#5) vsp
      (afterNextPC (afterPrelude σ) (0x8000343c#64))
      (sigma3_alu σ (0x8000343c#64) Register.x12 (vsp + sign_extend (m := 64) (0x0f0#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x12 _ (vsp + sign_extend (m := 64) (0x0f0#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003440: `jal ra,0x80002c10` (word `0xfd0ff0ef`, imm `0x1ff7d0` → `0x80002c10`,
rd=x1=ra, link 0x80003444). -/
theorem site_80003440_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003440#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff7d0#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1ff7d0#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003440 hmem
  exact stepObs_jal σ i u (0x80003440#64) vminstret (0xfd0ff0ef#32) (0x1ff7d0#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80003440#64) 4)
    (0xef#8) (0xf0#8) (0x0f#8) (0xfd#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fd0ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80003440#64) 4)) hi

/-- 0x80003444: `beq a0,x0,0x80003f80` NOT taken (found ⇒ `a0 ≠ 0`; word `0x32050ee3`). -/
theorem site_80003444_nottaken_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003444#64 : BitVec 64))
    (hv : (v10 == (0#64 : BitVec 64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003444 hmem
  have h10 : (afterNextPC (afterPrelude σ) (0x80003444#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80003444#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_branch_nottaken σ i u (0x80003444#64) vminstret (0xb3c#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BEQ (0x32050ee3#32)
    (0xe3#8) (0x0e#8) (0x05#8) (0x32#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_32050ee3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0xb3c#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
      v10 (0#64) (afterNextPC (afterPrelude σ) (0x80003444#64))
      (rX_bits_x10 _ v10 h10) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### The three result-buffer loads (`ld a3/a4/a5, 0xf0/0xf8/0x100(sp)`) and the
four epilogue restores (`ld ra/s0/s2/s1, off(sp)`).  Each is an `ld rd,off(sp)`;
they differ only in PC, offset, destination register/index, word, and code bytes. -/

/-- 0x80003448: `ld a3,0xf0(sp)` → `x13 := *(sp+0xf0)` (word `0x0f013683`). -/
theorem site_80003448_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003448#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x0f0#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x0f0#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x0f0#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003448 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003448#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003448#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003448#64) vminstret (0x0f013683#32)
    (instruction.LOAD (0x0f0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0d#5, false, 8))
    Register.x13 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x36#8) (0x01#8) (0x0f#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0f013683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003448#64) (0x0f0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0d#5)
      (sigma3_alu σ (0x80003448#64) Register.x13
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x13 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000344c: `ld a4,0xf8(sp)` → `x14 := *(sp+0xf8)` (word `0x0f813703`). -/
theorem site_8000344c_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000344c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x0f8#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x0f8#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x0f8#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x0f8#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000344c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000344c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000344c#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x8000344c#64) vminstret (0x0f813703#32)
    (instruction.LOAD (0x0f8#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0e#5, false, 8))
    Register.x14 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x37#8) (0x81#8) (0x0f#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0f813703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000344c#64) (0x0f8#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x8000344c#64) Register.x14
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x14 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003450: `ld a5,0x100(sp)` → `x15 := *(sp+0x100)` (word `0x10013783`). -/
theorem site_80003450_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003450#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x100#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x100#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x100#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x100#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003450 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003450#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003450#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003450#64) vminstret (0x10013783#32)
    (instruction.LOAD (0x100#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x37#8) (0x01#8) (0x10#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_10013783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003450#64) (0x100#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80003450#64) Register.x15
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x15 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003454: `ld ra,1080(sp)` → `x1 := *(sp+1080)` (word `0x43813083`). -/
theorem site_80003454_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003454#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x438#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x438#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x438#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x438#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x438#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x1
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003454 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003454#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003454#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003454#64) vminstret (0x43813083#32)
    (instruction.LOAD (0x438#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x43#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_43813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003454#64) (0x438#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x80003454#64) Register.x1
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x1 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003458: `ld s0,1072(sp)` → `x8 := *(sp+1072)` (word `0x43013403`). -/
theorem site_80003458_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003458#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x430#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x430#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x430#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x430#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x430#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003458 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003458#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003458#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003458#64) vminstret (0x43013403#32)
    (instruction.LOAD (0x430#12, regidx.Regidx 0x02#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x34#8) (0x01#8) (0x43#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_43013403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003458#64) (0x430#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x80003458#64) Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x8 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000345c: `sd a3,0(s1)` → `mem[s1+0] := x13` (word `0x00d4b023`).  `s1 = sret`. -/
theorem site_8000345c_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vs1 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some vs1)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000345c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vs1 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vs1 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vs1 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vs1 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000345c#64)).mem
        (vs1 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000345c#64)).mem
            (vs1 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000345c hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x8000345c#64)).regs.get? Register.x9 = some vs1 := by
    rw [get?_afterNextPC σ (0x8000345c#64) _ (by decide) (by decide)]; exact hx9
  have hx13₂ : (afterNextPC (afterPrelude σ) (0x8000345c#64)).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ (0x8000345c#64) _ (by decide) (by decide)]; exact hx13
  exact stepObs_store σ i u (0x8000345c#64) vminstret (0x00d4b023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x09#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000345c#64)).mem
      (vs1 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13))
    (0x23#8) (0xb0#8) (0xd4#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00d4b023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000345c#64) (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x09#5)
      vs1 v13 hG (rX_bits_x9 _ vs1 hx9₂) (rX_bits_x13 _ v13 hx13₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003460: `sd a4,8(s1)` → `mem[s1+8] := x14` (word `0x00e4b423`). -/
theorem site_80003460_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vs1 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some vs1)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003460#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vs1 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vs1 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vs1 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vs1 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80003460#64)).mem
        (vs1 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v14) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80003460#64)).mem
            (vs1 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v14))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003460 hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80003460#64)).regs.get? Register.x9 = some vs1 := by
    rw [get?_afterNextPC σ (0x80003460#64) _ (by decide) (by decide)]; exact hx9
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80003460#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80003460#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_store σ i u (0x80003460#64) vminstret (0x00e4b423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x09#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80003460#64)).mem
      (vs1 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v14))
    (0x23#8) (0xb4#8) (0xe4#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e4b423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80003460#64) (0x008#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x09#5)
      vs1 v14 hG (rX_bits_x9 _ vs1 hx9₂) (rX_bits_x14 _ v14 hx14₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003464: `sd a5,16(s1)` → `mem[s1+16] := x15` (word `0x00f4b823`). -/
theorem site_80003464_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vs1 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some vs1)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003464#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vs1 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (vs1 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vs1 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (vs1 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80003464#64)).mem
        (vs1 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v15) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80003464#64)).mem
            (vs1 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003464 hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80003464#64)).regs.get? Register.x9 = some vs1 := by
    rw [get?_afterNextPC σ (0x80003464#64) _ (by decide) (by decide)]; exact hx9
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80003464#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80003464#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_store σ i u (0x80003464#64) vminstret (0x00f4b823#32)
    (instruction.STORE (0x010#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x09#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80003464#64)).mem
      (vs1 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v15))
    (0x23#8) (0xb8#8) (0xf4#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00f4b823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80003464#64) (0x010#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x09#5)
      vs1 v15 hG (rX_bits_x9 _ vs1 hx9₂) (rX_bits_x15 _ v15 hx15₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003468: `ld s2,1056(sp)` → `x18 := *(sp+1056)` (word `0x42013903`). -/
theorem site_80003468_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003468#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x420#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x420#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x420#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x420#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x420#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x18
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003468 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003468#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003468#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003468#64) vminstret (0x42013903#32)
    (instruction.LOAD (0x420#12, regidx.Regidx 0x02#5, regidx.Regidx 0x12#5, false, 8))
    Register.x18 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x39#8) (0x01#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42013903 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003468#64) (0x420#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x12#5)
      (sigma3_alu σ (0x80003468#64) Register.x18
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x18 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000346c: `addi a0,s1,0` (mv a0,s1) → `x10 := x9` (word `0x00048513`). -/
theorem site_8000346c_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000346c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v9 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000346c hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x8000346c#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x8000346c#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_alu σ i u (0x8000346c#64) vminstret (0x00048513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v9 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x85#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00048513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5) v9
      (afterNextPC (afterPrelude σ) (0x8000346c#64))
      (sigma3_alu σ (0x8000346c#64) Register.x10 (v9 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x9 _ v9 hx9₂) (wX_bits_x10 _ (v9 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003470: `ld s1,1064(sp)` → `x9 := *(sp+1064)` (word `0x42813483`). -/
theorem site_80003470_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003470#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x428#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x428#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x428#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x428#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x428#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003470 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003470#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003470#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003470#64) vminstret (0x42813483#32)
    (instruction.LOAD (0x428#12, regidx.Regidx 0x02#5, regidx.Regidx 0x09#5, false, 8))
    Register.x9 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x34#8) (0x81#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42813483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003470#64) (0x428#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x80003470#64) Register.x9
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x9 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003474: `addi sp,sp,1088` → `x2 := sp + 1088` (word `0x44010113`). -/
theorem site_80003474_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003474#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0x440#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003474 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003474#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003474#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80003474#64) vminstret (0x44010113#32)
    (instruction.ITYPE (0x440#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0x440#12)) (0x13#8) (0x01#8) (0x01#8) (0x44#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_44010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x440#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x80003474#64))
      (sigma3_alu σ (0x80003474#64) Register.x2 (vsp + sign_extend (m := 64) (0x440#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x440#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003478: `ret` (`jr x0, 0(ra)`; word `0x00008067`). -/
theorem site_80003478_var
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003478#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003478 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80003478#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80003478#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80003478#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80003478#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-- `Env_getLoaded` survives a `writeMap8` whose window `[a8, a8+8)` is disjoint from
the `env_get` code `[0x80002c10, 0x80002cdc)`.  Consumes the `hcalleeSurv` obligation
of `blockA_k` for the `.var` case (mirrors `loaded_str_writeMap8`). -/
theorem loaded_env_get_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x80002c10 ∨ 0x80002cdc ≤ a8) (h : Env_getLoaded mem) :
    Env_getLoaded (writeMap8 mem a8 d) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [env_getChunk0] at h0 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [env_getChunk1] at h1 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [env_getChunk2] at h2 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [env_getChunk3] at h3 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## `VarSlotPinned` — the `EX_VAR` (tag 4) jump-table slot pin

Slot at `jumpTableBase + 16` holds `dc 94 fe ff` (LE) = offset `0xfffe94dc`, and
`0x80019f58 + (Int32)0xfffe94dc = 0x80003434` (the var arm). Mirrors `StrSlotPinned`;
discharges `KindSlotPinned 4 0x80003434`. -/
def VarSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 16 : Nat)]? = some (0xdc : BitVec 8) ∧
  m[(jumpTableBase + 17 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 18 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 19 : Nat)]? = some (0xff : BitVec 8)

theorem var_slot_kindPinned {m : Mem} (h : VarSlotPinned m) :
    KindSlotPinned 4 (0x80003434#64) m := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨0xdc#8, 0x94#8, 0xfe#8, 0xff#8, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using p0
  · simpa using p1
  · simpa using p2
  · simpa using p3
  · apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide

/-! ## `VarPostCall` — the machine state at the `env_get` link return `0x80003444`

The FOUND-case post of the `env_get` call (`henv_get`, threaded from `EvalVarEntry`;
see the header for why this is an honest, clearly-scoped hypothesis rather than a
composition of existing lemmas). At `0x80003444`, `env_get` has returned with `a0 = 1`
(found ⇒ nonzero, so the `beq` is not taken), and the 24-byte result buffer at
`sp+0xf0` holds `ValueRepr … v` (the value the `EvalE.var` derivation supplies via
`store.get?`). The callee-saved spill slots, `s1 = sret`, the lowered `sp`, the store
representation, the eval_expr code image, the g-frame, the output, and all geometry
survive (no register/heap mutation on the lookup path — `env_get` only wrote the
result buffer). This is exactly what the inlined var-arm epilogue consumes. -/
def VarPostCall
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 mpc : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80003444#64) ∧
  (∃ a0v, c.σ.regs.get? Register.x10 = some a0v ∧ (a0v == (0#64 : BitVec 64)) = false) ∧
  c.σ.regs.get? Register.x9 = some sret ∧               -- s1 = sret
  c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧     -- sp lowered
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
  c.σ.mem = mpc ∧ Eval_exprLoaded mpc ∧
  -- the 24-byte result buffer at `sp+0xf0` holds three words `d0/d1/d2` which, when
  -- copied to `sret`, represent the produced value `v`.  The var arm copies exactly
  -- these three 64-bit words (via `ld a3/a4/a5; sd a3/a4/a5, {0,8,16}(s1)`); this
  -- states that the resulting 24-byte `sret` buffer is `ValueRepr … v`, for ANY
  -- memory that reads back those words at `sret` and agrees with `mpc` elsewhere.
  -- (`env_get`'s FOUND case writes `*out = ValueRepr v`; the arm relocates it to
  -- `sret`.  This is the honest `env_get`-found + relocation obligation.)
  (∃ d0 d1 d2 : BitVec 64,
    read64 mpc (sp.toNat - 1088 + 0xf0) = some d0.toNat ∧
    read64 mpc (sp.toNat - 1088 + 0xf8) = some d1.toNat ∧
    read64 mpc (sp.toNat - 1088 + 0x100) = some d2.toNat ∧
    (∀ m' : Mem, read64 m' sret.toNat = some d0.toNat →
      read64 m' (sret.toNat + 8) = some d1.toNat →
      read64 m' (sret.toNat + 16) = some d2.toNat →
      (∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mpc[k]? = m'[k]?) →
      ValueRepr m' N φc sret.toNat v)) ∧
  -- the store survives any write confined to the sret buffer (env_get did not mutate
  -- the arena; the arm's copy writes only `[sret, sret+24)`).  Same shape as
  -- `EvalStrEntry.store_survives`, restricted to the sret window.
  (∀ m' : Mem,
    (∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mpc[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store) ∧
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x2 == R) = false →
    c.σ.regs.get? R = g R) ∧
  -- the four callee-saved spill slots still hold the entry `ra`/`s0`/`s1`/`s2`.
  read64 mpc (sp.toNat - 8) = some r.toNat ∧
  read64 mpc (sp.toNat - 16) = some v8.toNat ∧
  read64 mpc (sp.toNat - 24) = some v9.toNat ∧
  read64 mpc (sp.toNat - 32) = some v18.toNat ∧
  g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
  g Register.x2 = some sp ∧
  -- memory frame: outside the stack window / arena / sret buffer, `mpc = m0`.
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpc[a]? = m0[a]?) ∧
  -- the result buffer `[sp+0xf0, sp+0x108)` (source of the copy) is disjoint from the
  -- destination sret buffer `[sret, sret+24)`, so the copy does not overwrite its source.
  (sp.toNat - 1088 + 0xf0 + 24 ≤ sret.toNat ∨ sret.toNat + 24 ≤ sp.toNat - 1088 + 0xf0) ∧
  -- geometry the epilogue loads + result-buffer loads need.
  sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ sret.toNat ∧
  0x80000000 ≤ sp.toNat - 1088 + 0xf0 ∧ sp.toNat - 1088 + 0x108 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ sp.toNat - 1088 + 0xf0 ∧ (sp.toNat - 1088 + 0xf0) % 8 = 0 ∧
  1088 ≤ sp.toNat ∧ sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
  tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧ SL.lo + 1088 ≤ sp.toNat ∧ r.toNat % 4 = 0

/-! ## `blockC_var` — the var-arm epilogue (`VarPostCall … v → EvalExit … v`)

The twelve instructions from the `env_get` link return `0x80003444` to the `ret`
`0x80003478`: the not-taken `beq`, the three result-buffer loads, the two initial
epilogue restores (`ld ra`, `ld s0`), the three-word copy of the `Value` into `sret`
(`sd a3/a4/a5, {0,8,16}(s1)`), the remaining restores (`ld s2`, `mv a0,s1`, `ld s1`,
`addi sp,1088`) and `ret`.  Because the epilogue is inlined and interleaved with the
copy, this reaches `EvalExit` directly (it does NOT go through the shared `blockD_v`).

The store frame `σ9.mem` = three `writeMap8`s into `[sret, sret+24)` over `mpc`.  The
`ValueRepr … sret v` conjunct of `EvalExit.result` comes from `VarPostCall`'s copy
obligation applied to `σ9.mem` (which reads back the three copied words at `sret` and
agrees with `mpc` outside `[sret, sret+24)`). `StoreRepr`/`Eval_exprLoaded`/`memFrame`
transfer along the same agreement (the sret buffer is disjoint from the store's arena
window and the code, threaded from `VarPostCall`). -/
/-- Positive small-offset stack address: `((sp-1088) + sext off).toNat = sp.toNat - 1088 + k`
when `sext off = k` (small, `< 0x800`) and `1088 ≤ sp.toNat`. -/
theorem var_off_pos (sp : BitVec 64) (off : BitVec 12) (k : Nat)
    (hoff : (sign_extend (m := 64) off : BitVec 64).toNat = k) (hk : k ≤ 1088)
    (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) off).toNat = sp.toNat - 1088 + k := by
  have hsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h]; have := sp.isLt; omega
  rw [BitVec.toNat_add, hsub, hoff]
  have := sp.isLt
  rw [Nat.mod_eq_of_lt (show sp.toNat - 1088 + k < 2^64 by omega)]

theorem blockC_var
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- the sret buffer is disjoint from the store's arena and from the code region
    -- (so the three copy writes preserve `StoreRepr` and `Eval_exprLoaded`).
    (hsret_arena : sret.toNat + 24 ≤ A.lo ∨ A.hi ≤ sret.toNat)
    (hsret_code : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat)
    (hsret_stack : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) :
    Triple
      (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c)
      (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st v sp r sret m0) := by
  intro c hc
  obtain ⟨mpc, hG, htick, hpc, ⟨a0v, ha0v, ha0vnz⟩, hs1, hsp, ⟨vmi, hmi⟩, hout, houtStr, hmem, hcode,
    ⟨d0, d1, d2, hsrc0, hsrc1, hsrc2, hcopy⟩, hstore, hframe,
    hslotRa, hslotS0, hslotS1, hslotS2, hgx8, hgx9, hgx18, hgx2, hmemframe, hbufsret,
    hsretAl, hsretLo, hsretHi, hsretWin,
    hbufLo, hbufHi, hbufWin, hbufAl,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLloSp, hraAl⟩ := hc
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- addresses of the three source words (positive small offsets from `sp-1088`).
  have hbuf0 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat = sp.toNat - 1088 + 0xf0 :=
    var_off_pos sp (0x0f0#12) 0xf0 (by decide) (by omega) hsp1088
  have hbuf1 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat = sp.toNat - 1088 + 0xf8 :=
    var_off_pos sp (0x0f8#12) 0xf8 (by decide) (by omega) hsp1088
  have hbuf2 : ((sp - 1088#64) + sign_extend (m := 64) (0x100#12)).toNat = sp.toNat - 1088 + 0x100 :=
    var_off_pos sp (0x100#12) 0x100 (by decide) (by omega) hsp1088
  -- addresses of the four epilogue restore slots (`sp - k`).
  have haRa : ((sp - 1088#64) + sign_extend (m := 64) (0x438#12)).toNat = sp.toNat - 8 := epi_off438 sp hsp1088
  have haS0 : ((sp - 1088#64) + sign_extend (m := 64) (0x430#12)).toNat = sp.toNat - 16 := epi_off430 sp hsp1088
  have haS2 : ((sp - 1088#64) + sign_extend (m := 64) (0x420#12)).toNat = sp.toNat - 32 := epi_off420 sp hsp1088
  have haS1 : ((sp - 1088#64) + sign_extend (m := 64) (0x428#12)).toNat = sp.toNat - 24 := epi_off428 sp hsp1088
  -- source-word byte facts (for the three result loads).
  obtain ⟨d0b0, d0b1, d0b2, d0b3, d0b4, d0b5, d0b6, d0b7, hd0b0, hd0b1, hd0b2, hd0b3, hd0b4, hd0b5, hd0b6, hd0b7, hd0Sext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 1088 + 0xf0) d0 hsrc0
  obtain ⟨d1b0, d1b1, d1b2, d1b3, d1b4, d1b5, d1b6, d1b7, hd1b0, hd1b1, hd1b2, hd1b3, hd1b4, hd1b5, hd1b6, hd1b7, hd1Sext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 1088 + 0xf8) d1 hsrc1
  obtain ⟨d2b0, d2b1, d2b2, d2b3, d2b4, d2b5, d2b6, d2b7, hd2b0, hd2b1, hd2b2, hd2b3, hd2b4, hd2b5, hd2b6, hd2b7, hd2Sext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 1088 + 0x100) d2 hsrc2
  -- epilogue-slot byte facts.
  obtain ⟨ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, hra0, hra1, hra2, hra3, hra4, hra5, hra6, hra7, hraSext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 8) r hslotRa
  obtain ⟨s00, s01, s02, s03, s04, s05, s06, s07, hs00, hs01, hs02, hs03, hs04, hs05, hs06, hs07, hs0Sext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 16) v8 hslotS0
  obtain ⟨s20, s21, s22, s23, s24, s25, s26, s27, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27, hs2Sext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 32) v18 hslotS2
  obtain ⟨s10, s11, s12, s13, s14, s15, s16, s17, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs1Sext⟩ :=
    spill_roundtrip_ee mpc (sp.toNat - 24) v9 hslotS1
  -- ============ 0x80003444: beq a0,x0 NOT taken ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80003444_nottaken_var c.σ c.tick c.steps (0x80003444#64) vmi a0v hG hpc hmi ha0v (hmem ▸ hcode) rfl ha0vnz htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hstep1'
  have hmem1e : σ1.mem = mpc := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003448#64) := by
    have := obs_bnottaken_pc hobs1
    rwa [show BitVec.addInt (0x80003444#64) 4 = (0x80003448#64:BitVec 64) from by decide] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_bnottaken_other' hobs1 Register.x9 (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) := obs_bnottaken_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_bnottaken_minstret hobs1
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x80003448: ld a3,0xf0(sp) → x13 := d0 ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003448_var σ1 i1 (c.steps + 1) (0x80003448#64) vmi1 (sp-1088#64)
      d0b0 d0b1 d0b2 d0b3 d0b4 d0b5 d0b6 d0b7 hG1 hpc1 hmi1 hsp_1 hcode1 rfl
      (by rw [hbuf0]; omega) (by rw [hbuf0]; omega) (by rw [hbuf0, htoh]; right; omega) (by rw [hbuf0]; omega)
      (by rw [hbuf0, hmem1e]; exact hd0b0) (by rw [hbuf0, hmem1e]; exact hd0b1) (by rw [hbuf0, hmem1e]; exact hd0b2)
      (by rw [hbuf0, hmem1e]; exact hd0b3) (by rw [hbuf0, hmem1e]; exact hd0b4) (by rw [hbuf0, hmem1e]; exact hd0b5)
      (by rw [hbuf0, hmem1e]; exact hd0b6) (by rw [hbuf0, hmem1e]; exact hd0b7) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps+1⟩ ⟨σ2, i2, c.steps+1+1⟩ := hstep2'
  have hmem2e : σ2.mem = mpc := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000344c#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80003448#64) 4 = (0x8000344c#64:BitVec 64) from by decide] at this
  have hx13_2 : σ2.regs.get? Register.x13 = some d0 := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hd0Sext] at this
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x8000344c: ld a4,0xf8(sp) → x14 := d1 ============
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_8000344c_var σ2 i2 (c.steps + 1 + 1) (0x8000344c#64) vmi2 (sp-1088#64)
      d1b0 d1b1 d1b2 d1b3 d1b4 d1b5 d1b6 d1b7 hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [hbuf1]; omega) (by rw [hbuf1]; omega) (by rw [hbuf1, htoh]; right; omega) (by rw [hbuf1]; omega)
      (by rw [hbuf1, hmem2e]; exact hd1b0) (by rw [hbuf1, hmem2e]; exact hd1b1) (by rw [hbuf1, hmem2e]; exact hd1b2)
      (by rw [hbuf1, hmem2e]; exact hd1b3) (by rw [hbuf1, hmem2e]; exact hd1b4) (by rw [hbuf1, hmem2e]; exact hd1b5)
      (by rw [hbuf1, hmem2e]; exact hd1b6) (by rw [hbuf1, hmem2e]; exact hd1b7) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps+1+1⟩ ⟨σ3, i3, c.steps+1+1+1⟩ := hstep3'
  have hmem3e : σ3.mem = mpc := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003450#64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x8000344c#64) 4 = (0x80003450#64:BitVec 64) from by decide] at this
  have hx14_3 : σ3.regs.get? Register.x14 = some d1 := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hd1Sext] at this
  have hx13_3 : σ3.regs.get? Register.x13 = some d0 := obs_alu_other' hobs3 Register.x13 (by decide) hx13_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- ============ 0x80003450: ld a5,0x100(sp) → x15 := d2 ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80003450_var σ3 i3 (c.steps + 1 + 1 + 1) (0x80003450#64) vmi3 (sp-1088#64)
      d2b0 d2b1 d2b2 d2b3 d2b4 d2b5 d2b6 d2b7 hG3 hpc3 hmi3 hsp_3 hcode3 rfl
      (by rw [hbuf2]; omega) (by rw [hbuf2]; omega) (by rw [hbuf2, htoh]; right; omega) (by rw [hbuf2]; omega)
      (by rw [hbuf2, hmem3e]; exact hd2b0) (by rw [hbuf2, hmem3e]; exact hd2b1) (by rw [hbuf2, hmem3e]; exact hd2b2)
      (by rw [hbuf2, hmem3e]; exact hd2b3) (by rw [hbuf2, hmem3e]; exact hd2b4) (by rw [hbuf2, hmem3e]; exact hd2b5)
      (by rw [hbuf2, hmem3e]; exact hd2b6) (by rw [hbuf2, hmem3e]; exact hd2b7) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps+1+1+1⟩ ⟨σ4, i4, c.steps+1+1+1+1⟩ := hstep4'
  have hmem4e : σ4.mem = mpc := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x80003454#64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80003450#64) 4 = (0x80003454#64:BitVec 64) from by decide] at this
  have hx15_4 : σ4.regs.get? Register.x15 = some d2 := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hd2Sext] at this
  have hx13_4 : σ4.regs.get? Register.x13 = some d0 := obs_alu_other' hobs4 Register.x13 (by decide) hx13_3
  have hx14_4 : σ4.regs.get? Register.x14 = some d1 := obs_alu_other' hobs4 Register.x14 (by decide) hx14_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_alu_other' hobs4 Register.x9 (by decide) hs1_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- ============ 0x80003454: ld ra,1080(sp) → x1 := r ============
  obtain ⟨σ5, i5, hstep5', hi5, hG5, hmem5, hobs5⟩ :=
    site_80003454_var σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80003454#64) vmi4 (sp-1088#64)
      ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haRa]; omega) (by rw [haRa]; omega) (by rw [haRa, htoh]; right; omega) (by rw [haRa]; omega)
      (by rw [haRa, hmem4e]; exact hra0) (by rw [haRa, hmem4e]; exact hra1) (by rw [haRa, hmem4e]; exact hra2)
      (by rw [haRa, hmem4e]; exact hra3) (by rw [haRa, hmem4e]; exact hra4) (by rw [haRa, hmem4e]; exact hra5)
      (by rw [haRa, hmem4e]; exact hra6) (by rw [haRa, hmem4e]; exact hra7) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps+1+1+1+1⟩ ⟨σ5, i5, c.steps+1+1+1+1+1⟩ := hstep5'
  have hmem5e : σ5.mem = mpc := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003458#64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80003454#64) 4 = (0x80003458#64:BitVec 64) from by decide] at this
  have hra_5 : σ5.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hraSext] at this
  have hx13_5 : σ5.regs.get? Register.x13 = some d0 := obs_alu_other' hobs5 Register.x13 (by decide) hx13_4
  have hx14_5 : σ5.regs.get? Register.x14 = some d1 := obs_alu_other' hobs5 Register.x14 (by decide) hx14_4
  have hx15_5 : σ5.regs.get? Register.x15 = some d2 := obs_alu_other' hobs5 Register.x15 (by decide) hx15_4
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_alu_other' hobs5 Register.x9 (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  -- ============ 0x80003458: ld s0,1072(sp) → x8 := v8 ============
  obtain ⟨σ6, i6, hstep6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80003458_var σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80003458#64) vmi5 (sp-1088#64)
      s00 s01 s02 s03 s04 s05 s06 s07 hG5 hpc5 hmi5 hsp_5 hcode5 rfl
      (by rw [haS0]; omega) (by rw [haS0]; omega) (by rw [haS0, htoh]; right; omega) (by rw [haS0]; omega)
      (by rw [haS0, hmem5e]; exact hs00) (by rw [haS0, hmem5e]; exact hs01) (by rw [haS0, hmem5e]; exact hs02)
      (by rw [haS0, hmem5e]; exact hs03) (by rw [haS0, hmem5e]; exact hs04) (by rw [haS0, hmem5e]; exact hs05)
      (by rw [haS0, hmem5e]; exact hs06) (by rw [haS0, hmem5e]; exact hs07) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps+1+1+1+1+1⟩ ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ := hstep6'
  have hmem6e : σ6.mem = mpc := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000345c#64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80003458#64) 4 = (0x8000345c#64:BitVec 64) from by decide] at this
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs0Sext] at this
  have hx13_6 : σ6.regs.get? Register.x13 = some d0 := obs_alu_other' hobs6 Register.x13 (by decide) hx13_5
  have hx14_6 : σ6.regs.get? Register.x14 = some d1 := obs_alu_other' hobs6 Register.x14 (by decide) hx14_5
  have hx15_6 : σ6.regs.get? Register.x15 = some d2 := obs_alu_other' hobs6 Register.x15 (by decide) hx15_5
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other' hobs6 Register.x9 (by decide) hs1_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs6 Register.x2 (by decide) hsp_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  -- ============ 0x8000345c: sd a3,0(s1) → mem[sret] := d0 ============
  have hsret0 : (sret + sign_extend (m := 64) (0x000#12)).toNat = sret.toNat := by
    rw [sext_zero, BitVec.add_zero]
  obtain ⟨σ7, i7, hstep7', hi7, hG7, hmem7, hobs7⟩ :=
    site_8000345c_var σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x8000345c#64) vmi6 sret d0
      hG6 hpc6 hmi6 hs1_6 hx13_6 hcode6 rfl
      (by rw [hsret0]; omega) (by rw [hsret0]; omega) (by rw [hsret0, htoh]; omega) (by rw [hsret0]; omega) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ ⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩ := hstep7'
  have hmem7e : σ7.mem = writeMap8 mpc sret.toNat (sdData_val d0) := by
    rw [hmem7, mem_afterNextPC, hsret0, hmem6e]
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003460#64) := by
    have := obs_store_pc_val hobs7; rwa [show BitVec.addInt (0x8000345c#64) 4 = (0x80003460#64:BitVec 64) from by decide] at this
  have hx14_7 : σ7.regs.get? Register.x14 = some d1 := obs_store_other_val' hobs7 Register.x14 (by decide) hx14_6
  have hx15_7 : σ7.regs.get? Register.x15 = some d2 := obs_store_other_val' hobs7 Register.x15 (by decide) hx15_6
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_store_other_val' hobs7 Register.x1 (by decide) hra_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 := obs_store_other_val' hobs7 Register.x8 (by decide) hx8_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_store_other_val' hobs7 Register.x9 (by decide) hs1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs7 Register.x2 (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret_val hobs7
  have hcode7w : Eval_exprLoaded (writeMap8 mpc sret.toNat (sdData_val d0)) :=
    loaded_eval_expr_agreeP mpc _ (fun k hk => (getElem_writeMap8_disjoint mpc sret.toNat k (sdData_val d0) (by rcases hsret_code with h|h <;> omega)).symm) hcode
  have hcode7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode7w
  -- ============ 0x80003460: sd a4,8(s1) → mem[sret+8] := d1 ============
  have hsret8 : (sret + sign_extend (m := 64) (0x008#12)).toNat = sret.toNat + 8 := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 from by decide]
    rw [Nat.mod_eq_of_lt (show sret.toNat + 8 < 2^64 by omega)]
  obtain ⟨σ8, i8, hstep8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80003460_var σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003460#64) vmi7 sret d1
      hG7 hpc7 hmi7 hs1_7 hx14_7 hcode7 rfl
      (by rw [hsret8]; omega) (by rw [hsret8]; omega) (by rw [hsret8, htoh]; omega) (by rw [hsret8]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩ ⟨σ8, i8, c.steps+1+1+1+1+1+1+1+1⟩ := hstep8'
  have hmem8e : σ8.mem = writeMap8 (writeMap8 mpc sret.toNat (sdData_val d0)) (sret.toNat + 8) (sdData_val d1) := by
    rw [hmem8, mem_afterNextPC, hsret8, hmem7e]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80003464#64) := by
    have := obs_store_pc_val hobs8; rwa [show BitVec.addInt (0x80003460#64) 4 = (0x80003464#64:BitVec 64) from by decide] at this
  have hx15_8 : σ8.regs.get? Register.x15 = some d2 := obs_store_other_val' hobs8 Register.x15 (by decide) hx15_7
  have hra_8 : σ8.regs.get? Register.x1 = some r := obs_store_other_val' hobs8 Register.x1 (by decide) hra_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 := obs_store_other_val' hobs8 Register.x8 (by decide) hx8_7
  have hs1_8 : σ8.regs.get? Register.x9 = some sret := obs_store_other_val' hobs8 Register.x9 (by decide) hs1_7
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs8 Register.x2 (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret_val hobs8
  have hcode8w : Eval_exprLoaded (writeMap8 (writeMap8 mpc sret.toNat (sdData_val d0)) (sret.toNat + 8) (sdData_val d1)) :=
    loaded_eval_expr_agreeP _ _ (fun k hk => (getElem_writeMap8_disjoint _ (sret.toNat + 8) k (sdData_val d1) (by rcases hsret_code with h|h <;> omega)).symm) hcode7w
  have hcode8 : Eval_exprLoaded σ8.mem := by rw [hmem8e]; exact hcode8w
  -- ============ 0x80003464: sd a5,16(s1) → mem[sret+16] := d2 ============
  have hsret16 : (sret + sign_extend (m := 64) (0x010#12)).toNat = sret.toNat + 16 := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 from by decide]
    rw [Nat.mod_eq_of_lt (show sret.toNat + 16 < 2^64 by omega)]
  obtain ⟨σ9, i9, hstep9', hi9, hG9, hmem9, hobs9⟩ :=
    site_80003464_var σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003464#64) vmi8 sret d2
      hG8 hpc8 hmi8 hs1_8 hx15_8 hcode8 rfl
      (by rw [hsret16]; omega) (by rw [hsret16]; omega) (by rw [hsret16, htoh]; omega) (by rw [hsret16]; omega) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps+1+1+1+1+1+1+1+1⟩ ⟨σ9, i9, c.steps+1+1+1+1+1+1+1+1+1⟩ := hstep9'
  have hmem9e : σ9.mem = writeMap8 (writeMap8 (writeMap8 mpc sret.toNat (sdData_val d0)) (sret.toNat + 8) (sdData_val d1)) (sret.toNat + 16) (sdData_val d2) := by
    rw [hmem9, mem_afterNextPC, hsret16, hmem8e]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80003468#64) := by
    have := obs_store_pc_val hobs9; rwa [show BitVec.addInt (0x80003464#64) 4 = (0x80003468#64:BitVec 64) from by decide] at this
  have hra_9 : σ9.regs.get? Register.x1 = some r := obs_store_other_val' hobs9 Register.x1 (by decide) hra_8
  have hx8_9 : σ9.regs.get? Register.x8 = some v8 := obs_store_other_val' hobs9 Register.x8 (by decide) hx8_8
  have hs1_9 : σ9.regs.get? Register.x9 = some sret := obs_store_other_val' hobs9 Register.x9 (by decide) hs1_8
  have hsp_9 : σ9.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs9 Register.x2 (by decide) hsp_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_val hobs9
  have hcode9 : Eval_exprLoaded σ9.mem := by
    rw [hmem9e]
    exact loaded_eval_expr_agreeP _ _ (fun k hk => (getElem_writeMap8_disjoint _ (sret.toNat + 16) k (sdData_val d2) (by rcases hsret_code with h|h <;> omega)).symm) hcode8w
  -- `σ9.mem` agrees with `mpc` outside `[sret, sret+24)` (the three writes stack).
  have hmfinAgree : ∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mpc[k]? = σ9.mem[k]? := by
    intro k hk
    rw [hmem9e, getElem_writeMap8_disjoint _ (sret.toNat + 16) k (sdData_val d2) (by omega),
      getElem_writeMap8_disjoint _ (sret.toNat + 8) k (sdData_val d1) (by omega),
      getElem_writeMap8_disjoint _ sret.toNat k (sdData_val d0) (by omega)]
  -- `σ9.mem` reads back the three copied words at `sret`.
  have hmfinRd0 : read64 σ9.mem sret.toNat = some d0.toNat := by
    rw [hmem9e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega), read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
      read64_writeMap8, sdData_toNat]
  have hmfinRd1 : read64 σ9.mem (sret.toNat + 8) = some d1.toNat := by
    rw [hmem9e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
  have hmfinRd2 : read64 σ9.mem (sret.toNat + 16) = some d2.toNat := by
    rw [hmem9e, read64_writeMap8, sdData_toNat]
  -- the produced value is represented at `sret` in `σ9.mem` (env_get-found copy obligation).
  have hvalFin : ValueRepr σ9.mem N φc sret.toNat v :=
    hcopy σ9.mem hmfinRd0 hmfinRd1 hmfinRd2 hmfinAgree
  -- store representation survives the sret writes (via the survival function).
  have hstoreFin : StoreRepr σ9.mem N A φf φc st.store :=
    hstore σ9.mem (fun k hk => hmfinAgree k hk)
  -- the four spill slots survive (disjoint from sret buffer).
  have hslotRaFin : read64 σ9.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP (P := fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24))
      (fun k hk => hmfinAgree k hk) (fun j hj => by rcases hsret_stack with h|h <;> omega)]; exact hslotRa
  have hslotS0Fin : read64 σ9.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP (P := fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24))
      (fun k hk => hmfinAgree k hk) (fun j hj => by rcases hsret_stack with h|h <;> omega)]; exact hslotS0
  have hslotS1Fin : read64 σ9.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP (P := fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24))
      (fun k hk => hmfinAgree k hk) (fun j hj => by rcases hsret_stack with h|h <;> omega)]; exact hslotS1
  have hslotS2Fin : read64 σ9.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP (P := fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24))
      (fun k hk => hmfinAgree k hk) (fun j hj => by rcases hsret_stack with h|h <;> omega)]; exact hslotS2
  -- fresh byte facts on `σ9.mem` for the two remaining epilogue-slot loads.
  obtain ⟨t20, t21, t22, t23, t24, t25, t26, t27, ht20, ht21, ht22, ht23, ht24, ht25, ht26, ht27, ht2Sext⟩ :=
    spill_roundtrip_ee σ9.mem (sp.toNat - 32) v18 hslotS2Fin
  obtain ⟨t10, t11, t12, t13, t14, t15, t16, t17, ht10, ht11, ht12, ht13, ht14, ht15, ht16, ht17, ht1Sext⟩ :=
    spill_roundtrip_ee σ9.mem (sp.toNat - 24) v9 hslotS1Fin
  -- ============ 0x80003468: ld s2,1056(sp) → x18 := v18 ============
  obtain ⟨σ10, i10, hstep10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80003468_var σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003468#64) vmi9 (sp-1088#64)
      t20 t21 t22 t23 t24 t25 t26 t27 hG9 hpc9 hmi9 hsp_9 hcode9 rfl
      (by rw [haS2]; omega) (by rw [haS2]; omega) (by rw [haS2, htoh]; right; omega) (by rw [haS2]; omega)
      (by rw [haS2]; exact ht20) (by rw [haS2]; exact ht21) (by rw [haS2]; exact ht22)
      (by rw [haS2]; exact ht23) (by rw [haS2]; exact ht24) (by rw [haS2]; exact ht25)
      (by rw [haS2]; exact ht26) (by rw [haS2]; exact ht27) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps+1+1+1+1+1+1+1+1+1⟩ ⟨σ10, i10, c.steps+1+1+1+1+1+1+1+1+1+1⟩ := hstep10'
  have hmem10e : σ10.mem = σ9.mem := hmem10
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000346c#64) := by
    have := obs_alu_pc hobs10; rwa [show BitVec.addInt (0x80003468#64) 4 = (0x8000346c#64:BitVec 64) from by decide] at this
  have hx18_10 : σ10.regs.get? Register.x18 = some v18 := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [ht2Sext] at this
  have hra_10 : σ10.regs.get? Register.x1 = some r := obs_alu_other' hobs10 Register.x1 (by decide) hra_9
  have hx8_10 : σ10.regs.get? Register.x8 = some v8 := obs_alu_other' hobs10 Register.x8 (by decide) hx8_9
  have hs1_10 : σ10.regs.get? Register.x9 = some sret := obs_alu_other' hobs10 Register.x9 (by decide) hs1_9
  have hsp_10 : σ10.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs10 Register.x2 (by decide) hsp_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hcode10 : Eval_exprLoaded σ10.mem := by rw [hmem10e]; exact hcode9
  -- ============ 0x8000346c: mv a0,s1 → x10 := sret ============
  obtain ⟨σ11, i11, hstep11', hi11, hG11, hmem11, hobs11⟩ :=
    site_8000346c_var σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000346c#64) vmi10 sret
      hG10 hpc10 hmi10 hs1_10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11, i11, c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep11'
  have hmem11e : σ11.mem = σ9.mem := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80003470#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x8000346c#64) 4 = (0x80003470#64:BitVec 64) from by decide] at this
  have ha0_11 : σ11.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by rw [sext_zero, BitVec.add_zero]] at this
  have hra_11 : σ11.regs.get? Register.x1 = some r := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
  have hx8_11 : σ11.regs.get? Register.x8 = some v8 := obs_alu_other' hobs11 Register.x8 (by decide) hx8_10
  have hx18_11 : σ11.regs.get? Register.x18 = some v18 := obs_alu_other' hobs11 Register.x18 (by decide) hx18_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs11 Register.x2 (by decide) hsp_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hcode11 : Eval_exprLoaded σ11.mem := by rw [hmem11e]; exact hcode9
  -- ============ 0x80003470: ld s1,1064(sp) → x9 := v9 ============
  obtain ⟨σ12, i12, hstep12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80003470_var σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003470#64) vmi11 (sp-1088#64)
      t10 t11 t12 t13 t14 t15 t16 t17 hG11 hpc11 hmi11 hsp_11 hcode11 rfl
      (by rw [haS1]; omega) (by rw [haS1]; omega) (by rw [haS1, htoh]; right; omega) (by rw [haS1]; omega)
      (by rw [haS1, hmem11e]; exact ht10) (by rw [haS1, hmem11e]; exact ht11) (by rw [haS1, hmem11e]; exact ht12)
      (by rw [haS1, hmem11e]; exact ht13) (by rw [haS1, hmem11e]; exact ht14) (by rw [haS1, hmem11e]; exact ht15)
      (by rw [haS1, hmem11e]; exact ht16) (by rw [haS1, hmem11e]; exact ht17) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12, i12, c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep12'
  have hmem12e : σ12.mem = σ9.mem := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x80003474#64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80003470#64) 4 = (0x80003474#64:BitVec 64) from by decide] at this
  have hx9_12 : σ12.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [ht1Sext] at this
  have ha0_12 : σ12.regs.get? Register.x10 = some sret := obs_alu_other' hobs12 Register.x10 (by decide) ha0_11
  have hra_12 : σ12.regs.get? Register.x1 = some r := obs_alu_other' hobs12 Register.x1 (by decide) hra_11
  have hx8_12 : σ12.regs.get? Register.x8 = some v8 := obs_alu_other' hobs12 Register.x8 (by decide) hx8_11
  have hx18_12 : σ12.regs.get? Register.x18 = some v18 := obs_alu_other' hobs12 Register.x18 (by decide) hx18_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs12 Register.x2 (by decide) hsp_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hcode12 : Eval_exprLoaded σ12.mem := by rw [hmem12e]; exact hcode9
  -- ============ 0x80003474: addi sp,sp,1088 → x2 := sp ============
  obtain ⟨σ13, i13, hstep13', hi13, hG13, hmem13, hobs13⟩ :=
    site_80003474_var σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003474#64) vmi12 (sp-1088#64)
      hG12 hpc12 hmi12 hsp_12 hcode12 rfl hi12
  have hstep13 : Step ⟨σ12, i12, c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13, i13, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep13'
  have hmem13e : σ13.mem = σ9.mem := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x80003478#64) := by
    have := obs_alu_pc hobs13; rwa [show BitVec.addInt (0x80003474#64) 4 = (0x80003478#64:BitVec 64) from by decide] at this
  have hsp_13 : σ13.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [sp_add1088] at this
  have ha0_13 : σ13.regs.get? Register.x10 = some sret := obs_alu_other' hobs13 Register.x10 (by decide) ha0_12
  have hra_13 : σ13.regs.get? Register.x1 = some r := obs_alu_other' hobs13 Register.x1 (by decide) hra_12
  have hx8_13 : σ13.regs.get? Register.x8 = some v8 := obs_alu_other' hobs13 Register.x8 (by decide) hx8_12
  have hx9_13 : σ13.regs.get? Register.x9 = some v9 := obs_alu_other' hobs13 Register.x9 (by decide) hx9_12
  have hx18_13 : σ13.regs.get? Register.x18 = some v18 := obs_alu_other' hobs13 Register.x18 (by decide) hx18_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hcode13 : Eval_exprLoaded σ13.mem := by rw [hmem13e]; exact hcode9
  -- ============ 0x80003478: ret → PC := r ============
  have hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r hraAl]; exact hraAl
  obtain ⟨σ14, i14, hstep14', hi14, hG14, hmem14, hobs14⟩ :=
    site_80003478_var σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003478#64) vmi13 r
      hG13 hpc13 hmi13 hra_13 hcode13 rfl hrettgt hi13
  have hstep14 : Step ⟨σ13, i13, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14, i14, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep14'
  have hmem14e : σ14.mem = σ9.mem := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) := obs_jr_pc hobs14
  have ha0_14 : σ14.regs.get? Register.x10 = some sret := obs_jr_other' hobs14 Register.x10 (by decide) ha0_13
  have hra_14 : σ14.regs.get? Register.x1 = some r := obs_jr_other' hobs14 Register.x1 (by decide) hra_13
  have hsp_14 : σ14.regs.get? Register.x2 = some sp := obs_jr_other' hobs14 Register.x2 (by decide) hsp_13
  have hx8_14 : σ14.regs.get? Register.x8 = some v8 := obs_jr_other' hobs14 Register.x8 (by decide) hx8_13
  have hx9_14 : σ14.regs.get? Register.x9 = some v9 := obs_jr_other' hobs14 Register.x9 (by decide) hx9_13
  have hx18_14 : σ14.regs.get? Register.x18 = some v18 := obs_jr_other' hobs14 Register.x18 (by decide) hx18_13
  obtain ⟨vmi14, hmi14⟩ := obs_jr_minstret hobs14
  -- output invariance across the whole block.
  have hout14 : σ14.sailOutput = out0 := by
    rw [hobs14.out, sailOutput_sigmaPost_jump_x0, hobs13.out, sailOutput_sigmaPost_alu,
      hobs12.out, sailOutput_sigmaPost_alu, hobs11.out, sailOutput_sigmaPost_alu,
      hobs10.out, sailOutput_sigmaPost_alu, hobs9.out, sailOutput_sigmaPost_store,
      hobs8.out, sailOutput_sigmaPost_store, hobs7.out, sailOutput_sigmaPost_store,
      hobs6.out, sailOutput_sigmaPost_alu, hobs5.out, sailOutput_sigmaPost_alu,
      hobs4.out, sailOutput_sigmaPost_alu, hobs3.out, sailOutput_sigmaPost_alu,
      hobs2.out, sailOutput_sigmaPost_alu, hobs1.out, sailOutput_sigmaPost_branch_nottaken]; exact hout
  -- the full step chain.
  have hsteps : Steps c ⟨σ14, i14, _⟩ :=
    (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans (Steps.single hstep14)))))))))))))
  -- the epilogue register frame: every AbiPreservedNoise R restored to `g R`.
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  refine ⟨⟨σ14, i14, _⟩, hsteps, hG14, hi14, hpc14, ha0_14, hra_14, hsp_14, ⟨_, hmi14⟩,
    ⟨φc, PhiExtends.refl _ _, hmem14e ▸ hvalFin⟩,
    ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hmem14e ▸ hstoreFin⟩,
    ?_, ?_, ?_⟩
  · -- OutRepr σ14 st
    show Vsa.Machine.output σ14 = st.out
    simp only [Vsa.Machine.output]; rw [hout14]; exact houtStr
  · -- EvalExit.frame: AbiPreservedNoise R = g R at exit
    intro R hR
    by_cases h8 : (Register.x8 == R) = true
    · have : R = Register.x8 := by rw [beq_iff_eq] at h8; exact h8.symm
      subst this; rw [hx8_14]; exact hgx8.symm
    by_cases h9 : (Register.x9 == R) = true
    · have : R = Register.x9 := by rw [beq_iff_eq] at h9; exact h9.symm
      subst this; rw [hx9_14]; exact hgx9.symm
    by_cases h18 : (Register.x18 == R) = true
    · have : R = Register.x18 := by rw [beq_iff_eq] at h18; exact h18.symm
      subst this; rw [hx18_14]; exact hgx18.symm
    by_cases h2 : (Register.x2 == R) = true
    · have : R = Register.x2 := by rw [beq_iff_eq] at h2; exact h2.symm
      subst this; rw [hsp_14]; exact hgx2.symm
    · -- x1 (not AbiPreserved), x10 (a0 = sret), x13/x14/x15 (scratch) do not overlap
      -- AbiPreservedNoise besides s0/s1/s2/sp — every remaining `g R` came through
      -- the block untouched, i.e. `= c.σ.regs.get? R` (via the frame carried from
      -- `VarPostCall`).  Reduce to the not-taken/alu/store frame chain.
      have hab : AbiPreserved R = true := hR.1
      have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hab
      have h13 : (Register.x13 == R) = false := abi_ne' (by decide) hab
      have h14' : (Register.x14 == R) = false := abi_ne' (by decide) hab
      have h15 : (Register.x15 == R) = false := abi_ne' (by decide) hab
      have h1 : (Register.x1 == R) = false := abi_ne' (by decide) hab
      have h8f : (Register.x8 == R) = false := by simpa using h8
      have h9f : (Register.x9 == R) = false := by simpa using h9
      have h18f : (Register.x18 == R) = false := by simpa using h18
      have h2f : (Register.x2 == R) = false := by simpa using h2
      obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
      -- carry `R` unchanged through all 14 sites (it is none of the written regs).
      have fa : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {w : RegisterType rd},
          ReadsLikePost σb (sigmaPost_alu σa pc vm rd w) → (rd == R) = false →
          σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
        (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hrd hnpc' hmii')
      have fs : ∀ {σa σb : MState} {pc vm : BitVec 64} {m' : Mem},
          ReadsLikePost σb (sigmaPost_store σa pc vm m') →
          σb.regs.get? R = σa.regs.get? R := fun ho =>
        (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
      have fb : ∀ {σa σb : MState} {pc vm : BitVec 64},
          ReadsLikePost σb (sigmaPost_branch_nottaken σa pc vm) →
          σb.regs.get? R = σa.regs.get? R := fun ho =>
        (ho.1 R hmc' hmt' hmip').trans (post_branch_nottaken_other _ _ _ R hmi' hpc' hnpc' hmii')
      have fj : ∀ {σa σb : MState} {pc vm tgt : BitVec 64},
          ReadsLikePost σb (sigmaPost_jump_x0 σa pc vm tgt) →
          σb.regs.get? R = σa.regs.get? R := fun ho =>
        (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
      have hchain : σ14.regs.get? R = c.σ.regs.get? R :=
        (fj hobs14).trans ((fa hobs13 h2f).trans ((fa hobs12 h9f).trans ((fa hobs11 h10).trans
          ((fa hobs10 h18f).trans ((fs hobs9).trans ((fs hobs8).trans ((fs hobs7).trans
          ((fa hobs6 h8f).trans ((fa hobs5 h1).trans ((fa hobs4 h15).trans ((fa hobs3 h14').trans
          ((fa hobs2 h13).trans (fb hobs1)))))))))))))
      rw [hchain]
      exact hframe R ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ h8f h9f h18f h2f
  · -- EvalExit.memFrame: outside stack/arena, exit mem = m0.
    intro a hstk harena
    rw [hmem14e]
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · exact Or.inr ((hmfinAgree a hsr).symm.trans (by
        rcases hmemframe a hstk harena with h | h
        · exact absurd h hsr
        · exact h))

/-! ## `EvalVarEntry` — the machine precondition for the `EvalE.var` case

Mirrors `EvalStrEntry`'s shared geometry, but carries `VarSlotPinned` + `Env_getLoaded`
(the arm's callee) in place of the str-specific slot/callee, `ExprRepr … (.var x)`, and
— the field unique to `.var` — the **`env_get` FOUND-case contract** `env_get_found`
as an honest, clearly-scoped `Triple` (see the header): from the var arm's entry it
reaches the link return `0x80003444` with `a0 = 1`, the 24-byte result buffer at
`sp+0xf0` copying to `sret` as `ValueRepr … v`, and all invariants preserved.  The
found value `v = st.store.get? env x` is supplied by the `EvalE.var` derivation. -/
structure EvalVarEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Vsa.While.Addr) (x : String) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)
  a0 : c.σ.regs.get? Register.x10 = some sret
  a1 : c.σ.regs.get? Register.x11 = some aEnv
  a2 : c.σ.regs.get? Register.x12 = some aExpr
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  spReg : c.σ.regs.get? Register.x2 = some sp
  stackOK : StackOK SL sp (1088 + 1088)
  stackBudget : StackOK SL sp
    ((Expr.var x).stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  expr_bodies : Expr.bodiesBound Vsa.While.perCallBudget (Expr.var x) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = m0
  code : InterpCodeLoaded c.σ.mem
  expr : ExprRepr c.σ.mem aExpr.toNat (.var x)
  store : StoreRepr c.σ.mem N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr c.σ st
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  code_stack_disjoint : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  expr_stack_disjoint : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  expr_align : aExpr.toNat % 8 = 0
  expr_ram : 0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000
  expr_win : tohostAddr + 16 ≤ aExpr.toNat
  /-- The var-name CString bytes `[p, p + x.length]` (at `p = read64 m0 (aExpr+8)`)
  are disjoint from the live stack frame `[SL.lo, sp)` — the name lives in
  `.rodata`/heap.  Makes the `CString m0 p x` survive the prologue spills. -/
  var_stack_disjoint : ∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
    p + x.length < SL.lo ∨ sp.toNat ≤ p
  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  /-- sret disjoint from the store's arena (the copy writes only `[sret, sret+24)`). -/
  sret_arena_disjoint : sret.toNat + 24 ≤ A.lo ∨ A.hi ≤ sret.toNat
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  env_get_code : Env_getLoaded c.σ.mem
  /-- `env_get` code `[0x80002c10, 0x80002cdc)` disjoint from the live stack. -/
  env_get_stack_disjoint : (0x80002cdc : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80002c10
  var_slot : VarSlotPinned c.σ.mem
  table_stack_disjoint : (0x80019f58 : Nat) + 20 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 16
  spill_defined : (∃ w, c.σ.regs.get? Register.x8 = some w) ∧
    (∃ w, c.σ.regs.get? Register.x9 = some w) ∧ (∃ w, c.σ.regs.get? Register.x18 = some w)
  /-- **The `env_get` FOUND-case contract** (honest hypothesis).  From the var arm's
  dispatch entry (`ArmEntryK` at `0x80003434`) the argument-setup + `env_get` call
  reaches `VarPostCall` at the link return `0x80003444` (found ⇒ `a0=1`, result buffer
  at `sp+0xf0` copies to `sret` as `ValueRepr … v`).  Discharged by `env_get`'s full
  end-to-end spec once it lands; see the file header. -/
  env_get_found : Triple
    (fun c' => ∃ ment v8 v9 v18,
      ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
        sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c')
    (fun c' => ∃ mpc v8 v9 v18,
      VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 c.σ.sailOutput m0 mpc c')

/-- **The `EvalE.var` simulation goal.** -/
def EvalVarSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (x : String) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d a (.var x) st v →
    Triple
      (EvalVarEntry g N A SL φf φc st d a x v sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st v sp r sret m0)

/-- **The M4 `EvalE.var` gate.**  Composes `blockA_k` (k=4, prologue + dispatch →
`ArmEntryK` at the var arm `0x80003434`), the honest `env_get`-found contract
(`ArmEntryK → VarPostCall`), and `blockC_var` (var-arm epilogue → `EvalExit`). -/
theorem evalVarSim : EvalVarSimGoal := by
  intro g N A SL φf φc st d a x v sp r sret aEnv aExpr m0 _hEvalE
  intro c hc
  have hexpr_m0 : ExprRepr m0 aExpr.toNat (.var x) := hc.mem ▸ hc.expr
  -- expose the var-name pointer `p` and CString from `ExprRepr … (.var x)`.
  obtain ⟨p, hkm0, hp64, hpcstr⟩ : ∃ p, read32 m0 aExpr.toNat = some 4 ∧
      read64 m0 (aExpr.toNat + 8) = some p ∧ CString m0 p x := by
    cases hexpr_m0 with | var hk hp hcs => exact ⟨_, hk, hp, hcs⟩
  have hvarStk : p + x.length < SL.lo ∨ sp.toNat ≤ p :=
    hc.var_stack_disjoint p (hc.mem.symm ▸ hp64)
  -- === block A: prologue + dispatch → ArmEntryK (via blockA_k) ===
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st (.var x) 4 (0x80003434#64) Env_getLoaded
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      (var_slot_kindPinned (hc.mem ▸ hc.var_slot)) (hc.mem ▸ hc.env_get_code)
      (fun mem a8 dd hlo hhi hh => by
        have hvs := hc.env_get_stack_disjoint
        exact loaded_env_get_writeMap8 mem a8 dd (by omega) hh)
      (fun m' hag => by
        -- ExprRepr m' aExpr .var x: read32/read64 transfer via expr_stack_disjoint,
        -- CString via var_stack_disjoint (cstring_agreeP).
        have hstk := hc.expr_stack_disjoint
        have hlo := hc.stackOK.1
        refine ExprRepr.var (p := p) ?_ ?_ ?_
        · obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m0 aExpr.toNat 4 hkm0
          simp only [read32, readLE, bind, Option.bind]
          rw [← hag aExpr.toNat (by omega), ← hag (aExpr.toNat + 1) (by omega),
              ← hag (aExpr.toNat + 2) (by omega), ← hag (aExpr.toNat + 3) (by omega),
              hb0, hb1, hb2, hb3]
          simp only []; apply congrArg some; omega
        · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hrec⟩ :=
            read64_bytes m0 (aExpr.toNat + 8) p hp64
          simp only [read64, readLE, bind, Option.bind]
          rw [← hag (aExpr.toNat + 8) (by omega), ← hag (aExpr.toNat + 8 + 1) (by omega),
              ← hag (aExpr.toNat + 8 + 2) (by omega), ← hag (aExpr.toNat + 8 + 3) (by omega),
              ← hag (aExpr.toNat + 8 + 4) (by omega), ← hag (aExpr.toNat + 8 + 5) (by omega),
              ← hag (aExpr.toNat + 8 + 6) (by omega), ← hag (aExpr.toNat + 8 + 7) (by omega),
              hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
          simp only []; apply congrArg some; omega
        · exact cstring_agreeP (P := fun aa => ¬ (SL.lo ≤ aa ∧ aa < sp.toNat))
            (m := m0) (m' := m') hag hpcstr (fun k hk => by rcases hvarStk with h | h <;> omega))
      (by decide)
      (by have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
      hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
      hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
      hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
      hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
      hc.spill_defined⟩, rfl⟩
  -- === env_get found-case (honest hypothesis): ArmEntryK → VarPostCall ===
  obtain ⟨c2, hs2, mpc, v8', v9', v18', hPC⟩ :=
    hc.env_get_found c1 ⟨ment, v8, v9, v18, hArm⟩
  -- === block C: var-arm epilogue → EvalExit ===
  obtain ⟨c3, hs3, hExit⟩ :=
    blockC_var g N A SL φf φc st v sp r sret v8' v9' v18' c.σ.sailOutput m0
      hc.sret_arena_disjoint hc.sret_evalcode_disjoint hc.sret_stack_disjoint
      c2 ⟨mpc, hPC⟩
  exact ⟨c3, (hs1.trans hs2).trans hs3, hExit⟩

end Vsa.Sim
