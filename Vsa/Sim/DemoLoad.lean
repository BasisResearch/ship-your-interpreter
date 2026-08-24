import Vsa.Sim.StepAlu
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable
import Vsa.Sim.DecodeTable.Batch03Part18

/-!
# M2 LOAD-class demo instantiation — `ld x11, 8(x2)` (census word `0x00813583`)

The composability gate for the LOAD class.  Unlike the ALU and STORE classes there
is **no per-class step file**: an executed LOAD's post-state is a *single* `rd`
insert on top of the skeleton's `σ₂` (`afterNextPC (afterPrelude σ) pc`) — memory
reads leave the state unchanged on the M-mode / Bare / naturally-aligned hot path —
which is exactly `Vsa/Sim/StepAlu.lean`'s `sigma3_alu`.  So we compose the generic
`try_step_alu` / `step_alu_notick` directly and write **no** new generic step lemma;
this file stands in for a "StepLoad" file by demonstration.

Chosen word `0x00813583` decodes (`Vsa/Sim/DecodeTable/Batch03.lean:decode_00813583`)
to `instruction.LOAD (0x008#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0b#5, false, 8)`,
i.e. `ld x11, 8(x2)` — base `rs1 = x2` (sp), dest `rd = x11` (a1), distinct
registers, small nonzero offset `imm = 8`, signed (`is_unsigned = false`), width `8`
(count 100 in the census).

## Composition chain

* `decode_00813583 (afterPrelude σ)` (its `_hmisa`/`hpriv`/`hsec` come from
  `get?_afterPrelude` read-backs of `GoodState`) supplies the skeleton's `hdec`.
* The execute step (`hexec`) is assembled at `σ₂ := afterNextPC (afterPrelude σ) pc`
  by `execute_load_signed_char` (ExecuteLoad):
  - its `hread` is `vmem_read_data_eight` at `σ₂`, `rs = x2`,
    `offset = sign_extend 0x008#12`, `v1 = vbase`, resolving the effective address
    `a := vbase + sign_extend 0x008#12` and reading the eight little-endian bytes.
    Its register hyps read back through the two prelude inserts (`get?_afterNextPC`),
    its mem hyps through `mem_afterNextPC` (`σ₂.mem = σ.mem`);
  - its `hwr` is `wX_bits_x11` at `σ₂`, whose insert post-state coincides
    **definitionally** with `sigma3_alu σ pc Register.x11 (sign_extend data)`.
* This gives `hexec` in exactly the `sigma3_alu` shape `try_step_alu` expects, with
  `rd_reg := Register.x11`, `v := sign_extend (m := 64) data`.
* `try_step_alu` / `step_alu_notick`: the four `hrd_*` disequalities and
  `NonPinned x11` discharge by `decide` for the concrete `rd = x11`.

## Bridges reused from the STORE demo (`Vsa/Sim/DemoStore.lean`)

* control-plane σ₂ reads via `get?_afterNextPC σ pc _ (by decide) (by decide)` then
  the matching `GoodState` projection (identical to `exec_sd_x11_x2`);
* GPR reads of σ₂ from pinned σ values through the prelude frame the same way;
* `vpmpaddr := initPmpaddr` from `hG.pmpaddr_n`;
* the byte-word / non-RVC facts by `BitVec.eq_of_toNat_eq; decide`.

## LOAD-specific facts (not in the STORE demo)

* the executed value is `sign_extend (m := 64) data` with `data : BitVec (8*8)`;
  for width 8 `sign_extend` is width-preserving, so the write value **is** the
  8-byte little-endian assembly with no truncation/extension bridge needed;
* memory is *read-only* on this path, so unlike STORE the post-state carries no
  `mem` change — the `sigma3_alu` (single-`rd`-insert) reuse works verbatim;
* `execute_load_signed_char` folds the `execute (LOAD …)` dispatch internally, so
  there is no separate `simp only [execute]` dispatch bridge (STORE needed one to
  peel `execute (STORE …)` down to `execute_STORE …`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The concrete decoded AST for `0x00813583` (`ld x11, 8(x2)`). -/
abbrev ldAst : instruction :=
  instruction.LOAD (0x008#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0b#5, false, 8)

/-- The effective load address for `ld x11, 8(x2)`: `vbase + sign_extend 0x008`. -/
abbrev ldAddr (vbase : BitVec 64) : BitVec 64 :=
  vbase + sign_extend (m := 64) (0x008#12)

/-- The 8-byte little-endian loaded value: `b0` is the byte at `ldAddr vbase`. -/
abbrev ldData (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec (8 * 8) :=
  ((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0

/-! ## `execute` step for `ld x11, 8(x2)` in `hexec` (`sigma3_alu`) shape -/

/-- `execute (LOAD …)` at `σ₂ = afterNextPC (afterPrelude σ) pc` for `ld x11, 8(x2)`,
in exactly the `sigma3_alu` post-state shape `try_step_alu`'s `hexec` expects.
Assembled from `execute_load_signed_char` + `vmem_read_data_eight` (as `hread`) and
`wX_bits_x11` (as `hwr`), with the base GPR read reduced from the pinned `σ` value
through the prelude frame.  The written value is `sign_extend (m := 64) (ldData …)`
(width-preserving at width 8). -/
theorem exec_ld_x11_x2
    (σ : MState) (pc : BitVec 64) (vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ)
    (hx2 : σ.regs.get? Register.x2 = some vbase)
    (hlo : 0x80000000 ≤ (ldAddr vbase).toNat)
    (hhiram : (ldAddr vbase).toNat + 8 ≤ 0x100000000)
    (hhtif : (ldAddr vbase).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (ldAddr vbase).toNat)
    (halign : (ldAddr vbase).toNat % 8 = 0)
    (hm0 : σ.mem[(ldAddr vbase).toNat]? = some b0)
    (hm1 : σ.mem[(ldAddr vbase).toNat + 1]? = some b1)
    (hm2 : σ.mem[(ldAddr vbase).toNat + 2]? = some b2)
    (hm3 : σ.mem[(ldAddr vbase).toNat + 3]? = some b3)
    (hm4 : σ.mem[(ldAddr vbase).toNat + 4]? = some b4)
    (hm5 : σ.mem[(ldAddr vbase).toNat + 5]? = some b5)
    (hm6 : σ.mem[(ldAddr vbase).toNat + 6]? = some b6)
    (hm7 : σ.mem[(ldAddr vbase).toNat + 7]? = some b7) :
    (execute ldAst).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11
            (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7))) := by
  -- control-plane reads of σ₂ from GoodState, through the prelude frame
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  -- base GPR read of σ₂ from the pinned σ value, through the prelude frame
  have hx2₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx2
  have hrs1 : (rX_bits (regidx.Regidx 0x02#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x2 _ vbase hx2₂
  -- mstatus.MPRV = 0 on the M-mode hot path
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  -- the eight bytes at σ₂, bridged through `mem_afterNextPC` (`σ₂.mem = σ.mem`)
  -- note the effective address `vbase + sign_extend 0x008#12` is `ldAddr vbase`
  have hread := vmem_read_data_eight (afterNextPC (afterPrelude σ) pc)
    (regidx.Regidx 0x02#5) (sign_extend (m := 64) (0x008#12)) vbase
    b0 b1 b2 b3 b4 b5 b6 b7 initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase' hrs1
    hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact hm0) (by rw [mem_afterNextPC]; exact hm1)
    (by rw [mem_afterNextPC]; exact hm2) (by rw [mem_afterNextPC]; exact hm3)
    (by rw [mem_afterNextPC]; exact hm4) (by rw [mem_afterNextPC]; exact hm5)
    (by rw [mem_afterNextPC]; exact hm6) (by rw [mem_afterNextPC]; exact hm7)
  -- the GPR write of `rd = x11`, whose insert post-state is `sigma3_alu`
  have hwr : (wX_bits (regidx.Regidx 0x0b#5)
        (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok () (sigma3_alu σ pc Register.x11
          (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7))) :=
    wX_bits_x11 _ (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7))
  -- `execute_load_signed_char` folds the `execute (LOAD …)` dispatch internally
  exact execute_load_signed_char (0x008#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0b#5)
    8 (ldData b0 b1 b2 b3 b4 b5 b6 b7) (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x11 (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7)))
    (by decide) hread hwr

/-! ## Byte-word facts for `0x00813583`

Little-endian: word `0x00813583` = bytes `b0=0x83 b1=0x35 b2=0x81 b3=0x00`. -/

/-- The four code bytes of `0x00813583` assemble to the word. -/
theorem ld_bytes_word :
    (((0x00#8).append (0x81#8)).append (0x35#8)).append (0x83#8) = (0x00813583#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The word is non-RVC: its low two bits are `0b11`. -/
theorem ld_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x81#8)).append (0x35#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Demonstration instantiation — `ld x11, 8(x2)` (census word `0x00813583`)

The M2 composability gate for the LOAD class: `decode_00813583` (decode) +
`exec_ld_x11_x2` (execute, from `execute_load_signed_char` ∘ `vmem_read_data_eight`)
plug straight into the **generic** `step_alu_notick`, since an executed LOAD's
post-state is a single `rd` insert (`sigma3_alu`).  No LOAD-specific step lemma. -/

/-- **`step_alu` (no clock tick) on `ld x11, 8(x2)`** (census word `0x00813583`,
count 100): one architectural `Vsa.Machine.Step` with `GoodState` preserved,
composing `exec_ld_x11_x2` through the generic `step_alu_notick`.  `i+1 ≠ 2` (no
tick).  `rd = x11` gets `sign_extend (m := 64) (ldData …)`, PC := pc+4,
minstret := v+1. -/
theorem step_load_ld_x11_x2_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vbase)
    (hb0 : σ.mem[pc.toNat]? = some (0x83#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x35#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x81#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (halo : 0x80000000 ≤ (ldAddr vbase).toNat)
    (hahiram : (ldAddr vbase).toNat + 8 ≤ 0x100000000)
    (hahtif : (ldAddr vbase).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (ldAddr vbase).toNat)
    (haalign : (ldAddr vbase).toNat % 8 = 0)
    (hm0 : σ.mem[(ldAddr vbase).toNat]? = some b0)
    (hm1 : σ.mem[(ldAddr vbase).toNat + 1]? = some b1)
    (hm2 : σ.mem[(ldAddr vbase).toNat + 2]? = some b2)
    (hm3 : σ.mem[(ldAddr vbase).toNat + 3]? = some b3)
    (hm4 : σ.mem[(ldAddr vbase).toNat + 4]? = some b4)
    (hm5 : σ.mem[(ldAddr vbase).toNat + 5]? = some b5)
    (hm6 : σ.mem[(ldAddr vbase).toNat + 6]? = some b6)
    (hm7 : σ.mem[(ldAddr vbase).toNat + 7]? = some b7)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7)), i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7))) :=
  step_alu_notick σ i u pc vminstret (0x00813583#32 : BitVec 32) ldAst
    Register.x11 (sign_extend (m := 64) (ldData b0 b1 b2 b3 b4 b5 b6 b7))
    (0x83#8) (0x35#8) (0x81#8) (0x00#8)
    hG hpc hminstret ld_bytes_word ld_notrvc
    (Vsa.Sim.DecodeTable.decode_00813583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_x11_x2 σ pc vbase b0 b1 b2 b3 b4 b5 b6 b7 hG hx2
      halo hahiram hahtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 hlo hhi halign htick

end Vsa.Sim
