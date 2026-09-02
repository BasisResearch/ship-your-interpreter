import Vsa.Sim.ValueSites
import Vsa.Sim.MemLoadTotal

/-!
# TOTAL `execute (LOAD …)` characterizations (`exec_*_tot`)

The `exec_lw`/`exec_ld`/`exec_lbu_bm`/… family in `ValueSites`/`BlockMem` takes
per-byte PRESENCE hypotheses (`σ.mem[a+k]? = some bk`).  The Sail model does not
need them: `readByte a = (m.get? a).getD 0`, so a load reads TOTALLY and an
unmapped byte reads as `0`.  This file is the presence-free half of that family:
the loaded value is `bytesT*` — the total read — and there are NO byte
hypotheses at all.

Every proof here is the same three moves: lift `GoodState` to the site state
(`SiteGood`, one shared lemma instead of the 20-line block each `exec_*` used to
repeat), feed the total read chain (`vmem_read_data_*_total`), and close with
`execute_load_{signed,unsigned}_char`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

namespace Vsa.Sim

/-! ## `SiteGood` — `GoodState` transported to the site state

The seven register facts every `execute (LOAD …)` characterization needs at
`afterNextPC (afterPrelude σ) pc`.  Named fields, not a positional ∧-tower. -/

structure SiteGood (σ : MState) (pc : BitVec 64) : Prop where
  priv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
    = some (Privilege.Machine : RegisterType Register.cur_privilege)
  mstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus
  seccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64)
  pma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
    = some (initPmaRegions : RegisterType Register.pma_regions)
  cfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
    = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n)
  pmpaddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr
  tohost : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
    = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base)

/-- `GoodState` survives the fetch prelude + `nextPC` write, so it supplies
`SiteGood` at any `pc`. -/
theorem siteGood_of_good (σ : MState) (pc : BitVec 64) (hG : GoodState σ) : SiteGood σ pc where
  priv := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  mstatus := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  seccfg := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  pma := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  cfg := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  pmpaddr := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  tohost := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base

/-! ## The site-level total reads -/

/-- The width-1 total read at a load site. -/
theorem siteRead_one_total (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 : regidx)
    (vbase : BitVec 64) (hS : SiteGood σ pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (vmem_read rs1 (sign_extend (m := 64) off) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok (.Ok (bytesT1 σ.mem (vbase + sign_extend (m := 64) off).toNat))
          (afterNextPC (afterPrelude σ) pc) :=
  vmem_read_data_one_total (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase initMstatus initPmpaddr
    hS.priv hS.mstatus (by decide) hS.seccfg hS.pma hS.cfg hS.pmpaddr hS.tohost
    hrs1 hlo hhiram hhtif

/-- The width-2 total read at a load site. -/
theorem siteRead_two_total (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 : regidx)
    (vbase : BitVec 64) (hS : SiteGood σ pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0) :
    (vmem_read rs1 (sign_extend (m := 64) off) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok (.Ok (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat))
          (afterNextPC (afterPrelude σ) pc) :=
  vmem_read_data_two_total (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase initMstatus initPmpaddr
    hS.priv hS.mstatus (by decide) hS.seccfg hS.pma hS.cfg hS.pmpaddr hS.tohost
    hrs1 hlo hhiram hhtif halign

/-- The width-4 total read at a load site. -/
theorem siteRead_four_total (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 : regidx)
    (vbase : BitVec 64) (hS : SiteGood σ pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0) :
    (vmem_read rs1 (sign_extend (m := 64) off) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok (.Ok (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat))
          (afterNextPC (afterPrelude σ) pc) :=
  vmem_read_data_four_total (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase initMstatus initPmpaddr
    hS.priv hS.mstatus (by decide) hS.seccfg hS.pma hS.cfg hS.pmpaddr hS.tohost
    hrs1 hlo hhiram hhtif halign

/-- The width-8 total read at a load site. -/
theorem siteRead_eight_total (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 : regidx)
    (vbase : BitVec 64) (hS : SiteGood σ pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 8 = 0) :
    (vmem_read rs1 (sign_extend (m := 64) off) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok (.Ok (bytesT8 σ.mem (vbase + sign_extend (m := 64) off).toNat))
          (afterNextPC (afterPrelude σ) pc) :=
  vmem_read_data_eight_total (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase initMstatus initPmpaddr
    hS.priv hS.mstatus (by decide) hS.seccfg hS.pma hS.cfg hS.pmpaddr hS.tohost
    hrs1 hlo hhiram hhtif halign

/-! ## The presence-free `execute (LOAD …)` characterizations -/

/-- `ld rd,off(rs1)` — TOTAL: the loaded value is the eight-byte total read
`bytesT8 σ.mem (vbase + sext off).toNat`.  No byte-presence hypothesis. -/
theorem exec_ld_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (bytesT8 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 8)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 8 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, false, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_signed_char off rs1 rd 8 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (siteRead_eight_total σ pc off rs1 vbase (siteGood_of_good σ pc hG)
      hrs1 hlo hhiram hhtif halign) hwr

/-- `lw rd,off(rs1)` — TOTAL. -/
theorem exec_lw_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, false, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_signed_char off rs1 rd 4 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (siteRead_four_total σ pc off rs1 vbase (siteGood_of_good σ pc hG)
      hrs1 hlo hhiram hhtif halign) hwr

/-- `lwu rd,off(rs1)` — TOTAL. -/
theorem exec_lwu_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64)
        (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, true, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_unsigned_char off rs1 rd 4 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (siteRead_four_total σ pc off rs1 vbase (siteGood_of_good σ pc hG)
      hrs1 hlo hhiram hhtif halign) hwr

/-- `lh rd,off(rs1)` — TOTAL. -/
theorem exec_lh_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 2)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, false, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_signed_char off rs1 rd 2 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (siteRead_two_total σ pc off rs1 vbase (siteGood_of_good σ pc hG)
      hrs1 hlo hhiram hhtif halign) hwr

/-- `lhu rd,off(rs1)` — TOTAL. -/
theorem exec_lhu_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64)
        (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 2)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, true, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_unsigned_char off rs1 rd 2 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (siteRead_two_total σ pc off rs1 vbase (siteGood_of_good σ pc hG)
      hrs1 hlo hhiram hhtif halign) hwr

/-- `lbu rd,off(rs1)` — TOTAL.  Width 1 has no alignment side condition. -/
theorem exec_lbu_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64)
        (bytesT1 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 1)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, true, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_unsigned_char off rs1 rd 1 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (siteRead_one_total σ pc off rs1 vbase (siteGood_of_good σ pc hG)
      hrs1 hlo hhiram hhtif) hwr


/-! ## Value-parameterized siblings (`exec_*_totv`)

`block_mem_sound` names the loaded value through the block's `lds` list
(`bytesVal`), not as a literal total read, so it wants the total-read fact as an
EQUATION rather than as the shape of the conclusion.  These take the value `v`
plus `hv : <total read> = v`; `exec_*_tot` is the `v := <total read>`, `hv :=
rfl` instance.  This is the hinge that lets the reflected-execution layer keep
its `lds` naming while its memory obligations become total-read equalities
instead of presence claims. -/

/-- `ld` — TOTAL, value-parameterized. -/
theorem exec_ld_totv (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (sign_extend (m := 64)
      (bytesT8 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 8)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 8 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, false, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  subst hv
  exact exec_ld_tot σ pc off rs1 rd σ' vbase hG hrs1 hwr hlo hhiram hhtif halign

/-- `lw` — TOTAL, value-parameterized. -/
theorem exec_lw_totv (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (sign_extend (m := 64)
      (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, false, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  subst hv
  exact exec_lw_tot σ pc off rs1 rd σ' vbase hG hrs1 hwr hlo hhiram hhtif halign

/-- `lwu` — TOTAL, value-parameterized. -/
theorem exec_lwu_totv (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (zero_extend (m := 64)
      (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, true, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  subst hv
  exact exec_lwu_tot σ pc off rs1 rd σ' vbase hG hrs1 hwr hlo hhiram hhtif halign

/-- `lh` — TOTAL, value-parameterized. -/
theorem exec_lh_totv (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (sign_extend (m := 64)
      (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 2)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, false, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  subst hv
  exact exec_lh_tot σ pc off rs1 rd σ' vbase hG hrs1 hwr hlo hhiram hhtif halign

/-- `lhu` — TOTAL, value-parameterized. -/
theorem exec_lhu_totv (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (zero_extend (m := 64)
      (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 2)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0) :
    (execute (instruction.LOAD (off, rs1, rd, true, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  subst hv
  exact exec_lhu_tot σ pc off rs1 rd σ' vbase hG hrs1 hwr hlo hhiram hhtif halign

/-- `lbu` — TOTAL, value-parameterized. -/
theorem exec_lbu_totv (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (zero_extend (m := 64)
      (bytesT1 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 1)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, true, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  subst hv
  exact exec_lbu_tot σ pc off rs1 rd σ' vbase hG hrs1 hwr hlo hhiram hhtif

end Vsa.Sim
