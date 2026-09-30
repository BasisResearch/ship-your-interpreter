import Vsa.Sim.ValueSites
import Vsa.Sim.MemLoadTotal

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

namespace Vsa.Sim

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
