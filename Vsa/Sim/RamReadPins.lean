import Vsa.Sim.RamReadValue

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
namespace Vsa.Sim

theorem exec_lw_ram_bytes (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 3]? = some b3) :
    (execute (instruction.LOAD (off, rs1, rd, false, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_lw_ramv σ pc off rs1 rd σ' vbase _ hG hrs1 ?_ hwr hlo hhiram hhtif
  simp only [bytesT4, h0, h1, h2, h3, Option.getD_some]

theorem exec_lwu_ram_bytes (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 3]? = some b3) :
    (execute (instruction.LOAD (off, rs1, rd, true, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_lwu_ramv σ pc off rs1 rd σ' vbase _ hG hrs1 ?_ hwr hlo hhiram hhtif
  simp only [bytesT4, h0, h1, h2, h3, Option.getD_some]
end Vsa.Sim
