import Vsa.Sim.OutputAliasTrace
import Vsa.Sim.TermEntry
import Vsa.Sim.DecodeTable.Batch14Part06

open LeanRV64DExecutable LeanRV64DExecutable.Functions
open Sail ConcurrencyInterfaceV1 Vsa Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim.OutputAliasLoaded

/-- Execute the actual final `sd a5,-1164(a4)` at 0x80000190.
The command word 1 signals exit code 0. The existing reached `GoodState`
supplies mailbox presence; no additional HTIF staging premise is needed. -/
theorem TraceHolds.halted0 {d : TraceData} {c : Config}
    (h : TraceHolds d c)
    (hpc : d.pc = 0x80000190#64)
    (hpayload : d.payload = 0#4)
    (hbase : lookupG 14 d.regs = some (0x8001b18c#64))
    (hdata : lookupG 15 d.regs = some (1#64))
    (hb0 : logRead snapshotInitialRead d.log 0x80000190 = some (0x23#8))
    (hb1 : logRead snapshotInitialRead d.log 0x80000191 = some (0x3a#8))
    (hb2 : logRead snapshotInitialRead d.log 0x80000192 = some (0xf7#8))
    (hb3 : logRead snapshotInitialRead d.log 0x80000193 = some (0xb6#8)) :
    ∃ σf, Halted c 0 σf ∧ σf.sailOutput = d.out := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨th, hth⟩ := h.good.htif_tohost
  have ha4 := gholds_lookup d.regs h.regs hbase
  have ha5 := gholds_lookup d.regs h.regs hdata
  have hpc' : c.σ.regs.get? Register.PC = some (0x80000190#64) := by
    rw [h.pc, hpc]
  have hstep := stepOnce_tohost_G c.σ c.tick c.steps 0x80000190#64 vm
    0xb6f73a23#32 0xb74#12 (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
    0x8001b18c#64 1#64 1#64 0#64 th
    0x23#8 0x3a#8 0xf7#8 0xb6#8
    h.good hpc' hvm (by decide) (by decide)
    (DecodeTable.decode_b6f73a23 (afterPrelude c.σ)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.misa)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.cur_privilege)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.mseccfg))
    (by apply rX_bits_x14
        rw [get?_afterNextPC _ _ _ (by decide) (by decide)]
        exact ha4)
    (by apply rX_bits_x15
        rw [get?_afterNextPC _ _ _ (by decide) (by decide)]
        exact ha5)
    (by decide) rfl (by rw [h.payload, hpayload]) hth (by decide) (by decide)
    (by change c.σ.mem[0x80000190]? = some (0x23#8)
        rw [h.mem, snapshot_logRead]; exact hb0)
    (by change c.σ.mem[0x80000191]? = some (0x3a#8)
        rw [h.mem, snapshot_logRead]; exact hb1)
    (by change c.σ.mem[0x80000192]? = some (0xf7#8)
        rw [h.mem, snapshot_logRead]; exact hb2)
    (by change c.σ.mem[0x80000193]? = some (0xb6#8)
        rw [h.mem, snapshot_logRead]; exact hb3)
    (by decide) (by decide) (by decide)
  refine ⟨sigmaExitFinalG c.σ 0x80000190#64 0x80000194#64 vm 1#64 0#64, ?_, ?_⟩
  · exact Halted.mk hstep
  · exact (sailOutput_sigmaExitG_final c.σ 0x80000190#64 0x80000194#64 vm 1#64 0#64).trans h.out

/-- Close any already-proved prefix with the reached actual halt witness. -/
theorem halts_of_trace_halted {start c : Config} {σf : MState} {out : Array String}
    (hs : Steps start c) (hh : Halted c 0 σf) (ho : σf.sailOutput = out) :
    Halts start (String.join out.toList) 0 := by
  refine ⟨c, σf, hs, hh, ?_⟩
  unfold output
  rw [ho]

end Vsa.Sim.OutputAliasLoaded
