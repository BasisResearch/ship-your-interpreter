import Vsa.Sim.OutputAliasTrace
import Vsa.Sim.HtifStepObs
import Vsa.Sim.DecodeTable.Batch17

open LeanRV64DExecutable LeanRV64DExecutable.Functions
open Sail ConcurrencyInterfaceV1 Vsa Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim.OutputAliasLoaded

/-- The HTIF store emits a character and changes no GPR or ordinary byte memory. -/
def TraceData.afterPutchar (d : TraceData) (byte : BitVec 8) : TraceData :=
  { d with
    pc := BitVec.addInt d.pc 4
    out := d.out.push (toString (Char.ofNat byte.toNat))
    payload := 0#4 }

/-- Transport all homogeneous GPR reads through the actual HTIF/postlude frame.
The dependent-register dispatch is shared once, rather than repeated per pin. -/
private theorem gprGet_putchar_frame {σ' σ : MState}
    (hframe : ∀ R : Register,
      (Register.PC == R) = false → (Register.minstret == R) = false →
      (Register.minstret_increment == R) = false → (Register.nextPC == R) = false →
      (Register.htif_cmd_write == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_tohost == R) = false →
      (Register.mip == R) = false → (Register.mtime == R) = false →
      (Register.mcycle == R) = false →
      σ'.regs.get? R = σ.regs.get? R) (n : Nat) :
    gprGet σ' n = gprGet σ n := by
  unfold gprGet
  split <;> first
    | rfl
    | exact hframe _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem gholds_of_gprGet_eq {σ' σ : MState}
    (hframe : ∀ n, gprGet σ' n = gprGet σ n)
    (regs : GRegs) (h : GHolds σ regs) : GHolds σ' regs := by
  induction regs with
  | nil => trivial
  | cons pair rest ih =>
      exact ⟨(hframe pair.1).trans h.1, ih h.2⟩

/-- Execute the actual `sd a5,-856(a6)` instruction at 0x8000005c.
All premises are reached-state facts or finite byte/register checks; no step
or native-output transition is assumed. -/
theorem TraceHolds.putchar {d : TraceData} {c : Config}
    (h : TraceHolds d c) (byte : BitVec 8)
    (hpc : d.pc = 0x8000005c#64)
    (hpayload : d.payload = 0#4)
    (hbase : lookupG 16 d.regs = some (0x8001b058#64))
    (hdata : lookupG 15 d.regs =
      some ((0x0101000000000000#64) ||| BitVec.zeroExtend 64 byte))
    (hb0 : logRead snapshotInitialRead d.log 0x8000005c = some (0x23#8))
    (hb1 : logRead snapshotInitialRead d.log 0x8000005d = some (0x34#8))
    (hb2 : logRead snapshotInitialRead d.log 0x8000005e = some (0xf8#8))
    (hb3 : logRead snapshotInitialRead d.log 0x8000005f = some (0xca#8)) :
    ∃ c', Steps c c' ∧ TraceHolds (d.afterPutchar byte) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨th, hth⟩ := h.good.htif_tohost
  have ha6 := gholds_lookup d.regs h.regs hbase
  have ha5 := gholds_lookup d.regs h.regs hdata
  have hpc' : c.σ.regs.get? Register.PC = some (0x8000005c#64) := by
    rw [h.pc, hpc]
  obtain ⟨σ', tick', hstep, htick', hgood', hmem', hout', hpc'', hvm', hpw', _, hframe⟩ :=
    stepObs_tohost_putchar c.σ c.tick c.steps 0x8000005c#64 vm
      0xcaf83423#32 0xca8#12 (regidx.Regidx 0x0f#5) (regidx.Regidx 0x10#5)
      0x8001b058#64
      ((0x0101000000000000#64) ||| BitVec.zeroExtend 64 byte)
      ((0x0101000000000000#64) ||| BitVec.zeroExtend 64 byte)
      byte th 0x23#8 0x34#8 0xf8#8 0xca#8
      h.good hpc' hvm (by decide) (by decide)
      (DecodeTable.decode_caf83423 (afterPrelude c.σ)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.misa)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.cur_privilege)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.mseccfg))
      (by apply rX_bits_x16
          rw [get?_afterNextPC _ _ _ (by decide) (by decide)]
          exact ha6)
      (by apply rX_bits_x15
          rw [get?_afterNextPC _ _ _ (by decide) (by decide)]
          exact ha5)
      (by decide) rfl (by rw [h.payload, hpayload]) hth rfl
      (by change c.σ.mem[0x8000005c]? = some (0x23#8)
          rw [h.mem, snapshot_logRead]; exact hb0)
      (by change c.σ.mem[0x8000005d]? = some (0x34#8)
          rw [h.mem, snapshot_logRead]; exact hb1)
      (by change c.σ.mem[0x8000005e]? = some (0xf8#8)
          rw [h.mem, snapshot_logRead]; exact hb2)
      (by change c.σ.mem[0x8000005f]? = some (0xca#8)
          rw [h.mem, snapshot_logRead]; exact hb3)
      (by decide) (by decide) (by decide) h.tick
  refine ⟨⟨σ', tick', c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_⟩
  exact {
    good := hgood'
    tick := htick'
    pc := by
      change σ'.regs.get? Register.PC = some (BitVec.addInt d.pc 4)
      rw [hpc]
      exact hpc''
    minstret := hvm'
    regs := gholds_of_gprGet_eq (gprGet_putchar_frame hframe) d.regs h.regs
    mem := hmem'.trans h.mem
    out := by
      change σ'.sailOutput = d.out.push (toString (Char.ofNat byte.toNat))
      rw [hout', h.out]
    payload := hpw' }

#print axioms TraceHolds.putchar

end Vsa.Sim.OutputAliasLoaded
