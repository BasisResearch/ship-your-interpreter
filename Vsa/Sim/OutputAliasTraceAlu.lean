import Vsa.Sim.OutputAliasTrace
import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch04Part02

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa Vsa.Machine

namespace Vsa.Sim.OutputAliasLoaded

def TraceData.afterAlu (d : TraceData) (rd : Nat) (v : BitVec 64) : TraceData :=
  { d with pc := BitVec.addInt d.pc 4, regs := (rd, v) :: eraseG rd d.regs }

def sltiuOneValue (v : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12))))

def sltuZeroValue (v : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v))

/-- Execute row 817, `sltiu a0,a0,1`, using the actual reached bytes and a0. -/
theorem TraceHolds.sltiu_800028dc {d : TraceData} {c : Config}
    (h : TraceHolds d c) (v : BitVec 64)
    (hpc : d.pc = 0x800028dc#64)
    (hk : KeysOK (keysG d.regs)) (hv : lookupG 10 d.regs = some v)
    (hb0 : logRead snapshotInitialRead d.log 0x800028dc = some (0x13#8))
    (hb1 : logRead snapshotInitialRead d.log 0x800028dd = some (0x35#8))
    (hb2 : logRead snapshotInitialRead d.log 0x800028de = some (0x15#8))
    (hb3 : logRead snapshotInitialRead d.log 0x800028df = some (0x00#8)) :
    ∃ c', Steps c c' ∧ TraceHolds (d.afterAlu 10 (sltiuOneValue v)) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  have ha0 := gholds_lookup d.regs h.regs hv
  have hpc' : c.σ.regs.get? Register.PC = some (0x800028dc#64) := by
    rw [h.pc, hpc]
  obtain ⟨σ', tick', hs, ht, hg, hm, ho⟩ :=
    stepObs_alu c.σ c.tick c.steps 0x800028dc#64 vm 0x00153513#32
      (instruction.ITYPE (0x001#12, gprIdx 10, gprIdx 10, iop.SLTIU))
      Register.x10 (sltiuOneValue v) 0x13#8 0x35#8 0x15#8 0x00#8
      h.good hpc' hvm (by decide) (by decide)
      (DecodeTable.decode_00153513 (afterPrelude c.σ)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.misa)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.cur_privilege)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.mseccfg))
      (execute_itype_sltiu_char 0x001#12 (gprIdx 10) (gprIdx 10) v _ _
        (rX_src c.σ 0x800028dc#64 10 (by decide) v ha0)
        (wX_bits_x10 _ (sltiuOneValue v)))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by change c.σ.mem[0x800028dc]? = some (0x13#8)
          rw [h.mem, snapshot_logRead]; exact hb0)
      (by change c.σ.mem[0x800028dd]? = some (0x35#8)
          rw [h.mem, snapshot_logRead]; exact hb1)
      (by change c.σ.mem[0x800028de]? = some (0x15#8)
          rw [h.mem, snapshot_logRead]; exact hb2)
      (by change c.σ.mem[0x800028df]? = some (0x00#8)
          rw [h.mem, snapshot_logRead]; exact hb3)
      (by decide) (by decide) (by decide) h.tick
  refine ⟨⟨σ', tick', c.steps + 1⟩, Steps.single hs, ?_⟩
  exact {
    good := hg
    tick := ht
    pc := by
      change σ'.regs.get? Register.PC = some (BitVec.addInt d.pc 4)
      rw [hpc]
      exact obs_alu_pc ho
    minstret := obs_alu_minstret ho
    regs := ⟨obs_gpr_rd 10 (by decide) (by decide) (sltiuOneValue v) ho,
      gholds_eraseG (n := 10) (v := sltiuOneValue v) ho
        (by decide) (by decide) d.regs hk h.regs⟩
    mem := hm.trans h.mem
    out := ho.out.trans h.out
    payload := obs_alu_other' ho Register.htif_payload_writes (by decide) h.payload }

/-- Execute row 823, `sltu a1,zero,a1`, with the source read before its overwrite. -/
theorem TraceHolds.sltu_800027f8 {d : TraceData} {c : Config}
    (h : TraceHolds d c) (v : BitVec 64)
    (hpc : d.pc = 0x800027f8#64)
    (hk : KeysOK (keysG d.regs)) (hv : lookupG 11 d.regs = some v)
    (hb0 : logRead snapshotInitialRead d.log 0x800027f8 = some (0xb3#8))
    (hb1 : logRead snapshotInitialRead d.log 0x800027f9 = some (0x35#8))
    (hb2 : logRead snapshotInitialRead d.log 0x800027fa = some (0xb0#8))
    (hb3 : logRead snapshotInitialRead d.log 0x800027fb = some (0x00#8)) :
    ∃ c', Steps c c' ∧ TraceHolds (d.afterAlu 11 (sltuZeroValue v)) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  have ha1 := gholds_lookup d.regs h.regs hv
  have hpc' : c.σ.regs.get? Register.PC = some (0x800027f8#64) := by
    rw [h.pc, hpc]
  obtain ⟨σ', tick', hs, ht, hg, hm, ho⟩ :=
    stepObs_alu c.σ c.tick c.steps 0x800027f8#64 vm 0x00b035b3#32
      (instruction.RTYPE (gprIdx 11, gprIdx 0, gprIdx 11, rop.SLTU))
      Register.x11 (sltuZeroValue v) 0xb3#8 0x35#8 0xb0#8 0x00#8
      h.good hpc' hvm (by decide) (by decide)
      (DecodeTable.decode_00b035b3 (afterPrelude c.σ)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.misa)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.cur_privilege)
        (by rw [get?_afterPrelude _ _ (by decide)]; exact h.good.mseccfg))
      (execute_rtype_sltu_char (gprIdx 11) (gprIdx 0) (gprIdx 11) (0#64) v _ _
        (rX_bits_zero _)
        (rX_src c.σ 0x800027f8#64 11 (by decide) v ha1)
        (wX_bits_x11 _ (sltuZeroValue v)))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by change c.σ.mem[0x800027f8]? = some (0xb3#8)
          rw [h.mem, snapshot_logRead]; exact hb0)
      (by change c.σ.mem[0x800027f9]? = some (0x35#8)
          rw [h.mem, snapshot_logRead]; exact hb1)
      (by change c.σ.mem[0x800027fa]? = some (0xb0#8)
          rw [h.mem, snapshot_logRead]; exact hb2)
      (by change c.σ.mem[0x800027fb]? = some (0x00#8)
          rw [h.mem, snapshot_logRead]; exact hb3)
      (by decide) (by decide) (by decide) h.tick
  refine ⟨⟨σ', tick', c.steps + 1⟩, Steps.single hs, ?_⟩
  exact {
    good := hg
    tick := ht
    pc := by
      change σ'.regs.get? Register.PC = some (BitVec.addInt d.pc 4)
      rw [hpc]
      exact obs_alu_pc ho
    minstret := obs_alu_minstret ho
    regs := ⟨obs_gpr_rd 11 (by decide) (by decide) (sltuZeroValue v) ho,
      gholds_eraseG (n := 11) (v := sltuZeroValue v) ho
        (by decide) (by decide) d.regs hk h.regs⟩
    mem := hm.trans h.mem
    out := ho.out.trans h.out
    payload := obs_alu_other' ho Register.htif_payload_writes (by decide) h.payload }

#print axioms TraceHolds.sltiu_800028dc
#print axioms TraceHolds.sltu_800027f8

end Vsa.Sim.OutputAliasLoaded
