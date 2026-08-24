import Vsa.Sim.SnprintfSpec7
import Vsa.Sim.Code.__ssprint_r
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part01

/-!
# M3 Layer-3 — `SnprintfSpec9` : the `__ssprint_r` return epilogue (`_ss`)

The common return tail of `__ssprint_r` (`0x8000e908`, the string-sink flush that
`snprintf("%lld", …)` calls to move the formatted iov into the caller buffer).
Both the empty-flush branch and the post-loop fall-through converge on the block
`0x8000e9b0 … 0x8000e9c8`:

```
8000e9b0: ld   ra,56(sp)       reload the return address
8000e9b4: sd   zero,16(s1)     clear the sink's _uio.uio_resid  (bytes-remaining)
8000e9b8: sw   zero,8(s1)      clear the sink's _uio.uio_iovcnt (iov-count)
8000e9bc: li   a0,0            return value 0 (success)
8000e9c0: ld   s1,40(sp)       reload s1
8000e9c4: addi sp,sp,64        pop the 64-byte frame
8000e9c8: ret                  jr ra  → the caller (svfprintf) resume PC
```

`ssprintTail_spec` is a `Triple` (`Steps`) over exactly these seven straight-line
instructions.  It is self-contained: no branch, no call, so it composes onto any
`__ssprint_r` run that reaches `0x8000e9b0` — in particular the empty-flush path
`0x8000e908 → 0x8000e91c (beqz resid=0) → 0x8000e9b0`, and (once the iov loop and
`__ssputs_r` are verified) the non-empty flush.

The two spilled callee-saves it reads back (`ra` at `sp+56`, `s1` at `sp+40`) are
supplied as `SlotHolds` facts and threaded through the two sink stores by the
existing `slotHolds_*` transport lemmas (`SnprintfSpec5`).  The sink FILE window
(`s1+8 … s1+24`) is required disjoint from those two stack slots so the reloads
survive.

Built on the shared `StepObs` site helpers + `obs_*` accessors (`Muldi3Spec`,
`MemcpySpec`, `SnprintfSpec4`) and the `__ssprint_rLoaded` byte facts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__ssprint_rLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Read-over-write for a byte store disjoint from the `__ssprint_r` code region
`[0x8000e908, 0x8000e9f8)`: a store at `k` outside that window leaves every code
read (`a ∈ [0x8000e908, 0x8000e9f8)`) unchanged. -/
theorem getElem?_insert_offcode_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : k < 0x8000e908 ∨ 0x8000e9f8 ≤ k) (a : Nat)
    (ha : 0x8000e908 ≤ a) (ha' : a < 0x8000e9f8) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- `__ssprint_rLoaded` survives a single insert disjoint from the code region. -/
theorem ssprint_insert_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : k < 0x8000e908 ∨ 0x8000e9f8 ≤ k) (h : __ssprint_rLoaded mem) :
    __ssprint_rLoaded (mem.insert k v) := by
  unfold __ssprint_rLoaded Vsa.Sim.Code.__ssprint_rChunk0 Vsa.Sim.Code.__ssprint_rChunk1
    Vsa.Sim.Code.__ssprint_rChunk2 Vsa.Sim.Code.__ssprint_rChunk3 at h ⊢
  simp (disch := omega) only [getElem?_insert_offcode_ss mem k v hk]
  exact h

/-- `__ssprint_rLoaded` survives a disjoint 8-byte `writeMap8` (eight inserts). -/
theorem ssprint_writeMap8_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : a + 8 ≤ 0x8000e908 ∨ 0x8000e9f8 ≤ a)
    (h : __ssprint_rLoaded mem) : __ssprint_rLoaded (writeMap8 mem a d) :=
  ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega) h)))))))

/-- `__ssprint_rLoaded` survives a disjoint 4-byte `writeMap4` (four inserts). -/
theorem ssprint_writeMap4_ss (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 4)) (ha : a + 4 ≤ 0x8000e908 ∨ 0x8000e9f8 ≤ a)
    (h : __ssprint_rLoaded mem) : __ssprint_rLoaded (writeMap4 mem a d) :=
  ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega)
    (ssprint_insert_ss _ _ _ (by omega) (ssprint_insert_ss _ _ _ (by omega) h)))

/-- `SlotHolds` survives a disjoint 4-byte `writeMap4` (four disjoint inserts). -/
theorem slotHolds_writeMap4_ss (vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 4))
    (hdis : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k
      ∨ k + 4 ≤ (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat)
    (h : SlotHolds vsp off v mem) : SlotHolds vsp off v (writeMap4 mem k d) :=
  slotHolds_insert vsp off v _ (k + 3) _ (by omega)
    (slotHolds_insert vsp off v _ (k + 2) _ (by omega)
      (slotHolds_insert vsp off v _ (k + 1) _ (by omega)
        (slotHolds_insert vsp off v _ k _ (by omega) h)))

/-- The `__ssprint_r` return epilogue `0x8000e9b0 … 0x8000e9c8`.

Entry at `0x8000e9b0` with the return address stored at `sp+56` and `s1` stored
at `sp+40` (both `SlotHolds`), the sink pointer `s1 = vsink` in `x9`, and the
sink window `[vsink+8, vsink+24)` writable and disjoint from those two spill
slots.  Steps to the return target `vra` (the loaded `ra`), with `a0 = 0`, the
frame popped (`sp := vsp + 64`), the sink's `resid`/`iovcnt` fields cleared, and
`s1`/`ra` restored to their spilled values. -/
theorem ssprintTail_spec
    (vsp vra vsink : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : __ssprint_rLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000e9b0#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx9 : c.σ.regs.get? Register.x9 = some vsink)
    (hra : SlotHolds vsp 0x038 vra c.σ.mem)
    (hs1 : SlotHolds vsp 0x028 vsink c.σ.mem)
    -- stack frame in RAM, above the HTIF window, 8-aligned
    (hsplo : 0x80000000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 64 ≤ 0x100000000)
    (hspwin : tohostAddr + 16 ≤ vsp.toNat)
    (hspalign : vsp.toNat % 8 = 0)
    -- the sink FILE, above the HTIF window; +8 (4-byte) and +16 (8-byte) fields
    (hsklo : 0x80000000 ≤ vsink.toNat)
    (hskhi : vsink.toNat + 24 ≤ 0x100000000)
    (hskwin : tohostAddr + 16 ≤ vsink.toNat)
    (hskalign : vsink.toNat % 8 = 0)
    -- disjointness of the sink write window [vsink+8, vsink+24) from the two
    -- stack reload slots sp+40 (s1) and sp+56 (ra), and target 4-alignment
    (hdis40 : vsink.toNat + 24 ≤ vsp.toNat + 40 ∨ vsp.toNat + 48 ≤ vsink.toNat + 8)
    (hdis56 : vsink.toNat + 24 ≤ vsp.toNat + 56 ∨ vsp.toNat + 64 ≤ vsink.toNat + 8)
    -- the sink write window `[vsink+8, vsink+24)` is disjoint from the code region
    (hoffcode : vsink.toNat + 24 ≤ 0x8000e908 ∨ 0x8000e9f8 ≤ vsink.toNat + 8)
    (hratgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC
        = some (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      c'.σ.regs.get? Register.x10 = some (0#64) ∧
      c'.σ.regs.get? Register.x1 = some vra ∧
      c'.σ.regs.get? Register.x9 = some vsink ∧
      c'.σ.regs.get? Register.x2 = some (vsp + sign_extend (m := 64) (0x040#12)) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  -- effective-address rewrites for the two stack slots (offsets 56, 40)
  have hoff56 : (vsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat + 56 :=
    addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw
  have hoff40 : (vsp + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat + 40 :=
    addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw
  -- effective-address rewrites for the two sink stores (offsets 16, 8)
  have hoff16 : (vsink + sign_extend (m := 64) (0x010#12)).toNat = vsink.toNat + 16 :=
    addoff_toNat_sn5 vsink (0x010#12) 16 (by omega) (by decide) (by omega)
  have hoff8 : (vsink + sign_extend (m := 64) (0x008#12)).toNat = vsink.toNat + 8 :=
    addoff_toNat_sn5 vsink (0x008#12) 8 (by omega) (by decide) (by omega)
  -- the sign-extended 8-byte reassembly of a `sd v` slot, as a local abbreviation
  -- === 8000e9b0: ld ra,56(sp)  ⇒  x1 := vra ===
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hra
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9b0 hload
  have hx2n1 : (afterNextPC (afterPrelude c.σ) (0x8000e9b0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC c.σ (0x8000e9b0#64) _ (by decide) (by decide)]; exact hx2
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x8000e9b0#64) vmi0 (0x03813083#32)
      (instruction.LOAD (0x038#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
      Register.x1 (sign_extend (m := 64)
        (((((((((sdData_val vra).extractLsb' 56 8).append ((sdData_val vra).extractLsb' 48 8)).append
          ((sdData_val vra).extractLsb' 40 8)).append ((sdData_val vra).extractLsb' 32 8)).append
          ((sdData_val vra).extractLsb' 24 8)).append ((sdData_val vra).extractLsb' 16 8)).append
          ((sdData_val vra).extractLsb' 8 8)).append ((sdData_val vra).extractLsb' 0 8)
          : BitVec (8 * 8)))
      (0x83#8) (0x30#8) (0x81#8) (0x03#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_03813083 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_ld c.σ (0x8000e9b0#64) (0x038#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
        (sigma3_alu c.σ (0x8000e9b0#64) Register.x1 (sign_extend (m := 64)
          (((((((((sdData_val vra).extractLsb' 56 8).append ((sdData_val vra).extractLsb' 48 8)).append
            ((sdData_val vra).extractLsb' 40 8)).append ((sdData_val vra).extractLsb' 32 8)).append
            ((sdData_val vra).extractLsb' 24 8)).append ((sdData_val vra).extractLsb' 16 8)).append
            ((sdData_val vra).extractLsb' 8 8)).append ((sdData_val vra).extractLsb' 0 8)
            : BitVec (8 * 8))))
        vsp _ _ _ _ _ _ _ _ hG (rX_bits_x2 _ vsp hx2n1)
        (wX_bits_x1 _ _)
        (by rw [hoff56]; omega) (by rw [hoff56]; omega) (Or.inr (by rw [hoff56]; omega))
        (by rw [hoff56]; omega)
        hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000e9b4#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000e9b0#64 : BitVec 64) 4 = (0x8000e9b4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_1 : σ1.regs.get? Register.x1 = some vra := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vra] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx9_1 : σ1.regs.get? Register.x9 = some vsink :=
    obs_alu_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9
  have hload1 : __ssprint_rLoaded σ1.mem := hmem1 ▸ hload
  have hs1_1 : SlotHolds vsp 0x028 vsink σ1.mem := hmem1 ▸ hs1
  -- === 8000e9b4: sd zero,16(s1)  (clear resid) ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9b4 hload1
  have hx9n2 : (afterNextPC (afterPrelude σ1) (0x8000e9b4#64)).regs.get? Register.x9 = some vsink := by
    rw [get?_afterNextPC σ1 (0x8000e9b4#64) _ (by decide) (by decide)]; exact hx9_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_store σ1 i1 (c.steps + 1) (0x8000e9b4#64) vmi1 (0x0004b823#32)
      (instruction.STORE (0x010#12, regidx.Regidx 0x00#5, regidx.Regidx 0x09#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ1) (0x8000e9b4#64)).mem
        (vsink + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (0#64)))
      (0x23#8) (0xb8#8) (0x04#8) (0x00#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0004b823 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (exec_sd_val σ1 (0x8000e9b4#64) (0x010#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x09#5)
        vsink (0#64) hG1 (rX_bits_x9 _ vsink hx9n2) (rX_bits_zero _)
        (by rw [hoff16]; omega) (by rw [hoff16]; omega) (by rw [hoff16]; omega) (by rw [hoff16]; omega))
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000e9b8#64) := by
    have := obs_store_pc_sn4 hobs2
    rwa [show BitVec.addInt (0x8000e9b4#64 : BitVec 64) 4 = (0x8000e9b8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_sn4 hobs2
  have hx1_2 : σ2.regs.get? Register.x1 = some vra :=
    obs_store_other_sn4 Register.x1 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx9_2 : σ2.regs.get? Register.x9 = some vsink :=
    obs_store_other_sn4 Register.x9 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_1
  have hNP1 : (afterNextPC (afterPrelude σ1) (0x8000e9b4#64)).mem = σ1.mem := rfl
  have hload2 : __ssprint_rLoaded σ2.mem := by
    rw [hmem2, hNP1]
    exact ssprint_writeMap8_ss _ _ _ (by rw [hoff16]; omega) hload1
  have hs1_2 : SlotHolds vsp 0x028 vsink σ2.mem := by
    rw [hmem2, hNP1]
    exact slotHolds_writeMap8 vsp 0x028 vsink σ1.mem _ _
      (by rw [hoff16, hoff40]; omega) hs1_1
  -- === 8000e9b8: sw zero,8(s1)  (clear iovcnt) ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9b8 hload2
  have hx9n3 : (afterNextPC (afterPrelude σ2) (0x8000e9b8#64)).regs.get? Register.x9 = some vsink := by
    rw [get?_afterNextPC σ2 (0x8000e9b8#64) _ (by decide) (by decide)]; exact hx9_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_store σ2 i2 (c.steps + 1 + 1) (0x8000e9b8#64) vmi2 (0x0004a423#32)
      (instruction.STORE (0x008#12, regidx.Regidx 0x00#5, regidx.Regidx 0x09#5, 4))
      (writeMap4 (afterNextPC (afterPrelude σ2) (0x8000e9b8#64)).mem
        (vsink + sign_extend (m := 64) (0x008#12)).toNat (swData (0#64)))
      (0x23#8) (0xa4#8) (0x04#8) (0x00#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0004a423 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (exec_sw σ2 (0x8000e9b8#64) (0x008#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x09#5)
        vsink (0#64) hG2 (rX_bits_x9 _ vsink hx9n3) (rX_bits_zero _)
        (by rw [hoff8]; omega) (by rw [hoff8]; omega) (by rw [hoff8]; omega) (by rw [hoff8]; omega))
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000e9bc#64) := by
    have := obs_store_pc_sn4 hobs3
    rwa [show BitVec.addInt (0x8000e9b8#64 : BitVec 64) 4 = (0x8000e9bc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_sn4 hobs3
  have hx1_3 : σ3.regs.get? Register.x1 = some vra :=
    obs_store_other_sn4 Register.x1 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx9_3 : σ3.regs.get? Register.x9 = some vsink :=
    obs_store_other_sn4 Register.x9 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_2
  have hNP2 : (afterNextPC (afterPrelude σ2) (0x8000e9b8#64)).mem = σ2.mem := rfl
  have hload3 : __ssprint_rLoaded σ3.mem := by
    rw [hmem3, hNP2]
    exact ssprint_writeMap4_ss _ _ _ (by rw [hoff8]; omega) hload2
  have hs1_3 : SlotHolds vsp 0x028 vsink σ3.mem := by
    rw [hmem3, hNP2]
    exact slotHolds_writeMap4_ss vsp 0x028 vsink σ2.mem _ _
      (by rw [hoff8, hoff40]; omega) hs1_2
  -- === 8000e9bc: li a0,0  ⇒  x10 := 0 ===
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9bc hload3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_alu σ3 i3 (c.steps + 1 + 1 + 1) (0x8000e9bc#64) vmi3 (0x00000513#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
      Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))
      (0x13#8) (0x05#8) (0x00#8) (0x00#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
        (afterNextPC (afterPrelude σ3) (0x8000e9bc#64))
        (sigma3_alu σ3 (0x8000e9bc#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
        (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000e9c0#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x8000e9bc#64 : BitVec 64) 4 = (0x8000e9c0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_4 : σ4.regs.get? Register.x10 = some (0#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hx1_4 : σ4.regs.get? Register.x1 = some vra :=
    obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_3
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hload4 : __ssprint_rLoaded σ4.mem := hmem4 ▸ hload3
  have hs1_4 : SlotHolds vsp 0x028 vsink σ4.mem := hmem4 ▸ hs1_3
  -- === 8000e9c0: ld s1,40(sp)  ⇒  x9 := vsink ===
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := hs1_4
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9c0 hload4
  have hx2n5 : (afterNextPC (afterPrelude σ4) (0x8000e9c0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ4 (0x8000e9c0#64) _ (by decide) (by decide)]; exact hx2_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000e9c0#64) vmi4 (0x02813483#32)
      (instruction.LOAD (0x028#12, regidx.Regidx 0x02#5, regidx.Regidx 0x09#5, false, 8))
      Register.x9 (sign_extend (m := 64)
        (((((((((sdData_val vsink).extractLsb' 56 8).append ((sdData_val vsink).extractLsb' 48 8)).append
          ((sdData_val vsink).extractLsb' 40 8)).append ((sdData_val vsink).extractLsb' 32 8)).append
          ((sdData_val vsink).extractLsb' 24 8)).append ((sdData_val vsink).extractLsb' 16 8)).append
          ((sdData_val vsink).extractLsb' 8 8)).append ((sdData_val vsink).extractLsb' 0 8)
          : BitVec (8 * 8)))
      (0x83#8) (0x34#8) (0x81#8) (0x02#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02813483 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (exec_ld σ4 (0x8000e9c0#64) (0x028#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x09#5)
        (sigma3_alu σ4 (0x8000e9c0#64) Register.x9 (sign_extend (m := 64)
          (((((((((sdData_val vsink).extractLsb' 56 8).append ((sdData_val vsink).extractLsb' 48 8)).append
            ((sdData_val vsink).extractLsb' 40 8)).append ((sdData_val vsink).extractLsb' 32 8)).append
            ((sdData_val vsink).extractLsb' 24 8)).append ((sdData_val vsink).extractLsb' 16 8)).append
            ((sdData_val vsink).extractLsb' 8 8)).append ((sdData_val vsink).extractLsb' 0 8)
            : BitVec (8 * 8))))
        vsp _ _ _ _ _ _ _ _ hG4 (rX_bits_x2 _ vsp hx2n5)
        (wX_bits_x9 _ _)
        (by rw [hoff40]; omega) (by rw [hoff40]; omega) (Or.inr (by rw [hoff40]; omega))
        (by rw [hoff40]; omega)
        hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000e9c4#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000e9c0#64 : BitVec 64) 4 = (0x8000e9c4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx9_5 : σ5.regs.get? Register.x9 = some vsink := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vsink] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx1_5 : σ5.regs.get? Register.x1 = some vra :=
    obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_4
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx10_5 : σ5.regs.get? Register.x10 = some (0#64) :=
    obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
  have hload5 : __ssprint_rLoaded σ5.mem := hmem5 ▸ hload4
  -- === 8000e9c4: addi sp,sp,64  ⇒  x2 := vsp + 64 ===
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9c4 hload5
  have hx2n6 : (afterNextPC (afterPrelude σ5) (0x8000e9c4#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ5 (0x8000e9c4#64) _ (by decide) (by decide)]; exact hx2_5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_alu σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x8000e9c4#64) vmi5 (0x04010113#32)
      (instruction.ITYPE (0x040#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
      Register.x2 (vsp + sign_extend (m := 64) (0x040#12))
      (0x13#8) (0x01#8) (0x01#8) (0x04#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_04010113 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_itype_addi_char (0x040#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
        (afterNextPC (afterPrelude σ5) (0x8000e9c4#64))
        (sigma3_alu σ5 (0x8000e9c4#64) Register.x2 (vsp + sign_extend (m := 64) (0x040#12)))
        (rX_bits_x2 _ vsp hx2n6) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x040#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000e9c8#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000e9c4#64 : BitVec 64) 4 = (0x8000e9c8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_6 : σ6.regs.get? Register.x2 = some (vsp + sign_extend (m := 64) (0x040#12)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hx1_6 : σ6.regs.get? Register.x1 = some vra :=
    obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_5
  have hx9_6 : σ6.regs.get? Register.x9 = some vsink :=
    obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_5
  have hx10_6 : σ6.regs.get? Register.x10 = some (0#64) :=
    obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_5
  have hload6 : __ssprint_rLoaded σ6.mem := hmem6 ▸ hload5
  -- === 8000e9c8: ret (jr ra)  ⇒  PC := vra ===
  obtain ⟨hi0', hi1', hi2', hi3'⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e9c8 hload6
  have hx1n7 : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ6) (0x8000e9c8#64))
      = .ok vra (afterNextPC (afterPrelude σ6) (0x8000e9c8#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ6 (0x8000e9c8#64) _ (by decide) (by decide)]; exact hx1_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_jr σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x8000e9c8#64) vmi6 vra
      (0x00008067#32) (0x000#12) (regidx.Regidx 0x01#5)
      (0x67#8) (0x80#8) (0x00#8) (0x00#8)
      hG6 hpc6 hmi6 hi0' hi1' hi2' hi3' (by decide) (by decide) (by decide)
      (by decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      hx1n7 hratgt hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC
      = some (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1) := obs_jr_pc hobs7
  have hx10_7 : σ7.regs.get? Register.x10 = some (0#64) :=
    obs_jr_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_6
  have hx1_7 : σ7.regs.get? Register.x1 = some vra :=
    obs_jr_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_6
  have hx9_7 : σ7.regs.get? Register.x9 = some vsink :=
    obs_jr_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_6
  have hx2_7 : σ7.regs.get? Register.x2 = some (vsp + sign_extend (m := 64) (0x040#12)) :=
    obs_jr_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  refine ⟨⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG7, hpc7, hx10_7, hx1_7, hx9_7, hx2_7,
    hi7, hG7.minstret⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      (Steps.single hstep7))))))
