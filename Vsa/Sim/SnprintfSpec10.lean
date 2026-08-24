import Vsa.Sim.SnprintfSpec9

/-!
# M3 Layer-3 — `SnprintfSpec10` : the `__ssprint_r` entry save-block + empty-flush
short-circuit head (`_ss10`)

The prologue and loop-guard head of `__ssprint_r` (`0x8000e908`, the string-sink
flush that `snprintf("%lld", …)` calls to move the formatted iov into the caller
buffer), on the **`resid == 0` (empty flush) path**:

```
8000e908: ld   a4,16(a2)      load  _uio.uio_resid  (bytes remaining)
8000e90c: addi sp,sp,-64      allocate the 64-byte frame
8000e910: sd   s1,40(sp)      spill the caller's s1
8000e914: sd   ra,56(sp)      spill the return address
8000e918: mv   s1,a2          s1 := the sink (uio) pointer
8000e91c: beqz a4,0x8000e9b0  resid == 0 ⇒ short-circuit to the return tail
```

`ssprintHeadEmpty_spec` is a `Triple` (`Steps`) over these six instructions on
the branch-taken arm, gluing directly onto `ssprintTail_spec` (`SnprintfSpec9`,
the block `0x8000e9b0 … 0x8000e9c8`) to give an **end-to-end run of the empty-flush
`__ssprint_r` call**: entry `0x8000e908` → return to the caller (`vra`).

## Effect characterized

From `0x8000e908` with `a2 = vsink` (the sink `FILE`/`uio` pointer), `sp = vsp`,
`ra = vra`, and the sink's `resid` field (`[vsink+16, vsink+24)`) holding `0`
(supplied as `SlotHolds vsink 0x010 0` — the caller has already drained the sink),
this runs to the caller resume PC `vra` with `a0 = 0` (success), the frame popped
back to `vsp`, `s1`/`ra` restored, and the sink's `resid`/`iovcnt` fields cleared.

## Composition with `ssprintTail_spec`

`ssprintTail_spec` requires, at its entry `0x8000e9b0`, that the current `s1`
(`x9`) equals the sink pointer `vsink` **and** that the spilled `s1` slot
(`sp+40`) also equals `vsink`.  The head spills the *caller's* `s1` at `sp+40`
(before the `mv s1,a2`), so the composition is sound exactly when the caller's
saved `s1` already holds the sink pointer.  We surface that as the explicit
hypothesis `hs1caller : (caller s1) = vsink`; the whole spec is stated with a
single `vsink` for both, matching `ssprintTail`'s convention.  (The general case,
where the reloaded `s1` differs from `vsink`, needs `ssprintTail` re-stated with
two independent values — a follow-up, see the report.)

Built on the shared `StepObs` site helpers + `obs_*` accessors and the
`__ssprint_rLoaded` byte facts, exactly as `ssprintTail_spec`.
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

/-- `SlotHolds` survives a disjoint single byte insert stated with a *raw* base
address `k` (not `sp+off`) — the mirror of `slotHolds_insert` used when the
disjoint store is the `addi`/`mv`-independent spill. -/
theorem slotHolds_writeMap8_ss10 (base : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (hdis : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ k
      ∨ k + 8 ≤ (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat)
    (h : SlotHolds base off v mem) : SlotHolds base off v (writeMap8 mem k d) :=
  slotHolds_writeMap8 base off v mem k d hdis h

/-- The `__ssprint_r` entry save-block + empty-flush short-circuit
`0x8000e908 … 0x8000e91c` (branch taken) composed with the return tail
`0x8000e9b0 … 0x8000e9c8` (`ssprintTail_spec`).

Entry at `0x8000e908` with the sink pointer `vsink` in `a2` (`x12`), stack `vsp`
in `sp` (`x2`), return address `vra` in `ra` (`x1`).  The sink's `resid` field
holds `0` (`SlotHolds vsink 0x010 0`), so the guard short-circuits to the tail.
Steps to the caller resume PC (the loaded `ra`), with `a0 = 0`, frame popped, the
sink cleared, and `s1`/`ra` restored.

`hs1caller` documents the composition constraint: the *caller's* `s1` value (which
this block spills at `sp-64+40` before overwriting `s1`) equals the sink pointer,
so the tail's `s1`-reload restores exactly `vsink` (see the file header). -/
theorem ssprintHeadEmpty_spec
    (vsp vra vsink vs1 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : __ssprint_rLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000e908#64))
    (hx1 : c.σ.regs.get? Register.x1 = some vra)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx9 : c.σ.regs.get? Register.x9 = some vs1)
    (hx12 : c.σ.regs.get? Register.x12 = some vsink)
    -- the sink's `resid` field (`[vsink+16, vsink+24)`) holds 0: empty flush
    (hresid : SlotHolds vsink 0x010 (0#64) c.σ.mem)
    -- composition constraint: the caller's spilled `s1` equals the sink pointer
    (hs1caller : vs1 = vsink)
    -- old (pre-frame) stack window in RAM, above the HTIF window, 8-aligned;
    -- 64 bytes are pushed, so require room for the frame below `vsp`
    (hsplo : 0x80000000 + 64 ≤ vsp.toNat)
    (hsphi : vsp.toNat ≤ 0x100000000)
    (hspwin : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hspalign : vsp.toNat % 8 = 0)
    -- the frame `[vsp-64, vsp)` is disjoint from the code region `[0x8000e908, 0x8000e9f8)`
    (hspcode : vsp.toNat ≤ 0x8000e908 ∨ 0x8000e9f8 + 64 ≤ vsp.toNat)
    -- the sink FILE, above the HTIF window, 8-aligned
    (hsklo : 0x80000000 ≤ vsink.toNat)
    (hskhi : vsink.toNat + 24 ≤ 0x100000000)
    (hskwin : tohostAddr + 16 ≤ vsink.toNat)
    (hskalign : vsink.toNat % 8 = 0)
    -- the sink window `[vsink+8, vsink+24)` is disjoint from the frame slots
    -- `sp-64+40` (s1) and `sp-64+56` (ra), and from the resid load slot itself
    -- is INSIDE it (the tail rewrites resid), so we only need the two callee slots.
    (hdis40 : vsink.toNat + 24 ≤ vsp.toNat - 64 + 40 ∨ vsp.toNat - 64 + 48 ≤ vsink.toNat + 8)
    (hdis56 : vsink.toNat + 24 ≤ vsp.toNat - 64 + 56 ∨ vsp.toNat - 64 + 64 ≤ vsink.toNat + 8)
    -- the sink window disjoint from the code region
    (hoffcode : vsink.toNat + 24 ≤ 0x8000e908 ∨ 0x8000e9f8 ≤ vsink.toNat + 8)
    -- the resid load window `[vsink+16, vsink+24)` disjoint from the two spill
    -- slots (so the spills don't clobber the resid value the branch reads) — but
    -- the resid load happens FIRST, so no constraint is needed; the sink window
    -- disjointness from code (for the frame stores landing in RAM) is via hspwin.
    (hratgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC
        = some (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      c'.σ.regs.get? Register.x10 = some (0#64) ∧
      c'.σ.regs.get? Register.x1 = some vra ∧
      c'.σ.regs.get? Register.x9 = some vsink ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  subst vs1
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  -- effective-address rewrite for the resid load slot (a2+16)
  have hoff16sk : (vsink + sign_extend (m := 64) (0x010#12)).toNat = vsink.toNat + 16 := by
    rw [BitVec.toNat_add,
      show (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  -- new stack pointer after the frame push
  have hnegoff : (sign_extend (m := 64) (0xfc0#12) : BitVec 64).toNat = 2 ^ 64 - 64 := by decide
  -- === 8000e908: ld a4,16(a2)  ⇒  x14 := resid = 0 ===
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hresid
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e908 hload
  have hx12n1 : (afterNextPC (afterPrelude c.σ) (0x8000e908#64)).regs.get? Register.x12 = some vsink := by
    rw [get?_afterNextPC c.σ (0x8000e908#64) _ (by decide) (by decide)]; exact hx12
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x8000e908#64) vmi0 (0x01063703#32)
      (instruction.LOAD (0x010#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, false, 8))
      Register.x14 (sign_extend (m := 64)
        (((((((((sdData_val (0#64)).extractLsb' 56 8).append ((sdData_val (0#64)).extractLsb' 48 8)).append
          ((sdData_val (0#64)).extractLsb' 40 8)).append ((sdData_val (0#64)).extractLsb' 32 8)).append
          ((sdData_val (0#64)).extractLsb' 24 8)).append ((sdData_val (0#64)).extractLsb' 16 8)).append
          ((sdData_val (0#64)).extractLsb' 8 8)).append ((sdData_val (0#64)).extractLsb' 0 8)
          : BitVec (8 * 8)))
      (0x03#8) (0x37#8) (0x06#8) (0x01#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01063703 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_ld c.σ (0x8000e908#64) (0x010#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5)
        (sigma3_alu c.σ (0x8000e908#64) Register.x14 (sign_extend (m := 64)
          (((((((((sdData_val (0#64)).extractLsb' 56 8).append ((sdData_val (0#64)).extractLsb' 48 8)).append
            ((sdData_val (0#64)).extractLsb' 40 8)).append ((sdData_val (0#64)).extractLsb' 32 8)).append
            ((sdData_val (0#64)).extractLsb' 24 8)).append ((sdData_val (0#64)).extractLsb' 16 8)).append
            ((sdData_val (0#64)).extractLsb' 8 8)).append ((sdData_val (0#64)).extractLsb' 0 8)
            : BitVec (8 * 8))))
        vsink _ _ _ _ _ _ _ _ hG (rX_bits_x12 _ vsink hx12n1)
        (wX_bits_x14 _ _)
        (by rw [hoff16sk]; omega) (by rw [hoff16sk]; omega) (Or.inr (by rw [hoff16sk]; omega))
        (by rw [hoff16sk]; omega)
        hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000e90c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000e908#64 : BitVec 64) 4 = (0x8000e90c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_1 : σ1.regs.get? Register.x14 = some (0#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble (0#64)] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx1_1 : σ1.regs.get? Register.x1 = some vra :=
    obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx9_1 : σ1.regs.get? Register.x9 = some vsink :=
    obs_alu_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9
  have hx12_1 : σ1.regs.get? Register.x12 = some vsink :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hload1 : __ssprint_rLoaded σ1.mem := hmem1 ▸ hload
  -- === 8000e90c: addi sp,sp,-64  ⇒  x2 := vsp - 64 ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e90c hload1
  have hx2n2 : (afterNextPC (afterPrelude σ1) (0x8000e90c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ1 (0x8000e90c#64) _ (by decide) (by decide)]; exact hx2_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x8000e90c#64) vmi1 (0xfc010113#32)
      (instruction.ITYPE (0xfc0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
      Register.x2 (vsp + sign_extend (m := 64) (0xfc0#12))
      (0x13#8) (0x01#8) (0x01#8) (0xfc#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_fc010113 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_itype_addi_char (0xfc0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
        (afterNextPC (afterPrelude σ1) (0x8000e90c#64))
        (sigma3_alu σ1 (0x8000e90c#64) Register.x2 (vsp + sign_extend (m := 64) (0xfc0#12)))
        (rX_bits_x2 _ vsp hx2n2) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0xfc0#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  -- the new sp value, as `ofNat (vsp.toNat - 64)`
  have hnsp : (vsp + sign_extend (m := 64) (0xfc0#12)).toNat = vsp.toNat - 64 := by
    rw [BitVec.toNat_add, hnegoff]
    have := vsp.isLt
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 64 < 2 ^ 64)]
    omega
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000e910#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000e90c#64 : BitVec 64) 4 = (0x8000e910#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_2 : σ2.regs.get? Register.x2 = some (vsp + sign_extend (m := 64) (0xfc0#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx1_2 : σ2.regs.get? Register.x1 = some vra :=
    obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
  have hx9_2 : σ2.regs.get? Register.x9 = some vsink :=
    obs_alu_other hobs2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_1
  have hx12_2 : σ2.regs.get? Register.x12 = some vsink :=
    obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hx14_2 : σ2.regs.get? Register.x14 = some (0#64) :=
    obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_1
  have hload2 : __ssprint_rLoaded σ2.mem := hmem2 ▸ hload1
  -- === 8000e910: sd s1,40(sp)  (spill caller s1 = vsink at nsp+40) ===
  -- abbreviate the new stack pointer (no Mathlib `set`)
  obtain ⟨nsp, hnspdef⟩ : ∃ nsp, nsp = vsp + sign_extend (m := 64) (0xfc0#12) := ⟨_, rfl⟩
  rw [← hnspdef] at hx2_2 hnsp
  have hoff40 : (nsp + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat - 64 + 40 := by
    rw [BitVec.toNat_add, hnsp,
      show (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e910 hload2
  have hx2n3 : (afterNextPC (afterPrelude σ2) (0x8000e910#64)).regs.get? Register.x2 = some nsp := by
    rw [get?_afterNextPC σ2 (0x8000e910#64) _ (by decide) (by decide)]; exact hx2_2
  have hx9n3 : (afterNextPC (afterPrelude σ2) (0x8000e910#64)).regs.get? Register.x9 = some vsink := by
    rw [get?_afterNextPC σ2 (0x8000e910#64) _ (by decide) (by decide)]; exact hx9_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_store σ2 i2 (c.steps + 1 + 1) (0x8000e910#64) vmi2 (0x02913423#32)
      (instruction.STORE (0x028#12, regidx.Regidx 0x09#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ2) (0x8000e910#64)).mem
        (nsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vsink))
      (0x23#8) (0x34#8) (0x91#8) (0x02#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02913423 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (exec_sd_val σ2 (0x8000e910#64) (0x028#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x02#5)
        nsp vsink hG2 (rX_bits_x2 _ nsp hx2n3) (rX_bits_x9 _ vsink hx9n3)
        (by rw [hoff40]; omega) (by rw [hoff40]; omega) (by rw [hoff40]; omega) (by rw [hoff40]; omega))
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000e914#64) := by
    have := obs_store_pc_sn4 hobs3
    rwa [show BitVec.addInt (0x8000e910#64 : BitVec 64) 4 = (0x8000e914#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_sn4 hobs3
  have hx1_3 : σ3.regs.get? Register.x1 = some vra :=
    obs_store_other_sn4 Register.x1 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
  have hx2_3 : σ3.regs.get? Register.x2 = some nsp :=
    obs_store_other_sn4 Register.x2 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx9_3 : σ3.regs.get? Register.x9 = some vsink :=
    obs_store_other_sn4 Register.x9 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_2
  have hx12_3 : σ3.regs.get? Register.x12 = some vsink :=
    obs_store_other_sn4 Register.x12 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hx14_3 : σ3.regs.get? Register.x14 = some (0#64) :=
    obs_store_other_sn4 Register.x14 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hNP2 : (afterNextPC (afterPrelude σ2) (0x8000e910#64)).mem = σ2.mem := rfl
  have hload3 : __ssprint_rLoaded σ3.mem := by
    rw [hmem3, hNP2]
    exact ssprint_writeMap8_ss _ _ _ (by rw [hoff40]; omega) hload2
  -- slot fact for s1 at nsp+40
  have hslotS1 : SlotHolds nsp 0x028 vsink σ3.mem := by
    rw [hmem3, hNP2]
    exact slotHolds_self nsp 0x028 _ vsink σ2.mem rfl
  -- === 8000e914: sd ra,56(sp)  (spill ra = vra at nsp+56) ===
  have hoff56 : (nsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat - 64 + 56 := by
    rw [BitVec.toNat_add, hnsp,
      show (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e914 hload3
  have hx2n4 : (afterNextPC (afterPrelude σ3) (0x8000e914#64)).regs.get? Register.x2 = some nsp := by
    rw [get?_afterNextPC σ3 (0x8000e914#64) _ (by decide) (by decide)]; exact hx2_3
  have hx1n4 : (afterNextPC (afterPrelude σ3) (0x8000e914#64)).regs.get? Register.x1 = some vra := by
    rw [get?_afterNextPC σ3 (0x8000e914#64) _ (by decide) (by decide)]; exact hx1_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_store σ3 i3 (c.steps + 1 + 1 + 1) (0x8000e914#64) vmi3 (0x02113c23#32)
      (instruction.STORE (0x038#12, regidx.Regidx 0x01#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ3) (0x8000e914#64)).mem
        (nsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vra))
      (0x23#8) (0x3c#8) (0x11#8) (0x02#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02113c23 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (exec_sd_val σ3 (0x8000e914#64) (0x038#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
        nsp vra hG3 (rX_bits_x2 _ nsp hx2n4) (rX_bits_x1 _ vra hx1n4)
        (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega))
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000e918#64) := by
    have := obs_store_pc_sn4 hobs4
    rwa [show BitVec.addInt (0x8000e914#64 : BitVec 64) 4 = (0x8000e918#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_sn4 hobs4
  have hx1_4 : σ4.regs.get? Register.x1 = some vra :=
    obs_store_other_sn4 Register.x1 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_3
  have hx2_4 : σ4.regs.get? Register.x2 = some nsp :=
    obs_store_other_sn4 Register.x2 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx9_4 : σ4.regs.get? Register.x9 = some vsink :=
    obs_store_other_sn4 Register.x9 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_3
  have hx12_4 : σ4.regs.get? Register.x12 = some vsink :=
    obs_store_other_sn4 Register.x12 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  have hx14_4 : σ4.regs.get? Register.x14 = some (0#64) :=
    obs_store_other_sn4 Register.x14 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_3
  have hNP3 : (afterNextPC (afterPrelude σ3) (0x8000e914#64)).mem = σ3.mem := rfl
  have hload4 : __ssprint_rLoaded σ4.mem := by
    rw [hmem4, hNP3]
    exact ssprint_writeMap8_ss _ _ _ (by rw [hoff56]; omega) hload3
  -- ra slot (fresh) and s1 slot (survives the ra store — disjoint 40 vs 56)
  have hslotRA : SlotHolds nsp 0x038 vra σ4.mem := by
    rw [hmem4, hNP3]
    exact slotHolds_self nsp 0x038 _ vra σ3.mem rfl
  have hslotS1' : SlotHolds nsp 0x028 vsink σ4.mem := by
    rw [hmem4, hNP3]
    exact slotHolds_writeMap8 nsp 0x028 vsink σ3.mem _ _
      (by rw [hoff56, hoff40]; omega) hslotS1
  -- === 8000e918: mv s1,a2  ⇒  x9 := vsink (already vsink; identity here) ===
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e918 hload4
  have hx12n5 : (afterNextPC (afterPrelude σ4) (0x8000e918#64)).regs.get? Register.x12 = some vsink := by
    rw [get?_afterNextPC σ4 (0x8000e918#64) _ (by decide) (by decide)]; exact hx12_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000e918#64) vmi4 (0x00060493#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x09#5, iop.ADDI))
      Register.x9 (vsink + sign_extend (m := 64) (0x000#12))
      (0x93#8) (0x04#8) (0x06#8) (0x00#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00060493 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x09#5) vsink
        (afterNextPC (afterPrelude σ4) (0x8000e918#64))
        (sigma3_alu σ4 (0x8000e918#64) Register.x9 (vsink + sign_extend (m := 64) (0x000#12)))
        (rX_bits_x12 _ vsink hx12n5) (wX_bits_x9 _ (vsink + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000e91c#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000e918#64 : BitVec 64) 4 = (0x8000e91c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hmv0 : (vsink + sign_extend (m := 64) (0x000#12) : BitVec 64) = vsink := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 from by decide]
    simp [Nat.mod_eq_of_lt vsink.isLt]
  have hx9_5 : σ5.regs.get? Register.x9 = some vsink := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hmv0] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx1_5 : σ5.regs.get? Register.x1 = some vra :=
    obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_4
  have hx2_5 : σ5.regs.get? Register.x2 = some nsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx14_5 : σ5.regs.get? Register.x14 = some (0#64) :=
    obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_4
  have hload5 : __ssprint_rLoaded σ5.mem := hmem5 ▸ hload4
  have hslotRA5 : SlotHolds nsp 0x038 vra σ5.mem := hmem5 ▸ hslotRA
  have hslotS15 : SlotHolds nsp 0x028 vsink σ5.mem := hmem5 ▸ hslotS1'
  -- === 8000e91c: beqz a4,0x8000e9b0  (taken since a4 = 0) ===
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.__ssprint_r_at_8000e91c hload5
  have hx14n6 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ5) (0x8000e91c#64))
      = .ok (0#64) (afterNextPC (afterPrelude σ5) (0x8000e91c#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ5 (0x8000e91c#64) _ (by decide) (by decide)]; exact hx14_5
  have hbtgt : ((0x8000e91c#64 : BitVec 64) + sign_extend (m := 64) (0x0094#13)).toNat % 4 = 0 := by
    decide
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_branch_taken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x8000e91c#64) vmi5
      (0x0094#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BEQ (0x08070a63#32)
      (0x63#8) (0x0a#8) (0x07#8) (0x08#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_08070a63 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_btype_beq_taken (0x0094#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5)
        (0#64) (0#64) (0x8000e91c#64) initMisa (afterNextPC (afterPrelude σ5) (0x8000e91c#64))
        hx14n6 (rX_bits_zero _)
        (by rw [get?_afterNextPC σ5 (0x8000e91c#64) _ (by decide) (by decide)]; exact hpc5)
        (by rw [get?_afterNextPC σ5 (0x8000e91c#64) _ (by decide) (by decide)]; exact hG5.misa)
        hbtgt (by decide))
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000e9b0#64) := by
    have := obs_branch_taken_pc hobs6
    rwa [show ((0x8000e91c#64 : BitVec 64) + sign_extend (m := 64) (0x0094#13))
      = (0x8000e9b0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_branch_taken_minstret hobs6
  have hx1_6 : σ6.regs.get? Register.x1 = some vra :=
    obs_branch_taken_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_5
  have hx2_6 : σ6.regs.get? Register.x2 = some nsp :=
    obs_branch_taken_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx9_6 : σ6.regs.get? Register.x9 = some vsink :=
    obs_branch_taken_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_5
  have hload6 : __ssprint_rLoaded σ6.mem := hmem6 ▸ hload5
  have hslotRA6 : SlotHolds nsp 0x038 vra σ6.mem := hmem6 ▸ hslotRA5
  have hslotS16 : SlotHolds nsp 0x028 vsink σ6.mem := hmem6 ▸ hslotS15
  -- === compose with ssprintTail_spec at 0x8000e9b0 (frame base = nsp) ===
  have hnspNat : nsp.toNat = vsp.toNat - 64 := hnsp
  obtain ⟨c', hsteps', hG', hpc', hx10', hx1', hx9', hx2', htick', hminstret'⟩ :=
    ssprintTail_spec nsp vra vsink ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      hG6 hload6 hpc6 hx2_6 hx9_6 hslotRA6 hslotS16
      (by rw [hnspNat]; omega) (by rw [hnspNat]; omega) (by rw [hnspNat]; omega)
      (by rw [hnspNat]; omega)
      (by omega) (by omega) (by omega) (by omega)
      (by rw [hnspNat]; omega) (by rw [hnspNat]; omega)
      hoffcode hratgt hi6
  refine ⟨c', ?_, hG', hpc', hx10', hx1', hx9', ?_, htick', hminstret'⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
        hsteps')))))
  · -- ssprintTail returns sp := nsp + 64 = vsp
    rw [hx2']
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hnsp,
      show (sign_extend (m := 64) (0x040#12) : BitVec 64).toNat = 64 from by decide]
    have := vsp.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end Vsa.Sim
