import Vsa.Sim.SnprintfSpec15
import Vsa.Sim.Code.SvfprintfSlice2
import Vsa.Sim.StrcpySites
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch15Part19
import Vsa.Sim.DecodeTable.Batch11Part05
import Vsa.Sim.DecodeTable.Batch08Part18
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch02Part31
import Vsa.Sim.DecodeTable.Batch02Part14
import Vsa.Sim.DecodeTable.Batch02Part12

/-!
# M3 Layer-3 — `SnprintfSpec16` : the `%lld` `'l'`/`"ll"` length-modifier **handler
gap** + the parse-dispatch → verified-digit-path composition (`_p16`)

`SnprintfSpec14.parseDispatch_l_full_spec` reaches the `'l'` handler entry
`0x80008534`, and `SnprintfSpec15.dispatchD_ll_to_printEntry_spec` runs the `'d'`
handler `ll`-branch `0x80008008 → 0x800080e4` (the entry of
`SnprintfSpec8.entryToPrint_neg_spec`).  Between them sit two short handlers that
were **outside** `SvfprintfSliceLoaded`'s coverage — now pinned in
`Code/SvfprintfSlice2.lean`:

```
  ── 'l' handler @ 0x80008534 → "ll" @ 0x80009060 ──  (handler_l_spec)
  80008534: lbu  s8,0(s9)          s8 := format[2]  (= 'l' = 0x6c)
  80008538: li   a5,108            a5 := 'l'
  8000853c: beq  s8,a5,0x80009060  format[2]=='l' ⇒ TAKEN → "ll" handler

  ── "ll" handler @ 0x80009060 → dispatch @ 0x80007798 ──  (handler_ll_spec)
  80009060: lbu  s8,1(s9)          s8 := format[3]  (= 'd' = 0x64)
  80009064: ori  t1,t1,32          x6 := x6 ||| 0x20   (SET THE ll-FLAG)
  80009068: addi s9,s9,1           advance format cursor
  8000906c: j    0x80007798        back to the conversion dispatch

  ── 2nd dispatch pass @ 0x80007798 → slot-load @ 0x800077b4 ──  (parseDispatchArith_d_spec)
  (sext.w / addiw / bltu-nottaken / slli / srli / add on char 'd' = 0x64)
```

Composing `parseDispatch_l_full_spec` ≫ `handler_l_spec` ≫ `handler_ll_spec` ≫
`parseDispatchArith_d_spec` ≫ `SnprintfSpec13.parseDispatch_d_spec` ≫
`dispatchD_ll_to_printEntry_spec` yields **`parseToDigitEntry_spec`**, a single
`Steps` chain from the first conversion dispatch head `0x80007798` (with the `'l'`
character in `x24`) all the way through to `0x800080e4` — the exact entry of
`entryToPrint_neg_spec`, onto which it composes.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded SvfprintfSlice2Loaded __hidden___udivdi3Loaded
  FlushPinsLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Local `jump_x0` (`j`) read-back consumers (mirroring `SnprintfSpec5` /
`EnvGetSpec7`; those live outside this import closure). -/

/-- Read the PC of a `j` (`jump_x0`) step: `PC = tgt`. -/
theorem obs_jx0_pc_p16 {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jump_x0_pc σ pc vm tgt)

/-- Read any non-written register across a `j` (`jump_x0`) step. -/
theorem obs_jx0_other_p16 {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_jump_x0_other σ pc vm tgt R h1 h2 h4 h5).trans hσ)

theorem printEntryFrame_branch_nottaken {σ' σ : MState} {pc vm : BitVec 64}
    {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm))
    (h : PrintEntryFrame σ v8 v23 v12) : PrintEntryFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_branch_nottaken_other hobs Register.x8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx8,
    obs_branch_nottaken_other hobs Register.x23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx23,
    obs_branch_nottaken_other hobs Register.x12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx12⟩

theorem printEntryFrame_jx0 {σ' σ : MState} {pc vm tgt : BitVec 64}
    {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt))
    (h : PrintEntryFrame σ v8 v23 v12) : PrintEntryFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_jx0_other_p16 hobs Register.x8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx8,
    obs_jx0_other_p16 hobs Register.x23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx23,
    obs_jx0_other_p16 hobs Register.x12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx12⟩

/-! ## `handler_l_spec` — the `'l'` handler `0x80008534 → 0x80009060`

From `0x80008534` with the format cursor `s9 = x25 = vcur` pointing at the second
`'l'` (`mem[vcur] = 0x6c`), run `lbu s8,0(s9)` / `li a5,108` / `beq s8,a5,…`; the
compare succeeds (`format[2] == 'l'`), so the `beq` is **taken** to the `"ll"`
handler `0x80009060`.  The ll-flag word `x6`, the field width `x20`, the frame
`x2`, and the cursor `x25` are threaded through unchanged. -/
theorem handler_l_spec
    (vsp vcur v6 v20 v22 v26 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSlice2Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008534#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    -- s6 (x22) = table base, s10 (x26) = dispatch bound — carried, never written
    (hx22 : c.σ.regs.get? Register.x22 = some v22)
    (hx26 : c.σ.regs.get? Register.x26 = some v26)
    -- s11 (x27) — carried, never written (source of the later `mv t3,s11`)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    -- s9 = format cursor, pointing at the second 'l'
    (hx25 : c.σ.regs.get? Register.x25 = some vcur)
    -- format[2] = 'l' (0x6c) at the cursor
    (hbyte : c.σ.mem[vcur.toNat]? = some (0x6c#8))
    -- the cursor is readable RAM above the HTIF window
    (hclo : 0x80000000 ≤ vcur.toNat)
    (hchiram : vcur.toNat + 1 ≤ 0x100000000)
    (hchtif : vcur.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80009060#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some vcur ∧
      c'.σ.regs.get? Register.x22 = some v22 ∧
      c'.σ.regs.get? Register.x26 = some v26 ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      SvfprintfSlice2Loaded c'.σ.mem ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
        PrintEntryFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff0 : (vcur + sign_extend (m := 64) (0x000#12)).toNat = vcur.toNat := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x000#12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt vcur.isLt]
  -- ══ 80008534: lbu s8,0(s9)  ⇒ x24 := zext(format[2]) = 0x6c ══
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_80008534 hload
  have hx25n0 : (afterNextPC (afterPrelude c.σ) (0x80008534#64)).regs.get? Register.x25 = some vcur := by
    rw [get?_afterNextPC c.σ (0x80008534#64) _ (by decide) (by decide)]; exact hx25
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x80008534#64) vmi0 (0x000ccc03#32)
      (instruction.LOAD (0x000#12, regidx.Regidx 0x19#5, regidx.Regidx 0x18#5, true, 1))
      Register.x24 (zero_extend (m := 64) (0x6c#8))
      (0x03#8) (0xcc#8) (0x0c#8) (0x00#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000ccc03 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_lbu_gen c.σ (0x80008534#64) (0x000#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x18#5)
        vcur (0x6c#8) (sigma3_alu c.σ (0x80008534#64) Register.x24 (zero_extend (m := 64) (0x6c#8)))
        hG (rX_bits_x25 _ vcur hx25n0) (wX_bits_x24 _ _)
        (by rw [hoff0]; exact hclo) (by rw [hoff0]; exact hchiram) (by rw [hoff0]; exact hchtif)
        (by rw [hoff0]; exact hbyte))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x80008538#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80008534#64 : BitVec 64) 4 = (0x80008538#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx24_1 : σ1.regs.get? Register.x24 = some (BitVec.ofNat 64 0x6c) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x6c#8)) = BitVec.ofNat 64 0x6c from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx25_1 : σ1.regs.get? Register.x25 = some vcur :=
    obs_alu_other hobs1 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25
  have hx22_1 : σ1.regs.get? Register.x22 = some v22 :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hx26_1 : σ1.regs.get? Register.x26 = some v26 :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26
  have hx27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27
  have hload1 : SvfprintfSlice2Loaded σ1.mem := hmem1 ▸ hload
  have hframe1 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ1 v8 v23 v12 := fun _ _ _ h =>
    printEntryFrame_alu hobs1 (by decide) (by decide) (by decide) h
  -- ══ 80008538: li a5,108  (= addi a5,x0,108)  ⇒ x15 := 0x6c ══
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_80008538 hload1
  have hx0n1 : (rX_bits (regidx.Regidx 0x00#5)).run (afterNextPC (afterPrelude σ1) (0x80008538#64))
      = .ok (0#64) (afterNextPC (afterPrelude σ1) (0x80008538#64)) := rX_bits_zero _
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x80008538#64) vmi1 (0x06c00793#32)
      (instruction.ITYPE (0x06c#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
      Register.x15 ((0#64) + (sign_extend (m := 64) (0x06c#12)))
      (0x93#8) (0x07#8) (0xc0#8) (0x06#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_06c00793 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_itype_addi_char (0x06c#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5)
        (0#64) (afterNextPC (afterPrelude σ1) (0x80008538#64))
        (sigma3_alu σ1 (0x80008538#64) Register.x15 ((0#64) + (sign_extend (m := 64) (0x06c#12))))
        hx0n1 (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000853c#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80008538#64 : BitVec 64) 4 = (0x8000853c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx15_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 0x6c) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + (sign_extend (m := 64) (0x06c#12))) = BitVec.ofNat 64 0x6c from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx24_2 : σ2.regs.get? Register.x24 = some (BitVec.ofNat 64 0x6c) :=
    obs_alu_other hobs2 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx24_1
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx25_2 : σ2.regs.get? Register.x25 = some vcur :=
    obs_alu_other hobs2 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_1
  have hx22_2 : σ2.regs.get? Register.x22 = some v22 :=
    obs_alu_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hx26_2 : σ2.regs.get? Register.x26 = some v26 :=
    obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_1
  have hload2 : SvfprintfSlice2Loaded σ2.mem := hmem2 ▸ hload1
  have hframe2 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ2 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs2 (by decide) (by decide) (by decide) (hframe1 v8 v23 v12 h)
  -- ══ 8000853c: beq s8,a5,0x80009060  ⇒ TAKEN (0x6c == 0x6c)  → 0x80009060 ══
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_8000853c hload2
  have hx24n2 : (rX_bits (regidx.Regidx 0x18#5)).run (afterNextPC (afterPrelude σ2) (0x8000853c#64))
      = .ok (BitVec.ofNat 64 0x6c) (afterNextPC (afterPrelude σ2) (0x8000853c#64)) := by
    apply rX_bits_x24
    rw [get?_afterNextPC σ2 (0x8000853c#64) _ (by decide) (by decide)]; exact hx24_2
  have hx15n2 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ2) (0x8000853c#64))
      = .ok (BitVec.ofNat 64 0x6c) (afterNextPC (afterPrelude σ2) (0x8000853c#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ2 (0x8000853c#64) _ (by decide) (by decide)]; exact hx15_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_branch_taken σ2 i2 (c.steps + 1 + 1) (0x8000853c#64) vmi2
      (0x0b24#13) (regidx.Regidx 0x18#5) (regidx.Regidx 0x0f#5) bop.BEQ (0x32fc02e3#32)
      (0xe3#8) (0x02#8) (0xfc#8) (0x32#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_32fc02e3 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_btype_beq_taken (0x0b24#13) (regidx.Regidx 0x18#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 0x6c) (BitVec.ofNat 64 0x6c) (0x8000853c#64) (Vsa.Sim.initMisa)
        (afterNextPC (afterPrelude σ2) (0x8000853c#64))
        hx24n2 hx15n2
        (by rw [get?_afterNextPC σ2 (0x8000853c#64) _ (by decide) (by decide)]; exact hpc2)
        (by rw [get?_afterNextPC σ2 (0x8000853c#64) _ (by decide) (by decide)]; exact hG2.misa)
        (by decide) (by decide))
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x80009060#64) := by
    have := obs_branch_taken_pc hobs3
    rwa [show (0x8000853c#64 : BitVec 64) + sign_extend (m := 64) (0x0b24#13)
        = (0x80009060#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some v6 :=
    obs_branch_taken_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_branch_taken_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx25_3 : σ3.regs.get? Register.x25 = some vcur :=
    obs_branch_taken_other hobs3 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_2
  have hx22_3 : σ3.regs.get? Register.x22 = some v22 :=
    obs_branch_taken_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hx26_3 : σ3.regs.get? Register.x26 = some v26 :=
    obs_branch_taken_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx27_3 : σ3.regs.get? Register.x27 = some v27 :=
    obs_branch_taken_other hobs3 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_2
  have hload3 : SvfprintfSlice2Loaded σ3.mem := hmem3 ▸ hload2
  have hmemc : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  have hframe3 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ3 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_branch hobs3 (hframe2 v8 v23 v12 h)
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩, ?_, hG3, hpc3, hx2_3, hx6_3, hx20_3, hx25_3, hx22_3, hx26_3,
    hx27_3, hload3, hmemc, hframe3, hi3⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans (Steps.single hstep3))

/-! ## `handler_ll_spec` — the `"ll"` handler `0x80009060 → 0x80007798`

Sets the ll-flag `x6 := x6 ||| 0x20`, reads the conversion char `format[3]` into
`s8 = x24`, bumps the cursor `s9 := s9 + 1`, and jumps back to the conversion
dispatch head `0x80007798`.  For the `%lld` path `format[3] = 'd' = 0x64`, so
`x24 = 0x64` at the re-entry (feeding the second dispatch pass). -/
theorem handler_ll_spec
    (vsp vcur v6 v20 v22 v26 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSlice2Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80009060#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    -- s6 (x22) = table base, s10 (x26) = dispatch bound — carried, never written
    (hx22 : c.σ.regs.get? Register.x22 = some v22)
    (hx26 : c.σ.regs.get? Register.x26 = some v26)
    -- s11 (x27) — carried, never written
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (hx25 : c.σ.regs.get? Register.x25 = some vcur)
    -- format[3] = 'd' (0x64) at cursor+1
    (hbyte : c.σ.mem[vcur.toNat + 1]? = some (0x64#8))
    -- the format cursor is in RAM below 2^32 (so `cursor+1` does not wrap)
    (hcurhi : vcur.toNat + 1 ≤ 0x100000000)
    (hclo : 0x80000000 ≤ (vcur + sign_extend (m := 64) (0x001#12)).toNat)
    (hchiram : (vcur + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ 0x100000000)
    (hchtif : (vcur + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (vcur + sign_extend (m := 64) (0x001#12)).toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007798#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some (v6 ||| (sign_extend (m := 64) (0x020#12))) ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) ∧
      c'.σ.regs.get? Register.x25 = some (vcur + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x22 = some v22 ∧
      c'.σ.regs.get? Register.x26 = some v26 ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      SvfprintfSlice2Loaded c'.σ.mem ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
        PrintEntryFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff1 : (vcur + sign_extend (m := 64) (0x001#12)).toNat = vcur.toNat + 1 := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x001#12)).toNat = 1 from by decide]
    rw [Nat.mod_eq_of_lt (by omega)]
  -- ══ 80009060: lbu s8,1(s9)  ⇒ x24 := zext(format[3]) = 0x64 ══
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_80009060 hload
  have hx25n0 : (afterNextPC (afterPrelude c.σ) (0x80009060#64)).regs.get? Register.x25 = some vcur := by
    rw [get?_afterNextPC c.σ (0x80009060#64) _ (by decide) (by decide)]; exact hx25
  have hbyte' : c.σ.mem[(vcur + sign_extend (m := 64) (0x001#12)).toNat]? = some (0x64#8) := by
    rw [hoff1]; exact hbyte
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x80009060#64) vmi0 (0x001ccc03#32)
      (instruction.LOAD (0x001#12, regidx.Regidx 0x19#5, regidx.Regidx 0x18#5, true, 1))
      Register.x24 (zero_extend (m := 64) (0x64#8))
      (0x03#8) (0xcc#8) (0x1c#8) (0x00#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001ccc03 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_lbu_gen c.σ (0x80009060#64) (0x001#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x18#5)
        vcur (0x64#8) (sigma3_alu c.σ (0x80009060#64) Register.x24 (zero_extend (m := 64) (0x64#8)))
        hG (rX_bits_x25 _ vcur hx25n0) (wX_bits_x24 _ _)
        hclo hchiram hchtif hbyte')
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x80009064#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80009060#64 : BitVec 64) 4 = (0x80009064#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx24_1 : σ1.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x64#8)) = BitVec.ofNat 64 0x64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx25_1 : σ1.regs.get? Register.x25 = some vcur :=
    obs_alu_other hobs1 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25
  have hx22_1 : σ1.regs.get? Register.x22 = some v22 :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hx26_1 : σ1.regs.get? Register.x26 = some v26 :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26
  have hx27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27
  have hload1 : SvfprintfSlice2Loaded σ1.mem := hmem1 ▸ hload
  have hframe1 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ1 v8 v23 v12 := fun _ _ _ h =>
    printEntryFrame_alu hobs1 (by decide) (by decide) (by decide) h
  -- ══ 80009064: ori t1,t1,32  ⇒ x6 := x6 ||| 0x20 ══
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_80009064 hload1
  have hx6n1 : (rX_bits (regidx.Regidx 0x06#5)).run (afterNextPC (afterPrelude σ1) (0x80009064#64))
      = .ok v6 (afterNextPC (afterPrelude σ1) (0x80009064#64)) := by
    apply rX_bits_x6
    rw [get?_afterNextPC σ1 (0x80009064#64) _ (by decide) (by decide)]; exact hx6_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x80009064#64) vmi1 (0x02036313#32)
      (instruction.ITYPE (0x020#12, regidx.Regidx 0x06#5, regidx.Regidx 0x06#5, iop.ORI))
      Register.x6 (v6 ||| (sign_extend (m := 64) (0x020#12)))
      (0x13#8) (0x63#8) (0x03#8) (0x02#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02036313 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_itype_ori_char (0x020#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x06#5)
        v6 (afterNextPC (afterPrelude σ1) (0x80009064#64))
        (sigma3_alu σ1 (0x80009064#64) Register.x6 (v6 ||| (sign_extend (m := 64) (0x020#12))))
        hx6n1 (wX_bits_x6 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x80009068#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80009064#64 : BitVec 64) 4 = (0x80009068#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx6_2 : σ2.regs.get? Register.x6 = some (v6 ||| (sign_extend (m := 64) (0x020#12))) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx24_2 : σ2.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) :=
    obs_alu_other hobs2 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx24_1
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx25_2 : σ2.regs.get? Register.x25 = some vcur :=
    obs_alu_other hobs2 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_1
  have hx22_2 : σ2.regs.get? Register.x22 = some v22 :=
    obs_alu_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hx26_2 : σ2.regs.get? Register.x26 = some v26 :=
    obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_1
  have hload2 : SvfprintfSlice2Loaded σ2.mem := hmem2 ▸ hload1
  have hframe2 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ2 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs2 (by decide) (by decide) (by decide) (hframe1 v8 v23 v12 h)
  -- ══ 80009068: addi s9,s9,1  ⇒ x25 := vcur + 1 ══
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_80009068 hload2
  have hx25n2 : (rX_bits (regidx.Regidx 0x19#5)).run (afterNextPC (afterPrelude σ2) (0x80009068#64))
      = .ok vcur (afterNextPC (afterPrelude σ2) (0x80009068#64)) := by
    apply rX_bits_x25
    rw [get?_afterNextPC σ2 (0x80009068#64) _ (by decide) (by decide)]; exact hx25_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_alu σ2 i2 (c.steps + 1 + 1) (0x80009068#64) vmi2 (0x001c8c93#32)
      (instruction.ITYPE (0x001#12, regidx.Regidx 0x19#5, regidx.Regidx 0x19#5, iop.ADDI))
      Register.x25 (vcur + (sign_extend (m := 64) (0x001#12)))
      (0x93#8) (0x8c#8) (0x1c#8) (0x00#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001c8c93 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x19#5)
        vcur (afterNextPC (afterPrelude σ2) (0x80009068#64))
        (sigma3_alu σ2 (0x80009068#64) Register.x25 (vcur + (sign_extend (m := 64) (0x001#12))))
        hx25n2 (wX_bits_x25 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000906c#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80009068#64 : BitVec 64) 4 = (0x8000906c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx25_3 : σ3.regs.get? Register.x25 = some (vcur + (sign_extend (m := 64) (0x001#12))) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx6_3 : σ3.regs.get? Register.x6 = some (v6 ||| (sign_extend (m := 64) (0x020#12))) :=
    obs_alu_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx24_3 : σ3.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) :=
    obs_alu_other hobs3 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx24_2
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx22_3 : σ3.regs.get? Register.x22 = some v22 :=
    obs_alu_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hx26_3 : σ3.regs.get? Register.x26 = some v26 :=
    obs_alu_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx27_3 : σ3.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs3 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_2
  have hload3 : SvfprintfSlice2Loaded σ3.mem := hmem3 ▸ hload2
  have hframe3 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ3 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs3 (by decide) (by decide) (by decide) (hframe2 v8 v23 v12 h)
  -- ══ 8000906c: j 0x80007798  ⇒ PC := 0x80007798 ══
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice2_at_8000906c hload3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_j σ3 i3 (c.steps + 1 + 1 + 1) (0x8000906c#64) vmi3 (0xf2cfe06f#32)
      (0x1fe72c#21) (0x6f#8) (0xe0#8) (0xcf#8) (0xf2#8)
      hG3 hpc3 hmi3 he0 he1 he2 he3 (by decide) (by simp only [tohostAddr]; decide) (by decide)
      (by decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_f2cfe06f (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have htgteq : (0x8000906c#64 : BitVec 64) + sign_extend (m := 64) (0x1fe72c#21)
      = (0x80007798#64 : BitVec 64) := by apply BitVec.eq_of_toNat_eq; decide
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007798#64) := by
    have := obs_jx0_pc_p16 hobs4; rwa [htgteq] at this
  have hx6_4 : σ4.regs.get? Register.x6 = some (v6 ||| (sign_extend (m := 64) (0x020#12))) :=
    obs_jx0_other_p16 hobs4 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx24_4 : σ4.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) :=
    obs_jx0_other_p16 hobs4 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx24_3
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_jx0_other_p16 hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_jx0_other_p16 hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx25_4 : σ4.regs.get? Register.x25 = some (vcur + (sign_extend (m := 64) (0x001#12))) :=
    obs_jx0_other_p16 hobs4 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_3
  have hx22_4 : σ4.regs.get? Register.x22 = some v22 :=
    obs_jx0_other_p16 hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx26_4 : σ4.regs.get? Register.x26 = some v26 :=
    obs_jx0_other_p16 hobs4 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_3
  have hx27_4 : σ4.regs.get? Register.x27 = some v27 :=
    obs_jx0_other_p16 hobs4 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_3
  have hload4 : SvfprintfSlice2Loaded σ4.mem := hmem4 ▸ hload3
  have hmemc : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
  have hframe4 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ4 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_jx0 hobs4 (hframe3 v8 v23 v12 h)
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, ?_, hG4, hpc4, hx2_4, hx6_4, hx20_4, hx24_4, hx25_4,
    hx22_4, hx26_4, hx27_4, hload4, hmemc, hframe4, hi4⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    (Steps.single hstep4)))

/-! ## `parseDispatchArith_d_spec` — 2nd-pass slot-address arithmetic for `'d'`

Identical to `SnprintfSpec14.parseDispatchArith_l_spec` but for the conversion
character `'d' = 0x64` (index `0x64-32 = 68`), driving the SECOND dispatch pass the
`"ll"` handler branches back to.  `0x80007798 → 0x800077b4` with the `'d'` slot
address in `x15`. -/
theorem parseDispatchArith_d_spec
    (vsp vs9 v6 v20 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007798#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    -- s8 = the conversion character 'd' = 0x64
    (hx24 : c.σ.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64))
    -- s10 = 90 (dispatch upper bound, from parseInit)
    (hx26 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90))
    -- s6 = jump-table base (from parseInit's auipc/addi)
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    -- s9 = loop counter (read+bumped; final value = vs9+1)
    (hx25 : c.σ.regs.get? Register.x25 = some vs9)
    -- x6/x20/x27 are threaded unchanged through the dispatch arithmetic
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800077b4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x15
        = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x64 - 32))) ∧
      c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
        PrintEntryFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  -- === 7798: addi s9,s9,1  ⇒  x25 := vs9 + 1  (dead) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007798 hload
  have hx25n1 : (afterNextPC (afterPrelude c.σ) (0x80007798#64)).regs.get? Register.x25 = some vs9 := by
    rw [get?_afterNextPC c.σ (0x80007798#64) _ (by decide) (by decide)]; exact hx25
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x80007798#64) vmi0 (0x001c8c93#32)
      (instruction.ITYPE (0x001#12, regidx.Regidx 0x19#5, regidx.Regidx 0x19#5, iop.ADDI))
      Register.x25 (vs9 + sign_extend (m := 64) (0x001#12))
      (0x93#8) (0x8c#8) (0x1c#8) (0x00#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001c8c93 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x19#5) vs9
        (afterNextPC (afterPrelude c.σ) (0x80007798#64))
        (sigma3_alu c.σ (0x80007798#64) Register.x25 (vs9 + sign_extend (m := 64) (0x001#12)))
        (rX_bits_x25 _ vs9 hx25n1) (wX_bits_x25 _ (vs9 + sign_extend (m := 64) (0x001#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000779c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007798#64 : BitVec 64) 4 = (0x8000779c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx24_1 : σ1.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) :=
    obs_alu_other hobs1 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx24
  have hx26_1 : σ1.regs.get? Register.x26 = some (BitVec.ofNat 64 90) :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26
  have hx22_1 : σ1.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hx25_1 : σ1.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx6_1 : σ1.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hframe1 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ1 v8 v23 v12 := fun _ _ _ h =>
    printEntryFrame_alu hobs1 (by decide) (by decide) (by decide) h
  -- === 779c: sext.w s8,s8  ⇒  x24 := sext32(extractLsb (0x64 + 0) 31 0) = 0x64 ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000779c hload1
  have hx24n2 : (afterNextPC (afterPrelude σ1) (0x8000779c#64)).regs.get? Register.x24
      = some (BitVec.ofNat 64 0x64) := by
    rw [get?_afterNextPC σ1 (0x8000779c#64) _ (by decide) (by decide)]; exact hx24_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x8000779c#64) vmi1 (0x000c0c1b#32)
      (instruction.ADDIW (0x000#12, regidx.Regidx 0x18#5, regidx.Regidx 0x18#5))
      Register.x24
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x64) + sign_extend (m := 64) (0x000#12)) 31 0))
      (0x1b#8) (0x0c#8) (0x0c#8) (0x00#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000c0c1b (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_addiw_char (0x000#12) (regidx.Regidx 0x18#5) (regidx.Regidx 0x18#5)
        (BitVec.ofNat 64 0x64) (afterNextPC (afterPrelude σ1) (0x8000779c#64))
        (sigma3_alu σ1 (0x8000779c#64) Register.x24
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x64) + sign_extend (m := 64) (0x000#12)) 31 0)))
        (rX_bits_x24 _ (BitVec.ofNat 64 0x64) hx24n2)
        (wX_bits_x24 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x800077a0#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000779c#64 : BitVec 64) 4 = (0x800077a0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx24_2 : σ2.regs.get? Register.x24 = some (BitVec.ofNat 64 0x64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x64) + sign_extend (m := 64) (0x000#12)) 31 0))
        = BitVec.ofNat 64 0x64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx26_2 : σ2.regs.get? Register.x26 = some (BitVec.ofNat 64 90) :=
    obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx22_2 : σ2.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hx25_2 : σ2.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs2 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_1
  have hx6_2 : σ2.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hframe2 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ2 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs2 (by decide) (by decide) (by decide) (hframe1 v8 v23 v12 h)
  -- === 77a0: addiw a5,s8,-32  ⇒  x15 := sext32(0x64 - 32) = 0x64-32 = 76 ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a0 hload2
  have hx24n3 : (afterNextPC (afterPrelude σ2) (0x800077a0#64)).regs.get? Register.x24
      = some (BitVec.ofNat 64 0x64) := by
    rw [get?_afterNextPC σ2 (0x800077a0#64) _ (by decide) (by decide)]; exact hx24_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_alu σ2 i2 (c.steps + 1 + 1) (0x800077a0#64) vmi2 (0xfe0c079b#32)
      (instruction.ADDIW (0xfe0#12, regidx.Regidx 0x18#5, regidx.Regidx 0x0f#5))
      Register.x15
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x64) + sign_extend (m := 64) (0xfe0#12)) 31 0))
      (0x9b#8) (0x07#8) (0x0c#8) (0xfe#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_fe0c079b (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_addiw_char (0xfe0#12) (regidx.Regidx 0x18#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 0x64) (afterNextPC (afterPrelude σ2) (0x800077a0#64))
        (sigma3_alu σ2 (0x800077a0#64) Register.x15
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x64) + sign_extend (m := 64) (0xfe0#12)) 31 0)))
        (rX_bits_x24 _ (BitVec.ofNat 64 0x64) hx24n3)
        (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x800077a4#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800077a0#64 : BitVec 64) 4 = (0x800077a4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx15_3 : σ3.regs.get? Register.x15 = some (BitVec.ofNat 64 (0x64 - 32)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x64) + sign_extend (m := 64) (0xfe0#12)) 31 0))
        = BitVec.ofNat 64 (0x64 - 32) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx26_3 : σ3.regs.get? Register.x26 = some (BitVec.ofNat 64 90) :=
    obs_alu_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx22_3 : σ3.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hx25_3 : σ3.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs3 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_2
  have hx6_3 : σ3.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx27_3 : σ3.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs3 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hframe3 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ3 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs3 (by decide) (by decide) (by decide) (hframe2 v8 v23 v12 h)
  -- === 77a4: bltu s10,a5,+..  ⇒  NOT taken (90 not < 76); falls through to 77a8 ===
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a4 hload3
  have hs10r : (rX_bits (regidx.Regidx 0x1a#5)).run (afterNextPC (afterPrelude σ3) (0x800077a4#64))
      = .ok (BitVec.ofNat 64 90) (afterNextPC (afterPrelude σ3) (0x800077a4#64)) := by
    apply rX_bits_x26
    rw [get?_afterNextPC σ3 (0x800077a4#64) _ (by decide) (by decide)]; exact hx26_3
  have ha5r : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ3) (0x800077a4#64))
      = .ok (BitVec.ofNat 64 (0x64 - 32)) (afterNextPC (afterPrelude σ3) (0x800077a4#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ3 (0x800077a4#64) _ (by decide) (by decide)]; exact hx15_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_branch_nottaken σ3 i3 (c.steps + 1 + 1 + 1) (0x800077a4#64) vmi3
      (0x0054#13) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x0f#5) bop.BLTU (0x04fd6a63#32)
      (0x63#8) (0x6a#8) (0xfd#8) (0x04#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_04fd6a63 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_btype_bltu_nottaken (0x0054#13) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 90) (BitVec.ofNat 64 (0x64 - 32))
        (afterNextPC (afterPrelude σ3) (0x800077a4#64)) hs10r ha5r (by decide))
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x800077a8#64) := by
    have := obs_branch_nottaken_pc hobs4
    rwa [show BitVec.addInt (0x800077a4#64 : BitVec 64) 4 = (0x800077a8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_branch_nottaken_minstret hobs4
  have hx15_4 : σ4.regs.get? Register.x15 = some (BitVec.ofNat 64 (0x64 - 32)) :=
    obs_branch_nottaken_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_3
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx22_4 : σ4.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_branch_nottaken_other hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx25_4 : σ4.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_branch_nottaken_other hobs4 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_3
  have hx6_4 : σ4.regs.get? Register.x6 = some v6 :=
    obs_branch_nottaken_other hobs4 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_branch_nottaken_other hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx27_4 : σ4.regs.get? Register.x27 = some v27 :=
    obs_branch_nottaken_other hobs4 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hframe4 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ4 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_branch_nottaken hobs4 (hframe3 v8 v23 v12 h)
  -- === 77a8: slli a4,a5,0x20  ⇒  x14 := a5 <<< 32 ===
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a8 hload4
  have ha5n5 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ4) (0x800077a8#64))
      = .ok (BitVec.ofNat 64 (0x64 - 32)) (afterNextPC (afterPrelude σ4) (0x800077a8#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ4 (0x800077a8#64) _ (by decide) (by decide)]; exact hx15_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800077a8#64) vmi4 (0x02079713#32)
      (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, sop.SLLI))
      Register.x14
      (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      (0x13#8) (0x97#8) (0x07#8) (0x02#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02079713 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_shiftiop_slli_char (0x20#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
        (BitVec.ofNat 64 (0x64 - 32)) (afterNextPC (afterPrelude σ4) (0x800077a8#64))
        (sigma3_alu σ4 (0x800077a8#64) Register.x14
          (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0)))
        ha5n5 (wX_bits_x14 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x800077ac#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800077a8#64 : BitVec 64) 4 = (0x800077ac#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx14_5 : σ5.regs.get? Register.x14
      = some (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0)) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx22_5 : σ5.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other hobs5 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_4
  have hx25_5 : σ5.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs5 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_4
  have hx6_5 : σ5.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_4
  have hx20_5 : σ5.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_4
  have hx27_5 : σ5.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs5 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hframe5 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ5 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs5 (by decide) (by decide) (by decide) (hframe4 v8 v23 v12 h)
  -- === 77ac: srli a5,a4,0x1e  ⇒  x15 := a4 >>> 30 = 4*(0x64-32) ===
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077ac hload5
  have ha4n6 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ5) (0x800077ac#64))
      = .ok (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (afterNextPC (afterPrelude σ5) (0x800077ac#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ5 (0x800077ac#64) _ (by decide) (by decide)]; exact hx14_5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_alu σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x800077ac#64) vmi5 (0x01e75793#32)
      (instruction.SHIFTIOP (0x1e#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, sop.SRLI))
      Register.x15
      (shift_bits_right
        (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1e#6) 5 0))
      (0x93#8) (0x57#8) (0xe7#8) (0x01#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01e75793 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_shiftiop_srli_char (0x1e#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
        (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (afterNextPC (afterPrelude σ5) (0x800077ac#64))
        (sigma3_alu σ5 (0x800077ac#64) Register.x15
          (shift_bits_right
            (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
            (Sail.BitVec.extractLsb (0x1e#6) 5 0)))
        ha4n6 (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x800077b0#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x800077ac#64 : BitVec 64) 4 = (0x800077b0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- x15 = 4*(0x64-32) via slotIndexShift
  have hshift : (shift_bits_right
        (shift_bits_left (BitVec.ofNat 64 (0x64 - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1e#6) 5 0))
      = BitVec.ofNat 64 (4 * (0x64 - 32)) := by
    show ((BitVec.ofNat 64 (0x64 - 32)) <<< (Sail.BitVec.extractLsb (0x20#6) 5 0))
        >>> (Sail.BitVec.extractLsb (0x1e#6) 5 0) = BitVec.ofNat 64 (4 * (0x64 - 32))
    rw [show (Sail.BitVec.extractLsb (0x20#6) 5 0) = (32#6) from by decide,
        show (Sail.BitVec.extractLsb (0x1e#6) 5 0) = (30#6) from by decide]
    exact slotIndexShift (0x64 - 32) (by decide)
  have hx15_6 : σ6.regs.get? Register.x15 = some (BitVec.ofNat 64 (4 * (0x64 - 32))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hshift] at this
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx22_6 : σ6.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hx25_6 : σ6.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs6 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_5
  have hx6_6 : σ6.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs6 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_5
  have hx20_6 : σ6.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_5
  have hx27_6 : σ6.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs6 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hframe6 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ6 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs6 (by decide) (by decide) (by decide) (hframe5 v8 v23 v12 h)
  -- === 77b0: add a5,a5,s6  ⇒  x15 := 4*(0x64-32) + base = slot address ===
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077b0 hload6
  have ha5n7 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ6) (0x800077b0#64))
      = .ok (BitVec.ofNat 64 (4 * (0x64 - 32))) (afterNextPC (afterPrelude σ6) (0x800077b0#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ6 (0x800077b0#64) _ (by decide) (by decide)]; exact hx15_6
  have hs6n7 : (rX_bits (regidx.Regidx 0x16#5)).run (afterNextPC (afterPrelude σ6) (0x800077b0#64))
      = .ok (BitVec.ofNat 64 parseTableBase) (afterNextPC (afterPrelude σ6) (0x800077b0#64)) := by
    apply rX_bits_x22
    rw [get?_afterNextPC σ6 (0x800077b0#64) _ (by decide) (by decide)]; exact hx22_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800077b0#64) vmi6 (0x016787b3#32)
      (instruction.RTYPE (regidx.Regidx 0x16#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
      Register.x15 ((BitVec.ofNat 64 (4 * (0x64 - 32))) + (BitVec.ofNat 64 parseTableBase))
      (0xb3#8) (0x87#8) (0x67#8) (0x01#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_016787b3 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (execute_rtype_add_char (regidx.Regidx 0x16#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 (4 * (0x64 - 32))) (BitVec.ofNat 64 parseTableBase)
        (afterNextPC (afterPrelude σ6) (0x800077b0#64))
        (sigma3_alu σ6 (0x800077b0#64) Register.x15
          ((BitVec.ofNat 64 (4 * (0x64 - 32))) + (BitVec.ofNat 64 parseTableBase)))
        ha5n7 hs6n7 (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x800077b4#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800077b0#64 : BitVec 64) 4 = (0x800077b4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_7 : σ7.regs.get? Register.x15
      = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x64 - 32))) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((BitVec.ofNat 64 (4 * (0x64 - 32))) + (BitVec.ofNat 64 parseTableBase))
        = BitVec.ofNat 64 (parseTableBase + 4 * (0x64 - 32)) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx22_7 : σ7.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hx25_7 : σ7.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs7 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_6
  have hx6_7 : σ7.regs.get? Register.x6 = some v6 :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hx20_7 : σ7.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_6
  have hx27_7 : σ7.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs7 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_6
  -- memory preserved end-to-end (all steps are ALU/branch, no stores)
  have hmemc : σ7.mem = c.σ.mem := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hframe7 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ7 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs7 (by decide) (by decide) (by decide) (hframe6 v8 v23 v12 h)
  -- assemble
  refine ⟨⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG7, hpc7, hx2_7, hx15_7, hx22_7,
    hx6_7, hx20_7, hx25_7, hx27_7, hmemc, hframe7, hi7⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    (Steps.single hstep7))))))

/-! ## `handlerGap_spec` — the full length-modifier gap `0x80008534 → 0x800077b4`

Composes `handler_l_spec` ≫ `handler_ll_spec` ≫ `parseDispatchArith_d_spec` into a
single verified `Steps` chain from the `'l'` handler entry `0x80008534` (exactly
where `SnprintfSpec14.parseDispatch_l_full_spec` lands) through the `"ll"` handler
and the **second** dispatch pass' slot-address arithmetic to the `'d'` slot-load
`0x800077b4` — the entry of `SnprintfSpec13.parseDispatch_d_spec`.

The dispatch upper bound `x26 = 90` and table base `x22 = parseTableBase` are
carried from `parseInit` (untouched by the handlers).  Two format bytes pin the
`%lld` conversion: `format[2] = 'l'` (drives the `beq` into `"ll"`) and
`format[3] = 'd'` (the conversion char for the second dispatch). -/
theorem handlerGap_spec
    (vsp vcur v6 v20 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hload2 : SvfprintfSlice2Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008534#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (hx25 : c.σ.regs.get? Register.x25 = some vcur)
    (hx26 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90))
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    -- the `%lld` conversion spec: format[2]='l', format[3]='d'
    (hbyteL : c.σ.mem[vcur.toNat]? = some (0x6c#8))
    (hbyteD : c.σ.mem[vcur.toNat + 1]? = some (0x64#8))
    -- the format cursor + its two read bytes live in readable RAM below 2^32
    (hcurlo : 0x80000000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 2 ≤ 0x100000000)
    (hcurhtif : vcur.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800077b4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x15
        = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x64 - 32))) ∧
      c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) ∧
      c'.σ.regs.get? Register.x6
        = some (v6 ||| sign_extend (m := 64) (0x020#12)) ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25
        = some ((vcur + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
        PrintEntryFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  -- `cursor+1` does not wrap (format string in RAM below 2^32)
  have hoff1 : (vcur + sign_extend (m := 64) (0x001#12)).toNat = vcur.toNat + 1 := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x001#12)).toNat = 1 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  -- STEP 1: 'l' handler 0x80008534 → 0x80009060 ("ll")
  obtain ⟨c1, hs1, hG1, hpc1, hx2_1, hx6_1, hx20_1, hx25_1, hx22_1, hx26_1, hx27_1, _, hmem1,
      hframe1, htick1⟩ :=
    handler_l_spec vsp vcur v6 v20 (BitVec.ofNat 64 parseTableBase) (BitVec.ofNat 64 90) v27 c
      hG hload2 hpc hx2 hx6 hx20 hx22 hx26 hx27 hx25 hbyteL
      hcurlo (by omega) (hcurhtif.imp (by omega) (by omega)) htick
  -- transport the byte/slice facts across handler_l's mem-preserving steps
  have hbyteD_1 : c1.σ.mem[vcur.toNat + 1]? = some (0x64#8) := by rw [hmem1]; exact hbyteD
  have hload2_1 : SvfprintfSlice2Loaded c1.σ.mem := by rw [hmem1]; exact hload2
  -- STEP 2: "ll" handler 0x80009060 → 0x80007798 (sets ll-flag, char := 'd')
  obtain ⟨c2, hs2, hG2, hpc2, hx2_2, hx6_2, hx20_2, hx24_2, hx25_2, hx22_2, hx26_2, hx27_2, _,
      hmem2, hframe2, htick2⟩ :=
    handler_ll_spec vsp vcur v6 v20 (BitVec.ofNat 64 parseTableBase) (BitVec.ofNat 64 90) v27 c1
      hG1 hload2_1 hpc1 hx2_1 hx6_1 hx20_1 hx22_1 hx26_1 hx27_1 hx25_1 hbyteD_1
      (by omega) (by rw [hoff1]; omega) (by rw [hoff1]; omega)
      (by rw [hoff1]; exact hcurhtif.imp (by omega) (by omega)) htick1
  -- transport the MAIN slice across both handlers' mem-preserving steps
  have hmemcomp : c2.σ.mem = c.σ.mem := by rw [hmem2, hmem1]
  have hload_2 : SvfprintfSliceLoaded c2.σ.mem := by rw [hmemcomp]; exact hload
  -- STEP 3: 2nd-pass dispatch arithmetic 0x80007798 → 0x800077b4 (char 'd')
  obtain ⟨c3, hs3, hG3, hpc3, hx2_3, hx15_3, hx22_3, hx6_3, hx20_3, hx25_3, hx27_3, hmem3,
      hframe3, htick3⟩ :=
    parseDispatchArith_d_spec vsp (vcur + sign_extend (m := 64) (0x001#12))
      (v6 ||| sign_extend (m := 64) (0x020#12)) v20 v27 c2 hG2 hload_2
      hpc2 hx2_2 hx24_2 hx26_2 hx22_2 hx25_2 hx6_2 hx20_2 hx27_2 htick2
  refine ⟨c3, hs1.trans (hs2.trans hs3), hG3, hpc3, hx2_3, hx15_3, hx22_3, hx6_3, hx20_3,
    hx25_3, hx27_3, ?_, ?_, htick3⟩
  · rw [hmem3, hmemcomp]
  · intro v8 v23 v12 h
    exact hframe3 v8 v23 v12 (hframe2 v8 v23 v12 (hframe1 v8 v23 v12 h))

/-! ## `parseToDigitEntry_spec` — length-modifier gap + 2nd dispatch `0x80008534 → 0x80008008`

Extends `handlerGap_spec` through the `.rodata` jump table (`parseDispatch_d_spec`)
to the `'d'` integer-conversion handler entry `0x80008008` — a single verified
`Steps` chain from the `'l'` length-modifier handler entry (where
`SnprintfSpec14.parseDispatch_l_full_spec` lands) all the way to the `'d'` handler.

This is the composition
`handler_l ≫ handler_ll ≫ parseDispatchArith_d ≫ parseDispatch_d`; from `0x80008008`,
`SnprintfSpec15.dispatchD_ll_to_printEntry_spec` continues to `0x800080e4`, the
entry of `SnprintfSpec8.entryToPrint_neg_spec` — see `parseToPrintEntry_spec`. -/
theorem parseToDigitEntry_spec
    (vsp vcur v6 v20 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hload2 : SvfprintfSlice2Loaded c.σ.mem)
    (hslot : ParseSlotPinned 0x64 (0x80008008#64) c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008534#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (hx25 : c.σ.regs.get? Register.x25 = some vcur)
    (hx26 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90))
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    (hbyteL : c.σ.mem[vcur.toNat]? = some (0x6c#8))
    (hbyteD : c.σ.mem[vcur.toNat + 1]? = some (0x64#8))
    (hcurlo : 0x80000000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 2 ≤ 0x100000000)
    (hcurhtif : vcur.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80008008#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6
        = some (v6 ||| sign_extend (m := 64) (0x020#12)) ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25
        = some ((vcur + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.σ.mem = c.σ.mem ∧
      (∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
        PrintEntryFrame c'.σ v8 v23 v12) ∧
      c'.tick < 2 := by
  obtain ⟨c1, hs1, hG1, hpc1, hx2_1, hx15_1, hx22_1, hx6_1, hx20_1, hx25_1, hx27_1, hmem1,
      hframe1, htick1⟩ :=
    handlerGap_spec vsp vcur v6 v20 v27 c hG hload hload2 hpc hx2 hx6 hx20 hx27 hx25 hx26 hx22
      hbyteL hbyteD hcurlo hcurhi hcurhtif htick
  have hload_1 : SvfprintfSliceLoaded c1.σ.mem := by rw [hmem1]; exact hload
  have hslot_1 : ParseSlotPinned 0x64 (0x80008008#64) c1.σ.mem := by rw [hmem1]; exact hslot
  obtain ⟨c2, hs2, hG2, hpc2, hx2_2, hx6_2, hx20_2, hx25_2, hx27_2, hmem2,
      hframe2, htick2⟩ :=
    parseDispatch_d_spec vsp (v6 ||| sign_extend (m := 64) (0x020#12)) v20
      ((vcur + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12)) v27 c1
      hG1 hload_1 hslot_1 hpc1 hx15_1 hx22_1 hx2_1 hx6_1 hx20_1 hx25_1 hx27_1 htick1
  refine ⟨c2, hs1.trans hs2, hG2, hpc2, hx2_2, hx6_2, hx20_2, hx25_2, hx27_2,
    by rw [hmem2, hmem1], ?_, htick2⟩
  intro v8 v23 v12 h
  rcases hframe1 v8 v23 v12 h with ⟨hx8_1, hx23_1, hx12_1⟩
  exact hframe2 v8 v23 v12 ⟨hx8_1, hx23_1, hx12_1⟩


/-! ## `parseToPrintEntry_spec` — length-modifier gap → verified digit path `0x80008534 → 0x800080e4`

The full span this module targets: composes `parseToDigitEntry_spec`
(`0x80008534 → 0x80008008`, the `'d'` handler entry) with
`SnprintfSpec15.dispatchD_ll_to_printEntry_spec` (`0x80008008 → 0x800080e4`, the
`ll` long-long arg fetch) into a single verified `Steps` chain from the `'l'`
length-modifier handler entry all the way to `0x800080e4` — the **exact** entry of
`SnprintfSpec8.entryToPrint_neg_spec`, onto which the sign/digit path continues.

`parseToDigitEntry_spec` preserves memory and threads the four registers consumed
by the `ll` argument-fetch path: the flag word `x6`, format cursor `x25`, source
register `x27`, and field width `x20`. -/
theorem parseToPrintEntry_spec
    (vsp vcur vptr v20 v27 v8 v23 v12 : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 8)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hload2 : SvfprintfSlice2Loaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hslot : ParseSlotPinned 0x64 (0x80008008#64) c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008534#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some (0#64))
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (hx25 : c.σ.regs.get? Register.x25 = some vcur)
    (hx26 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90))
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    (hbyteL : c.σ.mem[vcur.toNat]? = some (0x6c#8))
    (hbyteD : c.σ.mem[vcur.toNat + 1]? = some (0x64#8))
    (hcurlo : 0x80000000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 2 ≤ 0x100000000)
    (hcurhtif : vcur.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat)
    (htick : c.tick < 2)
    -- frame geometry for the `'d'`-handler `ll` arg fetch (SnprintfSpec15)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    -- the va_area pointer bytes at sp+24 (little-endian `vptr`), in `c.σ.mem`
    (hp0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0)
    (hp1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1)
    (hp2 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2)
    (hp3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3)
    (hp4 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4)
    (hp5 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5)
    (hp6 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6)
    (hp7 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7)
    (hvptr : (((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0
        : BitVec (8 * 8)) = vptr)
    (hvlo : 0x80000000 ≤ vptr.toNat) (hvhiram : vptr.toNat + 8 ≤ 0x100000000)
    (hvhtif : vptr.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vptr.toNat)
    (hvalign : vptr.toNat % 8 = 0)
    (hvdisj : vptr.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 356 ≤ vptr.toNat)
    (ha0 : c.σ.mem[vptr.toNat]? = some a0) (ha1 : c.σ.mem[vptr.toNat + 1]? = some a1)
    (ha2 : c.σ.mem[vptr.toNat + 2]? = some a2) (ha3 : c.σ.mem[vptr.toNat + 3]? = some a3)
    (ha4 : c.σ.mem[vptr.toNat + 4]? = some a4b) (ha5 : c.σ.mem[vptr.toNat + 5]? = some a5b)
    (ha6 : c.σ.mem[vptr.toNat + 6]? = some a6) (ha7 : c.σ.mem[vptr.toNat + 7]? = some a7) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800080e4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x28 = some v27 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x23 = some v23 ∧
      c'.σ.regs.get? Register.x12 = some v12 ∧
      c'.σ.regs.get? Register.x13
        = some (sign_extend (m := 64)
            ((((((((a7.append a6).append a5b).append a4b).append a3).append a2).append a1).append a0)
              : BitVec (8 * 8))) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__umoddi3Loaded c'.σ.mem ∧
      __hidden___udivdi3Loaded c'.σ.mem ∧
      FlushPinsLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  -- STEP A: gap + 2nd dispatch → 0x80008008, memory unchanged
  obtain ⟨c8, hs8, hG8, hpc8, hx2_8, hx6_8_raw, hx20_8, hx25_8, hx27_8, hmem8,
      hframe8, htick8⟩ :=
    parseToDigitEntry_spec vsp vcur (0#64) v20 v27 c hG hload hload2 hslot hpc hx2 hx6 hx20 hx27
      hx25 hx26 hx22
      hbyteL hbyteD hcurlo hcurhi hcurhtif htick
  -- transport every mem-stated fact from `c` to `c8` (memory preserved)
  have hload8 : SvfprintfSliceLoaded c8.σ.mem := by rw [hmem8]; exact hload
  have hflag : ((0#64) ||| sign_extend (m := 64) (0x020#12)) = BitVec.ofNat 64 0x20 := by decide
  have hx6_8 : c8.σ.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) := by
    simpa only [hflag] using hx6_8_raw
  -- STEP B: 'd'-handler ll-branch fetch 0x80008008 → 0x800080e4 (SnprintfSpec15)
  obtain ⟨c', hs', hG', hpc', hx2', hx6', hx20', hx28', hx13', hload',
      hframe', hrt', htick'⟩ :=
    dispatchD_ll_to_printEntry_spec vsp vptr
      ((vcur + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12)) v27 v20
      p0 p1 p2 p3 p4 p5 p6 p7
      a0 a1 a2 a3 a4b a5b a6 a7 c8 hG8 hload8 hpc8 hx2_8 hx6_8 hx25_8 hx27_8 hx20_8
      htlo hhi halign
      (by rw [hmem8]; exact hp0) (by rw [hmem8]; exact hp1) (by rw [hmem8]; exact hp2)
      (by rw [hmem8]; exact hp3) (by rw [hmem8]; exact hp4) (by rw [hmem8]; exact hp5)
      (by rw [hmem8]; exact hp6) (by rw [hmem8]; exact hp7) hvptr hvlo hvhiram hvhtif hvalign hvdisj
      (by rw [hmem8]; exact ha0) (by rw [hmem8]; exact ha1) (by rw [hmem8]; exact ha2)
      (by rw [hmem8]; exact ha3) (by rw [hmem8]; exact ha4) (by rw [hmem8]; exact ha5)
      (by rw [hmem8]; exact ha6) (by rw [hmem8]; exact ha7) htick8
  obtain ⟨huload', hcuload', hfp'⟩ := hrt' (by
    rw [hmem8]
    exact ⟨huload, hcuload, hfp⟩)
  obtain ⟨hx8_8, hx23_8, hx12_8⟩ := hframe8 v8 v23 v12 ⟨hx8, hx23, hx12⟩
  obtain ⟨hx8', hx23', hx12'⟩ := hframe' v8 v23 v12 ⟨hx8_8, hx23_8, hx12_8⟩
  exact ⟨c', hs8.trans hs', hG', hpc', hx2', hx6', hx20', hx28', hx8', hx23', hx12', hx13', hload',
    huload', hcuload', hfp', htick'⟩

/-- Compact entry facts for the parsed negative `%lld` default-width path. -/
structure ParseNegDefaultWidthPre
    (vsp vcur vptr v27 v8 v23 v12 : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 8)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config) : Prop where
  good : GoodState c.σ
  slice : SvfprintfSliceLoaded c.σ.mem
  slice2 : SvfprintfSlice2Loaded c.σ.mem
  runtime : SnprintfRuntimeLoaded c.σ.mem
  slot : ParseSlotPinned 0x64 (0x80008008#64) c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80008534#64)
  sp : c.σ.regs.get? Register.x2 = some vsp
  flags : c.σ.regs.get? Register.x6 = some (0#64)
  width : c.σ.regs.get? Register.x20 = some ((0#64) - (0x1#64))
  source : c.σ.regs.get? Register.x27 = some v27
  frame : PrintEntryFrame c.σ v8 v23 v12
  cursor : c.σ.regs.get? Register.x25 = some vcur
  tableLimit : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90)
  tableBase : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase)
  byteL : c.σ.mem[vcur.toNat]? = some (0x6c#8)
  byteD : c.σ.mem[vcur.toNat + 1]? = some (0x64#8)
  cursorLo : 0x80000000 ≤ vcur.toNat
  cursorHi : vcur.toNat + 2 ≤ 0x100000000
  cursorHtif : vcur.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vcur.toNat
  tick : c.tick < 2
  stackLo : tohostAddr + 16 + 64 ≤ vsp.toNat
  stackHi : vsp.toNat + 356 ≤ 0x100000000
  stackAlign : vsp.toNat % 8 = 0
  ptr0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0
  ptr1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1
  ptr2 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2
  ptr3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3
  ptr4 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4
  ptr5 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5
  ptr6 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6
  ptr7 : c.σ.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7
  ptrValue :
    (((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0
      : BitVec (8 * 8)) = vptr
  ptrLo : 0x80000000 ≤ vptr.toNat
  ptrHi : vptr.toNat + 8 ≤ 0x100000000
  ptrHtif : vptr.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vptr.toNat
  ptrAlign : vptr.toNat % 8 = 0
  ptrStackDisj : vptr.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 356 ≤ vptr.toNat
  arg0 : c.σ.mem[vptr.toNat]? = some a0
  arg1 : c.σ.mem[vptr.toNat + 1]? = some a1
  arg2 : c.σ.mem[vptr.toNat + 2]? = some a2
  arg3 : c.σ.mem[vptr.toNat + 3]? = some a3
  arg4 : c.σ.mem[vptr.toNat + 4]? = some a4b
  arg5 : c.σ.mem[vptr.toNat + 5]? = some a5b
  arg6 : c.σ.mem[vptr.toNat + 6]? = some a6
  arg7 : c.σ.mem[vptr.toNat + 7]? = some a7

/-- Complete parsed negative `%lld` default-width path to the PRINT entry. -/
theorem parseToPrint_neg_default_width_spec
    (vsp vcur vptr v27 v8 v23 v12 : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 8)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (h : ParseNegDefaultWidthPre vsp vcur vptr v27 v8 v23 v12
      p0 p1 p2 p3 p4 p5 p6 p7 a0 a1 a2 a3 a4b a5b a6 a7 c)
    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)
    (hmag : 9 < ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) signByte) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat =
        (- (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toNat ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  obtain ⟨huload, hcuload, hfp⟩ := h.runtime
  obtain ⟨hx8, hx23, hx12⟩ := h.frame
  obtain ⟨c1, hs1, hG1, hpc1, hx2_1, hx6_1, hx20_1, hx28_1, hx8_1, hx23_1,
      hx12_1, hx13_1, hload1, huload1, hcuload1, hfp1, htick1⟩ :=
    parseToPrintEntry_spec vsp vcur vptr ((0#64) - (0x1#64)) v27 v8 v23 v12
      p0 p1 p2 p3 p4 p5 p6 p7 a0 a1 a2 a3 a4b a5b a6 a7 c
      h.good h.slice h.slice2 huload hcuload hfp h.slot h.pc h.sp h.flags h.width h.source
      hx8 hx23 hx12 h.cursor h.tableLimit h.tableBase h.byteL h.byteD h.cursorLo h.cursorHi
      h.cursorHtif h.tick h.stackLo h.stackHi h.stackAlign
      h.ptr0 h.ptr1 h.ptr2 h.ptr3 h.ptr4 h.ptr5 h.ptr6 h.ptr7 h.ptrValue
      h.ptrLo h.ptrHi h.ptrHtif h.ptrAlign h.ptrStackDisj
      h.arg0 h.arg1 h.arg2 h.arg3 h.arg4 h.arg5 h.arg6 h.arg7
  obtain ⟨c', hs2, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi'⟩ :=
    entryToPrint_neg_default_width_spec (llArg a0 a1 a2 a3 a4b a5b a6 a7)
      vsp (BitVec.ofNat 64 0x20) v8 v23 v27 v12 c1
      hG1 hload1 huload1 hcuload1 hfp1 hpc1 hx13_1 hx2_1 hx6_1 hx8_1 hx20_1
      hx23_1 hx28_1 hx12_1 (by decide) hneg hmag h.stackLo h.stackHi h.stackAlign htick1
  exact ⟨c', hs1.trans hs2, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi'⟩

end Vsa.Sim
