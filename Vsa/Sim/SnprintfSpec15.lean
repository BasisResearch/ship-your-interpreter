import Vsa.Sim.SnprintfSpec14
import Vsa.Sim.SnprintfSpec8
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites

/-!
# M3 Layer-3 — `SnprintfSpec15` : the `'d'` integer-conversion **`ll`-branch** entry
`0x80008008 → 0x800080e4` (`_d15`)

This module verifies the executed `%lld` **`'d'` conversion-handler entry** for the
`ll` (long-long) length-modifier case — the segment that runs *after* the parse
dispatch has reached the `'d'` handler and *after* the `"ll"` handler set the
`ll`-flag `0x20` in the flags word `x6`.  It is the last un-verified straight-line
segment before `SnprintfSpec8.entryToPrint_neg_spec` picks up the sign/digit path
at `0x800080e4`, and it composes **exactly** onto that entry.

## The executed `%lld` handler chain (decoded from `c/while-riscv-htif.elf`)

```
  ── 'l' handler @ 0x80008534 ───────────────────────────────────  (NOT in coverage)
  80008534: lbu  s8,0(s9)          s8 := format[2]  (the 2nd 'l')
  80008538: li   a5,108            a5 := 'l' (0x6c)
  8000853c: beq  s8,a5,0x80009060  format[2]=='l' ⇒ goto "ll" handler
  80008540: ori  t1,t1,16          (single-'l' path: set 'l'-flag, not taken here)
  80008544: j    0x80007798

  ── "ll" handler @ 0x80009060 ──────────────────────────────────  (NOT in coverage)
  80009060: lbu  s8,1(s9)          s8 := format[3]  (the conversion char, 'd')
  80009064: ori  t1,t1,32          x6 := x6 ||| 0x20   (SET THE ll-FLAG)
  80009068: addi s9,s9,1           advance format cursor
  8000906c: j    0x80007798        back to the conversion dispatch (→ 'd' via table)

  ── 'd' handler @ 0x80008008 ───────────────────────────────────  (IN coverage ✓)
  80008008: ld   a5,24(sp)         a5 := va_area ptr           [THIS MODULE START]
  8000800c: sd   s9,0(sp)          spill format cursor
  80008010: andi a4,t1,32          a4 := x6 & 0x20   (test the ll-flag)
  80008014: mv   t3,s11            t3 := s11
  80008018: addi a5,a5,8           a5 += 8   (bump va_area past the 8-byte arg)
  8000801c: bnez a4,0x800080d8     ll-flag set ⇒ TAKEN → 0x800080d8

  ── ll long-long arg fetch @ 0x800080d8 ────────────────────────  (IN coverage ✓)
  800080d8: ld   a4,24(sp)         a4 := va_area ptr (pre-bump)
  800080dc: ld   a3,0(a4)          a3 := *(va_area)  = the 64-bit long-long value
  800080e0: sd   a5,24(sp)         store bumped va_area ptr
  800080e4: mv   a4,a3             [entryToPrint_neg_spec START — SnprintfSpec8]
```

## Coverage boundary (honest)

`SvfprintfSliceLoaded` (`Vsa/Sim/Code/SvfprintfSlice.lean`) covers
`[0x80007654,0x80007a00) ∪ [0x80007fc0,0x80008400) ∪ [0x80008a80,0x80008b10)`.
The `'d'` handler (`0x80008008…`) and the `ll` arg-fetch block (`0x800080d8…e4`)
are **inside** the middle sub-range, so this whole segment is verified from the
pinned code bytes.  The two **preceding** handlers are **outside** coverage:

* `'l'`  handler `[0x80008534, 0x80008548)` — GAP (add to the SvfprintfSlice generator);
* `"ll"` handler `[0x80009060, 0x80009070)` — GAP.

Those two handlers do not compose here (their code bytes are not pinned); the
`ll`-flag `x6 = 0x20` they establish is therefore stated as an **entry hypothesis**
(`hx6`), matching what the `"ll"` handler's `ori x6,x6,32` leaves.  Extending
coverage to those ranges + widening `parseDispatch_d_spec` to surface `x6`/`s9`
would let this chain onto `SnprintfSpec14.parseDispatch_l_full_spec`.

## What lands (`dispatchD_ll_to_printEntry_spec`)

A single `Steps` chain `0x80008008 → 0x800080e4` (9 instructions), taking the
`ll`-flag branch.  Postcondition: `PC = 0x800080e4` (exactly the entry of
`SnprintfSpec8.entryToPrint_neg_spec`), `x6 = 0x20` (ll-flag preserved),
`x20 = v20` (parsed field width, untouched), `x2 = vsp` (frame preserved), and
`x13 = v` — the fetched 64-bit `long long` argument — surfaced as the value the
sign/digit path formats.  The stack stores at `sp+0` and `sp+24` leave the code
region intact (`SvfprintfSliceLoaded` preserved).  The `va_area` pointer in the
spill slot `sp+24` and its target are supplied as caller (`va_list`) state.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded __hidden___udivdi3Loaded FlushPinsLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `0x20 & 0x20 = 0x20`, sign-extended: the `andi a4,t1,32` on the `ll`-flag word
`x6 = 0x20` yields `0x20`, which is `≠ 0`, so `bnez a4` is taken.  Stated as the
`(v != w) = true` guard the taken-branch executor needs (`a4 ≠ x0 = 0`). -/
theorem ll_flag_andi_ne_zero :
    (((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12))) != (0#64)) = true := by
  decide

/-! ## Reusable frames for the argument-fetch path -/

/-- Registers needed by the sign/digit path and untouched by the argument-fetch
instructions. -/
def PrintEntryFrame (σ : MState) (v8 v23 v12 : BitVec 64) : Prop :=
  σ.regs.get? Register.x8 = some v8 ∧
  σ.regs.get? Register.x23 = some v23 ∧
  σ.regs.get? Register.x12 = some v12

theorem printEntryFrame_alu {σ' σ : MState} {pc vm : BitVec 64}
    {rd : Register} {v : RegisterType rd} {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (h8 : (rd == Register.x8) = false) (h23 : (rd == Register.x23) = false)
    (h12 : (rd == Register.x12) = false) (h : PrintEntryFrame σ v8 v23 v12) :
    PrintEntryFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_alu_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide)
      (by decide) h8 (by decide) (by decide) hx8,
    obs_alu_other hobs Register.x23 (by decide) (by decide) (by decide) (by decide)
      (by decide) h23 (by decide) (by decide) hx23,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
      (by decide) h12 (by decide) (by decide) hx12⟩

theorem printEntryFrame_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)} {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (h : PrintEntryFrame σ v8 v23 v12) : PrintEntryFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_store_other_sn4 Register.x8 hobs (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx8,
    obs_store_other_sn4 Register.x23 hobs (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx23,
    obs_store_other_sn4 Register.x12 hobs (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx12⟩

theorem printEntryFrame_branch {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    {v8 v23 v12 : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm))
    (h : PrintEntryFrame σ v8 v23 v12) : PrintEntryFrame σ' v8 v23 v12 := by
  rcases h with ⟨hx8, hx23, hx12⟩
  exact ⟨obs_branch_taken_other hobs Register.x8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx8,
    obs_branch_taken_other hobs Register.x23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx23,
    obs_branch_taken_other hobs Register.x12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx12⟩

/-- Runtime code needed after the argument fetch. -/
def SnprintfRuntimeLoaded (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  Vsa.Sim.Code.__umoddi3Loaded mem ∧ __hidden___udivdi3Loaded mem ∧ FlushPinsLoaded mem

/-- All downstream runtime code survives an eight-byte stack write. -/
theorem snprintfRuntimeLoaded_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : 0x8000b000 ≤ a) (h : SnprintfRuntimeLoaded mem) :
    SnprintfRuntimeLoaded (writeMap8 mem a d) := by
  rcases h with ⟨hu, hcu, hfp⟩
  exact ⟨umoddi3_writeMap8_sn5 _ _ _ (by omega) hu,
    cudivdi3_writeMap8_sn5 _ _ _ (by omega) hcu,
    flushPins_writeMap8_fl _ _ _ ha hfp⟩

/-- **The `'d'` conversion-handler `ll`-branch entry.**

From `0x80008008` (the `'d'` integer-conversion handler entry) with the `ll`-flag
set in `x6` (`= 0x20`, as the `"ll"` handler's `ori x6,x6,32` leaves it), run the
nine-instruction `ll` path — spill/flag-test/va-bump, the `bnez` taken, the
long-long arg fetch — landing at `0x800080e4`, the entry of
`SnprintfSpec8.entryToPrint_neg_spec`.

The `va_area` pointer lives in spill slot `sp+24`; `vptr` is its value and the
eight bytes `p0..p7` are its little-endian encoding (caller `va_list` state).  The
64-bit argument sits at `vptr`, bytes `a0..a7`; the fetched value
`v = sext(a7‖…‖a0)` is surfaced in `x13` for the sign/digit path.  All addresses
are 8-aligned readable RAM above the HTIF window; the two stack stores (`sp+0`,
`sp+24`) are above the code region so `SvfprintfSliceLoaded` survives. -/
theorem dispatchD_ll_to_printEntry_spec
    (vsp vptr v9 v27 v20 : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 8)   -- va_area ptr bytes at sp+24
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8) -- the 64-bit long-long value bytes at vptr
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008008#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    -- x6 (t1) = the ll-flag word the "ll" handler left (`ori x6,x6,32`)
    (hx6 : c.σ.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20))
    -- x25 (s9) = format cursor (spilled at sp+0)
    (hx25 : c.σ.regs.get? Register.x25 = some v9)
    -- x27 (s11) = the value `mv t3,s11` copies (into the dead x28)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    -- x20 (s4) = the parsed field width (untouched by this segment; carried through)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    -- frame geometry: stack well above the HTIF window, 8-aligned, in RAM
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    -- the va_area pointer bytes at sp+24 (little-endian `vptr`)
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
    -- vptr points to 8-aligned readable RAM above the HTIF window
    (hvlo : 0x80000000 ≤ vptr.toNat)
    (hvhiram : vptr.toNat + 8 ≤ 0x100000000)
    (hvhtif : vptr.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vptr.toNat)
    (hvalign : vptr.toNat % 8 = 0)
    -- the `va_area` argument does NOT alias the sprintf scratch stack frame
    -- `[sp, sp+356)` (else the two spill stores would clobber the fetched value):
    (hvdisj : vptr.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 356 ≤ vptr.toNat)
    -- the 64-bit long-long argument bytes at vptr
    (ha0 : c.σ.mem[vptr.toNat]? = some a0)
    (ha1 : c.σ.mem[vptr.toNat + 1]? = some a1)
    (ha2 : c.σ.mem[vptr.toNat + 2]? = some a2)
    (ha3 : c.σ.mem[vptr.toNat + 3]? = some a3)
    (ha4 : c.σ.mem[vptr.toNat + 4]? = some a4b)
    (ha5 : c.σ.mem[vptr.toNat + 5]? = some a5b)
    (ha6 : c.σ.mem[vptr.toNat + 6]? = some a6)
    (ha7 : c.σ.mem[vptr.toNat + 7]? = some a7)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800080e4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) ∧
      -- the parsed field width (x20 / s4), carried through untouched
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x28 = some v27 ∧
      -- the fetched 64-bit `long long` argument, in x13 (a3), for the sign/digit path
      c'.σ.regs.get? Register.x13
        = some (sign_extend (m := 64)
            ((((((((a7.append a6).append a5b).append a4b).append a3).append a2).append a1).append a0)
              : BitVec (8 * 8))) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧
      (∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
        PrintEntryFrame c'.σ v8 v23 v12) ∧
      (SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded c'.σ.mem) ∧
      c'.tick < 2 := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have htlo' : 0x8001ad50 ≤ vsp.toNat := by simp only [tohostAddr] at htlo; omega
  -- offset helper: sp+24 as a Nat
  have hoff24 : (vsp + sign_extend (m := 64) (0x018#12)).toNat = vsp.toNat + 24 := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x018#12)).toNat = 24 from by decide]
    rw [Nat.mod_eq_of_lt (by omega)]
  -- ══ 80008008: ld a5,24(sp)  ⇒ x15 := (dead) ══
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008008 hload
  have hx2n0 : (afterNextPC (afterPrelude c.σ) (0x80008008#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC c.σ (0x80008008#64) _ (by decide) (by decide)]; exact hx2
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x80008008#64) vmi0 (0x01813783#32)
      (instruction.LOAD (0x018#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0f#5, false, 8))
      Register.x15 (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80008008#64))
          (vsp + sign_extend (m := 64) (0x018#12))))
      (0x83#8) (0x37#8) (0x81#8) (0x01#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01813783 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_ld_total c.σ (0x80008008#64) (0x018#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0f#5)
        vsp (sigma3_alu c.σ (0x80008008#64) Register.x15 (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80008008#64))
            (vsp + sign_extend (m := 64) (0x018#12)))))
        hG (rX_bits_x2 _ vsp hx2n0) (wX_bits_x15 _ _)
        (by rw [hoff24]; omega) (by rw [hoff24]; omega) (Or.inr (by rw [hoff24]; simp only [tohostAddr]; omega))
        (by rw [hoff24]; omega))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000800c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80008008#64 : BitVec 64) 4 = (0x8000800c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx25_1 : σ1.regs.get? Register.x25 = some v9 :=
    obs_alu_other hobs1 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25
  have hx27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27
  -- x15 = the (dead) loaded va-area word; thread it concretely to the addi at 0x80008018.
  -- (its exact value is irrelevant; we only need *some* pinned value for the addi's rs1.)
  obtain ⟨v15, hx15_1⟩ : ∃ v, σ1.regs.get? Register.x15 = some v :=
    ⟨_, obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hframe1 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ1 v8 v23 v12 := fun _ _ _ h =>
    printEntryFrame_alu hobs1 (by decide) (by decide) (by decide) h
  have hrt1 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ1.mem :=
    fun h => hmem1 ▸ h
  -- va_area bytes preserved (ALU step, no mem change)
  have hp0_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0 := hmem1 ▸ hp0
  have hp1_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1 := hmem1 ▸ hp1
  have hp2_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2 := hmem1 ▸ hp2
  have hp3_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3 := hmem1 ▸ hp3
  have hp4_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4 := hmem1 ▸ hp4
  have hp5_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5 := hmem1 ▸ hp5
  have hp6_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6 := hmem1 ▸ hp6
  have hp7_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7 := hmem1 ▸ hp7
  have ha0_1 : σ1.mem[vptr.toNat]? = some a0 := hmem1 ▸ ha0
  have ha1_1 : σ1.mem[vptr.toNat + 1]? = some a1 := hmem1 ▸ ha1
  have ha2_1 : σ1.mem[vptr.toNat + 2]? = some a2 := hmem1 ▸ ha2
  have ha3_1 : σ1.mem[vptr.toNat + 3]? = some a3 := hmem1 ▸ ha3
  have ha4_1 : σ1.mem[vptr.toNat + 4]? = some a4b := hmem1 ▸ ha4
  have ha5_1 : σ1.mem[vptr.toNat + 5]? = some a5b := hmem1 ▸ ha5
  have ha6_1 : σ1.mem[vptr.toNat + 6]? = some a6 := hmem1 ▸ ha6
  have ha7_1 : σ1.mem[vptr.toNat + 7]? = some a7 := hmem1 ▸ ha7
  -- ══ 8000800c: sd s9,0(sp)  ⇒ store cursor at sp+0 ══
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000800c hload1
  have hx2n1 : (afterNextPC (afterPrelude σ1) (0x8000800c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ1 (0x8000800c#64) _ (by decide) (by decide)]; exact hx2_1
  have hx25n1 : (afterNextPC (afterPrelude σ1) (0x8000800c#64)).regs.get? Register.x25 = some v9 := by
    rw [get?_afterNextPC σ1 (0x8000800c#64) _ (by decide) (by decide)]; exact hx25_1
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x000#12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt vsp.isLt]
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_store σ1 i1 (c.steps + 1) (0x8000800c#64) vmi1 (0x01913023#32)
      (instruction.STORE (0x000#12, regidx.Regidx 0x19#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ1) (0x8000800c#64)).mem
        (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v9))
      (0x23#8) (0x30#8) (0x91#8) (0x01#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01913023 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (exec_sd_val σ1 (0x8000800c#64) (0x000#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x02#5)
        vsp v9 hG1 (rX_bits_x2 _ vsp hx2n1) (rX_bits_x25 _ v9 hx25n1)
        (by rw [hoff0]; omega) (by rw [hoff0]; omega) (by rw [hoff0]; simp only [tohostAddr]; omega) (by rw [hoff0]; omega))
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x80008010#64) := by
    have := obs_store_pc_sn4 hobs2
    rwa [show BitVec.addInt (0x8000800c#64 : BitVec 64) 4 = (0x80008010#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_sn4 hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_store_other_sn4 Register.x6 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4 Register.x20 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_store_other_sn4 Register.x27 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_1
  have hx15_2 : σ2.regs.get? Register.x15 = some v15 :=
    obs_store_other_sn4 Register.x15 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_1
  -- memory after the store: writeMap8 at key sp+0 (≥ 0x80009000, so code + va bytes survive)
  have hNP2 : (afterNextPC (afterPrelude σ1) (0x8000800c#64)).mem = σ1.mem := rfl
  have hkey0 : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat := by
    rw [hoff0]; omega
  have hload2 : SvfprintfSliceLoaded σ2.mem := by
    rw [hmem2, hNP2]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hkey0 hload1
  have hframe2 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ2 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_store hobs2 (hframe1 v8 v23 v12 h)
  have hrt2 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ2.mem := fun h => by
    rw [hmem2, hNP2]
    exact snprintfRuntimeLoaded_writeMap8 _ _ _ (by rw [hoff0]; omega) (hrt1 h)
  -- va_area bytes survive the store (key sp+0 disjoint from sp+24 and from vptr)
  have hp0_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp0_1
  have hp1_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp1_1
  have hp2_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp2_1
  have hp3_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp3_1
  have hp4_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp4_1
  have hp5_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp5_1
  have hp6_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp6_1
  have hp7_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0, hoff24]; omega)]; exact hp7_1
  have ha0_2 : σ2.mem[vptr.toNat]? = some a0 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha0_1
  have ha1_2 : σ2.mem[vptr.toNat + 1]? = some a1 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha1_1
  have ha2_2 : σ2.mem[vptr.toNat + 2]? = some a2 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha2_1
  have ha3_2 : σ2.mem[vptr.toNat + 3]? = some a3 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha3_1
  have ha4_2 : σ2.mem[vptr.toNat + 4]? = some a4b := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha4_1
  have ha5_2 : σ2.mem[vptr.toNat + 5]? = some a5b := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha5_1
  have ha6_2 : σ2.mem[vptr.toNat + 6]? = some a6 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha6_1
  have ha7_2 : σ2.mem[vptr.toNat + 7]? = some a7 := by
    rw [hmem2, hNP2, getElem?_writeMap8_out _ _ _ _ (by rw [hoff0]; omega)]; exact ha7_1
  -- ══ 80008010: andi a4,t1,32  ⇒ x14 := x6 & 0x20 = 0x20 ══
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008010 hload2
  have hx6n2 : (rX_bits (regidx.Regidx 0x06#5)).run (afterNextPC (afterPrelude σ2) (0x80008010#64))
      = .ok (BitVec.ofNat 64 0x20) (afterNextPC (afterPrelude σ2) (0x80008010#64)) := by
    apply rX_bits_x6
    rw [get?_afterNextPC σ2 (0x80008010#64) _ (by decide) (by decide)]; exact hx6_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_alu σ2 i2 (c.steps + 1 + 1) (0x80008010#64) vmi2 (0x02037713#32)
      (instruction.ITYPE (0x020#12, regidx.Regidx 0x06#5, regidx.Regidx 0x0e#5, iop.ANDI))
      Register.x14 ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12)))
      (0x13#8) (0x77#8) (0x03#8) (0x02#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02037713 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_itype_andi_char (0x020#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x0e#5)
        (BitVec.ofNat 64 0x20) (afterNextPC (afterPrelude σ2) (0x80008010#64))
        (sigma3_alu σ2 (0x80008010#64) Register.x14
          ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12))))
        hx6n2 (wX_bits_x14 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x80008014#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80008010#64 : BitVec 64) 4 = (0x80008014#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx14_3 : σ3.regs.get? Register.x14
      = some ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12))) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_alu_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx27_3 : σ3.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs3 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_2
  have hx15_3 : σ3.regs.get? Register.x15 = some v15 :=
    obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hframe3 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ3 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs3 (by decide) (by decide) (by decide) (hframe2 v8 v23 v12 h)
  have hrt3 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ3.mem :=
    fun h => hmem3 ▸ hrt2 h
  have hp0_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0 := hmem3 ▸ hp0_2
  have hp1_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1 := hmem3 ▸ hp1_2
  have hp2_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2 := hmem3 ▸ hp2_2
  have hp3_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3 := hmem3 ▸ hp3_2
  have hp4_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4 := hmem3 ▸ hp4_2
  have hp5_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5 := hmem3 ▸ hp5_2
  have hp6_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6 := hmem3 ▸ hp6_2
  have hp7_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7 := hmem3 ▸ hp7_2
  have ha0_3 : σ3.mem[vptr.toNat]? = some a0 := hmem3 ▸ ha0_2
  have ha1_3 : σ3.mem[vptr.toNat + 1]? = some a1 := hmem3 ▸ ha1_2
  have ha2_3 : σ3.mem[vptr.toNat + 2]? = some a2 := hmem3 ▸ ha2_2
  have ha3_3 : σ3.mem[vptr.toNat + 3]? = some a3 := hmem3 ▸ ha3_2
  have ha4_3 : σ3.mem[vptr.toNat + 4]? = some a4b := hmem3 ▸ ha4_2
  have ha5_3 : σ3.mem[vptr.toNat + 5]? = some a5b := hmem3 ▸ ha5_2
  have ha6_3 : σ3.mem[vptr.toNat + 6]? = some a6 := hmem3 ▸ ha6_2
  have ha7_3 : σ3.mem[vptr.toNat + 7]? = some a7 := hmem3 ▸ ha7_2
  -- ══ 80008014: mv t3,s11  (= addi t3,s11,0)  ⇒ x28 := v27  (dead) ══
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008014 hload3
  have hx27n3 : (rX_bits (regidx.Regidx 0x1b#5)).run (afterNextPC (afterPrelude σ3) (0x80008014#64))
      = .ok v27 (afterNextPC (afterPrelude σ3) (0x80008014#64)) := by
    apply rX_bits_x27
    rw [get?_afterNextPC σ3 (0x80008014#64) _ (by decide) (by decide)]; exact hx27_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_alu σ3 i3 (c.steps + 1 + 1 + 1) (0x80008014#64) vmi3 (0x000d8e13#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x1b#5, regidx.Regidx 0x1c#5, iop.ADDI))
      Register.x28 (v27 + (sign_extend (m := 64) (0x000#12)))
      (0x13#8) (0x8e#8) (0x0d#8) (0x00#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000d8e13 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x1b#5) (regidx.Regidx 0x1c#5)
        v27 (afterNextPC (afterPrelude σ3) (0x80008014#64))
        (sigma3_alu σ3 (0x80008014#64) Register.x28 (v27 + (sign_extend (m := 64) (0x000#12))))
        hx27n3 (wX_bits_x28 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x80008018#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80008014#64 : BitVec 64) 4 = (0x80008018#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx6_4 : σ4.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_alu_other hobs4 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx14_4 : σ4.regs.get? Register.x14
      = some ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12))) :=
    obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_3
  have hx15_4 : σ4.regs.get? Register.x15 = some v15 :=
    obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hx28_4 : σ4.regs.get? Register.x28 = some v27 := by
    have h := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa only [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide,
      BitVec.add_zero] using h
  have hframe4 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ4 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs4 (by decide) (by decide) (by decide) (hframe3 v8 v23 v12 h)
  have hrt4 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ4.mem :=
    fun h => hmem4 ▸ hrt3 h
  have hp0_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0 := hmem4 ▸ hp0_3
  have hp1_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1 := hmem4 ▸ hp1_3
  have hp2_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2 := hmem4 ▸ hp2_3
  have hp3_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3 := hmem4 ▸ hp3_3
  have hp4_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4 := hmem4 ▸ hp4_3
  have hp5_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5 := hmem4 ▸ hp5_3
  have hp6_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6 := hmem4 ▸ hp6_3
  have hp7_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7 := hmem4 ▸ hp7_3
  have ha0_4 : σ4.mem[vptr.toNat]? = some a0 := hmem4 ▸ ha0_3
  have ha1_4 : σ4.mem[vptr.toNat + 1]? = some a1 := hmem4 ▸ ha1_3
  have ha2_4 : σ4.mem[vptr.toNat + 2]? = some a2 := hmem4 ▸ ha2_3
  have ha3_4 : σ4.mem[vptr.toNat + 3]? = some a3 := hmem4 ▸ ha3_3
  have ha4_4 : σ4.mem[vptr.toNat + 4]? = some a4b := hmem4 ▸ ha4_3
  have ha5_4 : σ4.mem[vptr.toNat + 5]? = some a5b := hmem4 ▸ ha5_3
  have ha6_4 : σ4.mem[vptr.toNat + 6]? = some a6 := hmem4 ▸ ha6_3
  have ha7_4 : σ4.mem[vptr.toNat + 7]? = some a7 := hmem4 ▸ ha7_3
  -- ══ 80008018: addi a5,a5,8  ⇒ x15 += 8  (dead) ══
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008018 hload4
  have hx15n4 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ4) (0x80008018#64))
      = .ok v15 (afterNextPC (afterPrelude σ4) (0x80008018#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ4 (0x80008018#64) _ (by decide) (by decide)]; exact hx15_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80008018#64) vmi4 (0x00878793#32)
      (instruction.ITYPE (0x008#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))
      Register.x15 (v15 + (sign_extend (m := 64) (0x008#12)))
      (0x93#8) (0x87#8) (0x87#8) (0x00#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00878793 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_itype_addi_char (0x008#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        v15 (afterNextPC (afterPrelude σ4) (0x80008018#64))
        (sigma3_alu σ4 (0x80008018#64) Register.x15 (v15 + (sign_extend (m := 64) (0x008#12))))
        hx15n4 (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000801c#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80008018#64 : BitVec 64) 4 = (0x8000801c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx6_5 : σ5.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_4
  have hx20_5 : σ5.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_4
  have hx14_5 : σ5.regs.get? Register.x14
      = some ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12))) :=
    obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_4
  have hx15_5 : σ5.regs.get? Register.x15 = some (v15 + (sign_extend (m := 64) (0x008#12))) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hframe5 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ5 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs5 (by decide) (by decide) (by decide) (hframe4 v8 v23 v12 h)
  have hx28_5 : σ5.regs.get? Register.x28 = some v27 :=
    obs_alu_other hobs5 Register.x28 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx28_4
  have hrt5 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ5.mem :=
    fun h => hmem5 ▸ hrt4 h
  have hp0_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0 := hmem5 ▸ hp0_4
  have hp1_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1 := hmem5 ▸ hp1_4
  have hp2_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2 := hmem5 ▸ hp2_4
  have hp3_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3 := hmem5 ▸ hp3_4
  have hp4_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4 := hmem5 ▸ hp4_4
  have hp5_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5 := hmem5 ▸ hp5_4
  have hp6_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6 := hmem5 ▸ hp6_4
  have hp7_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7 := hmem5 ▸ hp7_4
  have ha0_5 : σ5.mem[vptr.toNat]? = some a0 := hmem5 ▸ ha0_4
  have ha1_5 : σ5.mem[vptr.toNat + 1]? = some a1 := hmem5 ▸ ha1_4
  have ha2_5 : σ5.mem[vptr.toNat + 2]? = some a2 := hmem5 ▸ ha2_4
  have ha3_5 : σ5.mem[vptr.toNat + 3]? = some a3 := hmem5 ▸ ha3_4
  have ha4_5 : σ5.mem[vptr.toNat + 4]? = some a4b := hmem5 ▸ ha4_4
  have ha5_5 : σ5.mem[vptr.toNat + 5]? = some a5b := hmem5 ▸ ha5_4
  have ha6_5 : σ5.mem[vptr.toNat + 6]? = some a6 := hmem5 ▸ ha6_4
  have ha7_5 : σ5.mem[vptr.toNat + 7]? = some a7 := hmem5 ▸ ha7_4
  -- ══ 8000801c: bnez a4,0x800080d8  ⇒ TAKEN (a4 = 0x20 ≠ 0)  → 0x800080d8 ══
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000801c hload5
  have hx14n5 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ5) (0x8000801c#64))
      = .ok ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12)))
        (afterNextPC (afterPrelude σ5) (0x8000801c#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ5 (0x8000801c#64) _ (by decide) (by decide)]; exact hx14_5
  have hx0n5 : (rX_bits (regidx.Regidx 0x00#5)).run (afterNextPC (afterPrelude σ5) (0x8000801c#64))
      = .ok (0#64) (afterNextPC (afterPrelude σ5) (0x8000801c#64)) := rX_bits_zero _
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_branch_taken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x8000801c#64) vmi5
      (0x00bc#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x0a071e63#32)
      (0x63#8) (0x1e#8) (0x07#8) (0x0a#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0a071e63 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_btype_bne_taken (0x00bc#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5)
        ((BitVec.ofNat 64 0x20) &&& (sign_extend (m := 64) (0x020#12))) (0#64)
        (0x8000801c#64) (Vsa.Sim.initMisa)
        (afterNextPC (afterPrelude σ5) (0x8000801c#64))
        hx14n5 hx0n5
        (by rw [get?_afterNextPC σ5 (0x8000801c#64) _ (by decide) (by decide)]; exact hpc5)
        (by rw [get?_afterNextPC σ5 (0x8000801c#64) _ (by decide) (by decide)]; exact hG5.misa)
        (by decide) ll_flag_andi_ne_zero)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x800080d8#64) := by
    have := obs_branch_taken_pc hobs6
    rwa [show (0x8000801c#64 : BitVec 64) + sign_extend (m := 64) (0x00bc#13)
        = (0x800080d8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_branch_taken_minstret hobs6
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx6_6 : σ6.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_branch_taken_other hobs6 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_5
  have hx20_6 : σ6.regs.get? Register.x20 = some v20 :=
    obs_branch_taken_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_5
  have hx15_6 : σ6.regs.get? Register.x15 = some (v15 + (sign_extend (m := 64) (0x008#12))) :=
    obs_branch_taken_other hobs6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hframe6 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ6 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_branch hobs6 (hframe5 v8 v23 v12 h)
  have hx28_6 : σ6.regs.get? Register.x28 = some v27 :=
    obs_branch_taken_other hobs6 Register.x28 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx28_5
  have hrt6 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ6.mem :=
    fun h => hmem6 ▸ hrt5 h
  have hp0_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat]? = some p0 := hmem6 ▸ hp0_5
  have hp1_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some p1 := hmem6 ▸ hp1_5
  have hp2_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some p2 := hmem6 ▸ hp2_5
  have hp3_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some p3 := hmem6 ▸ hp3_5
  have hp4_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some p4 := hmem6 ▸ hp4_5
  have hp5_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some p5 := hmem6 ▸ hp5_5
  have hp6_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some p6 := hmem6 ▸ hp6_5
  have hp7_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some p7 := hmem6 ▸ hp7_5
  have ha0_6 : σ6.mem[vptr.toNat]? = some a0 := hmem6 ▸ ha0_5
  have ha1_6 : σ6.mem[vptr.toNat + 1]? = some a1 := hmem6 ▸ ha1_5
  have ha2_6 : σ6.mem[vptr.toNat + 2]? = some a2 := hmem6 ▸ ha2_5
  have ha3_6 : σ6.mem[vptr.toNat + 3]? = some a3 := hmem6 ▸ ha3_5
  have ha4_6 : σ6.mem[vptr.toNat + 4]? = some a4b := hmem6 ▸ ha4_5
  have ha5_6 : σ6.mem[vptr.toNat + 5]? = some a5b := hmem6 ▸ ha5_5
  have ha6_6 : σ6.mem[vptr.toNat + 6]? = some a6 := hmem6 ▸ ha6_5
  have ha7_6 : σ6.mem[vptr.toNat + 7]? = some a7 := hmem6 ▸ ha7_5
  -- ══ 800080d8: ld a4,24(sp)  ⇒ x14 := vptr (the va_area ptr) ══
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800080d8 hload6
  have hx2n6 : (afterNextPC (afterPrelude σ6) (0x800080d8#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ6 (0x800080d8#64) _ (by decide) (by decide)]; exact hx2_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800080d8#64) vmi6 (0x01813703#32)
      (instruction.LOAD (0x018#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0e#5, false, 8))
      Register.x14 (sign_extend (m := 64)
        ((((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0)
          : BitVec (8 * 8)))
      (0x03#8) (0x37#8) (0x81#8) (0x01#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01813703 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (exec_ld σ6 (0x800080d8#64) (0x018#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0e#5)
        (sigma3_alu σ6 (0x800080d8#64) Register.x14 (sign_extend (m := 64)
          ((((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0)
            : BitVec (8 * 8))))
        vsp p0 p1 p2 p3 p4 p5 p6 p7 hG6 (rX_bits_x2 _ vsp hx2n6) (wX_bits_x14 _ _)
        (by rw [hoff24]; omega) (by rw [hoff24]; omega) (Or.inr (by rw [hoff24]; simp only [tohostAddr]; omega))
        (by rw [hoff24]; omega)
        hp0_6 hp1_6 hp2_6 hp3_6 hp4_6 hp5_6 hp6_6 hp7_6)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x800080dc#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800080d8#64 : BitVec 64) 4 = (0x800080dc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  -- x14 now holds vptr (rewrite via hvptr)
  have hsext_vptr : (sign_extend (m := 64) vptr : BitVec 64) = vptr := by
    simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have hx14_7 : σ7.regs.get? Register.x14 = some vptr := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hvptr, hsext_vptr] at this; exact this
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx6_7 : σ7.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hx20_7 : σ7.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_6
  have hx15_7 : σ7.regs.get? Register.x15 = some (v15 + (sign_extend (m := 64) (0x008#12))) :=
    obs_alu_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_6
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hframe7 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ7 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs7 (by decide) (by decide) (by decide) (hframe6 v8 v23 v12 h)
  have hx28_7 : σ7.regs.get? Register.x28 = some v27 :=
    obs_alu_other hobs7 Register.x28 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx28_6
  have hrt7 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ7.mem :=
    fun h => hmem7 ▸ hrt6 h
  have ha0_7 : σ7.mem[vptr.toNat]? = some a0 := hmem7 ▸ ha0_6
  have ha1_7 : σ7.mem[vptr.toNat + 1]? = some a1 := hmem7 ▸ ha1_6
  have ha2_7 : σ7.mem[vptr.toNat + 2]? = some a2 := hmem7 ▸ ha2_6
  have ha3_7 : σ7.mem[vptr.toNat + 3]? = some a3 := hmem7 ▸ ha3_6
  have ha4_7 : σ7.mem[vptr.toNat + 4]? = some a4b := hmem7 ▸ ha4_6
  have ha5_7 : σ7.mem[vptr.toNat + 5]? = some a5b := hmem7 ▸ ha5_6
  have ha6_7 : σ7.mem[vptr.toNat + 6]? = some a6 := hmem7 ▸ ha6_6
  have ha7_7 : σ7.mem[vptr.toNat + 7]? = some a7 := hmem7 ▸ ha7_6
  -- ══ 800080dc: ld a3,0(a4)  ⇒ x13 := sext(*(vptr)) = the long-long value `v` ══
  obtain ⟨hi0, hi1', hi2', hi3'⟩ := Vsa.Sim.Code.svfprintfSlice_at_800080dc hload7
  have hx14n7 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ7) (0x800080dc#64))
      = .ok vptr (afterNextPC (afterPrelude σ7) (0x800080dc#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ7 (0x800080dc#64) _ (by decide) (by decide)]; exact hx14_7
  have hvoff0 : (vptr + sign_extend (m := 64) (0x000#12)).toNat = vptr.toNat := by
    rw [BitVec.toNat_add, show (sign_extend (m := 64) (0x000#12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt vptr.isLt]
  obtain ⟨σ8, i8, hs8s, hi8, hG8, hmem8, hobs8⟩ :=
    stepObs_alu σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800080dc#64) vmi7 (0x00073683#32)
      (instruction.LOAD (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0d#5, false, 8))
      Register.x13 (sign_extend (m := 64)
        ((((((((a7.append a6).append a5b).append a4b).append a3).append a2).append a1).append a0)
          : BitVec (8 * 8)))
      (0x83#8) (0x36#8) (0x07#8) (0x00#8)
      hG7 hpc7 hmi7 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00073683 (afterPrelude σ7)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.misa)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.cur_privilege)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.mseccfg))
      (exec_ld σ7 (0x800080dc#64) (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0d#5)
        (sigma3_alu σ7 (0x800080dc#64) Register.x13 (sign_extend (m := 64)
          ((((((((a7.append a6).append a5b).append a4b).append a3).append a2).append a1).append a0)
            : BitVec (8 * 8))))
        vptr a0 a1 a2 a3 a4b a5b a6 a7 hG7 hx14n7 (wX_bits_x13 _ _)
        (by rw [hvoff0]; exact hvlo) (by rw [hvoff0]; exact hvhiram)
        (by rw [hvoff0]; exact hvhtif) (by rw [hvoff0]; exact hvalign)
        (by rw [hvoff0]; exact ha0_7) (by rw [hvoff0]; exact ha1_7) (by rw [hvoff0]; exact ha2_7)
        (by rw [hvoff0]; exact ha3_7) (by rw [hvoff0]; exact ha4_7) (by rw [hvoff0]; exact ha5_7)
        (by rw [hvoff0]; exact ha6_7) (by rw [hvoff0]; exact ha7_7))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hi0 hi1' hi2' hi3' (by decide) (by decide) (by decide) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8s
  have hpc8 : σ8.regs.get? Register.PC = some (0x800080e0#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x800080dc#64 : BitVec 64) 4 = (0x800080e0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx13_8 : σ8.regs.get? Register.x13
      = some (sign_extend (m := 64)
          ((((((((a7.append a6).append a5b).append a4b).append a3).append a2).append a1).append a0)
            : BitVec (8 * 8))) :=
    obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx6_8 : σ8.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_alu_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_7
  have hx20_8 : σ8.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_7
  have hx15_8 : σ8.regs.get? Register.x15 = some (v15 + (sign_extend (m := 64) (0x008#12))) :=
    obs_alu_other hobs8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hframe8 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ8 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_alu hobs8 (by decide) (by decide) (by decide) (hframe7 v8 v23 v12 h)
  have hx28_8 : σ8.regs.get? Register.x28 = some v27 :=
    obs_alu_other hobs8 Register.x28 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx28_7
  have hrt8 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ8.mem :=
    fun h => hmem8 ▸ hrt7 h
  -- ══ 800080e0: sd a5,24(sp)  ⇒ store bumped va-ptr at sp+24 ══
  obtain ⟨hj0, hj1, hj2, hj3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800080e0 hload8
  have hx2n8 : (afterNextPC (afterPrelude σ8) (0x800080e0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ8 (0x800080e0#64) _ (by decide) (by decide)]; exact hx2_8
  have hx15n8 : (afterNextPC (afterPrelude σ8) (0x800080e0#64)).regs.get? Register.x15 = some (v15 + (sign_extend (m := 64) (0x008#12))) := by
    rw [get?_afterNextPC σ8 (0x800080e0#64) _ (by decide) (by decide)]; exact hx15_8
  obtain ⟨σ9, i9, hs9s, hi9, hG9, hmem9, hobs9⟩ :=
    stepObs_store σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800080e0#64) vmi8 (0x00f13c23#32)
      (instruction.STORE (0x018#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ8) (0x800080e0#64)).mem
        (vsp + sign_extend (m := 64) (0x018#12)).toNat (sdData_val (v15 + (sign_extend (m := 64) (0x008#12)))))
      (0x23#8) (0x3c#8) (0xf1#8) (0x00#8)
      hG8 hpc8 hmi8 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00f13c23 (afterPrelude σ8)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.misa)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.cur_privilege)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.mseccfg))
      (exec_sd_val σ8 (0x800080e0#64) (0x018#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x02#5)
        vsp (v15 + (sign_extend (m := 64) (0x008#12))) hG8 (rX_bits_x2 _ vsp hx2n8) (rX_bits_x15 _ (v15 + (sign_extend (m := 64) (0x008#12))) hx15n8)
        (by rw [hoff24]; omega) (by rw [hoff24]; omega) (by rw [hoff24]; simp only [tohostAddr]; omega) (by rw [hoff24]; omega))
      hj0 hj1 hj2 hj3 (by decide) (by decide) (by decide) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9s
  have hpc9 : σ9.regs.get? Register.PC = some (0x800080e4#64) := by
    have := obs_store_pc_sn4 hobs9
    rwa [show BitVec.addInt (0x800080e0#64 : BitVec 64) 4 = (0x800080e4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx6_9 : σ9.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    obs_store_other_sn4 Register.x6 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_8
  have hx20_9 : σ9.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4 Register.x20 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_8
  have hx13_9 : σ9.regs.get? Register.x13
      = some (sign_extend (m := 64)
          ((((((((a7.append a6).append a5b).append a4b).append a3).append a2).append a1).append a0)
            : BitVec (8 * 8))) :=
    obs_store_other_sn4 Register.x13 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_8
  have hNP9 : (afterNextPC (afterPrelude σ8) (0x800080e0#64)).mem = σ8.mem := rfl
  have hkey24 : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x018#12)).toNat := by
    rw [hoff24]; omega
  have hload9 : SvfprintfSliceLoaded σ9.mem := by
    rw [hmem9, hNP9]; exact svfprintfSlice_writeMap8_sn5 _ _ _ hkey24 hload8
  have hframe9 : ∀ v8 v23 v12, PrintEntryFrame c.σ v8 v23 v12 →
      PrintEntryFrame σ9 v8 v23 v12 := fun v8 v23 v12 h =>
    printEntryFrame_store hobs9 (hframe8 v8 v23 v12 h)
  have hx28_9 : σ9.regs.get? Register.x28 = some v27 :=
    obs_store_other_sn4 Register.x28 hobs9 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx28_8
  have hrt9 : SnprintfRuntimeLoaded c.σ.mem → SnprintfRuntimeLoaded σ9.mem := fun h => by
    rw [hmem9, hNP9]
    exact snprintfRuntimeLoaded_writeMap8 _ _ _ (by rw [hoff24]; omega) (hrt8 h)
  -- assemble the 9-step chain
  refine ⟨⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG9, hpc9, hx2_9, hx6_9,
    hx20_9, hx28_9, hx13_9, hload9, hframe9, hrt9, hi9⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    ((Steps.single hstep7).trans ((Steps.single hstep8).trans (Steps.single hstep9))))))))

/-- The signed 64-bit value fetched from the caller's `va_list`. -/
abbrev llArg (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) : BitVec 64 :=
  sign_extend (m := 64)
    ((((((((a7.append a6).append a5).append a4).append a3).append a2).append a1).append a0)
      : BitVec (8 * 8))

/-- Concrete default-width negative `%lld` path from the `'d'` handler through
argument fetch, sign handling, decimal conversion, and the PRINT entry. -/
theorem dispatchD_ll_to_print_neg_default_width_spec
    (vsp vptr v9 v27 v8 v23 v12 : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 8)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008008#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20))
    (hx25 : c.σ.regs.get? Register.x25 = some v9)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (hx20 : c.σ.regs.get? Register.x20 = some ((0#64) - (0x1#64)))
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
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
    (hvlo : 0x80000000 ≤ vptr.toNat)
    (hvhiram : vptr.toNat + 8 ≤ 0x100000000)
    (hvhtif : vptr.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vptr.toNat)
    (hvalign : vptr.toNat % 8 = 0)
    (hvdisj : vptr.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 356 ≤ vptr.toNat)
    (ha0 : c.σ.mem[vptr.toNat]? = some a0)
    (ha1 : c.σ.mem[vptr.toNat + 1]? = some a1)
    (ha2 : c.σ.mem[vptr.toNat + 2]? = some a2)
    (ha3 : c.σ.mem[vptr.toNat + 3]? = some a3)
    (ha4 : c.σ.mem[vptr.toNat + 4]? = some a4b)
    (ha5 : c.σ.mem[vptr.toNat + 5]? = some a5b)
    (ha6 : c.σ.mem[vptr.toNat + 6]? = some a6)
    (ha7 : c.σ.mem[vptr.toNat + 7]? = some a7)
    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)
    (hmag : 9 < ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) signByte) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat =
        (- (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toNat ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  obtain ⟨c1, hs1, hG1, hpc1, hx2_1, hx6_1, hx20_1, hx28_1, hx13_1, hload1,
      hframe1, hrt1, htick1⟩ :=
    dispatchD_ll_to_printEntry_spec vsp vptr v9 v27 ((0#64) - (0x1#64))
      p0 p1 p2 p3 p4 p5 p6 p7 a0 a1 a2 a3 a4b a5b a6 a7 c
      hG hload hpc hx2 hx6 hx25 hx27 hx20 htlo hhi halign
      hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hvptr hvlo hvhiram hvhtif hvalign hvdisj
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 htick
  obtain ⟨hx8_1, hx23_1, hx12_1⟩ := hframe1 v8 v23 v12 ⟨hx8, hx23, hx12⟩
  obtain ⟨huload1, hcuload1, hfp1⟩ := hrt1 ⟨huload, hcuload, hfp⟩
  obtain ⟨c', hs2, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi'⟩ :=
    entryToPrint_neg_default_width_spec (llArg a0 a1 a2 a3 a4b a5b a6 a7)
      vsp (BitVec.ofNat 64 0x20) v8 v23 v27 v12 c1
      hG1 hload1 huload1 hcuload1 hfp1 hpc1 hx13_1 hx2_1 hx6_1 hx8_1 hx20_1
      hx23_1 hx28_1 hx12_1 (by decide) hneg hmag htlo hhi halign htick1
  exact ⟨c', hs1.trans hs2, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi'⟩

end Vsa.Sim
