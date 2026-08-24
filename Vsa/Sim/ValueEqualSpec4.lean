import Vsa.Sim.ValueEqualSpec3

/-!
# Layer 3 — the `str`-`str` handler epilogue and the unified `value_equal` spec

`ValueEqualSpec3` carried the `str` handler from `0x800028c4` **through the `strcmp` call**
to the return-site `0x800028d8` (`ve_str_reaches_result`), recovering `sp` across the call
via strcmp's ghost frame (the fix retrofitted in this cluster: `strcmp_post` now exposes a
`NotWrittenStrcmp` blanket frame, so `x2 = sp - 16` survives the call).

This file finishes the handler:

```
0x800028d8  ld ra,8(sp)      ; restore ra := r from the spill slot (mem[sp-8], untouched)
0x800028dc  seqz a0,a0       ; a0 := (strcmp result == 0) ? 1 : 0 = Value.equal (.str sa)(.str sb)
0x800028e0  addi sp,sp,16    ; sp := entry_sp
0x800028e4  ret              ; PC := ra = r
```

and assembles:

* `ve_str_epilogue` — `0x800028d8 → ret`, from the post-call state to the return.
* `ve_str_handler` — the whole `str` handler `0x800028c4 → ret`.
* `value_equal_spec_str` — from `ve_pre` (`str`-`str`) + the stack witnesses to the
  **stack-window post** `ve_str_post` (`mem` agrees with `m0` off `[entry_sp-16, entry_sp)`).
* `value_equal_spec_full` — either branch: `str`-`str` via `value_equal_spec_str`, everything
  else via `value_equal_spec_nonstr` (whose `mem = m0` post trivially weakens to the window
  form).

## Why the stack-window post

The five non-`str` handlers are read-only (`mem = m0`). The `str` handler spills `ra` into
`[entry_sp-16, entry_sp)`; the spilled dword is never cleaned up, so at the return `mem ≠ m0`
inside that window. The honest unified post therefore weakens `mem = m0` to *agreement with
`m0` outside the scratch window* (the `MallocContract`/`env_new` framing form from
AMENDMENT 2). Every other observable — `PC = r`, `x1 = r`, `x2 = entry_sp` restored, the
result `x10`, `tick < 2`, and the `NotWrittenVE` frame — is exact.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `str`-`str` stack-window post

`ve_str_post g r sp va vb m0` is `ve_post` weakened at the memory clause: instead of
`mem = m0`, memory agrees with `m0` outside the scratch window `[sp-16, sp)`, and `x2` is
back to the entry `sp`. -/
def ve_str_post (g : (R : Register) → Option (RegisterType R)) (r sp : BitVec 64)
    (va vb : Value) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some (cond (Value.equal va vb) (1#64) (0#64)) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  c.σ.regs.get? Register.x2 = some sp ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  (∀ a, ¬ (sp.toNat - 16 ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?) ∧
  -- The frame is over `NotWrittenVEStr` — strcmp additionally clobbers its caller-saved
  -- scratch (`x5-x7`, `x11-x13`), which the str handler does NOT restore, so the wider
  -- `NotWrittenVE` frame is not honest here; `x1`/`x2` are restored and asserted above.
  (∀ R : Register, NotWrittenVEStr R → c.σ.regs.get? R = g R)

/-! ## The epilogue `0x800028d8 … 0x800028e4`

From the post-call state (`ve_str_reaches_result`'s conclusion) at `0x800028d8` with
`x1 = 0x800028d8` (the `jal` link), `x10 = x` (strcmp result), `x2 = sp - 16`, `mem = m1`
where `m1` agrees with `m0` off `[sp-16, sp)` and the spill slot `[sp-8, sp)` holds
`sdData_val r`, run the four epilogue instructions to the return at `r`. -/

/-- The epilogue restores `ra`, computes `seqz`, restores `sp`, and returns. The `ld ra`
reads the spilled `r` back from the untouched slot `mem[sp-8] = sdData_val r`. -/
theorem ve_str_epilogue
    (g : (R : Register) → Option (RegisterType R)) (r sp : BitVec 64) (x : BitVec 64)
    (va vb : Value) (m0 m1 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) (hi : c.tick < 2) (hG : GoodState c.σ)
    (hloaded1 : Value_equalLoaded m1) (hmem : c.σ.mem = m1)
    (hpc : c.σ.regs.get? Register.PC = some (0x800028d8#64 : BitVec 64))
    (hra : c.σ.regs.get? Register.x1 = some (0x800028d8#64 : BitVec 64))
    (hx10 : c.σ.regs.get? Register.x10 = some x)
    (hsp : c.σ.regs.get? Register.x2 = some (sp - 16#64))
    (vmi : BitVec 64) (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (hframe : ∀ R : Register, NotWrittenVEStr R → c.σ.regs.get? R = g R)
    -- the result bridge
    (hbridge : (x == 0#64) = Value.equal va vb)
    -- stack facts: `sp` 16-aligned window in RAM, above HTIF; `r` 4-aligned
    (hsp16 : 16 ≤ sp.toNat) (hwin_lo : 0x80000000 ≤ sp.toNat - 16)
    (hwin_hi : sp.toNat ≤ 0x100000000) (hwin_htif : tohostAddr + 16 ≤ sp.toNat - 16)
    (hwin_align : (sp.toNat - 16) % 8 = 0)
    (hralign : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (he4lo : 0x80000000 ≤ (0x800028e4 : Nat)) (he4hi : (0x800028e4 : Nat) + 4 ≤ tohostAddr)
    -- the spill slot `[sp-8, sp)` of `m1` holds `sdData_val r` (from the `sd ra,8(sp)`)
    (hspill : m1 = writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r)) :
    ∃ c', Steps c c' ∧ ve_str_post g r sp va vb m0 c' := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- spn = sp - 16 arithmetic
  have hspn_toNat : (sp - 16#64).toNat = sp.toNat - 16 := ve_sp_sub16_toNat sp hsp16
  have hspn8 : ((sp - 16#64) + sign_extend (m := 64) (0x008#12)).toNat = (sp - 16#64).toNat + 8 := by
    apply ve_off8; rw [hspn_toNat]; have := sp.isLt; omega
  -- the 8 spilled bytes of `m1` at [spn+8, spn+16)
  have hb0 : m1[(sp - 16#64).toNat + 8]? = some ((sdData_val r).extractLsb' 0 8) := by
    rw [hspill]; exact getElem_writeMap8_0 m0 _ _
  have hb1 : m1[(sp - 16#64).toNat + 8 + 1]? = some ((sdData_val r).extractLsb' 8 8) := by
    rw [hspill]; exact getElem_writeMap8_1 m0 _ _
  have hb2 : m1[(sp - 16#64).toNat + 8 + 2]? = some ((sdData_val r).extractLsb' 16 8) := by
    rw [hspill]; exact getElem_writeMap8_2 m0 _ _
  have hb3 : m1[(sp - 16#64).toNat + 8 + 3]? = some ((sdData_val r).extractLsb' 24 8) := by
    rw [hspill]; exact getElem_writeMap8_3 m0 _ _
  have hb4 : m1[(sp - 16#64).toNat + 8 + 4]? = some ((sdData_val r).extractLsb' 32 8) := by
    rw [hspill]; exact getElem_writeMap8_4 m0 _ _
  have hb5 : m1[(sp - 16#64).toNat + 8 + 5]? = some ((sdData_val r).extractLsb' 40 8) := by
    rw [hspill]; exact getElem_writeMap8_5 m0 _ _
  have hb6 : m1[(sp - 16#64).toNat + 8 + 6]? = some ((sdData_val r).extractLsb' 48 8) := by
    rw [hspill]; exact getElem_writeMap8_6 m0 _ _
  have hb7 : m1[(sp - 16#64).toNat + 8 + 7]? = some ((sdData_val r).extractLsb' 56 8) := by
    rw [hspill]; exact getElem_writeMap8_7 m0 _ _
  have hloadedσ : Value_equalLoaded c.σ.mem := hmem ▸ hloaded1
  -- === 0x800028d8: ld ra,8(sp) ⇒ x1 := sext(spilled bytes) = r ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800028d8 c.σ c.tick c.steps (0x800028d8#64) vmi (sp - 16#64)
      ((sdData_val r).extractLsb' 0 8) ((sdData_val r).extractLsb' 8 8)
      ((sdData_val r).extractLsb' 16 8) ((sdData_val r).extractLsb' 24 8)
      ((sdData_val r).extractLsb' 32 8) ((sdData_val r).extractLsb' 40 8)
      ((sdData_val r).extractLsb' 48 8) ((sdData_val r).extractLsb' 56 8)
      hG hpc hmi hsp hloadedσ rfl
      (by rw [hspn8, hspn_toNat]; omega)
      (by rw [hspn8, hspn_toNat]; omega)
      (by rw [hspn8, hspn_toNat]; right; rw [htoh]; rw [htoh] at hwin_htif; omega)
      (by rw [hspn8, hspn_toNat]; omega)
      (by rw [hspn8, hmem]; exact hb0) (by rw [hspn8, hmem]; exact hb1)
      (by rw [hspn8, hmem]; exact hb2) (by rw [hspn8, hmem]; exact hb3)
      (by rw [hspn8, hmem]; exact hb4) (by rw [hspn8, hmem]; exact hb5)
      (by rw [hspn8, hmem]; exact hb6) (by rw [hspn8, hmem]; exact hb7) hi
  have hmem1eq : σ1.mem = m1 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800028dc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800028d8#64) 4 = (0x800028dc#64 : BitVec 64) from by decide] at this
  have hra_1 : σ1.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ve_sext_reassemble r]
  have hx10_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10
  have hsp_1 := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVEStr R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_vestr hobs1 R hR hR.1).trans (hframe R hR)
  -- === 0x800028dc: seqz a0,a0 ⇒ x10 := cond (x == 0) 1 0 = Value.equal va vb ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800028dc σ1 i1 (c.steps + 1) (0x800028dc#64) vmi1 x hG1 hpc1 hmi1 hx10_1 (hmem1eq ▸ hloaded1) rfl hi1
  have hmem2eq : σ2.mem = m1 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x800028e0#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800028dc#64) 4 = (0x800028e0#64 : BitVec 64) from by decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (cond (Value.equal va vb) (1#64) (0#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, seqz_val, hbridge]
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hsp_2 := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVEStr R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_vestr hobs2 R hR hR.2.2.2.2.2.1).trans (hframe1 R hR)
  -- === 0x800028e0: addi sp,sp,16 ⇒ x2 := (sp-16) + 16 = sp ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800028e0 σ2 i2 (c.steps + 1 + 1) (0x800028e0#64) vmi2 (sp - 16#64)
      hG2 hpc2 hmi2 hsp_2 (hmem2eq ▸ hloaded1) rfl hi2
  have hmem3eq : σ3.mem = m1 := by rw [hmem3, hmem2eq]
  have hpc3 : σ3.regs.get? Register.PC = some (0x800028e4#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800028e0#64) 4 = (0x800028e4#64 : BitVec 64) from by decide] at this
  have hsp_3 : σ3.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ve_sp_restore sp]
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hframe3 : ∀ R : Register, NotWrittenVEStr R → σ3.regs.get? R = g R := fun R hR =>
    (frame_alu_vestr hobs3 R hR hR.2.1).trans (hframe2 R hR)
  -- === 0x800028e4: ret ⇒ PC := r ===
  obtain ⟨hbe0, hbe1, hbe2, hbe3⟩ := value_equal_at_800028e4 (hmem3eq ▸ hloaded1)
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_ret_gen σ3 i3 (c.steps + 1 + 1 + 1) (0x800028e4#64) vmi3 r
      (0x67#8) (0x80#8) (0x00#8) (0x00#8)
      hG3 hpc3 hmi3 hra_3
      (by show σ3.mem[(0x800028e4 : Nat)]? = _; exact hbe0)
      (by show σ3.mem[(0x800028e4 : Nat) + 1]? = _; exact hbe1)
      (by show σ3.mem[(0x800028e4 : Nat) + 2]? = _; exact hbe2)
      (by show σ3.mem[(0x800028e4 : Nat) + 3]? = _; exact hbe3)
      (by apply BitVec.eq_of_toNat_eq; decide) (by show (0x80000000 : Nat) ≤ _; exact he4lo)
      (by show (0x800028e4 : Nat) + 4 ≤ _; exact he4hi) (by decide) hralign hi3
  have hmem4eq : σ4.mem = m1 := by rw [hmem4, hmem3eq]
  -- assemble the four steps
  have hpc4 : σ4.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) :=
    obs_jr_pc hobs4
  have ha0_4 := obs_jr_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have hra_4 := obs_jr_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hsp_4 := obs_jr_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_jr_minstret hobs4
  have hframe4 : ∀ R : Register, NotWrittenVEStr R → σ4.regs.get? R = g R := fun R hR =>
    (frame_jr_vestr hobs4 R hR).trans (hframe3 R hR)
  -- the memory window frame: σ4.mem = m1 agrees with m0 off [sp-16, sp)
  have hmemframe : ∀ a, ¬ (sp.toNat - 16 ≤ a ∧ a < sp.toNat) → σ4.mem[a]? = m0[a]? := by
    intro a ha
    rw [hmem4eq, hspill, getElem_writeMap8_disjoint _ _ _ _ (by rw [hspn_toNat]; omega)]
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩,
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4),
    hG4, hpc4, ha0_4, hra_4, hsp_4, ⟨vmi4, hmi4⟩, hi4, hmemframe, hframe4⟩

/-! ## The whole `str` handler `0x800028c4 → ret`

`ve_str_reaches_result` (through the call) then `ve_str_epilogue`. -/

/-- **The `str`-`str` handler.** From the handler entry `0x800028c4` to the return at `r`,
with the stack-window post. -/
theorem ve_str_handler
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (sa sb : String) (pa' pb' : Nat) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hloaded : Value_equalLoaded m0)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0)
    (hpc : σ.regs.get? Register.PC = some (0x800028c4#64 : BitVec 64))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r) (hsp : σ.regs.get? Register.x2 = some sp)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hralign : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hraln4 : r.toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    (hpa : read64 m0 (bufa.toNat + 8) = some pa') (hpb : read64 m0 (bufb.toNat + 8) = some pb')
    (hca : CStr m0 pa' csa) (hcb : CStr m0 pb' csb)
    (hsa : sa = String.ofList csa) (hsb : sb = String.ofList csb)
    (hbra : StrcmpRegion (BitVec.ofNat 64 pa') csa.length)
    (hbrb : StrcmpRegion (BitVec.ofNat 64 pb') csb.length)
    (hwra : StrcmpWRegion (BitVec.ofNat 64 pa') csa.length)
    (hwrb : StrcmpWRegion (BitVec.ofNat 64 pb') csb.length)
    (hSR : VEStrRegions sp pa' pb' csa.length csb.length) :
    ∃ c', Steps c c' ∧ ve_str_post g r sp (.str sa) (.str sb) m0 c' := by
  -- the str frame at the handler entry (`NotWrittenVEStr ⊆ NotWrittenVE`)
  have hframestr : ∀ R : Register, NotWrittenVEStr R → σ.regs.get? R = g R :=
    fun R hR => hframe R (notWrittenVE_of_str hR)
  -- run through the strcmp call to `0x800028d8`
  obtain ⟨c6, m1, x, hs6, hG6, htick6, hpc6, hra6, hx10_6, hbridge, hsp6, hmem6, _hmemframe6,
    hframeStr6, hm1def, hloaded1⟩ :=
    ve_str_reaches_result g bufa bufb r sp sa sb pa' pb' csa csb m0 c σ i steps0
      hsteps0 hi hG hmem hloaded hstrc hmask hpc ha0 ha1 hra hsp vmi hmi hrega hregb hraln4
      hframe hpa hpb hca hcb hsa hsb hbra hbrb hwra hwrb hSR
  -- run the epilogue (minstret at c6 comes from `GoodState`)
  obtain ⟨vmi6, hmi6⟩ := hG6.minstret
  obtain ⟨c', hs', hpost'⟩ :=
    ve_str_epilogue g r sp x (.str sa) (.str sb) m0 m1 c6 htick6 hG6 hloaded1 hmem6
      hpc6 hra6 hx10_6 hsp6 vmi6 hmi6 hframeStr6 hbridge
      hSR.sp16 hSR.win_lo hSR.win_hi hSR.win_htif hSR.win_align hralign (by decide) (by decide)
      hm1def
  exact ⟨c', hs6.trans hs', hpost'⟩

/-! ## The `str`-`str` spec (`value_equal_spec_str`)

From `ve_pre` (`str`-`str`) plus the stack/region witnesses to the stack-window post. The
dispatch (`ve_to_handler`) reaches the handler at `0x800028c4`; `ve_str_handler` finishes. -/

/-- **`value_equal` on two strings.** From the entry `0x8000285c` (with the extra stack
witnesses) to the return, deciding `sa = sb` via `strcmp`, with the stack-window post. -/
theorem value_equal_spec_str
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (sa sb : String)
    (pa' pb' : Nat) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (hpre : ve_pre g bufa bufb r N φc (.str sa) (.str sb) m0 c)
    (hsp : c.σ.regs.get? Register.x2 = some sp)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0)
    (hraln4 : r.toNat % 4 = 0)
    -- the two string payloads (matching `ValueRepr .str`)
    (hpa : read64 m0 (bufa.toNat + 8) = some pa') (hpb : read64 m0 (bufb.toNat + 8) = some pb')
    (hca : CStr m0 pa' csa) (hcb : CStr m0 pb' csb)
    (hsa : sa = String.ofList csa) (hsb : sb = String.ofList csb)
    (hbra : StrcmpRegion (BitVec.ofNat 64 pa') csa.length)
    (hbrb : StrcmpRegion (BitVec.ofNat 64 pb') csb.length)
    (hwra : StrcmpWRegion (BitVec.ofNat 64 pa') csa.length)
    (hwrb : StrcmpWRegion (BitVec.ofNat 64 pb') csb.length)
    (hSR : VEStrRegions sp pa' pb' csa.length csb.length) :
    ∃ c', Steps c c' ∧ ve_str_post g r sp (.str sa) (.str sb) m0 c' := by
  obtain ⟨hG, hloaded, hjt, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hra', hrb', hrega, hregb, hrettgt, hframe⟩ := hpre
  -- dispatch to the handler at `0x800028c4` (`handlerAddr (.str _)`)
  obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
    ve_to_handler g bufa bufb r N φc (.str sa) (.str sb) m0 c rfl hG hloaded hjt
      hmem hpc ha0 ha1 hra vmi hmi htick hra' hrb' hrega hregb hframe
  rw [show handlerAddr (Value.str sa) = 0x800028c4#64 from rfl] at hpcd
  -- `x2 = sp` survives the dispatch (`x2 ∈ NotWrittenVE`, tied to `g`)
  have hspd : σd.regs.get? Register.x2 = some sp := by
    rw [hframed Register.x2 (by decide)]
    have := hframe Register.x2 (by decide); rw [hsp] at this; exact this.symm
  -- run the handler from `0x800028c4`
  exact ve_str_handler g bufa bufb r sp sa sb pa' pb' csa csb m0 c σd idd
    (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hstepsd hidd hGd hmemd (hmem ▸ hloaded)
    hstrc hmask hpcd ha0d ha1d hrad hspd vmid hmid hrega hregb hrettgt hraln4 hframed
    hpa hpb hca hcb hsa hsb hbra hbrb hwra hwrb hSR

/-! ## The unified `value_equal` spec (`value_equal_spec_full`)

Either the `str`-`str` branch (`value_equal_spec_str`) or one of the five non-`str`
branches (`value_equal_spec_nonstr`), unified under the weaker stack-window post: the
non-`str` post `mem = m0` trivially agrees with `m0` off any window, and `x2` is never
touched (`x2 = g x2 = sp`). -/

/-- **`value_equal`, both cases.** From `ve_pre` plus the `str`-path witnesses (needed only
if both operands are strings) to the stack-window post `ve_str_post`. -/
theorem value_equal_spec_full
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b)
    (hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h)
    (hpre : ve_pre g bufa bufb r N φc va vb m0 c)
    (hsp : c.σ.regs.get? Register.x2 = some sp)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0) (hraln4 : r.toNat % 4 = 0)
    -- `str`-path witnesses, only consumed when `va = .str sa ∧ vb = .str sb`
    (hstrwit : ∀ sa sb, va = .str sa → vb = .str sb →
      ∃ (pa' pb' : Nat) (csa csb : List Char),
        read64 m0 (bufa.toNat + 8) = some pa' ∧ read64 m0 (bufb.toNat + 8) = some pb' ∧
        CStr m0 pa' csa ∧ CStr m0 pb' csb ∧ sa = String.ofList csa ∧ sb = String.ofList csb ∧
        StrcmpRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpRegion (BitVec.ofNat 64 pb') csb.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pb') csb.length ∧
        VEStrRegions sp pa' pb' csa.length csb.length) :
    ∃ c', Steps c c' ∧ ve_str_post g r sp va vb m0 c' := by
  by_cases hstr : ∃ sa sb, va = .str sa ∧ vb = .str sb
  · obtain ⟨sa, sb, hva, hvb⟩ := hstr
    subst hva; subst hvb
    obtain ⟨pa', pb', csa, csb, hpa, hpb, hca, hcb, hsa, hsb, hbra, hbrb, hwra, hwrb, hSR⟩ :=
      hstrwit sa sb rfl rfl
    exact value_equal_spec_str g bufa bufb r sp N φc sa sb pa' pb' csa csb m0 c hpre hsp
      hstrc hmask hraln4 hpa hpb hca hcb hsa hsb hbra hbrb hwra hwrb hSR
  · -- non-`str`: use `value_equal_spec_nonstr`, weaken `mem = m0` to the window form
    have hnotstr : ∀ sa sb, ¬ (va = .str sa ∧ vb = .str sb) :=
      fun sa sb ⟨h1, h2⟩ => hstr ⟨sa, sb, h1, h2⟩
    -- `g x2 = sp` from the entry frame (`x2 ∈ NotWrittenVE`)
    have hgx2 : g Register.x2 = some sp := by
      have hframe0 : ∀ R : Register, NotWrittenVE R → c.σ.regs.get? R = g R :=
        hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have := hframe0 Register.x2 (by decide); rw [hsp] at this; exact this.symm
    obtain ⟨c', hs', hG', hpc', ha0', hra', ⟨w, hmi'⟩, htick', hmem', hframe'⟩ :=
      value_equal_spec_nonstr g bufa bufb r N φc va vb m0 hφc hN hnotstr c hpre
    -- `x2` is untouched by the non-`str` handlers: `x2 = g x2 = sp`
    have hsp' : c'.σ.regs.get? Register.x2 = some sp := by
      rw [hframe' Register.x2 (by decide), hgx2]
    refine ⟨c', hs', hG', hpc', ha0', hra', hsp', ⟨w, hmi'⟩, htick', ?_,
      fun R hR => hframe' R (notWrittenVE_of_str hR)⟩
    intro a _; rw [hmem']

end Vsa.Sim
