import Vsa.Sim.MemcpySpecFramed

/-!
# Frame-preserving `memcpy` — the WORD route (`memcpy_spec_framed_word`)

`memcpy_spec_framed_byte` (`MemcpySpecFramed.lean`) covers the byte routes
(misaligned ∨ `n < 8`) of the dispatch carrying the ABI-callee-saved frame
`∀ R, AbiPreserved R → get? R = gm R` — the register half of `EnvDefFrame`.
This file completes the picture with the **aligned WORD route** (case (C) of
`memcpy_spec`: `dst % 8 = 0 ∧ 8*(n/8) ≤ 64`), so a `len+1`-byte C-string copy
into a fresh word-aligned `malloc` block whose length rounds to ≤ 64 words takes
the framed word route (the `env_define` `memcpy(copy,name,len+1)` case when
`src`/`dst` share alignment and `len+1 ≥ 8`).

**Why a framed re-run and not a `bytepath_abi`-style transport.**  The word route
factors into three stages:

* `dispatch_to_word` : `AtBd4 → ∃ g', PreW g'` — `AtBd4` carries NO ghost/frame
  field, so there is nothing to transport the ABI conjunct through; we re-run its
  12 register-only sites carrying `∀ R AbiPreserved, get? R = gm R` via the REUSED
  `strlenFrame_alu`/`strlenFrame_bnottaken` primitives (the `to_bd4_framed`
  idiom).  `NotWrittenW`'s written GPRs `{x13,x15,x16}` are all NON-`AbiPreserved`,
  so every site preserves the AbiPreserved subset.
* `word_loop_spec` : `PreW g' → StWDone g'` — SAME `g'`, both `hframe` over
  `NotWrittenW ⊇ AbiPreserved`, so the ABI conjunct transports for FREE via `g'`
  (`wordloop_abi`, no re-run) — the `bytepath_abi` pattern.
* `epilogue_{notail,tail}` : `StWDone g' → ∃ g'', memcpy_bytepath_post g''` — the
  epilogue writes `{x11,x12,x14}` (all NON-`AbiPreserved`) but RESETS the ghost at
  the `NotWrittenW → NotWrittenB` crossover, so `g''` has no exposed relation to
  `g'`; we re-run its ≤ 15 register-only sites carrying the ABI conjunct.

The post carries `memcpy_bytepath_post g''` (PC=r, x10=dst, described copy into
`[dst,dst+n)`, everything OUTSIDE `[dst,dst+n)` = `m0`) PLUS the ABI-callee-saved
tie `∀ R AbiPreserved, get? R = gm R` — identical shape to
`memcpy_spec_framed_byte`, so `EnvDefCompose.envDefMemcpyFramed` consumes it the
same way; `memcpy_framed_ainv_stable` applies verbatim.

Additive: `dispatch_to_word`/`word_loop_spec`/`epilogue_*` UNCHANGED; no consumer
touched.  No `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Alloc (AbiPreserved)
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `AbiPreserved ⊆ NotWrittenW`

The word-path blanket frame `NotWrittenW` writes only `{x13,x15,x16}` (+ control),
none `AbiPreserved` (`x2/x3/x4/x8/x9/x18..x27`), so the ABI-callee-saved set is a
subset — exactly what lets the `PreW`/`StWDone` `hframe` (over `NotWrittenW`)
deliver the ABI conjunct. -/
theorem abiPreserved_notWrittenW {R : Register} (hR : AbiPreserved R = true) :
    NotWrittenW R := by
  cases R <;> simp_all [AbiPreserved, NotWrittenW]

/-! ## Framed dispatch `AtBd4 → ∃ g', PreW g'` (word route)

Re-run of `dispatch_to_word`'s 12 register-only sites carrying the ABI frame.
Each site preserves every `AbiPreserved` register (none is `x13`/`x15`/`x16`),
lifted by the REUSED `strlenFrame_alu`/`strlenFrame_bnottaken`.  Lands `PreW g'`
with the fresh `g' = c'.σ.regs.get?` AND the ABI conjunct. -/
theorem dispatch_to_word_framed (gm : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign_xor : (src.toNat ^^^ dst.toNat) % 8 = 0) (hbig : 8 ≤ n)
    (hda : dst.toNat % 8 = 0) (hfit : 8 * (n / 8) ≤ 64) :
    Triple
      (fun c => AtBd4 r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g', PreW g' (n / 8) r dst src n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hSt, hgh0⟩
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha5, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv⟩ := hSt
  have hnn := hreg.dst_nowrap
  have h8p0 : 8 * (n / 8) ≤ n := by omega
  have hppos0 : 0 < n / 8 := by omega
  generalize hp_def : n / 8 = p at hfit h8p0 hppos0 ⊢
  have h8p : 8 * p ≤ n := h8p0
  have hppos : 0 < p := hppos0
  -- === bd4: bnez a5 nottaken → bd8 ===
  have hv4 : (((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = false := by
    apply and7_eq_zero_false; rw [xor_toNat]; exact halign_xor
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006bd4_nottaken c.σ c.tick c.steps (0x80006bd4#64) vmi
      ((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12))
      hgood hpc hmi ha5 hloaded rfl hv4 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006bd8#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006bd4#64) 4 = (0x80006bd8#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
  have ha7_1 := obs_bnottaken_other' hobs1 Register.x17 (by decide) ha7
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  have hg1 : ∀ R, AbiPreserved R = true → σ1.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_bnottaken hobs1 R hR]; exact hgh0 R hR
  -- === bd8: sltiu a2,a2,8 → bdc ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006bd8 σ1 i1 (c.steps + 1) (0x80006bd8#64) vmi1 (BitVec.ofNat 64 n)
      hG1 hpc1 hmi1' ha2_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006bdc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006bd8#64) 4 = (0x80006bdc#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha7_2 := obs_alu_other' hobs2 Register.x17 (by decide) ha7_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hg2 : ∀ R, AbiPreserved R = true → σ2.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs2 R (by decide) hR]; exact hg1 R hR
  -- === bdc: bnez a2 nottaken (n ≥ 8 ⇒ a2 = 0) → be0 ===
  have hvdc : ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12))))) != (0#64)) = false := by
    apply sltiu8_ge_false; rw [a2_ofNat_toNat n (by omega)]; exact hbig
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006bdc_nottaken σ2 i2 (c.steps + 1 + 1) (0x80006bdc#64) vmi2
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12)))))
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hvdc hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006be0#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs3; rwa [show BitVec.addInt (0x80006bdc#64) 4 = (0x80006be0#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_bnottaken_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_bnottaken_other' hobs3 Register.x11 (by decide) ha1_2
  have ha7_3 := obs_bnottaken_other' hobs3 Register.x17 (by decide) ha7_2
  have hra_3 := obs_bnottaken_other' hobs3 Register.x1 (by decide) hra_2
  obtain ⟨vmi3, hmi3'⟩ := obs_bnottaken_minstret hobs3
  have hg3 : ∀ R, AbiPreserved R = true → σ3.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_bnottaken hobs3 R hR]; exact hg2 R hR
  -- === be0: andi a5,a0,7 → be4 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006be0 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006be0#64) vmi3 dst
      hG3 hpc3 hmi3' ha0_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006be4#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006be0#64) 4 = (0x80006be4#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_alu_other' hobs4 Register.x11 (by decide) ha1_3
  have ha7_4 := obs_alu_other' hobs4 Register.x17 (by decide) ha7_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha5_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  have hg4 : ∀ R, AbiPreserved R = true → σ4.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs4 R (by decide) hR]; exact hg3 R hR
  -- === be4: mv a4,a0 → be8 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006be4 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006be4#64) vmi4 dst
      hG4 hpc4 hmi4' ha0_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006be8#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006be4#64) 4 = (0x80006be8#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha7_5 := obs_alu_other' hobs5 Register.x17 (by decide) ha7_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha5_5 := obs_alu_other' hobs5 Register.x15 (by decide) ha5_4
  have ha4_5 : σ5.regs.get? Register.x14 = some dst := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show dst + sign_extend (m := 64) (0x000#12) = dst from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero dst] at this
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  have hg5 : ∀ R, AbiPreserved R = true → σ5.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs5 R (by decide) hR]; exact hg4 R hR
  -- === be8: bnez a5 nottaken (a5 = dst&7 = 0, dst%8=0) → bec ===
  have hv8 : (((dst &&& sign_extend (m := 64) (0x007#12))) != (0#64)) = false := by
    apply and7_eq_zero_false; exact hda
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006be8_nottaken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006be8#64) vmi5
      (dst &&& sign_extend (m := 64) (0x007#12))
      hG5 hpc5 hmi5' ha5_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hv8 hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006bec#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs6; rwa [show BitVec.addInt (0x80006be8#64) 4 = (0x80006bec#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_bnottaken_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_bnottaken_other' hobs6 Register.x11 (by decide) ha1_5
  have ha7_6 := obs_bnottaken_other' hobs6 Register.x17 (by decide) ha7_5
  have hra_6 := obs_bnottaken_other' hobs6 Register.x1 (by decide) hra_5
  have ha4_6 := obs_bnottaken_other' hobs6 Register.x14 (by decide) ha4_5
  obtain ⟨vmi6, hmi6'⟩ := obs_bnottaken_minstret hobs6
  have hg6 : ∀ R, AbiPreserved R = true → σ6.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_bnottaken hobs6 R hR]; exact hg5 R hR
  -- === bec: andi a2,a7,-8 → bf0 ===  (a7 = dst+n, a2 := dst + 8p)
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006bec σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bec#64) vmi6
      (dst + BitVec.ofNat 64 n)
      hG6 hpc6 hmi6' ha7_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006bf0#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006bec#64) 4 = (0x80006bf0#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 := obs_alu_other' hobs7 Register.x11 (by decide) ha1_6
  have ha7_7 := obs_alu_other' hobs7 Register.x17 (by decide) ha7_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha4_7 := obs_alu_other' hobs7 Register.x14 (by decide) ha4_6
  have ha2_7 : σ7.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [andneg8_dst_span dst n hda (by omega), hp_def] at this; exact this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  have hg7 : ∀ R, AbiPreserved R = true → σ7.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs7 R (by decide) hR]; exact hg6 R hR
  -- === bf0: sub a3,a2,a4 → bf4 ===  (a3 := (dst+8p) - dst = ofNat 8p)
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006bf0 σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bf0#64) vmi7
      (dst + BitVec.ofNat 64 (8 * p)) dst
      hG7 hpc7 hmi7' ha2_7 ha4_7 (by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006bf4#64 : BitVec 64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006bf0#64) 4 = (0x80006bf4#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_alu_other' hobs8 Register.x10 (by decide) ha0_7
  have ha1_8 := obs_alu_other' hobs8 Register.x11 (by decide) ha1_7
  have ha7_8 := obs_alu_other' hobs8 Register.x17 (by decide) ha7_7
  have hra_8 := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
  have ha4_8 := obs_alu_other' hobs8 Register.x14 (by decide) ha4_7
  have ha2_8 := obs_alu_other' hobs8 Register.x12 (by decide) ha2_7
  have ha3_8 : σ8.regs.get? Register.x13 = some (BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sub_base_span dst (8 * p)] at this
  obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
  have hg8 : ∀ R, AbiPreserved R = true → σ8.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs8 R (by decide) hR]; exact hg7 R hR
  -- === bf4: li a5,64 → bf8 ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006bf4 σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bf4#64) vmi8
      hG8 hpc8 hmi8' (by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x80006bf8#64 : BitVec 64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80006bf4#64) 4 = (0x80006bf8#64 : BitVec 64) from by decide] at this
  have ha0_9 := obs_alu_other' hobs9 Register.x10 (by decide) ha0_8
  have ha1_9 := obs_alu_other' hobs9 Register.x11 (by decide) ha1_8
  have ha7_9 := obs_alu_other' hobs9 Register.x17 (by decide) ha7_8
  have hra_9 := obs_alu_other' hobs9 Register.x1 (by decide) hra_8
  have ha4_9 := obs_alu_other' hobs9 Register.x14 (by decide) ha4_8
  have ha2_9 := obs_alu_other' hobs9 Register.x12 (by decide) ha2_8
  have ha3_9 := obs_alu_other' hobs9 Register.x13 (by decide) ha3_8
  have ha5_9 := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi9, hmi9'⟩ := obs_alu_minstret hobs9
  have hg9 : ∀ R, AbiPreserved R = true → σ9.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs9 R (by decide) hR]; exact hg8 R hR
  -- === bf8: blt a5,a3 nottaken (64 ≥s 8p) → bfc ===
  have hv8b : zopz0zI_s ((0#64) + sign_extend (m := 64) (0x040#12)) (BitVec.ofNat 64 (8 * p)) = false :=
    blt64_span_false p hfit
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80006bf8_nottaken σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bf8#64) vmi9
      ((0#64) + sign_extend (m := 64) (0x040#12)) (BitVec.ofNat 64 (8 * p))
      hG9 hpc9 hmi9' ha5_9 ha3_9 (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hv8b hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x80006bfc#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs10; rwa [show BitVec.addInt (0x80006bf8#64) 4 = (0x80006bfc#64 : BitVec 64) from by decide] at this
  have ha0_10 := obs_bnottaken_other' hobs10 Register.x10 (by decide) ha0_9
  have ha1_10 := obs_bnottaken_other' hobs10 Register.x11 (by decide) ha1_9
  have ha7_10 := obs_bnottaken_other' hobs10 Register.x17 (by decide) ha7_9
  have hra_10 := obs_bnottaken_other' hobs10 Register.x1 (by decide) hra_9
  have ha4_10 := obs_bnottaken_other' hobs10 Register.x14 (by decide) ha4_9
  have ha2_10 := obs_bnottaken_other' hobs10 Register.x12 (by decide) ha2_9
  obtain ⟨vmi10, hmi10'⟩ := obs_bnottaken_minstret hobs10
  have hg10 : ∀ R, AbiPreserved R = true → σ10.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_bnottaken hobs10 R hR]; exact hg9 R hR
  -- === bfc: mv a3,a1 → c00 ===  (a3 := src)
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80006bfc σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bfc#64) vmi10 src
      hG10 hpc10 hmi10' ha1_10 (by rw [hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x80006c00#64 : BitVec 64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80006bfc#64) 4 = (0x80006c00#64 : BitVec 64) from by decide] at this
  have ha0_11 := obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
  have ha1_11 := obs_alu_other' hobs11 Register.x11 (by decide) ha1_10
  have ha7_11 := obs_alu_other' hobs11 Register.x17 (by decide) ha7_10
  have hra_11 := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
  have ha4_11 := obs_alu_other' hobs11 Register.x14 (by decide) ha4_10
  have ha2_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha2_10
  have ha3_11 : σ11.regs.get? Register.x13 = some src := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show src + sign_extend (m := 64) (0x000#12) = src from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero src] at this
  obtain ⟨vmi11, hmi11'⟩ := obs_alu_minstret hobs11
  have hg11 : ∀ R, AbiPreserved R = true → σ11.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs11 R (by decide) hR]; exact hg10 R hR
  -- === c00: mv a5,a4 → c04 ===  (a5 := dst)
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80006c00 σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c00#64) vmi11 dst
      hG11 hpc11 hmi11' ha4_11 (by rw [hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi11
  have hpc12 : σ12.regs.get? Register.PC = some (0x80006c04#64 : BitVec 64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80006c00#64) 4 = (0x80006c04#64 : BitVec 64) from by decide] at this
  have ha0_12 := obs_alu_other' hobs12 Register.x10 (by decide) ha0_11
  have ha1_12 := obs_alu_other' hobs12 Register.x11 (by decide) ha1_11
  have ha7_12 := obs_alu_other' hobs12 Register.x17 (by decide) ha7_11
  have hra_12 := obs_alu_other' hobs12 Register.x1 (by decide) hra_11
  have ha4_12 := obs_alu_other' hobs12 Register.x14 (by decide) ha4_11
  have ha2_12 := obs_alu_other' hobs12 Register.x12 (by decide) ha2_11
  have ha3_12 := obs_alu_other' hobs12 Register.x13 (by decide) ha3_11
  have ha5_12 : σ12.regs.get? Register.x15 = some dst := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show dst + sign_extend (m := 64) (0x000#12) = dst from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero dst] at this
  obtain ⟨vmi12, hmi12'⟩ := obs_alu_minstret hobs12
  have hg12 : ∀ R, AbiPreserved R = true → σ12.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs12 R (by decide) hR]; exact hg11 R hR
  have hmem12eq : σ12.mem = c.σ.mem := by
    rw [hmem12, hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hsteps : Steps c ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    (((((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8)).trans (Steps.single hs9)).trans
      (Steps.single hs10)).trans (Steps.single hs11)).trans (Steps.single hs12)
  refine ⟨⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    ⟨fun R => σ12.regs.get? R, ?_⟩, hg12⟩
  -- PreW at p = n/8
  refine ⟨hG12, by rw [hmem12eq]; exact hloaded, hpc12, ha0_12, ha1_12, ha2_12, ha3_12, ha4_12,
    ha5_12, ha7_12, hra_12, ⟨_, hmi12'⟩, hi12, hreg, hda, ?_, hppos, h8p, ?_, fun R _ => rfl⟩
  · exact src_align_of_xor src.toNat dst.toNat halign_xor hda
  · rw [hmem12eq]; exact hminv

/-! ## The word loop preserves the ABI frame (FREE — `bytepath_abi`-style)

`word_loop_spec g'` : `PreW g' → StWDone g'` ties the SAME `g'` at both ends over
`NotWrittenW ⊇ AbiPreserved`, so the entry ABI conjunct (`get? R = gm R`)
transports to the exit via `g'` with no re-run. -/
theorem wordloop_abi (gm g' : (R : Register) → Option (RegisterType R))
    (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple
      (fun c => PreW g' p r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => StWDone g' p r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hPre, hgh⟩
  -- entry ABI values pinned to g' via PreW.hframe (AbiPreserved ⊆ NotWrittenW)
  have hentry : ∀ R, AbiPreserved R = true → g' R = gm R := fun R hR => by
    rw [← hPre.hframe R (abiPreserved_notWrittenW hR)]; exact hgh R hR
  obtain ⟨c', hsteps, hpost⟩ := word_loop_spec g' p r dst src n m0 bs c hPre
  refine ⟨c', hsteps, hpost, fun R hR => ?_⟩
  -- exit: get? R = g' R (StWDone's NotWrittenW frame) = gm R (hentry)
  rw [hpost.hframe R (abiPreserved_notWrittenW hR)]; exact hentry R hR

/-! ## Framed no-tail epilogue `StWDone g' → ∃ g'', memcpy_bytepath_post g''`

Re-run of `epilogue_notail_spec`'s 9 register-only sites (7 ALU + `bltu` not-taken
+ `ret`) carrying the ABI frame.  Each preserves every `AbiPreserved` register
(the epilogue writes `{x11,x12,x14}`, none `AbiPreserved`; the `ret` writes only
PC), lifted by `strlenFrame_alu`/`_bnottaken`/`_jr`.  Lands
`memcpy_bytepath_post g''` (fresh `g''`) with the ABI conjunct. -/
theorem epilogue_notail_framed (gm g' : (R : Register) → Option (RegisterType R))
    (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hpos : 1 ≤ p) (hnotail : 8 * p = n) (halign : r.toNat % 4 = 0) :
    Triple
      (fun c => StWDone g' p r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g'', memcpy_bytepath_post g'' r dst n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hSt, hgh0⟩
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hple, hminv, _⟩ := hSt
  have hnw := hreg.dst_nowrap
  -- === c1c: addi a2,a2,-1 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c1c c.σ c.tick c.steps (0x80006c1c#64) vmi (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha2 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c20#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c1c#64) 4 = (0x80006c20#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha4_1 := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have ha7_1 := obs_alu_other' hobs1 Register.x17 (by decide) ha7
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha2_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  have hg1 : ∀ R, AbiPreserved R = true → σ1.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs1 R (by decide) hR]; exact hgh0 R hR
  -- === c20: sub a2,a2,a4 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c20 σ1 i1 (c.steps + 1) (0x80006c20#64) vmi1
      ((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) dst
      hG1 hpc1 hmi1' ha2_1 ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c24#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006c20#64) 4 = (0x80006c24#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have ha7_2 := obs_alu_other' hobs2 Register.x17 (by decide) ha7_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hg2 : ∀ R, AbiPreserved R = true → σ2.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs2 R (by decide) hR]; exact hg1 R hR
  -- === c24: andi a2,a2,-8 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006c24 σ2 i2 (c.steps + 1 + 1) (0x80006c24#64) vmi2
      (((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) - dst)
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c28#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006c24#64) 4 = (0x80006c28#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha7_3 := obs_alu_other' hobs3 Register.x17 (by decide) ha7_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hg3 : ∀ R, AbiPreserved R = true → σ3.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs3 R (by decide) hR]; exact hg2 R hR
  -- === c28: addi a1,a1,8 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006c28 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006c28#64) vmi3 src
      hG3 hpc3 hmi3' ha1_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006c2c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006c28#64) 4 = (0x80006c2c#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have ha7_4 := obs_alu_other' hobs4 Register.x17 (by decide) ha7_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha2_4 : σ4.regs.get? Register.x12 = some (BitVec.ofNat 64 (8 * (p - 1))) := by
    have := obs_alu_other' hobs4 Register.x12 (by decide)
      (by have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
          rwa [epilogue_a2 dst p (by omega) (by omega)] at this)
    exact this
  have ha1_4 : σ4.regs.get? Register.x11 = some (src + sign_extend (m := 64) (0x008#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  have hg4 : ∀ R, AbiPreserved R = true → σ4.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs4 R (by decide) hR]; exact hg3 R hR
  -- === c2c: addi a4,a4,8 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006c2c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006c2c#64) vmi4 dst
      hG4 hpc4 hmi4' ha4_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006c30#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006c2c#64) 4 = (0x80006c30#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha7_5 := obs_alu_other' hobs5 Register.x17 (by decide) ha7_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 := obs_alu_other' hobs5 Register.x12 (by decide) ha2_4
  have ha4_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  have hg5 : ∀ R, AbiPreserved R = true → σ5.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs5 R (by decide) hR]; exact hg4 R hR
  -- === c30: add a1,a1,a2 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006c30 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006c30#64) vmi5
      (src + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG5 hpc5 hmi5' ha1_5 ha2_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006c34#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006c30#64) 4 = (0x80006c34#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha7_6 := obs_alu_other' hobs6 Register.x17 (by decide) ha7_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha2_6 := obs_alu_other' hobs6 Register.x12 (by decide) ha2_5
  have ha4_6 := obs_alu_other' hobs6 Register.x14 (by decide) ha4_5
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hg6 : ∀ R, AbiPreserved R = true → σ6.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs6 R (by decide) hR]; exact hg5 R hR
  -- === c34: add a4,a4,a2 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006c34 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c34#64) vmi6
      (dst + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG6 hpc6 hmi6' ha4_6 ha2_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006c38#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006c34#64) 4 = (0x80006c38#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha7_7 := obs_alu_other' hobs7 Register.x17 (by decide) ha7_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha4_7 : σ7.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_ptr dst p (by omega)] at this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  have hmem7eq : σ7.mem = c.σ.mem := by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hg7 : ∀ R, AbiPreserved R = true → σ7.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs7 R (by decide) hR]; exact hg6 R hR
  -- === c38: bltu a4,a7 not-taken (8p = n) → c3c ===
  have hv : zopz0zI_u (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n) = false :=
    bltu_notail_false dst n p hnotail
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006c38_nottaken σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c38#64) vmi7
      (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n)
      hG7 hpc7 hmi7' ha4_7 ha7_7 (by rw [hmem7eq]; exact hloaded) rfl hv hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006c3c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs8
    rwa [show BitVec.addInt (0x80006c38#64) 4 = (0x80006c3c#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_bnottaken_other' hobs8 Register.x10 (by decide) ha0_7
  have hra_8 := obs_bnottaken_other' hobs8 Register.x1 (by decide) hra_7
  obtain ⟨vmi8, hmi8'⟩ := obs_bnottaken_minstret hobs8
  have hmem8eq : σ8.mem = c.σ.mem := by rw [hmem8, hmem7eq]
  have hg8 : ∀ R, AbiPreserved R = true → σ8.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_bnottaken hobs8 R hR]; exact hg7 R hR
  -- === c3c: ret → r ===
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006c3c σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c3c#64) vmi8 r
      hG8 hpc8 hmi8' hra_8 (by rw [hmem8eq]; exact hloaded) rfl htgt hi8
  have hpc9 : σ9.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs9, ret_tgt r halign]
  have ha0_9 := obs_jr_other' hobs9 Register.x10 (by decide) ha0_8
  have hra_9 := obs_jr_other' hobs9 Register.x1 (by decide) hra_8
  have hmem9eq : σ9.mem = c.σ.mem := by rw [hmem9, hmem8eq]
  have hg9 : ∀ R, AbiPreserved R = true → σ9.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_jr hobs9 R hR]; exact hg8 R hR
  have hminv_n : MemInv dst src n bs n m0 c.σ.mem := hnotail ▸ hminv
  have hsteps : Steps c ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    ((((((((Steps.single hs1).trans (Steps.single hs2)).trans
      (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
      (Steps.single hs6)).trans (Steps.single hs7)).trans (Steps.single hs8)).trans (Steps.single hs9)
  refine ⟨⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    ⟨fun R => σ9.regs.get? R, ?_⟩, hg9⟩
  refine ⟨hG9, hpc9, ha0_9, hra_9, ?_, ?_, hi9, fun R _ => rfl⟩
  · intro k hk; rw [hmem9eq]; exact hminv_n.copied k hk
  · intro a ha; rw [hmem9eq]; exact hminv_n.outside a ha

/-! ## Framed byte-tail epilogue `StWDone g' → ∃ g'', memcpy_bytepath_post g''`

For the word route with a non-empty byte tail (`8*(n/8) < n`), the epilogue
recomputes the pointers, the `c38 bltu` is TAKEN, and control enters the byte
loop at `c48` copying the remaining `n - 8p` bytes.  We re-run the 8 register-only
sites of `epilogue_to_bytehead` carrying the ABI frame (`epilogue_to_bytehead_framed`)
landing `StB g''` with the ABI conjunct, then transport through the byte loop +
ret via the SAME `g''` (its `StB`/`memcpy_bytepath_post` frames are over
`NotWrittenB ⊇ AbiPreserved`), the `bytepath_abi` pattern. -/

/-- Re-run of `epilogue_to_bytehead`'s 8 sites carrying the ABI frame. -/
theorem epilogue_to_bytehead_framed (gm g' : (R : Register) → Option (RegisterType R))
    (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hpos : 1 ≤ p) (htail : 8 * p < n) :
    Triple
      (fun c => StWDone g' p r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g'', StB g'' (0x80006c48#64) (8 * p) r dst src n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hSt, hgh0⟩
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hple, hminv, _⟩ := hSt
  have hnw := hreg.dst_nowrap
  -- === c1c: addi a2,a2,-1 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c1c c.σ c.tick c.steps (0x80006c1c#64) vmi (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha2 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c20#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c1c#64) 4 = (0x80006c20#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha4_1 := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have ha7_1 := obs_alu_other' hobs1 Register.x17 (by decide) ha7
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha2_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  have hg1 : ∀ R, AbiPreserved R = true → σ1.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs1 R (by decide) hR]; exact hgh0 R hR
  -- === c20: sub a2,a2,a4 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c20 σ1 i1 (c.steps + 1) (0x80006c20#64) vmi1
      ((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) dst
      hG1 hpc1 hmi1' ha2_1 ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c24#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006c20#64) 4 = (0x80006c24#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have ha7_2 := obs_alu_other' hobs2 Register.x17 (by decide) ha7_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hg2 : ∀ R, AbiPreserved R = true → σ2.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs2 R (by decide) hR]; exact hg1 R hR
  -- === c24: andi a2,a2,-8 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006c24 σ2 i2 (c.steps + 1 + 1) (0x80006c24#64) vmi2
      (((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) - dst)
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c28#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006c24#64) 4 = (0x80006c28#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha7_3 := obs_alu_other' hobs3 Register.x17 (by decide) ha7_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha2_3 : σ3.regs.get? Register.x12 = some (BitVec.ofNat 64 (8 * (p - 1))) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_a2 dst p (by omega) (by omega)] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hg3 : ∀ R, AbiPreserved R = true → σ3.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs3 R (by decide) hR]; exact hg2 R hR
  -- === c28: addi a1,a1,8 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006c28 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006c28#64) vmi3 src
      hG3 hpc3 hmi3' ha1_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006c2c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006c28#64) 4 = (0x80006c2c#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have ha7_4 := obs_alu_other' hobs4 Register.x17 (by decide) ha7_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
  have ha1_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  have hg4 : ∀ R, AbiPreserved R = true → σ4.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs4 R (by decide) hR]; exact hg3 R hR
  -- === c2c: addi a4,a4,8 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006c2c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006c2c#64) vmi4 dst
      hG4 hpc4 hmi4' ha4_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006c30#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006c2c#64) 4 = (0x80006c30#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha7_5 := obs_alu_other' hobs5 Register.x17 (by decide) ha7_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha2_5 := obs_alu_other' hobs5 Register.x12 (by decide) ha2_4
  have ha4_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  have hg5 : ∀ R, AbiPreserved R = true → σ5.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs5 R (by decide) hR]; exact hg4 R hR
  -- === c30: add a1,a1,a2 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006c30 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006c30#64) vmi5
      (src + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG5 hpc5 hmi5' ha1_5 ha2_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006c34#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006c30#64) 4 = (0x80006c34#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha7_6 := obs_alu_other' hobs6 Register.x17 (by decide) ha7_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha2_6 := obs_alu_other' hobs6 Register.x12 (by decide) ha2_5
  have ha4_6 := obs_alu_other' hobs6 Register.x14 (by decide) ha4_5
  have ha1_6 : σ6.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_ptr src p (by omega)] at this
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hg6 : ∀ R, AbiPreserved R = true → σ6.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs6 R (by decide) hR]; exact hg5 R hR
  -- === c34: add a4,a4,a2 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006c34 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c34#64) vmi6
      (dst + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG6 hpc6 hmi6' ha4_6 ha2_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006c38#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006c34#64) 4 = (0x80006c38#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 := obs_alu_other' hobs7 Register.x11 (by decide) ha1_6
  have ha7_7 := obs_alu_other' hobs7 Register.x17 (by decide) ha7_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha4_7 : σ7.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_ptr dst p (by omega)] at this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  have hmem7eq : σ7.mem = c.σ.mem := by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hg7 : ∀ R, AbiPreserved R = true → σ7.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs7 R (by decide) hR]; exact hg6 R hR
  -- === c38: bltu a4,a7 taken (8p < n) → c48 ===
  have hv : zopz0zI_u (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n) = true :=
    bltu_tail_true dst n p hnw htail
  have htgt : ((0x80006c38#64 : BitVec 64) + sign_extend (m := 64) (0x0010#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006c38_taken σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c38#64) vmi7
      (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n)
      hG7 hpc7 hmi7' ha4_7 ha7_7 (by rw [hmem7eq]; exact hloaded) rfl htgt hv hi7
  have hpceq : (0x80006c38#64 : BitVec 64) + sign_extend (m := 64) (0x0010#13) = (0x80006c48#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006c48#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs8, hpceq]
  have hg8 : ∀ R, AbiPreserved R = true → σ8.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_btaken hobs8 R hR]; exact hg7 R hR
  have hsteps : Steps c ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    (((((((Steps.single hs1).trans (Steps.single hs2)).trans
      (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
      (Steps.single hs6)).trans (Steps.single hs7)).trans (Steps.single hs8)
  refine ⟨⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    ⟨fun R => σ8.regs.get? R, ?_⟩, hg8⟩
  refine ⟨hG8, by rw [hmem8, hmem7eq]; exact hloaded, hpc8,
    obs_btaken_other' hobs8 Register.x10 (by decide) ha0_7,
    obs_btaken_other' hobs8 Register.x11 (by decide) ha1_7,
    obs_btaken_other' hobs8 Register.x14 (by decide) ha4_7,
    obs_btaken_other' hobs8 Register.x17 (by decide) ha7_7,
    obs_btaken_other' hobs8 Register.x1 (by decide) hra_7,
    obs_btaken_minstret hobs8, hi8, hreg, by omega, ?_, fun R _ => rfl⟩
  rw [hmem8, hmem7eq]; exact hminv

/-- Framed byte-tail epilogue: re-run to the byte head, then transport through the
byte loop + ret via `g''` (`StB`/`memcpy_bytepath_post` frames over
`NotWrittenB ⊇ AbiPreserved`), the `bytepath_abi` pattern. -/
theorem epilogue_tail_framed (gm g' : (R : Register) → Option (RegisterType R))
    (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hpos : 1 ≤ p) (htail : 8 * p < n) (halign : r.toNat % 4 = 0) :
    Triple
      (fun c => StWDone g' p r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g'', memcpy_bytepath_post g'' r dst n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  refine (epilogue_to_bytehead_framed gm g' p r dst src n m0 bs hpos htail).seq ?_
  intro c ⟨⟨g'', hStB⟩, hgh⟩
  -- ABI values pinned to g'' via StB.hframe (AbiPreserved ⊆ NotWrittenB)
  have hentry : ∀ R, AbiPreserved R = true → g'' R = gm R := fun R hR => by
    rw [← hStB.hframe R (abiPreserved_notWrittenB hR)]; exact hgh R hR
  -- StB → memcpy_bytepath_post via the byte loop + ret (same g'')
  have hhead : Triple (StB g'' (0x80006c48#64) (8 * p) r dst src n m0 bs)
      (StBDone g'' r dst src n m0 bs) :=
    fun cc hcc => loop_to_doneB g'' r dst src n m0 bs cc (Or.inl ⟨8 * p, htail, hcc⟩)
  have hbyte : Triple (StB g'' (0x80006c48#64) (8 * p) r dst src n m0 bs)
      (memcpy_bytepath_post g'' r dst n m0 bs) :=
    hhead.seq (tr_retB g'' r dst src n m0 bs halign)
  obtain ⟨c', hs', hpost⟩ := hbyte c hStB
  refine ⟨c', hs', ⟨g'', hpost⟩, fun R hR => ?_⟩
  rw [hpost.2.2.2.2.2.2.2 R (abiPreserved_notWrittenB hR)]; exact hentry R hR

/-! ## `memcpy_spec_framed_word` — the framed WORD route (both sub-cases)

For the `env_define` `memcpy(copy,name,len+1)` call on the aligned word route
(`dst % 8 = 0`, `8*(n/8) ≤ 64`, `n ≥ 8` — case (C) of `memcpy_spec`), carry the
ABI frame end-to-end: `dispatch_to_word_framed` ≫ `wordloop_abi` ≫ the epilogue.
The epilogue splits on whether the copy is word-exact (`8*(n/8) = n` → no-tail
ret via `epilogue_notail_framed`) or has a byte tail (`8*(n/8) < n` → byte loop
via `epilogue_tail_framed`).  Same post as `memcpy_spec_framed_byte`, so
`memcpy_framed_ainv_stable` and the `EnvDefCompose` consumer apply verbatim.

This is the EXACT framed analogue of `memcpy_spec`'s route (C): same route
hypothesis shape (`halign_xor ∧ hbig ∧ hda ∧ hfit`), the ABI conjunct threaded. -/
theorem memcpy_spec_framed_word (gm : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0)
    (halign_xor : (src.toNat ^^^ dst.toNat) % 8 = 0)
    (hbig : 8 ≤ n) (hda : dst.toNat % 8 = 0)
    (hfit : 8 * (n / 8) ≤ 64) :
    Triple
      (fun c => PreDispatch gm r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g', memcpy_bytepath_post g' r dst n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  refine (to_bd4_framed gm r dst src n m0 bs).seq ?_
  refine (dispatch_to_word_framed gm r dst src n m0 bs halign_xor hbig hda hfit).seq ?_
  intro c ⟨⟨g', hPreW⟩, hgh⟩
  obtain ⟨c1, hs1, hSt, hgh1⟩ :=
    wordloop_abi gm g' (n / 8) r dst src n m0 bs c ⟨hPreW, hgh⟩
  by_cases hdvd : 8 * (n / 8) = n
  · obtain ⟨c2, hs2, hpost, hgh2⟩ :=
      epilogue_notail_framed gm g' (n / 8) r dst src n m0 bs (by omega) hdvd halign c1 ⟨hSt, hgh1⟩
    exact ⟨c2, hs1.trans hs2, hpost, hgh2⟩
  · obtain ⟨c2, hs2, hpost, hgh2⟩ :=
      epilogue_tail_framed gm g' (n / 8) r dst src n m0 bs (by omega) (by omega) halign c1 ⟨hSt, hgh1⟩
    exact ⟨c2, hs1.trans hs2, hpost, hgh2⟩

#print axioms abiPreserved_notWrittenW
#print axioms dispatch_to_word_framed
#print axioms wordloop_abi
#print axioms epilogue_notail_framed
#print axioms epilogue_to_bytehead_framed
#print axioms epilogue_tail_framed
#print axioms memcpy_spec_framed_word

end Vsa.Sim
