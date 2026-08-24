import Vsa.Sim.StrlenSpec

/-!
# Layer 3 — `strlen` unaligned head-peel + full spec (`strlen_full_spec`)

Completes the `strlen` total-correctness spec for the **unaligned** entry path
(`bnez a5` taken at `0xcf8` → `0xd78`), and assembles the top-level
`strlen_full_spec` that dispatches on `p.toNat % 8 = 0`.

This file is purely additive over the verified `Vsa/Sim/StrlenSpec.lean` (whose
aligned `strlen_spec` and the three head transitions `head_body`/`head_nul_exit`/
`head_continue` are reused unchanged).

## Control flow (unaligned path), from the disassembly

* entry `0xcf0..0xcf8`: `andi a5,a0,7; mv a4,a0; bnez a5,d78` — TAKEN (unaligned),
  jumping directly to `0xd78` with `a0 = a4 = base`.
* head peel `0xd78..0xd84`: `lbu a5,0(a4); addi a4,a4,1; andi a3,a4,7; bnez a5,d74`.
* `0xd74 beqz a3`: alignment test on the ADVANCED pointer `base+(m+1)`.  Taken
  (aligned) rejoins the aligned scan at `0xcfc` (`a0 = base`, `a4 = base+off0`
  8-aligned, `off0 = m+1`); not taken loops back to `0xd78`.
* NUL-in-head exit `0xd88..0xd90`: `sub a4,a4,a0; addi a0,a4,-1; ret`, returning
  `a0 = m = len`.

## Two segments

1. **Head loop** (`Triple.loop`): from the unaligned entry, peel bytes until either
   the NUL is found (→ `Done`) or 8-alignment is reached (→ the rejoin config at
   `0xcfc`).
2. **Offset-generalized word scan**: from the rejoin config, scan 8-aligned words
   starting at `q = base + off0` with `a0 = base` (`≠ q` in general).  This clones
   the aligned word-loop/tail machinery with a `base`/`off0` split.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Unaligned entry (`0xcf0 → 0xd78`)

`UPre`: entry precondition for the unaligned path (`p.toNat % 8 ≠ 0`).  Runs
`andi a5,a0,7` (`a5 = p & 7 ≠ 0`), `mv a4,a0` (`a4 = p`), `bnez a5` TAKEN → `0xd78`,
establishing the head-loop head `HSt p r len cs m0 0`. -/

/-- Entry precondition at `0x80006cf0` (unaligned path: `p.toNat % 8 ≠ 0`). -/
structure UPre (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some p
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions p len
  align : p.toNat % 8 ≠ 0
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len

/-- For an unaligned `p`, `p &&& sext(0x007) ≠ 0` (some low bit set). -/
theorem andi7_unaligned (p : BitVec 64) (halign : p.toNat % 8 ≠ 0) :
    (p &&& sign_extend (m := 64) (0x007#12)) ≠ 0#64 := by
  intro h
  apply halign
  have : (p &&& sign_extend (m := 64) (0x007#12)).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^3 = 8 from rfl] at this
  exact this

/-- `bnez a5` (`a5 ≠ 0`) is taken. -/
theorem bnez_nonzero_true (v : BitVec 64) (h : v ≠ 0#64) : ((v) != (0#64)) = true := by
  rw [bne_iff_ne]; exact h

/-- **Unaligned entry** (`0xcf0 → 0xd78`): establishes the head-loop head `HSt 0`.
`andi a5,a0,7` yields `p & 7 ≠ 0` (unaligned), `mv a4,a0` sets `a4 = p`, `bnez a5`
TAKEN jumps to `0xd78`. -/
theorem entry_unaligned (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (UPre p r len cs m0) (HSt p r len cs m0 0) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hreg, halign, hcstr, hlen⟩ := hPre
  -- cf0: andi a5,a0,7  → a5 = p & 7 ≠ 0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006cf0 c.σ c.tick c.steps (0x80006cf0#64) vmi p hgood hpc hmi ha0 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006cf4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006cf0#64) 4 = (0x80006cf4#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some (p &&& sign_extend (m := 64) (0x007#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- cf4: mv a4,a0  → a4 = p
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006cf4 σ1 i1 (c.steps + 1) (0x80006cf4#64) vmi1 p hG1 hpc1 hmi1' ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006cf8#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006cf4#64) 4 = (0x80006cf8#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  have ha4_2 : σ2.regs.get? Register.x14 = some p := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- cf8: bnez a5 (a5 ≠ 0) TAKEN → d78
  have hv : ((p &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true :=
    bnez_nonzero_true _ (andi7_unaligned p halign)
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006cf8_taken σ2 i2 (c.steps + 1 + 1) (0x80006cf8#64) vmi2 (p &&& sign_extend (m := 64) (0x007#12))
      hG2 hpc2 hmi2' ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hv hi2
  have hpceq : (0x80006cf8#64 : BitVec 64) + sign_extend (m := 64) (0x0080#13) = (0x80006d78#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d78#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs3, hpceq]
  have ha0_3 := obs_btaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_btaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha4_3 := obs_btaken_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_2
  obtain ⟨vmi3, hmi3'⟩ := obs_btaken_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3),
    hG3, by rw [hmem3eq]; exact hloaded, by rw [hmem3eq]; exact hmem, hpc3, ha0_3, ?_, hra_3,
    ⟨vmi3, hmi3'⟩, hi3, hreg, hcstr, hlen, by omega⟩
  · rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]; exact ha4_3

/-! ## Alignment-exit rejoin config (`0xcfc`)

`HAlign base r len cs m0 off0`: the config at `0xcfc` after peeling `off0 = m+1`
bytes and finding the pointer `base+off0` 8-aligned (`(base+off0) % 8 = 0`), with no
NUL in `[base, base+off0)` (so `off0 ≤ len`).  Here `a0 = base` (the length origin),
`a4 = base+off0` (the aligned scan base `q`), and `x1 = r`.  From here the magic setup
and word loop scan the rest — but with `a0 = base ≠ a4` in general. -/
structure HAlign (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006cfc#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some base
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 off0)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  off0le : off0 ≤ len
  qalign : (base.toNat + off0) % 8 = 0
  offpos : 0 < off0

/-- Head alignment-exit (`0xd84` bnez taken → `0xd74` beqz taken, `m < len`, pointer
`base+(m+1)` 8-aligned): rejoins the aligned scan at `0xcfc` as `HAlign (m+1)`. -/
theorem head_align_exit (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (hlt : m < len)
    (hal : (base.toNat + (m+1)) % 8 = 0) :
    Triple (HDec base r len cs m0 m) (HAlign base r len cs m0 (m+1)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hcstr, hlen, hmle⟩ := hSt
  have hnw : base.toNat + (m+1) < 2^64 := by have := hreg.nowrap; omega
  -- d84: bnez a5 taken → d74
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) != (0#64)) = true := by
    rw [hdec_guard base len m cs m0 hcstr hlen hmle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d84_taken c.σ c.tick c.steps (0x80006d84#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpceq1 : (0x80006d84#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13) = (0x80006d74#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d74#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs1, hpceq1]
  have ha0_1 := obs_btaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_btaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_btaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_btaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
  -- d74: beqz a3 TAKEN (aligned) → cfc
  have hv2 : (((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true := by
    rw [head_align_guard base m hnw]; simp [hal]
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d74_taken σ1 i1 (c.steps + 1) (0x80006d74#64) vmi1
      ((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12))
      hG1 hpc1 hmi1' ha3_1 (by rw [hmem1]; exact hloaded) rfl hv2 hi1
  have hpceq2 : (0x80006d74#64 : BitVec 64) + sign_extend (m := 64) (0x1f88#13) = (0x80006cfc#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006cfc#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs2, hpceq2]
  have ha0_2 := obs_btaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha4_2 := obs_btaken_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_btaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2'⟩ := obs_btaken_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha4_2, hra_2,
    ⟨vmi2, hmi2'⟩, hi2, hreg, hcstr, hlen, by omega, by omega, by omega⟩

/-! ## Head NUL-exit to the pre-`ret` state

`head_nul_exit` bundles the `ret`; for the loop we need to stop at a PC distinct from
the head (`0xd78`) and from `r`, so we peel only up to the pre-`ret` `AtRet` state at
`0xd90` (`sub a4,a4,a0; addi a0,a4,-1`).  The `ret` is run once after the loop. -/

/-- Head NUL-exit up to `0xd90` (`0xd84` bnez not-taken, `m = len`): `0xd88 sub a4,a4,a0`;
`0xd8c addi a0,a4,-1` (`a0 = m = len`), landing at `AtRet r len m0 0xd90`. -/
theorem head_nul_to_ret (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (hm : m = len) :
    Triple (HDec base r len cs m0 m) (AtRet r len m0 (0x80006d90#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hcstr, hlen, hmle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) != (0#64)) = false := by
    rw [hdec_guard base len m cs m0 hcstr hlen hmle]; simp [hm]
  -- d84: bnez a5 not taken → d88
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d84_nottaken c.σ c.tick c.steps (0x80006d84#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d88#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d84#64) 4 = (0x80006d88#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- d88: sub a4,a4,a0  → a4 = ofNat(m+1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d88 σ1 i1 (c.steps + 1) (0x80006d88#64) vmi1 (base + BitVec.ofNat 64 (m+1)) base
      hG1 hpc1 hmi1' ha4_1 ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d8c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d88#64) 4 = (0x80006d8c#64 : BitVec 64) from by decide] at this
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (BitVec.ofNat 64 (m+1)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sub_a4_a0_val] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- d8c: addi a0,a4,-1  → a0 = ofNat len
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d8c σ2 i2 (c.steps + 1 + 1) (0x80006d8c#64) vmi2 (BitVec.ofNat 64 (m+1))
      hG2 hpc2 hmi2' ha4_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d90#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d8c#64) 4 = (0x80006d90#64 : BitVec 64) from by decide] at this
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha0_3 : σ3.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (BitVec.ofNat 64 (m+1)) + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 len from by
      rw [show (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -(BitVec.ofNat 64 1) from by
            apply BitVec.eq_of_toNat_eq; decide, BitVec.add_neg_eq_sub, ofNat_sub (m+1) 1 (by omega),
          show (m+1) - 1 = len from by omega]] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  exact ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3),
    hG3, by rw [hmem3eq]; exact hloaded, by rw [hmem3eq]; exact hmem, hpc3, ha0_3, hra_3,
    ⟨vmi3, hmi3'⟩, hi3⟩

/-! ## Head-loop assembly (`Triple.loop`)

Invariant `HLoopI`: at the head `0xd78` (some peel-count `m`, `m ≤ len`), or at the
pre-`ret` NUL-exit state `0xd90` (`AtRet`), or rejoined the aligned scan at `0xcfc`
(`HAlign off0`).  All three PCs are distinct literals, so the measure — `len + 1 - m`
at the head, else `0` — is provably `0` on the two exit disjuncts.  Guard `HLoopB`: at
the head.  The body runs one `head_body`, then dispatches: NUL (`m = len`) → `AtRet`;
aligned → `HAlign`; else → `HSt (m+1)` (measure drops). -/

/-- Head disjunct: at `0xd78`, peel-count `m ≤ len`. -/
def HAtHead (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ m, HSt base r len cs m0 m c

/-- Aligned-rejoin disjunct: at `0xcfc`, off `off0`. -/
def HAtAlign (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ off0, HAlign base r len cs m0 off0 c

def HLoopI (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  HAtHead base r len cs m0 c ∨ AtRet r len m0 (0x80006d90#64) c ∨ HAtAlign base r len cs m0 c

def HLoopB (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  HAtHead base r len cs m0 c

/-- Measure: `len + 1 - m` at the head `0xd78` (`a4 = base+m`, so `m = a4-base`),
else `0`. -/
def HLoopMu (base : BitVec 64) (len : Nat) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006d78#64)
  then len + 1 - (((c.σ.regs.get? Register.x14).getD (0#64)).toNat - base.toNat)
  else 0

/-- At the head, `HLoopMu = len + 1 - m`. -/
theorem hloopmu_head (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (c : Config) (hSt : HSt base r len cs m0 m c) :
    HLoopMu base len c = len + 1 - m := by
  simp only [HLoopMu, hSt.pc, hSt.a4, Option.getD_some, if_pos]
  have h4 : (base + BitVec.ofNat 64 m).toNat = base.toNat + m :=
    ptrN base m (by have := hSt.regions.nowrap; have := hSt.mle; omega)
  rw [h4]; omega

/-- `AtRet 0xd90` and `HAlign` are not at the head PC `0xd78`, so their measure is `0`. -/
theorem hloopmu_atret (base r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) (hRet : AtRet r len m0 (0x80006d90#64) c) : HLoopMu base len c = 0 := by
  have hpc : c.σ.regs.get? Register.PC = some (0x80006d90#64) := hRet.2.2.2.1
  have hne : ¬ (c.σ.regs.get? Register.PC = some (0x80006d78#64)) := by
    rw [hpc]; intro h; injection h with h; exact absurd h (by decide)
  simp only [HLoopMu, if_neg hne]

theorem hloopmu_align (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config)
    (hAl : HAlign base r len cs m0 off0 c) : HLoopMu base len c = 0 := by
  have hne : ¬ (c.σ.regs.get? Register.PC = some (0x80006d78#64)) := by
    rw [hAl.pc]; intro h; injection h with h; exact absurd h (by decide)
  simp only [HLoopMu, if_neg hne]

/-- **Head-loop body**: one peel re-establishes `HLoopI`, strictly decreasing `HLoopMu`.
NUL (`m = len`): `AtRet`, measure `0`.  Aligned: `HAlign`, measure `0`.  Else: `HSt (m+1)`,
measure `len+1-(m+1) < len+1-m`. -/
theorem hloop_body (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) :
    Triple (fun c => HLoopI base r len cs m0 c ∧ HLoopB base r len cs m0 c ∧ HLoopMu base len c = k)
           (fun c => HLoopI base r len cs m0 c ∧ HLoopMu base len c < k) := by
  intro c hc
  obtain ⟨_, ⟨m, hSt⟩, hmu⟩ := hc
  have hmu_eq : HLoopMu base len c = len + 1 - m := hloopmu_head base r len cs m0 m c hSt
  rw [hmu_eq] at hmu
  have hmle := hSt.mle
  -- head body to 0xd84
  obtain ⟨c1, hs1, hDec⟩ := head_body base r len cs m0 m c hSt
  by_cases hnul : m = len
  · -- NUL found: AtRet
    obtain ⟨c2, hs2, hRet⟩ := head_nul_to_ret base r len cs m0 m hnul c1 hDec
    refine ⟨c2, hs1.trans hs2, Or.inr (Or.inl hRet), ?_⟩
    rw [hloopmu_atret base r len m0 c2 hRet, ← hmu]; omega
  · have hlt : m < len := by omega
    by_cases hal : (base.toNat + (m+1)) % 8 = 0
    · -- aligned: HAlign
      obtain ⟨c2, hs2, hAl⟩ := head_align_exit base r len cs m0 m hlt hal c1 hDec
      refine ⟨c2, hs1.trans hs2, Or.inr (Or.inr ⟨m+1, hAl⟩), ?_⟩
      rw [hloopmu_align base r len cs m0 (m+1) c2 hAl, ← hmu]; omega
    · -- continue peeling: HSt (m+1)
      obtain ⟨c2, hs2, hSt2⟩ := head_continue base r len cs m0 m hlt hal c1 hDec
      refine ⟨c2, hs1.trans hs2, Or.inl ⟨m+1, hSt2⟩, ?_⟩
      rw [hloopmu_head base r len cs m0 (m+1) c2 hSt2, ← hmu]; omega

/-- The head loop runs from `HLoopI` to `AtRet 0xd90 ∨ HAtAlign` (byte peel complete). -/
theorem hloop_to_exit (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (HLoopI base r len cs m0)
           (fun c => AtRet r len m0 (0x80006d90#64) c ∨ HAtAlign base r len cs m0 c) := by
  have hloop := Triple.loop (I := HLoopI base r len cs m0) (B := HLoopB base r len cs m0)
    (HLoopMu base len) (hloop_body base r len cs m0)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hRet | hAlign
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, Or.inl hRet⟩
  · exact ⟨c, .refl c, Or.inr hAlign⟩

/-! ## Offset-generalized word scan (`0xcfc → Done`)

From `HAlign base r len cs m0 off0` (at `0xcfc`, `a0 = base`, `a4 = base+off0`,
`(base+off0) % 8 = 0`, `off0 ≤ len`), the magic setup runs then the word loop scans
8-aligned words starting at `q = base+off0`.  This clones the aligned word-loop/tail
machinery decoupling `a0 = base` (length origin) from the scan base `q`.  The string
facts are about `base`; scan positions are `off0 + 8j`.  Setting `off0 = 0`, `base = q`
recovers the aligned spec — so the arithmetic is identical modulo the `off0` shift.

We phrase the scan positions via a single index `t = off0 + 8j` (bytes scanned from
`base`).  The load, detection, and exit arithmetic all read `t`. -/

/-- Generalized taken detection: word at `base + t` (`t + 8 ≤ len`) has no zero byte. -/
theorem detect_takenG (σ : SequentialState RegisterType trivialChoiceSource) (base : BitVec 64)
    (len t : Nat) (cs : List Char) (hcs : CStr σ.mem base.toNat cs) (hlen : cs.length = len)
    (hpos : (base + BitVec.ofNat 64 t).toNat = base.toNat + t) (hle : t + 8 ≤ len) :
    strlenWordVal (ldBytesT σ (base + BitVec.ofNat 64 t)) = BitVec.allOnes 64 := by
  rw [detect_all_ones]
  intro k hk
  rw [ldBytesT_byte σ _ k hk, hpos]
  obtain ⟨b, hb, hbne⟩ := cstr_byte_ne σ.mem hcs (t + k) (by omega)
  rw [show base.toNat + t + k = base.toNat + (t + k) from by omega, hb]
  simpa using hbne

/-- Generalized not-taken detection: word at `base + t` (`t ≤ len < t+8`) has the NUL. -/
theorem detect_nottakenG (σ : SequentialState RegisterType trivialChoiceSource) (base : BitVec 64)
    (len t : Nat) (cs : List Char) (hcs : CStr σ.mem base.toNat cs) (hlen : cs.length = len)
    (hlo : t ≤ len) (hhi : len < t + 8)
    (hpos : (base + BitVec.ofNat 64 t).toNat = base.toNat + t) :
    strlenWordVal (ldBytesT σ (base + BitVec.ofNat 64 t)) ≠ BitVec.allOnes 64 := by
  intro hall
  rw [detect_all_ones] at hall
  have hk : len - t < 8 := by omega
  have := hall (len - t) hk
  rw [ldBytesT_byte σ _ _ hk, hpos] at this
  apply this
  have hnul : σ.mem[base.toNat + cs.length]? = some 0 := cstr_byte_nul σ.mem hcs
  rw [hlen] at hnul
  rw [show base.toNat + t + (len - t) = base.toNat + len from by omega, hnul]
  rfl

/-! ### Generalized word-loop states

`WStG base r len cs m0 off0 j`: word-loop head `0xd10`, scan position `base + (off0+8j)`,
`a0 = base`, `a4 = base + ofNat(off0+8j)`.  `t = off0+8j` is the byte index from `base`.
`W28G`, `WTailG` mirror the aligned `W28`/`WTail` with the `base`/`off0` split. -/

structure WStG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d10#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some base
  a1 : c.σ.regs.get? Register.x11 = some (BitVec.allOnes 64)
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (off0 + 8*j))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  qalign : (base.toNat + off0) % 8 = 0
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  jle : off0 + 8*j ≤ len

structure WTailG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d2c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some base
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (off0 + 8*(j+1)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  qalign : (base.toNat + off0) % 8 = 0
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  jlo : off0 + 8*j ≤ len
  jhi : len < off0 + 8*(j+1)

structure W28G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d28#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some base
  a1 : c.σ.regs.get? Register.x11 = some (BitVec.allOnes 64)
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a5 : c.σ.regs.get? Register.x15 = some (strlenWordVal (strlenWordAt m0 (base.toNat + (off0 + 8*j))))
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (off0 + 8*(j+1)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  qalign : (base.toNat + off0) % 8 = 0
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  jle : off0 + 8*j ≤ len

/-- Bounds for the generalized load at `a4 = base + (off0+8j)` (`t = off0+8j`, aligned). -/
theorem wload_boundsG (base : BitVec 64) (len off0 j : Nat) (hreg : StrRegions base len)
    (hqal : (base.toNat + off0) % 8 = 0) (hj : off0 + 8*j ≤ len) :
    (base + BitVec.ofNat 64 (off0 + 8*j)).toNat = base.toNat + (off0 + 8*j) ∧
    0x80000000 ≤ ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    (((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat) ∧
    ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have htn : (base + BitVec.ofNat 64 (off0+8*j)).toNat = base.toNat + (off0+8*j) :=
    ptrN base (off0+8*j) (by have := hreg.nowrap; omega)
  have hlo := hreg.lo; have hhi := hreg.hi; have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, ?_⟩
  all_goals rw [sext0_add, htn]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega
  · omega

/-- `(base + ofNat(off0+8j)) + sext 8 = base + ofNat(off0+8(j+1))`. -/
theorem a4_incrG (base : BitVec 64) (off0 j : Nat) :
    (base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x008#12)
      = base + BitVec.ofNat 64 (off0+8*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2

/-- Generalized straight-line word body (`0xd10 → 0xd28`). -/
theorem wloop_straightG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) :
    Triple (WStG base r len cs m0 off0 j) (W28G base r len cs m0 off0 j) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha3, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen, hjle⟩ := hSt
  obtain ⟨htn, hlo, hhi, hhtif, halgn⟩ := wload_boundsG base len off0 j hreg hqal hjle
  -- d10: ld a2,0(a4)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d10 c.σ c.tick c.steps (0x80006d10#64) vmi (base + BitVec.ofNat 64 (off0+8*j))
      hgood hpc hmi ha4 hloaded rfl hlo hhi hhtif halgn htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d14#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006d10#64) 4 = (0x80006d14#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha3_1 := obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hword : (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80006d10#64))
          ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12))))
      = strlenWordAt m0 (base.toNat + (off0+8*j)) := by
    rw [sext64_self, sext0_add, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem, htn]
  have ha2_1 : σ1.regs.get? Register.x12 = some (strlenWordAt m0 (base.toNat + (off0+8*j))) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hword] at this
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- d14: addi a4,a4,8
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d14 σ1 i1 (c.steps + 1) (0x80006d14#64) vmi1 (base + BitVec.ofNat 64 (off0+8*j))
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d18#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d14#64) 4 = (0x80006d18#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha2_2 := obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (off0+8*(j+1))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [a4_incrG base off0 j] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- d18: and a5,a2,a3
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d18 σ2 i2 (c.steps + 1 + 1) (0x80006d18#64) vmi2 (strlenWordAt m0 (base.toNat + (off0+8*j))) magic7f
      hG2 hpc2 hmi2' ha2_2 ha3_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d1c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d18#64) 4 = (0x80006d1c#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha2_3 := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_2
  have ha3_3 := obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_2
  have ha4_3 := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha5_3 := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- d1c: add a5,a5,a3
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006d1c σ3 i3 (c.steps + 1 + 1 + 1) (0x80006d1c#64) vmi3 (strlenWordAt m0 (base.toNat + (off0+8*j)) &&& magic7f) magic7f
      hG3 hpc3 hmi3' ha5_3 ha3_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006d20#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006d1c#64) 4 = (0x80006d20#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have ha2_4 := obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_3
  have ha3_4 := obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_3
  have ha4_4 := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have ha5_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- d20: or a5,a5,a2
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006d20 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006d20#64) vmi4
      ((strlenWordAt m0 (base.toNat + (off0+8*j)) &&& magic7f) + magic7f) (strlenWordAt m0 (base.toNat + (off0+8*j)))
      hG4 hpc4 hmi4' ha5_4 ha2_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d24#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006d20#64) 4 = (0x80006d24#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have ha3_5 := obs_alu_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_4
  have ha4_5 := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_4
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have ha5_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- d24: or a5,a5,a3
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006d24 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006d24#64) vmi5
      (((strlenWordAt m0 (base.toNat + (off0+8*j)) &&& magic7f) + magic7f) ||| strlenWordAt m0 (base.toNat + (off0+8*j))) magic7f
      hG5 hpc5 hmi5' ha5_5 ha3_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006d28#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006d24#64) 4 = (0x80006d28#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have ha1_6 := obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_5
  have ha3_6 := obs_alu_other hobs6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_5
  have ha4_6 := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_5
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have ha5_6 : σ6.regs.get? Register.x15 = some (strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j)))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [strlenWordVal_eq] at this
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6),
    hG6, by rw [hmem6eq]; exact hloaded, by rw [hmem6eq]; exact hmem, hpc6, ha0_6, ha1_6, ha3_6,
    ha5_6, ha4_6, hra_6, ⟨vmi6, hmi6'⟩, hi6, hreg, hqal, hcstr, hlen, hjle⟩

/-- Generalized back-edge (`0xd28 → 0xd10`, taken, `off0+8(j+1) ≤ len`). -/
theorem wloop_backG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hle : off0 + 8*(j+1) ≤ len) :
    Triple (W28G base r len cs m0 off0 j) (WStG base r len cs m0 off0 (j+1)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen, hjle⟩ := hSt
  have hpos : (base + BitVec.ofNat 64 (off0+8*j)).toNat = base.toNat + (off0+8*j) :=
    ptrN base (off0+8*j) (by have := hreg.nowrap; omega)
  have hdet : strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j))) = BitVec.allOnes 64 := by
    rw [show strlenWordAt m0 (base.toNat + (off0+8*j)) = ldBytesT c.σ (base + BitVec.ofNat 64 (off0+8*j)) from by
      rw [ldBytesT_wordAt, hmem, hpos]]
    exact detect_takenG c.σ base len (off0+8*j) cs (by rw [hmem]; exact hcstr) hlen hpos (by omega)
  have hv : ((strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j)))) == (BitVec.allOnes 64)) = true := by
    rw [hdet]; simp
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d28_taken c.σ c.tick c.steps (0x80006d28#64) vmi
      (strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j)))) (BitVec.allOnes 64)
      hgood hpc hmi ha5 ha1 hloaded rfl hv htick
  have hpceq : (0x80006d28#64 : BitVec 64) + sign_extend (m := 64) (0x1fe8#13) = (0x80006d10#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc'' : σ'.regs.get? Register.PC = some (0x80006d10#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs, hpceq]
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc'',
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
    obs_btaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, hqal, hcstr, hlen, by omega⟩

/-- Generalized word-loop exit (`0xd28 → 0xd2c`, not taken, `off0+8j ≤ len < off0+8(j+1)`). -/
theorem wloop_exitG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlo : off0 + 8*j ≤ len) (hhi : len < off0 + 8*(j+1)) :
    Triple (W28G base r len cs m0 off0 j) (WTailG base r len cs m0 off0 j) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen, hjle⟩ := hSt
  have hpos : (base + BitVec.ofNat 64 (off0+8*j)).toNat = base.toNat + (off0+8*j) :=
    ptrN base (off0+8*j) (by have := hreg.nowrap; omega)
  have hdet : strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j))) ≠ BitVec.allOnes 64 := by
    rw [show strlenWordAt m0 (base.toNat + (off0+8*j)) = ldBytesT c.σ (base + BitVec.ofNat 64 (off0+8*j)) from by
      rw [ldBytesT_wordAt, hmem, hpos]]
    exact detect_nottakenG c.σ base len (off0+8*j) cs (by rw [hmem]; exact hcstr) hlen hlo hhi hpos
  have hv : ((strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j)))) == (BitVec.allOnes 64)) = false := by
    rw [beq_eq_false_iff_ne]; exact hdet
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d28_nottaken c.σ c.tick c.steps (0x80006d28#64) vmi
      (strlenWordVal (strlenWordAt m0 (base.toNat + (off0+8*j)))) (BitVec.allOnes 64)
      hgood hpc hmi ha5 ha1 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006d2c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006d28#64) 4 = (0x80006d2c#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc',
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_bnottaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, hqal, hcstr, hlen, hlo, hhi⟩

/-! ### Generalized word-loop assembly (`Triple.loop`) -/

def WAtHeadG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  ∃ j, WStG base r len cs m0 off0 j c

def WAtTailG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  ∃ j, WTailG base r len cs m0 off0 j c

def WLoopIG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  WAtHeadG base r len cs m0 off0 c ∨ WAtTailG base r len cs m0 off0 c

def WLoopBG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  WAtHeadG base r len cs m0 off0 c

/-- Measure: `len + 1 - (a4 - base)` at `0xd10`, else `0`.  At the head `a4 = base+(off0+8j)`
so this is `len + 1 - (off0+8j)`. -/
def WLoopMuG (base : BitVec 64) (len : Nat) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006d10#64)
  then len + 1 - (((c.σ.regs.get? Register.x14).getD (0#64)).toNat - base.toNat)
  else 0

theorem wloopmuG_head (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (c : Config)
    (hSt : WStG base r len cs m0 off0 j c) : WLoopMuG base len c = len + 1 - (off0 + 8*j) := by
  simp only [WLoopMuG, hSt.pc, hSt.a4, Option.getD_some, if_pos]
  have h4 : (base + BitVec.ofNat 64 (off0+8*j)).toNat = base.toNat + (off0+8*j) :=
    ptrN base (off0+8*j) (by have := hSt.regions.nowrap; have := hSt.jle; omega)
  rw [h4]; omega

theorem wloop_bodyG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 k : Nat) :
    Triple (fun c => WLoopIG base r len cs m0 off0 c ∧ WLoopBG base r len cs m0 off0 c ∧ WLoopMuG base len c = k)
           (fun c => WLoopIG base r len cs m0 off0 c ∧ WLoopMuG base len c < k) := by
  intro c hc
  obtain ⟨_, ⟨j, hSt⟩, hmu⟩ := hc
  have hmu_eq : WLoopMuG base len c = len + 1 - (off0 + 8*j) := wloopmuG_head base r len cs m0 off0 j c hSt
  rw [hmu_eq] at hmu
  have hjle := hSt.jle
  obtain ⟨c1, hs1, hSt28⟩ := wloop_straightG base r len cs m0 off0 j c hSt
  by_cases hdone : off0 + 8*(j+1) ≤ len
  · obtain ⟨c2, hs2, hSt2⟩ := wloop_backG base r len cs m0 off0 j hdone c1 hSt28
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨j+1, hSt2⟩, ?_⟩
    have hmu2 := wloopmuG_head base r len cs m0 off0 (j+1) c2 hSt2
    rw [hmu2, ← hmu]; omega
  · have hhi : len < off0 + 8*(j+1) := by omega
    obtain ⟨c2, hs2, hTail⟩ := wloop_exitG base r len cs m0 off0 j hjle hhi c1 hSt28
    refine ⟨c2, hs1.trans hs2, Or.inr ⟨j, hTail⟩, ?_⟩
    have hmu2 : WLoopMuG base len c2 = 0 := by
      have hne : ¬ (c2.σ.regs.get? Register.PC = some (0x80006d10#64)) := by
        rw [hTail.pc]; intro h; injection h with h; exact absurd h (by decide)
      simp only [WLoopMuG, if_neg hne]
    rw [hmu2]; omega

theorem wloop_to_tailG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) :
    Triple (WLoopIG base r len cs m0 off0) (WAtTailG base r len cs m0 off0) := by
  have hloop := Triple.loop (I := WLoopIG base r len cs m0 off0) (B := WLoopBG base r len cs m0 off0)
    (WLoopMuG base len) (wloop_bodyG base r len cs m0 off0)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hTail
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hTail⟩

/-! ### Magic setup from the alignment rejoin (`0xcfc → 0xd10`)

From `HAlign base r len cs m0 off0` (at `0xcfc`, `a0 = base`, `a4 = base+off0`), the magic
setup `lui/addi/slli/add/li` builds `a3 = magic7f`, `a1 = allOnes` (leaving `a0`, `a4`
untouched), landing at the word-loop head `WStG off0 0` (`a4 = base+off0 = base+(off0+8·0)`). -/
theorem align_entry_word (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) :
    Triple (HAlign base r len cs m0 off0) (WAtHeadG base r len cs m0 off0) := by
  intro c hAl
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hcstr, hlen, hoff0le, hqal, hoffpos⟩ := hAl
  -- cfc: lui a5,0x7f7f8
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006cfc c.σ c.tick c.steps (0x80006cfc#64) vmi hgood hpc hmi hloaded rfl htick
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006d00#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006cfc#64) 4 = (0x80006d00#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha4_4 := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have ha5_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- d00: addi a5,a5,-129
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006d00 σ4 i4 (c.steps + 1) (0x80006d00#64) vmi4
      (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)))
      hG4 hpc4 hmi4' ha5_4 (by rw [hmem4]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d04#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006d00#64) 4 = (0x80006d04#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have ha4_5 := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_4
  have ha5_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- d04: slli a3,a5,0x20
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006d04 σ5 i5 (c.steps + 1 + 1) (0x80006d04#64) vmi5
      (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      hG5 hpc5 hmi5' ha5_5 (by rw [hmem5, hmem4]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006d08#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006d04#64) 4 = (0x80006d08#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have ha4_6 := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_5
  have ha5_6 := obs_alu_other hobs6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_5
  have ha3_6 := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  -- d08: add a3,a3,a5
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006d08 σ6 i6 (c.steps + 1 + 1 + 1) (0x80006d08#64) vmi6
      (shift_bits_left (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      hG6 hpc6 hmi6' ha3_6 ha5_6 (by rw [hmem6, hmem5, hmem4]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006d0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006d08#64) 4 = (0x80006d0c#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have hra_7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have ha4_7 := obs_alu_other hobs7 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_6
  have ha3_7 : σ7.regs.get? Register.x13 = some magic7f := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [magic_build] at this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  -- d0c: li a1,-1
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006d0c σ7 i7 (c.steps + 1 + 1 + 1 + 1) (0x80006d0c#64) vmi7
      hG7 hpc7 hmi7' (by rw [hmem7, hmem6, hmem5, hmem4]; exact hloaded) rfl hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006d10#64 : BitVec 64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006d0c#64) 4 = (0x80006d10#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_alu_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7
  have hra_8 := obs_alu_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7
  have ha4_8 := obs_alu_other hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_7
  have ha3_8 := obs_alu_other hobs8 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_7
  have ha1_8 : σ8.regs.get? Register.x11 = some (BitVec.allOnes 64) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [allOnes_build] at this
  obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
  have hmem8eq : σ8.mem = c.σ.mem := by rw [hmem8, hmem7, hmem6, hmem5, hmem4]
  refine ⟨⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs4).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8)),
    0, hG8, by rw [hmem8eq]; exact hloaded, by rw [hmem8eq]; exact hmem, hpc8, ha0_8, ha1_8,
    ha3_8, ?_, hra_8, ⟨vmi8, hmi8'⟩, hi8, hreg, hqal, hcstr, hlen, by omega⟩
  · rw [show off0 + 8*0 = off0 from by omega]; exact ha4_8

/-! ### Generalized byte tail (`WTailG → Done`)

Mirrors the aligned `WTail → Done`, with `a0 = base` (length origin), scan base
`q = base+off0`, `a4 = base + ofNat(off0+8(j+1))`.  The `sub a3,a4,a0` gives
`a3 = ofNat(off0+8(j+1))` and the exit `addi a0,a3,-(8-k)` computes
`off0+8(j+1)-(8-k) = off0+8j+k = len`.  Byte at tail offset `k` is the string byte at
index `off0+8j+k` from `base`.  We phrase the tail via the byte index `t = off0+8j`. -/

/-- Generalized exit-addi: `a3 = ofNat(off0+8(j+1))`, `imm = -(8-k)`, `off0+8j+k = len`
⇒ result `= ofNat len`. -/
theorem exit_addi_valG (off0 j len k : Nat) (imm : BitVec 12)
    (hk : k ≤ 8) (hlen : off0 + 8*j + k = len)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) :
    (BitVec.ofNat 64 (off0+8*(j+1)) + sign_extend (m := 64) imm) = BitVec.ofNat 64 len := by
  rw [himm, BitVec.add_neg_eq_sub, ofNat_sub (off0+8*(j+1)) (8-k) (by omega)]
  congr 1; omega

/-- Generalized `lbu` effective address at tail offset `k`: `a4 + sext(-(8-k)) = base + (off0+8j+k)`. -/
theorem lbu_addrG (base : BitVec 64) (off0 j k : Nat) (hk : k ≤ 8) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8-k))) :
    (base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) imm
      = base + BitVec.ofNat 64 (off0+8*j + k) := by
  rw [himm, BitVec.add_assoc, BitVec.add_neg_eq_sub, ofNat_sub (off0+8*(j+1)) (8-k) (by omega)]
  congr 2; omega

/-- Generalized tail byte at string index `off0+8j+k` (`≤ len`): mapped, NUL iff `= len`. -/
theorem tail_byte_someG (base : BitVec 64) (len off0 j k : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 base.toNat cs) (hlen : cs.length = len)
    (hk : off0 + 8*j + k ≤ len) :
    ∃ b : BitVec 8, m0[base.toNat + (off0+8*j) + k]? = some b ∧ (b = 0 ↔ off0 + 8*j + k = len) := by
  by_cases heq : off0 + 8*j + k = len
  · refine ⟨0, ?_, by simp [heq]⟩
    have hnul := cstr_byte_nul m0 hcstr; rw [hlen] at hnul
    rw [show base.toNat + (off0+8*j) + k = base.toNat + len from by omega]; exact hnul
  · obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m0 hcstr (off0+8*j + k) (by omega)
    refine ⟨b, by rw [show base.toNat + (off0+8*j) + k = base.toNat + (off0+8*j+k) from by omega]; exact hb, ?_⟩
    exact ⟨fun h => absurd h hbne, fun h => by omega⟩

/-- Generalized tail `lbu` RAM/window bounds at string index `off0+8j+k` (`k ≤ 7`). -/
theorem tail_lbu_boundsG (base : BitVec 64) (len off0 j k : Nat) (hreg : StrRegions base len)
    (hj : off0 + 8*j ≤ len) (hk : k ≤ 7) :
    0x80000000 ≤ (base.toNat + (off0+8*j) + k) ∧
    (base.toNat + (off0+8*j) + k) + 1 ≤ 0x100000000 ∧
    ((base.toNat + (off0+8*j) + k) + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (base.toNat + (off0+8*j) + k)) := by
  have hlo := hreg.lo; have hhi := hreg.hi; have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by omega, by omega, ?_⟩
  rcases hh with h | h
  · left; omega
  · right; omega

/-- Generalized tail decision state at offset `k` (`decpc`), byte index `off0+8j+k`. -/
structure TDecG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j k : Nat) (decpc : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some decpc
  a0 : c.σ.regs.get? Register.x10 = some base
  a3 : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (off0+8*(j+1)))
  a5 : c.σ.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + k]?).getD 0))
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (off0+8*(j+1)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  qalign : (base.toNat + off0) % 8 = 0
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  jlo : off0 + 8*j ≤ len
  jhi : len < off0 + 8*(j+1)
  kle : off0 + 8*j + k ≤ len

/-- Generalized `beqz` guard: `(a5 == 0) = (off0+8j+k = len)`. -/
theorem tdec_guardG (base : BitVec 64) (len off0 j k : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 base.toNat cs) (hlen : cs.length = len)
    (hkle : off0 + 8*j + k ≤ len) :
    ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + k]?).getD 0)) == (0#64))
      = decide (off0 + 8*j + k = len) := by
  obtain ⟨b, hbmem, hbz⟩ := tail_byte_someG base len off0 j k cs m0 hcstr hlen hkle
  rw [hbmem, Option.getD_some, zext_beqz, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  exact hbz

/-- Generalized tail entry (`0xd2c → 0xd34`): `lbu a5,-8(a4)` (offset 0); `sub a3,a4,a0`
(`a3 = ofNat(off0+8(j+1))`). -/
theorem tail_entryG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) :
    Triple (WTailG base r len cs m0 off0 j) (TDecG base r len cs m0 off0 j 0 (0x80006d34#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen, hjlo, hjhi⟩ := hSt
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 0 hreg hjlo (by omega)
  obtain ⟨b0, hb0mem, _⟩ := tail_byte_someG base len off0 j 0 cs m0 hcstr hlen (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xff8#12)).toNat
      = base.toNat + (off0+8*j) + 0 := by
    rw [lbu_addrG base off0 j 0 (by omega) (0xff8#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    rw [show (off0+8*j + 0 : Nat) = off0+8*j from by omega]
    exact ptrN base (off0+8*j) (by have := hreg.nowrap; omega)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d2c c.σ c.tick c.steps (0x80006d2c#64) vmi (base + BitVec.ofNat 64 (off0+8*(j+1))) b0
      hgood hpc hmi ha4 hloaded rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr]; rw [hmem]; exact hb0mem) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d30#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006d2c#64) 4 = (0x80006d30#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha4_1 := obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- d30: sub a3,a4,a0
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d30 σ1 i1 (c.steps + 1) (0x80006d30#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) base
      hG1 hpc1 hmi1' ha4_1 ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d34#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d30#64) 4 = (0x80006d34#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  have ha3_2 : σ2.regs.get? Register.x13 = some (BitVec.ofNat 64 (off0+8*(j+1))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sub_a4_a0_val] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  have ha5b : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 0]?).getD 0)) := by
    rw [ha5_2, show b0 = (m0[base.toNat + (off0+8*j) + 0]?).getD 0 from by rw [hb0mem]; rfl]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5b,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, hqal, hcstr, hlen, hjlo, hjhi, by omega⟩

/-- Generalized exit-addi state: `a3 = ofNat(off0+8(j+1))`, at `addipc`. -/
def AtAddiG (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (off0 j : Nat) (addipc : BitVec 64) (c : Config) : Prop :=
  GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some addipc ∧
  c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (off0+8*(j+1))) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2

/-- Generalized offset-0 exit-addi `addi a0,a3,-8` (`0xd9c → 0xda0`). -/
theorem addi_d9cG (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlen : off0 + 8*j + 0 = len) :
    Triple (AtAddiG r len m0 off0 j (0x80006d9c#64)) (AtRet r len m0 (0x80006da0#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d9c c.σ c.tick c.steps (0x80006d9c#64) vmi (BitVec.ofNat 64 (off0+8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006da0#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006d9c#64) 4 = (0x80006da0#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_valG off0 j len 0 (0xff8#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Generalized offset-1 exit-addi `addi a0,a3,-7` (`0xd94 → 0xd98`). -/
theorem addi_d94G (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlen : off0 + 8*j + 1 = len) :
    Triple (AtAddiG r len m0 off0 j (0x80006d94#64)) (AtRet r len m0 (0x80006d98#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d94 c.σ c.tick c.steps (0x80006d94#64) vmi (BitVec.ofNat 64 (off0+8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006d98#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006d94#64) 4 = (0x80006d98#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_valG off0 j len 1 (0xff9#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Generalized offset-2 exit-addi `addi a0,a3,-6` (`0xdac → 0xdb0`). -/
theorem addi_dacG (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlen : off0 + 8*j + 2 = len) :
    Triple (AtAddiG r len m0 off0 j (0x80006dac#64)) (AtRet r len m0 (0x80006db0#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006dac c.σ c.tick c.steps (0x80006dac#64) vmi (BitVec.ofNat 64 (off0+8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006db0#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006dac#64) 4 = (0x80006db0#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_valG off0 j len 2 (0xffa#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Generalized offset-3 exit-addi `addi a0,a3,-5` (`0xda4 → 0xda8`). -/
theorem addi_da4G (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlen : off0 + 8*j + 3 = len) :
    Triple (AtAddiG r len m0 off0 j (0x80006da4#64)) (AtRet r len m0 (0x80006da8#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006da4 c.σ c.tick c.steps (0x80006da4#64) vmi (BitVec.ofNat 64 (off0+8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006da8#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006da4#64) 4 = (0x80006da8#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_valG off0 j len 3 (0xffb#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Generalized offset-4 exit-addi `addi a0,a3,-4` (`0xdb4 → 0xdb8`). -/
theorem addi_db4G (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlen : off0 + 8*j + 4 = len) :
    Triple (AtAddiG r len m0 off0 j (0x80006db4#64)) (AtRet r len m0 (0x80006db8#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006db4 c.σ c.tick c.steps (0x80006db4#64) vmi (BitVec.ofNat 64 (off0+8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006db8#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006db4#64) 4 = (0x80006db8#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_valG off0 j len 4 (0xffc#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Generalized offset-5 exit-addi `addi a0,a3,-3` (`0xdbc → 0xdc0`). -/
theorem addi_dbcG (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat)
    (hlen : off0 + 8*j + 5 = len) :
    Triple (AtAddiG r len m0 off0 j (0x80006dbc#64)) (AtRet r len m0 (0x80006dc0#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006dbc c.σ c.tick c.steps (0x80006dbc#64) vmi (BitVec.ofNat 64 (off0+8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006dc0#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006dbc#64) 4 = (0x80006dc0#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_valG off0 j len 5 (0xffd#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-! ### Generalized tail `beqz` exits (→ `Done`) and advances (→ next offset) -/

/-- Generalized offset-0 tail exit (`0xd34` beqz taken, `off0+8j = len`) → `Done`. -/
theorem tdec_exit_0G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlen : off0 + 8*j + 0 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 0 (0x80006d34#64)) (Done base r len m0) := by
  have hto_addi : Triple (TDecG base r len cs m0 off0 j 0 (0x80006d34#64)) (AtAddiG r len m0 off0 j (0x80006d9c#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 0]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guardG base len off0 j 0 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d34_taken c.σ c.tick c.steps (0x80006d34#64) vmi
        (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 0]?).getD 0))
        hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d34#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13) = (0x80006d9c#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
      obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_d9cG r len m0 off0 j hlen)).seq (ret_to_done base r len m0 (0x80006da0#64) retbytes_da0 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006da0#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006da0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006da0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Generalized offset-1 tail exit (`0xd3c` beqz taken, `off0+8j+1 = len`) → `Done`. -/
theorem tdec_exit_1G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlen : off0 + 8*j + 1 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 1 (0x80006d3c#64)) (Done base r len m0) := by
  have hto_addi : Triple (TDecG base r len cs m0 off0 j 1 (0x80006d3c#64)) (AtAddiG r len m0 off0 j (0x80006d94#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 1]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guardG base len off0 j 1 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d3c_taken c.σ c.tick c.steps (0x80006d3c#64) vmi
        (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 1]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d3c#64 : BitVec 64) + sign_extend (m := 64) (0x0058#13) = (0x80006d94#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
      obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_d94G r len m0 off0 j hlen)).seq (ret_to_done base r len m0 (0x80006d98#64) retbytes_d98 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006d98#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006d98#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006d98#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Generalized offset-2 tail exit (`0xd44` beqz taken, `off0+8j+2 = len`) → `Done`. -/
theorem tdec_exit_2G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlen : off0 + 8*j + 2 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 2 (0x80006d44#64)) (Done base r len m0) := by
  have hto_addi : Triple (TDecG base r len cs m0 off0 j 2 (0x80006d44#64)) (AtAddiG r len m0 off0 j (0x80006dac#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 2]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guardG base len off0 j 2 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d44_taken c.σ c.tick c.steps (0x80006d44#64) vmi
        (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 2]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d44#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13) = (0x80006dac#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
      obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_dacG r len m0 off0 j hlen)).seq (ret_to_done base r len m0 (0x80006db0#64) retbytes_db0 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006db0#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006db0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006db0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Generalized offset-3 tail exit (`0xd4c` beqz taken, `off0+8j+3 = len`) → `Done`. -/
theorem tdec_exit_3G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlen : off0 + 8*j + 3 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 3 (0x80006d4c#64)) (Done base r len m0) := by
  have hto_addi : Triple (TDecG base r len cs m0 off0 j 3 (0x80006d4c#64)) (AtAddiG r len m0 off0 j (0x80006da4#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 3]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guardG base len off0 j 3 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d4c_taken c.σ c.tick c.steps (0x80006d4c#64) vmi
        (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 3]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d4c#64 : BitVec 64) + sign_extend (m := 64) (0x0058#13) = (0x80006da4#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
      obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_da4G r len m0 off0 j hlen)).seq (ret_to_done base r len m0 (0x80006da8#64) retbytes_da8 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006da8#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006da8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006da8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Generalized offset-4 tail exit (`0xd54` beqz taken, `off0+8j+4 = len`) → `Done`. -/
theorem tdec_exit_4G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlen : off0 + 8*j + 4 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 4 (0x80006d54#64)) (Done base r len m0) := by
  have hto_addi : Triple (TDecG base r len cs m0 off0 j 4 (0x80006d54#64)) (AtAddiG r len m0 off0 j (0x80006db4#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 4]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guardG base len off0 j 4 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d54_taken c.σ c.tick c.steps (0x80006d54#64) vmi
        (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 4]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d54#64 : BitVec 64) + sign_extend (m := 64) (0x0060#13) = (0x80006db4#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
      obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_db4G r len m0 off0 j hlen)).seq (ret_to_done base r len m0 (0x80006db8#64) retbytes_db8 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006db8#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006db8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006db8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Generalized offset-5 tail exit (`0xd5c` beqz taken, `off0+8j+5 = len`) → `Done`. -/
theorem tdec_exit_5G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlen : off0 + 8*j + 5 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 5 (0x80006d5c#64)) (Done base r len m0) := by
  have hto_addi : Triple (TDecG base r len cs m0 off0 j 5 (0x80006d5c#64)) (AtAddiG r len m0 off0 j (0x80006dbc#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 5]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guardG base len off0 j 5 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d5c_taken c.σ c.tick c.steps (0x80006d5c#64) vmi
        (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 5]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d5c#64 : BitVec 64) + sign_extend (m := 64) (0x0060#13) = (0x80006dbc#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
      obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_dbcG r len m0 off0 j hlen)).seq (ret_to_done base r len m0 (0x80006dc0#64) retbytes_dc0 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006dc0#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006dc0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006dc0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Generalized offset-`k`→`k+1` tail advance body (`beqz` not-taken + next `lbu`).
Given the beqz-not-taken site, the fall-through `lbu` site, the offsets/imms/PCs, this
re-establishes `TDecG (k+1)`.  We instantiate it per offset below. -/
theorem tdec_next_0G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlt : off0 + 8*j + 0 < len) :
    Triple (TDecG base r len cs m0 off0 j 0 (0x80006d34#64)) (TDecG base r len cs m0 off0 j 1 (0x80006d3c#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 0]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guardG base len off0 j 0 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d34_nottaken c.σ c.tick c.steps (0x80006d34#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 0]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d38#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d34#64) 4 = (0x80006d38#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 1 hreg hjlo (by omega)
  obtain ⟨b1, hb1mem, _⟩ := tail_byte_someG base len off0 j 1 cs m0 hcstr hlen' (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xff9#12)).toNat
      = base.toNat + (off0+8*j) + 1 := by
    rw [lbu_addrG base off0 j 1 (by omega) (0xff9#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN base (off0+8*j + 1) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d38 σ1 i1 (c.steps + 1) (0x80006d38#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) b1
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb1mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d3c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d38#64) 4 = (0x80006d3c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 1]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b1 = (m0[base.toNat + (off0+8*j) + 1]?).getD 0 from by rw [hb1mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, hqal, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Generalized offset-1→2 advance (`0xd3c` not-taken). -/
theorem tdec_next_1G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlt : off0 + 8*j + 1 < len) :
    Triple (TDecG base r len cs m0 off0 j 1 (0x80006d3c#64)) (TDecG base r len cs m0 off0 j 2 (0x80006d44#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 1]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guardG base len off0 j 1 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d3c_nottaken c.σ c.tick c.steps (0x80006d3c#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 1]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d40#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d3c#64) 4 = (0x80006d40#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 2 hreg hjlo (by omega)
  obtain ⟨b2, hb2mem, _⟩ := tail_byte_someG base len off0 j 2 cs m0 hcstr hlen' (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffa#12)).toNat
      = base.toNat + (off0+8*j) + 2 := by
    rw [lbu_addrG base off0 j 2 (by omega) (0xffa#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN base (off0+8*j + 2) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d40 σ1 i1 (c.steps + 1) (0x80006d40#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) b2
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb2mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d44#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d40#64) 4 = (0x80006d44#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 2]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b2 = (m0[base.toNat + (off0+8*j) + 2]?).getD 0 from by rw [hb2mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, hqal, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Generalized offset-2→3 advance (`0xd44` not-taken). -/
theorem tdec_next_2G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlt : off0 + 8*j + 2 < len) :
    Triple (TDecG base r len cs m0 off0 j 2 (0x80006d44#64)) (TDecG base r len cs m0 off0 j 3 (0x80006d4c#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 2]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guardG base len off0 j 2 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d44_nottaken c.σ c.tick c.steps (0x80006d44#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 2]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d48#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d44#64) 4 = (0x80006d48#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 3 hreg hjlo (by omega)
  obtain ⟨b3, hb3mem, _⟩ := tail_byte_someG base len off0 j 3 cs m0 hcstr hlen' (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffb#12)).toNat
      = base.toNat + (off0+8*j) + 3 := by
    rw [lbu_addrG base off0 j 3 (by omega) (0xffb#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN base (off0+8*j + 3) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d48 σ1 i1 (c.steps + 1) (0x80006d48#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) b3
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb3mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d4c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d48#64) 4 = (0x80006d4c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 3]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b3 = (m0[base.toNat + (off0+8*j) + 3]?).getD 0 from by rw [hb3mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, hqal, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Generalized offset-3→4 advance (`0xd4c` not-taken). -/
theorem tdec_next_3G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlt : off0 + 8*j + 3 < len) :
    Triple (TDecG base r len cs m0 off0 j 3 (0x80006d4c#64)) (TDecG base r len cs m0 off0 j 4 (0x80006d54#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 3]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guardG base len off0 j 3 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d4c_nottaken c.σ c.tick c.steps (0x80006d4c#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 3]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d50#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d4c#64) 4 = (0x80006d50#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 4 hreg hjlo (by omega)
  obtain ⟨b4, hb4mem, _⟩ := tail_byte_someG base len off0 j 4 cs m0 hcstr hlen' (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffc#12)).toNat
      = base.toNat + (off0+8*j) + 4 := by
    rw [lbu_addrG base off0 j 4 (by omega) (0xffc#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN base (off0+8*j + 4) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d50 σ1 i1 (c.steps + 1) (0x80006d50#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) b4
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb4mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d54#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d50#64) 4 = (0x80006d54#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 4]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b4 = (m0[base.toNat + (off0+8*j) + 4]?).getD 0 from by rw [hb4mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, hqal, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Generalized offset-4→5 advance (`0xd54` not-taken). -/
theorem tdec_next_4G (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlt : off0 + 8*j + 4 < len) :
    Triple (TDecG base r len cs m0 off0 j 4 (0x80006d54#64)) (TDecG base r len cs m0 off0 j 5 (0x80006d5c#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 4]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guardG base len off0 j 4 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d54_nottaken c.σ c.tick c.steps (0x80006d54#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 4]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d58#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d54#64) 4 = (0x80006d58#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 5 hreg hjlo (by omega)
  obtain ⟨b5, hb5mem, _⟩ := tail_byte_someG base len off0 j 5 cs m0 hcstr hlen' (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffd#12)).toNat
      = base.toNat + (off0+8*j) + 5 := by
    rw [lbu_addrG base off0 j 5 (by omega) (0xffd#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN base (off0+8*j + 5) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d58 σ1 i1 (c.steps + 1) (0x80006d58#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) b5
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb5mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d5c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d58#64) 4 = (0x80006d5c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 5]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b5 = (m0[base.toNat + (off0+8*j) + 5]?).getD 0 from by rw [hb5mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, hqal, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Generalized `snez`-path arithmetic: `snez_val + ofNat(off0+8(j+1)) + sext(-2) = ofNat len`. -/
theorem snez_finalG (off0 j len : Nat) (b6 : BitVec 8)
    (hlo : off0 + 8*j + 5 < len) (hhi : len < off0 + 8*(j+1)) (hnw : off0 + 8*(j+1) + 8 < 2^64)
    (hb6 : b6 = 0 ↔ off0 + 8*j + 6 = len) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))
      + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 len := by
  have hsext : (sign_extend (m := 64) (0xffe#12) : BitVec 64) = -(BitVec.ofNat 64 2) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hsnez : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat
      = (if b6 = 0 then 0 else 1) := snez_toNat b6
  -- the snez value's toNat, bounded and pinned by `hsnez`
  have hsvlt : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat < 2 := by
    rw [hsnez]; by_cases h : b6 = 0
    · simp only [if_pos h]; decide
    · simp only [if_neg h]; decide
  have hval : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) - 2 = len := by
    rw [hsnez]
    by_cases h : b6 = 0
    · have := hb6.mp h; simp only [if_pos h]; omega
    · have hne : ¬ (off0 + 8*j + 6 = len) := fun hc => h (hb6.mpr hc); simp only [if_neg h]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, hsext, BitVec.toNat_neg]
  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
  rw [h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2^64 from by omega),
    Nat.mod_eq_of_lt (show off0+8*(j+1) < 2^64 from by omega),
    Nat.mod_eq_of_lt (show (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) < 2^64 from by omega)]
  have hm2 : (2^64 - 2) % 2^64 = 2^64 - 2 := Nat.mod_eq_of_lt (by omega)
  rw [hm2]
  rw [show (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) + (2^64 - 2) = len + 2^64 from by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (show len < 2^64 from by omega)]

/-- Generalized `snez` tail path (`0xd5c` not-taken → `0xd70` ret, `off0+8j+5 < len`) → `Done`. -/
theorem tdec_snezG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (hlt : off0 + 8*j + 5 < len) (halign : r.toNat % 4 = 0) :
    Triple (TDecG base r len cs m0 off0 j 5 (0x80006d5c#64)) (Done base r len m0) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hqal, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 5]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guardG base len off0 j 5 cs m0 hcstr hlen' hkle]; simp; omega
  -- d5c: beqz not taken → d60
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d5c_nottaken c.σ c.tick c.steps (0x80006d5c#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + (off0+8*j) + 5]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d60#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d5c#64) 4 = (0x80006d60#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- d60: lbu a5,-2(a4) → byte offset 6
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_boundsG base len off0 j 6 hreg hjlo (by omega)
  obtain ⟨b6, hb6mem, hb6z⟩ := tail_byte_someG base len off0 j 6 cs m0 hcstr hlen' (by omega)
  have haddr : ((base + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffe#12)).toNat
      = base.toNat + (off0+8*j) + 6 := by
    rw [lbu_addrG base off0 j 6 (by omega) (0xffe#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN base (off0+8*j + 6) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d60 σ1 i1 (c.steps + 1) (0x80006d60#64) vmi1 (base + BitVec.ofNat 64 (off0+8*(j+1))) b6
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb6mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d64#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d60#64) 4 = (0x80006d64#64 : BitVec 64) from by decide] at this
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- d64: snez a0,a5
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d64 σ2 i2 (c.steps + 1 + 1) (0x80006d64#64) vmi2 (zero_extend (m := 64) b6)
      hG2 hpc2 hmi2' ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d68#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d64#64) 4 = (0x80006d68#64 : BitVec 64) from by decide] at this
  have ha3_3 := obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha0_3 := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- d68: add a0,a0,a3
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006d68 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006d68#64) vmi3
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6))))
      (BitVec.ofNat 64 (off0+8*(j+1)))
      hG3 hpc3 hmi3' ha0_3 ha3_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006d6c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006d68#64) 4 = (0x80006d6c#64 : BitVec 64) from by decide] at this
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have ha0_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- d6c: addi a0,a0,-2 → a0 = ofNat len
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006d6c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006d6c#64) vmi4
      ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))) + BitVec.ofNat 64 (off0+8*(j+1)))
      hG4 hpc4 hmi4' ha0_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d70#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006d6c#64) 4 = (0x80006d70#64 : BitVec 64) from by decide] at this
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have ha0_5 : σ5.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [snez_finalG off0 j len b6 hlt hjhi (by have := hreg.nowrap; have := hreg.lo; have := hreg.hi; omega) (by rw [hb6z])] at this
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  have hmem5eq : σ5.mem = c.σ.mem := by rw [hmem5, hmem4, hmem3, hmem2, hmem1]
  have hAtRet : AtRet r len m0 (0x80006d70#64) ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := by
    refine ⟨hG5, by rw [hmem5eq]; exact hloaded, by rw [hmem5eq]; exact hmem, hpc5, ha0_5, hra_5,
      ⟨vmi5, hmi5'⟩, hi5⟩
  obtain ⟨cf, hsf, hDone⟩ := ret_to_done base r len m0 (0x80006d70#64) retbytes_d70
    (by decide) (by decide) (by decide) halign ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ hAtRet
  refine ⟨cf, ?_, hDone⟩
  exact (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
    (Steps.single hs4)).trans (Steps.single hs5)).trans hsf

/-! ### Generalized byte-tail assembly (`WTailG → Done`) -/

theorem tail_to_doneG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (halign : r.toNat % 4 = 0) :
    Triple (WTailG base r len cs m0 off0 j) (Done base r len m0) := by
  refine (tail_entryG base r len cs m0 off0 j).seq ?_
  intro c hSt
  have hjlo := hSt.jlo; have hjhi := hSt.jhi
  rcases (show len = off0+8*j + 0 ∨ len = off0+8*j + 1 ∨ len = off0+8*j + 2 ∨ len = off0+8*j + 3 ∨
      len = off0+8*j + 4 ∨ len = off0+8*j + 5 ∨ len = off0+8*j + 6 ∨ len = off0+8*j + 7 from by omega)
    with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact tdec_exit_0G base r len cs m0 off0 j (by omega) halign c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      (tdec_exit_1G base r len cs m0 off0 j (by omega) halign)) c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_1G base r len cs m0 off0 j (by omega)).seq
      (tdec_exit_2G base r len cs m0 off0 j (by omega) halign))) c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_1G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_2G base r len cs m0 off0 j (by omega)).seq
      (tdec_exit_3G base r len cs m0 off0 j (by omega) halign)))) c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_1G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_2G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_3G base r len cs m0 off0 j (by omega)).seq
      (tdec_exit_4G base r len cs m0 off0 j (by omega) halign))))) c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_1G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_2G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_3G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_4G base r len cs m0 off0 j (by omega)).seq
      (tdec_exit_5G base r len cs m0 off0 j (by omega) halign)))))) c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_1G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_2G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_3G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_4G base r len cs m0 off0 j (by omega)).seq
      (tdec_snezG base r len cs m0 off0 j (by omega) halign)))))) c hSt
  · exact ((tdec_next_0G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_1G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_2G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_3G base r len cs m0 off0 j (by omega)).seq
      ((tdec_next_4G base r len cs m0 off0 j (by omega)).seq
      (tdec_snezG base r len cs m0 off0 j (by omega) halign)))))) c hSt

theorem wattail_to_doneG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (halign : r.toNat % 4 = 0) :
    Triple (WAtTailG base r len cs m0 off0) (Done base r len m0) :=
  Triple.exists_pre (fun j => tail_to_doneG base r len cs m0 off0 j halign)

/-- **Alignment-exit word scan** (`HAlign → Done`): magic setup, word loop, byte tail. -/
theorem align_to_done (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (halign : r.toNat % 4 = 0) :
    Triple (HAlign base r len cs m0 off0) (Done base r len m0) :=
  ((align_entry_word base r len cs m0 off0).seq
    ((fun c hc => wloop_to_tailG base r len cs m0 off0 c (Or.inl hc)) :
      Triple (WAtHeadG base r len cs m0 off0) (WAtTailG base r len cs m0 off0))).seq
    (wattail_to_doneG base r len cs m0 off0 halign)

/-! ## Unaligned path assembly (`UPre → Done`) and `strlen_full_spec`

The head loop exits to `AtRet 0xd90 ∨ HAtAlign`; the NUL-exit `ret` (`AtRet → Done`)
and the alignment-exit word scan (`HAlign → Done`) both land in `Done`. -/

/-- The NUL-exit pre-`ret` state `AtRet 0xd90` returns to `r` (`Done`). -/
theorem atret_d90_to_done (base r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (halign : r.toNat % 4 = 0) :
    Triple (AtRet r len m0 (0x80006d90#64)) (Done base r len m0) :=
  ret_to_done base r len m0 (0x80006d90#64) retbytes_d90 (by decide) (by decide) (by decide) halign

/-- The head-loop exit disjunction reaches `Done`. -/
theorem head_exit_to_done (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (fun c => AtRet r len m0 (0x80006d90#64) c ∨ HAtAlign base r len cs m0 c)
           (Done base r len m0) := by
  refine Triple.cases (atret_d90_to_done base r len m0 halign) ?_
  exact Triple.exists_pre (fun off0 => align_to_done base r len cs m0 off0 halign)

/-- **Unaligned `strlen`** (`UPre → Done`): entry peel-loop then NUL-exit or aligned scan. -/
theorem strlen_unaligned_run (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (UPre p r len cs m0) (Done p r len m0) := by
  have hentry : Triple (UPre p r len cs m0) (HAtHead p r len cs m0) :=
    (entry_unaligned p r len cs m0).conseq (fun _ h => h) (fun c h => ⟨0, h⟩)
  have hexit : Triple (HAtHead p r len cs m0)
      (fun c => AtRet r len m0 (0x80006d90#64) c ∨ HAtAlign p r len cs m0 c) :=
    fun c hc => hloop_to_exit p r len cs m0 c (Or.inl hc)
  exact (hentry.seq hexit).seq (head_exit_to_done p r len cs m0 halign)

/-- Top-level unaligned precondition (`p.toNat % 8 ≠ 0`), `CString`-phrased. -/
def strlen_unaligned_pre (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some p ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  StrRegions p s.length ∧ p.toNat % 8 ≠ 0 ∧ CString m0 p.toNat s ∧ r.toNat % 4 = 0

/-- **`strlen` total-correctness spec (unaligned path, `p.toNat % 8 ≠ 0`).** -/
theorem strlen_unaligned_spec (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (strlen_unaligned_pre p r s m0) (strlen_post r s m0) := by
  intro c hpre
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, halign, hcstring, halignr⟩ := hpre
  obtain ⟨cs, hcstr, hlens⟩ := cstring_length m0 p.toNat s hcstring
  have hUPre : UPre p r s.length cs m0 c :=
    ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, halign, hcstr, hlens.symm⟩
  obtain ⟨c', hsteps, hdone⟩ := strlen_unaligned_run p r s.length cs m0 halignr c hUPre
  obtain ⟨hG', hpc', ha0', hra', hmem'⟩ := hdone
  exact ⟨c', hsteps, hG', hpc', ha0', hra', hmem'⟩

/-! ## Top-level full spec (`strlen_full_spec`)

`Triple.cases` over the `0xcf0` alignment test unifies the aligned fast path
(`strlen_spec`) and the unaligned head-peel path (`strlen_unaligned_spec`).  The shared
precondition `strlen_full_pre` omits the alignment guard (the machine decides it); both
paths share the postcondition `strlen_post`. -/

/-- Top-level full precondition (any alignment), `CString`-phrased. -/
def strlen_full_pre (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some p ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  StrRegions p s.length ∧ CString m0 p.toNat s ∧ r.toNat % 4 = 0

/-- **Top-level `strlen` full spec** — from `strlen_full_pre` the machine runs to
`strlen_post` (returns to `r` with `x10 = s.length`, memory unchanged) regardless of
`p`'s alignment.  Dispatches on `p.toNat % 8 = 0` into the aligned `strlen_spec` and the
unaligned `strlen_unaligned_spec`. -/
theorem strlen_full_spec (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (strlen_full_pre p r s m0) (strlen_post r s m0) := by
  intro c hpre
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, hcstring, halignr⟩ := hpre
  by_cases halgn : p.toNat % 8 = 0
  · exact strlen_spec p r s m0 c
      ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, halgn, hcstring, halignr⟩
  · exact strlen_unaligned_spec p r s m0 c
      ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, halgn, hcstring, halignr⟩

end Vsa.Sim
