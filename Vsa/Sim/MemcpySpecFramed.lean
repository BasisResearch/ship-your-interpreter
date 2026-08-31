import Vsa.Sim.MemcpySpec4
import Vsa.Sim.StrlenSpec

/-!
# Frame-preserving `memcpy` spec (`memcpy_spec_framed`) — the memcpy analogue of
`strlen_spec_framed` (`StrlenSpec.lean`), for the `env_define` composition seam.

The `env_define` append path (`EnvDefCompose.envDefAppendContract`) calls
`memcpy(copy, name, len+1)` between `malloc` and the store block.  The store
block (`0x80002b44..0x80002b88` + epilogue) reads the callee-saved registers
(`s0..s6`: env pointer, count, cap, name length), `sp`/`gp`, and needs the
allocator invariant `AInv` over the live extents to survive the copy — i.e. the
whole `EnvDefFrame` (the same carried caller-frame `envDefStrlenFramed` threads
across `strlen`).

**Reuse (the exponentiation finding).**  memcpy's *dispatch prologue* is
register-only `sigmaPost_alu`/`sigmaPost_branch_*` steps — the SAME families the
`strlen` frame primitives (`strlenFrame_alu`/`_btaken`/`_bnottaken`,
`abiPreserved_wr`/`abiPreserved_pinned`) act on.  Those primitives are keyed ONLY
on `AbiPreserved`, with NO strlen-specific site dependency, so they are REUSED
VERBATIM here: no clone, no factoring needed.  This file only re-runs the
dispatch prologue carrying `∀ R, AbiPreserved R → get? R = gm R`, then hands off
to the byte copy path, which **preserves the ghost natively** (`PreB g` →
`memcpy_bytepath_post g` carry the SAME `g` in their `hframe` field), so the
frame arrives at the return with the entry `gm` still tied.

**KEY DIFFERENCE vs `strlen` (the memory clause).**  strlen never stores
(`mem = m0`), so `AInv` survival is trivial.  memcpy WRITES the destination
`[dst, dst+n)`.  `memcpy_bytepath_post` already states the write-footprint
containment clause `∀ a, (a < dst ∨ dst+n ≤ a) → mem[a] = m0[a]` (agrees with
`m0` OUTSIDE `[dst,dst+n)`), so `AInv` survival is a *disjointness* corollary:
the copy footprint is the freshly-`malloc`'d block, disjoint from every live
extent the arena invariant owns.  We expose exactly that as
`memcpy_framed_ainv_stable` (the memcpy analogue of `strlen_framed_mem_stable`),
consumed by `EnvDefCompose.envDefMemcpyFramed`.

Additive: `memcpy_spec`/`memcpy_bytepath_post`/`PreDispatch` UNCHANGED; no
consumer touched.  No `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
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

/-! ## `PreDispatch` with the carried ABI frame

`PreDispatch g` already has a `hframe : ∀ R, NotWrittenB R → get? R = g R` field, but
`NotWrittenB` is the memcpy blanket frame (excludes `{x11,x14,x15}` + control); the
composition wants the ABI-callee-saved tie `∀ R, AbiPreserved R → get? R = gm R`.  Since
`AbiPreserved ⊆ NotWrittenB` (none of `x2/x3/x4/x8/x9/x18..x27` is `x11/x14/x15` or a
control register — `decide`), the ABI tie is what the dispatch threads.  We carry it as an
explicit conjunct alongside the (ghost-free) intermediate `AtBd4`. -/

/-- `AbiPreserved R` implies `NotWrittenB R` (the memcpy blanket frame is coarser than the
ABI-callee-saved set).  So the memcpy per-site frame readbacks (which the strlen primitives
give against `AbiPreserved`) suffice for every place `NotWrittenB` is demanded. -/
theorem abiPreserved_notWrittenB {R : Register} (hR : AbiPreserved R = true) :
    NotWrittenB R := by
  cases R <;> simp_all [AbiPreserved, NotWrittenB]

/-! ## Framed dispatch prologue `bc8 → bd4` (`to_bd4` re-run carrying the ABI frame)

Three register-only ALU steps (`xor a5`; `andi a5`; `add a7`).  Each preserves every
`AbiPreserved` register (none of `x15`/`x17` is `AbiPreserved`), lifted by the REUSED
`strlenFrame_alu`. -/
theorem to_bd4_framed (gm : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple
      (fun c => PreDispatch gm r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => AtBd4 r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hPre, hgh0⟩
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv, _⟩ := hPre
  -- === bc8: xor a5,a1,a0 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006bc8 c.σ c.tick c.steps (0x80006bc8#64) vmi src dst
      hgood hpc hmi ha1 ha0 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006bcc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006bc8#64) 4 = (0x80006bcc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  have hg1 : ∀ R, AbiPreserved R = true → σ1.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs1 R (by decide) hR]; exact hgh0 R hR
  -- === bcc: andi a5,a5,7 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006bcc σ1 i1 (c.steps + 1) (0x80006bcc#64) vmi1 (src ^^^ dst)
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006bd0#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006bcc#64) 4 = (0x80006bd0#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hg2 : ∀ R, AbiPreserved R = true → σ2.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs2 R (by decide) hR]; exact hg1 R hR
  -- === bd0: add a7,a0,a2 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006bd0 σ2 i2 (c.steps + 1 + 1) (0x80006bd0#64) vmi2 dst (BitVec.ofNat 64 n)
      hG2 hpc2 hmi2' ha0_2 ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006bd4#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006bd0#64) 4 = (0x80006bd4#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have ha7_3 : σ3.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hg3 : ∀ R, AbiPreserved R = true → σ3.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs3 R (by decide) hR]; exact hg2 R hR
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3), ?_, hg3⟩
  exact ⟨hG3, by rw [hmem3eq]; exact hloaded, hpc3, ha0_3, ha1_3, ha2_3, ha5_3, ha7_3,
    hra_3, ⟨vmi3, hmi3'⟩, hi3, hreg, hnpos, by rw [hmem3eq]; exact hminv⟩

/-! ## Framed byte-route dispatch: `AtBd4 ∧ Abi → PreB gm`

Both byte routes (misaligned `bd4`-taken; small `bd4`-nottaken ≫ `bd8` ≫ `bdc`-taken)
land `PreB` at `c40`.  We re-run them carrying the ABI frame and, crucially, land
`PreB gm` — the ghost is literally `gm` (not a fresh dispatch-successor ghost), because
`PreB.hframe` demands `∀ R NotWrittenB, get? R = gm R`, which the ABI frame delivers via
`abiPreserved_notWrittenB` for the AbiPreserved subset — but `PreB.hframe` is over
`NotWrittenB` which is WIDER than `AbiPreserved`.  So we cannot use `gm` for the ghost
slot directly.  Instead we land `PreB g'` with a fresh `g'` = the successor reads (as the
unframed dispatch does), AND separately carry the ABI conjunct; the byte path then
threads BOTH (the fresh `g'` for its `NotWrittenB` bookkeeping, the ABI conjunct for the
composition).  See `bytepath_framed`. -/

/-- The unframed misaligned/small dispatch, re-exposed to also carry the ABI frame.
`dispatch_*_to_byte` land `∃ g', PreB g'`; we thread `∀ R AbiPreserved, get? R = gm R`
alongside by re-running the (few) register-only sites with `strlenFrame_*`. -/
theorem dispatch_misaligned_to_byte_framed
    (gm : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hmis : (src.toNat ^^^ dst.toNat) % 8 ≠ 0) :
    Triple
      (fun c => AtBd4 r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g', PreB g' r dst src n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hSt, hgh0⟩
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha5, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv⟩ := hSt
  have hv : (((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true := by
    rw [and7_ne_zero_iff]; rw [xor_toNat] at *; exact hmis
  have htgt : ((0x80006bd4#64 : BitVec 64) + sign_extend (m := 64) (0x006c#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006bd4_taken c.σ c.tick c.steps (0x80006bd4#64) vmi
      ((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12))
      hgood hpc hmi ha5 hloaded rfl htgt hv htick
  have hpceq : (0x80006bd4#64 : BitVec 64) + sign_extend (m := 64) (0x006c#13) = (0x80006c40#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc' : σ'.regs.get? Register.PC = some (0x80006c40#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs, hpceq]
  refine ⟨⟨σ', i', c.steps + 1⟩, Steps.single hstep, ⟨fun R => σ'.regs.get? R, ?_⟩, ?_⟩
  · exact ⟨hG', by rw [hmem']; exact hloaded, hpc',
      obs_btaken_other' hobs Register.x10 (by decide) ha0,
      obs_btaken_other' hobs Register.x11 (by decide) ha1,
      obs_btaken_other' hobs Register.x17 (by decide) ha7,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi', hreg, hnpos, by rw [hmem']; exact hminv, fun R _ => rfl⟩
  · exact fun R hR => (strlenFrame_btaken hobs R hR).trans (hgh0 R hR)

theorem dispatch_small_to_byte_framed
    (gm : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign_xor : (src.toNat ^^^ dst.toNat) % 8 = 0) (hsmall : n < 8) :
    Triple
      (fun c => AtBd4 r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g', PreB g' r dst src n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hSt, hgh0⟩
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha5, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv⟩ := hSt
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
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  have hg2 : ∀ R, AbiPreserved R = true → σ2.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_alu hobs2 R (by decide) hR]; exact hg1 R hR
  -- === bdc: bnez a2 taken (n < 8 ⇒ a2 ≠ 0) → c40 ===
  have hvdc : ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12))))) != (0#64)) = true := by
    rw [sltiu8_ne_zero_iff]; rw [a2_ofNat_toNat n (by have := hreg.dst_nowrap; omega)]; exact hsmall
  have htgt : ((0x80006bdc#64 : BitVec 64) + sign_extend (m := 64) (0x0064#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006bdc_taken σ2 i2 (c.steps + 1 + 1) (0x80006bdc#64) vmi2
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12)))))
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2eq]; exact hloaded) rfl htgt hvdc hi2
  have hpceq : (0x80006bdc#64 : BitVec 64) + sign_extend (m := 64) (0x0064#13) = (0x80006c40#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c40#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs3, hpceq]
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2eq]
  have hg3 : ∀ R, AbiPreserved R = true → σ3.regs.get? R = gm R := fun R hR => by
    rw [strlenFrame_btaken hobs3 R hR]; exact hg2 R hR
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3),
    ⟨fun R => σ3.regs.get? R, ?_⟩, hg3⟩
  exact ⟨hG3, by rw [hmem3eq]; exact hloaded, hpc3,
    obs_btaken_other' hobs3 Register.x10 (by decide) ha0_2,
    obs_btaken_other' hobs3 Register.x11 (by decide) ha1_2,
    obs_btaken_other' hobs3 Register.x17 (by decide) ha7_2,
    obs_btaken_other' hobs3 Register.x1 (by decide) hra_2,
    obs_btaken_minstret hobs3, hi3, hreg, hnpos, by rw [hmem3eq]; exact hminv, fun R _ => rfl⟩

/-! ## The byte copy path preserves the ABI frame

`memcpy_bytepath_spec g'` gives `Triple (PreB g') (memcpy_bytepath_post g')`.  The byte
path only writes `{x1,x5,x11,x13,x14,x15}` (per `NotWrittenB`) plus memory `[dst,dst+n)`;
none of `x1`/`x5`/… is `AbiPreserved`, so an ABI conjunct carried alongside survives.
Rather than re-run the loop, we thread the ABI conjunct through the loop by the SAME
`NotWrittenB`-frame the byte path already maintains: `memcpy_bytepath_post g'` states
`∀ R NotWrittenB, get? R = g' R`, and the entry `PreB g'` states `get? R = g' R` too
(same `g'`); so the entry ABI conjunct (`get? R = gm R`, `R : AbiPreserved ⊆ NotWrittenB`)
transports to the exit via `g'`.  This is what `bytepath_abi` packages. -/

/-- Byte path preserving the carried ABI frame: from `PreB g' ∧ Abi(gm)` reach
`memcpy_bytepath_post g' ∧ Abi(gm)`.  The ABI conjunct survives because both endpoints tie
the `NotWrittenB ⊇ AbiPreserved` registers to the SAME `g'`. -/
theorem bytepath_abi (gm g' : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0) :
    Triple
      (fun c => PreB g' r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => memcpy_bytepath_post g' r dst n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  intro c ⟨hPre, hgh⟩
  -- entry ABI values pinned to g' via PreB.hframe (AbiPreserved ⊆ NotWrittenB)
  have hentry : ∀ R, AbiPreserved R = true → g' R = gm R := fun R hR => by
    rw [← hPre.hframe R (abiPreserved_notWrittenB hR)]; exact hgh R hR
  obtain ⟨c', hsteps, hpost⟩ := memcpy_bytepath_spec g' r dst src n m0 bs halign c hPre
  refine ⟨c', hsteps, hpost, fun R hR => ?_⟩
  -- exit: get? R = g' R (post's NotWrittenB frame) = gm R (hentry)
  rw [hpost.2.2.2.2.2.2.2 R (abiPreserved_notWrittenB hR)]; exact hentry R hR

/-! ## `memcpy_spec_framed` — byte route

For the `env_define` `memcpy(copy, name, len+1)` call, we cover the byte route of the
dispatch (misaligned or `n < 8`) carrying the ABI frame end-to-end.  The word route (the
`8*(n/8) ≤ 64` aligned small-word-loop path) resets the ghost at the `NotWrittenW →
NotWrittenB` epilogue crossover, so its ABI-frame carry needs the framed word epilogue —
a documented follow-up; a `len+1`-byte C-string copy into a fresh `malloc` block takes the
byte route whenever `src`/`dst` are mutually misaligned or `len+1 < 8`, the common case.

The post carries: `memcpy_bytepath_post g'` (PC=r, x10=dst, described copy into
`[dst,dst+n)`, everything OUTSIDE `[dst,dst+n)` = `m0`, `tick<2`) PLUS the ABI-callee-saved
tie `∀ R AbiPreserved, get? R = gm R` — exactly the register half of `EnvDefFrame`. -/
theorem memcpy_spec_framed_byte (gm : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0)
    (hroute : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ n < 8) :
    Triple
      (fun c => PreDispatch gm r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R))
      (fun c => (∃ g', memcpy_bytepath_post g' r dst n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R)) := by
  refine (to_bd4_framed gm r dst src n m0 bs).seq ?_
  rcases hroute with hmis | hsmall
  · -- (A) misaligned → byte path
    refine (dispatch_misaligned_to_byte_framed gm r dst src n m0 bs hmis).seq ?_
    intro c ⟨⟨g', hPreB⟩, hgh⟩
    obtain ⟨c', hsteps, hpost, hgh'⟩ :=
      bytepath_abi gm g' r dst src n m0 bs halign c ⟨hPreB, hgh⟩
    exact ⟨c', hsteps, ⟨g', hpost⟩, hgh'⟩
  · -- (B) small.  Case-split the alignment-xor to pick the byte sub-route.
    by_cases halx : (src.toNat ^^^ dst.toNat) % 8 = 0
    · refine (dispatch_small_to_byte_framed gm r dst src n m0 bs halx hsmall).seq ?_
      intro c ⟨⟨g', hPreB⟩, hgh⟩
      obtain ⟨c', hsteps, hpost, hgh'⟩ :=
        bytepath_abi gm g' r dst src n m0 bs halign c ⟨hPreB, hgh⟩
      exact ⟨c', hsteps, ⟨g', hpost⟩, hgh'⟩
    · refine (dispatch_misaligned_to_byte_framed gm r dst src n m0 bs halx).seq ?_
      intro c ⟨⟨g', hPreB⟩, hgh⟩
      obtain ⟨c', hsteps, hpost, hgh'⟩ :=
        bytepath_abi gm g' r dst src n m0 bs halign c ⟨hPreB, hgh⟩
      exact ⟨c', hsteps, ⟨g', hpost⟩, hgh'⟩

/-! ## `AInv` survival — the memory-clause corollary (the KEY DIFFERENCE)

Unlike `strlen` (`mem = m0`), memcpy WRITES `[dst,dst+n)`.  `memcpy_bytepath_post` already
carries the write-footprint containment `∀ a, (a < dst ∨ dst+n ≤ a) → mem[a] = m0[a]`.  So
any allocator invariant stable under memory-agreement-off-a-disjoint-footprint survives,
provided the copy footprint `[dst,dst+n)` is disjoint from every live extent (it is: `dst`
is the freshly-`malloc`'d block, not yet in the `AInv` ledger the store block re-establishes
— `EnvDefCompose` supplies this disjointness from the malloc post's `ExtDisjoint`).

`memcpy_framed_ainv_stable` exposes the outside-footprint clause as the memory agreement any
disjointness-aware `AInv`-stability property consumes. -/

/-- **Memory-clause corollary** (the memcpy analogue of `strlen_framed_mem_stable`).  From
`memcpy_bytepath_post`, memory agrees with `m0` at every address OUTSIDE `[dst,dst+n)`. -/
theorem memcpy_framed_ainv_stable
    (g' : (R : Register) → Option (RegisterType R)) (r dst : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config)
    (h : memcpy_bytepath_post g' r dst n m0 bs c) :
    ∀ a, (a < dst.toNat ∨ dst.toNat + n ≤ a) → c.σ.mem[a]? = m0[a]? :=
  h.2.2.2.2.2.1

#print axioms to_bd4_framed
#print axioms dispatch_misaligned_to_byte_framed
#print axioms dispatch_small_to_byte_framed
#print axioms bytepath_abi
#print axioms memcpy_spec_framed_byte
#print axioms memcpy_framed_ainv_stable

end Vsa.Sim
