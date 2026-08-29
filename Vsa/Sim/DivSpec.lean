import Vsa.Sim.DivSites
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

/-!
# Layer 3 — total-correctness spec for `__hidden___udivdi3` (unsigned 64-bit division)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/DivSites.lean`) into a total-correctness triple for libgcc's unsigned
64-bit division core `__hidden___udivdi3`.

We reuse the spec-independent observation consumers (`readback`, `obs_alu_*`,
`obs_btaken_*`, `obs_bnottaken_*`, `obs_jr_*`) and the `ret`-target helper
(`ret_tgt`) from `Vsa.Sim` (Muldi3Spec).

## Algorithm

Entry `0x800046ac`, `x10 = n`, `x11 = d`, `d ≠ 0`. Registers a0/a1/a2/a3 =
x10/x11/x12/x13 are the only clobbers; x1 (ra) and every other GPR are preserved
(blanket preservation conjunct). Returns via `ret` (reads x1). Result:
`x10 = n / d` (`BitVec.udiv` = Nat division), `x11 = n % d`.

Two loops: a *normalize* loop (`c0..d0`) shifting the divisor left until it is
`≥` the dividend or its sign bit is set, and a *divide* loop (`d8..ec`) doing
restoring shift-subtract long division.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate (`NotWritten`) + generic per-class helpers

`Ust` tracks the live GPRs `x10..x13`, `PC`, `x1`, `minstret`, `mem`, tick and
`GoodState`. To make preservation of *every other* register recoverable after
packaging into a `Triple` (needed by callers that stash the return address in a
scratch register like `t0`/`x5`, and by future interpreter callers that need
`s`-register / `sp` preservation), `Ust` carries a ghost snapshot
`g : (R : Register) → Option (RegisterType R)` and a blanket conjunct: every
register outside the write-set reads as its ghost value.

`NotWritten R` is the 11-way `Bool`-disequality conjunction over the union of the
tracked GPRs (`x10..x13`) and the per-step write-set / tick-set registers
(`PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip`). Each generic
frame helper consumes exactly the disequalities its class needs, so preservation
is threaded through every transition with a single helper application. -/

/-- `R` is outside the union of the tracked GPRs and every register any hot-path
step (ALU / branch / jump / tick) can write. Unfolds to an 11-way conjunction of
`(X == R) = false` `Bool` disequalities, which the read-back frame lemmas consume
directly. -/
abbrev NotWritten (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-- The blanket ghost-frame conjunct, as it appears in `Ust` and every derived
predicate: every non-written register reads as its ghost snapshot `g`. -/
abbrev Frame (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

theorem NotWritten.x10 {R : Register} (h : NotWritten R) : (Register.x10 == R) = false := h.1
theorem NotWritten.x11 {R : Register} (h : NotWritten R) : (Register.x11 == R) = false := h.2.1
theorem NotWritten.x12 {R : Register} (h : NotWritten R) : (Register.x12 == R) = false := h.2.2.1
theorem NotWritten.x13 {R : Register} (h : NotWritten R) : (Register.x13 == R) = false := h.2.2.2.1

/-- Generic ALU frame step: a variable-`R` read-back through an ALU observation
(write-set `rd, PC, minstret, nextPC, minstret_increment`, tick-set
`mcycle, mtime, mip`). `rd` is one of the tracked GPRs `x10..x13`; the caller
picks the matching disequality out of `NotWritten R` (via `NotWritten.x1{0..3}`). -/
theorem frame_alu {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWritten R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- Generic taken-branch frame step (write-set `PC, minstret, nextPC,
minstret_increment`; no `rd`). -/
theorem frame_btaken {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWritten R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

/-- Generic not-taken-branch frame step. -/
theorem frame_bnottaken {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWritten R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-- Generic `jr`/`ret` frame step (`jump_x0`: write-set `PC, minstret, nextPC,
minstret_increment`). -/
theorem frame_jr {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWritten R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## The config-level state predicate

`Ust g pc a0 a1 a2 a3 r m0 c`: standing observation at a program point — `c.σ` is
a `GoodState` with `__hidden___udivdi3` code loaded, memory pinned to `m0`, PC at
`pc`, live GPRs `x10 = a0`, `x11 = a1`, `x12 = a2`, `x13 = a3`, `x1 = r`,
`minstret` defined, tick `< 2`, and the blanket ghost-frame conjunct `hframe`:
every register outside the tracked/written set reads as the ghost snapshot `g`
(constant across the whole function — no step writes a non-tracked register). -/
structure Ust (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __hidden___udivdi3Loaded c.σ.mem
  mem : c.σ.mem = m0
  sailOut : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some a0
  a1 : c.σ.regs.get? Register.x11 = some a1
  a2 : c.σ.regs.get? Register.x12 = some a2
  a3 : c.σ.regs.get? Register.x13 = some a3
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  hframe : ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

/-! ## ALU straight-line transitions

Each is a one-step `Triple.of_step` over a `site_*` lemma, reading the successor
`Ust` fields off `ReadsLikePost` through the reused `obs_alu_*` consumers. -/

/-- `mv a2,a1` (ac → b0): `x12 := a1`. -/
theorem utr_ac_b0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2old a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046ac#64) a0 a1 a2old a3 r m0 o) (Ust g (0x800046b0#64) a0 a1 a1 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046ac c.σ c.tick c.steps (0x800046ac#64) vmi a1 hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [show a1 + sign_extend (m := 64) (0x000#12) = a1 from by rw [sext_zero]; exact BitVec.add_zero a1] at hrd

/-- `mv a1,a0` (b0 → b4): `x11 := a0`. -/
theorem utr_b0_b4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1old a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046b0#64) a0 a1old a2 a3 r m0 o) (Ust g (0x800046b4#64) a0 a0 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046b0 c.σ c.tick c.steps (0x800046b0#64) vmi a0 hSt.good hSt.pc hmi hSt.a0 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    ?_,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x11 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [show a0 + sign_extend (m := 64) (0x000#12) = a0 from by rw [sext_zero]; exact BitVec.add_zero a0] at hrd

/-- `li a0,-1` (b4 → b8): `x10 := -1`. -/
theorem utr_b4_b8 (g : (R : Register) → Option (RegisterType R))
    (a0old a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046b4#64) a0old a1 a2 a3 r m0 o)
           (Ust g (0x800046b8#64) ((0#64) + sign_extend (m := 64) (0xfff#12)) a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046b4 c.σ c.tick c.steps (0x800046b4#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩

/-- `li a3,1` (bc → c0): `x13 := 1`. -/
theorem utr_bc_c0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3old r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046bc#64) a0 a1 a2 a3old r m0 o)
           (Ust g (0x800046c0#64) a0 a1 a2 ((0#64) + sign_extend (m := 64) (0x001#12)) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046bc c.σ c.tick c.steps (0x800046bc#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩

/-- `slli a2,a2,1` (c8 → cc): `x12 := a2 <<< 1`. -/
theorem utr_c8_cc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046c8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046cc#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046c8 c.σ c.tick c.steps (0x800046c8#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shl_shamt a2] at hrd

/-- `slli a3,a3,1` (cc → d0): `x13 := a3 <<< 1`. -/
theorem utr_cc_d0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046cc#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d0#64) a0 a1 a2 (a3 <<< (1:Nat)) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046cc c.σ c.tick c.steps (0x800046cc#64) vmi a3 hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    ?_,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shl_shamt a3] at hrd

/-- `li a0,0` (d4 → d8): `x10 := 0`. -/
theorem utr_d4_d8 (g : (R : Register) → Option (RegisterType R))
    (a0old a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046d4#64) a0old a1 a2 a3 r m0 o) (Ust g (0x800046d8#64) (0#64) a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046d4 c.σ c.tick c.steps (0x800046d4#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs, ?_,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [show (0#64) + sign_extend (m := 64) (0x000#12) = (0#64) from by rw [sext_zero]; exact BitVec.add_zero (0#64)] at hrd

/-- `sub a1,a1,a2` (dc → e0): `x11 := a1 - a2`. -/
theorem utr_dc_e0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046dc#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e0#64) a0 (a1 - a2) a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046dc c.σ c.tick c.steps (0x800046dc#64) vmi a1 a2 hSt.good hSt.pc hmi hSt.a1 hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x11 hR).trans (hSt.hframe R hR)⟩

/-- `or a0,a0,a3` (e0 → e4): `x10 := a0 ||| a3`. -/
theorem utr_e0_e4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046e0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e4#64) (a0 ||| a3) a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046e0 c.σ c.tick c.steps (0x800046e0#64) vmi a0 a3 hSt.good hSt.pc hmi hSt.a0 hSt.a3 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩

/-- `srli a3,a3,1` (e4 → e8): `x13 := a3 >>> 1`. -/
theorem utr_e4_e8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046e4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e8#64) a0 a1 a2 (a3 >>> (1:Nat)) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046e4 c.σ c.tick c.steps (0x800046e4#64) vmi a3 hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    ?_,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shr_shamt a3] at hrd

/-- `srli a2,a2,1` (e8 → ec): `x12 := a2 >>> 1`. -/
theorem utr_e8_ec (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046e8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046ec#64) a0 a1 (a2 >>> (1:Nat)) a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046e8 c.σ c.tick c.steps (0x800046e8#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shr_shamt a2] at hrd

/-! ## Branch transitions (all GPRs preserved; only PC moves) -/

/-- `beqz a2` taken (b8 → f0, a2 = 0). -/
theorem utr_b8_f0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : ((0#64) == (0#64)) = true) :
    Triple (Ust g (0x800046b8#64) a0 a1 (0#64) a3 r m0 o) (Ust g (0x800046f0#64) a0 a1 (0#64) a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046b8_taken c.σ c.tick c.steps (0x800046b8#64) vmi (0#64) hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hv hSt.tick
  have hpceq : (0x800046b8#64 : BitVec 64) + sign_extend (m := 64) (0x0038#13) = (0x800046f0#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `beqz a2` not taken (b8 → bc, a2 ≠ 0). -/
theorem utr_b8_bc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a2 == (0#64)) = false) :
    Triple (Ust g (0x800046b8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046bc#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046b8_nottaken c.σ c.tick c.steps (0x800046b8#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hv hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-- `bgeu a2,a1` taken (c0 → d4, a2 ≥ a1 unsigned). -/
theorem utr_c0_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_u a2 a1 = true) :
    Triple (Ust g (0x800046c0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046c0_taken c.σ c.tick c.steps (0x800046c0#64) vmi a2 a1 hSt.good hSt.pc hmi hSt.a2 hSt.a1 hSt.loaded rfl hv hSt.tick
  have hpceq : (0x800046c0#64 : BitVec 64) + sign_extend (m := 64) (0x0014#13) = (0x800046d4#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bgeu a2,a1` not taken (c0 → c4, a2 < a1 unsigned). -/
theorem utr_c0_c4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_u a2 a1 = false) :
    Triple (Ust g (0x800046c0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046c0_nottaken c.σ c.tick c.steps (0x800046c0#64) vmi a2 a1 hSt.good hSt.pc hmi hSt.a2 hSt.a1 hSt.loaded rfl hv hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-- `blez a2` taken (c4 → d4, 0 ≥ a2 signed, i.e. a2 ≤ 0). -/
theorem utr_c4_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_s (0#64) a2 = true) :
    Triple (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046c4_taken c.σ c.tick c.steps (0x800046c4#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hv hSt.tick
  have hpceq : (0x800046c4#64 : BitVec 64) + sign_extend (m := 64) (0x0010#13) = (0x800046d4#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `blez a2` not taken (c4 → c8, 0 < a2 signed). -/
theorem utr_c4_c8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_s (0#64) a2 = false) :
    Triple (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c8#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046c4_nottaken c.σ c.tick c.steps (0x800046c4#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hv hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-- `bltu a2,a1` taken (d0 → c4, a2 < a1 unsigned): normalize-loop back-edge. -/
theorem utr_d0_c4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a2 a1 = true) :
    Triple (Ust g (0x800046d0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046d0_taken c.σ c.tick c.steps (0x800046d0#64) vmi a2 a1 hSt.good hSt.pc hmi hSt.a2 hSt.a1 hSt.loaded rfl hv hSt.tick
  have hpceq : (0x800046d0#64 : BitVec 64) + sign_extend (m := 64) (0x1ff4#13) = (0x800046c4#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bltu a2,a1` not taken (d0 → d4, a2 ≥ a1 unsigned): fall to divide loop. -/
theorem utr_d0_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a2 a1 = false) :
    Triple (Ust g (0x800046d0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046d0_nottaken c.σ c.tick c.steps (0x800046d0#64) vmi a2 a1 hSt.good hSt.pc hmi hSt.a2 hSt.a1 hSt.loaded rfl hv hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-- `bltu a1,a2` taken (d8 → e4, a1 < a2 unsigned): skip subtract. -/
theorem utr_d8_e4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a1 a2 = true) :
    Triple (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e4#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046d8_taken c.σ c.tick c.steps (0x800046d8#64) vmi a1 a2 hSt.good hSt.pc hmi hSt.a1 hSt.a2 hSt.loaded rfl hv hSt.tick
  have hpceq : (0x800046d8#64 : BitVec 64) + sign_extend (m := 64) (0x000c#13) = (0x800046e4#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bltu a1,a2` not taken (d8 → dc, a1 ≥ a2 unsigned): do subtract. -/
theorem utr_d8_dc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a1 a2 = false) :
    Triple (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046dc#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046d8_nottaken c.σ c.tick c.steps (0x800046d8#64) vmi a1 a2 hSt.good hSt.pc hmi hSt.a1 hSt.a2 hSt.loaded rfl hv hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-- `bnez a3` taken (ec → d8, a3 ≠ 0): divide-loop back-edge. -/
theorem utr_ec_d8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a3 != (0#64)) = true) :
    Triple (Ust g (0x800046ec#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046ec_taken c.σ c.tick c.steps (0x800046ec#64) vmi a3 hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hv hSt.tick
  have hpceq : (0x800046ec#64 : BitVec 64) + sign_extend (m := 64) (0x1fec#13) = (0x800046d8#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bnez a3` not taken (ec → f0, a3 = 0): fall through to ret. -/
theorem utr_ec_f0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a3 != (0#64)) = false) :
    Triple (Ust g (0x800046ec#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046f0#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046ec_nottaken c.σ c.tick c.steps (0x800046ec#64) vmi a3 hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hv hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken hobs R hR).trans (hSt.hframe R hR)⟩

/-! ## `ret` transition (f0 → r): PC → return address; GPRs preserved. -/

theorem utr_f0_ret (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (halign : r.toNat % 4 = 0) :
    Triple (Ust g (0x800046f0#64) a0 a1 a2 a3 r m0 o)
           (fun c => GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
             c.σ.regs.get? Register.x10 = some a0 ∧ c.σ.regs.get? Register.x11 = some a1 ∧
             c.σ.regs.get? Register.x1 = some r ∧ c.tick < 2 ∧
             (∀ R : Register, NotWritten R → c.σ.regs.get? R = g R)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_800046f0 c.σ c.tick c.steps (0x800046f0#64) vmi r hSt.good hSt.pc hmi hSt.ra hSt.loaded rfl htgt hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.mem, by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_jr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_jr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_jr_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    hi',
    fun R hR => (frame_jr hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_jr_pc hobs, ret_tgt r halign]

/-! ## Guard-predicate bridges (BitVec comparisons ⇒ Nat/top-bit facts) -/

theorem bgeu_true (a b : BitVec 64) (h : zopz0zKzJ_u a b = true) : b.toNat ≤ a.toNat := by
  unfold zopz0zKzJ_u at h; simp only [Sail.BitVec.toNatInt] at h
  exact Int.ofNat_le.mp (of_decide_eq_true h)

theorem bgeu_false (a b : BitVec 64) (h : zopz0zKzJ_u a b = false) : a.toNat < b.toNat := by
  unfold zopz0zKzJ_u at h; simp only [Sail.BitVec.toNatInt] at h
  have h2 : ¬ (Int.ofNat b.toNat ≤ Int.ofNat a.toNat) := of_decide_eq_false h
  rw [Int.not_le] at h2; exact Int.ofNat_lt.mp h2

theorem bltu_true (a b : BitVec 64) (h : zopz0zI_u a b = true) : a.toNat < b.toNat := by
  unfold zopz0zI_u at h; simp only [Sail.BitVec.toNatInt] at h
  exact Int.ofNat_lt.mp (of_decide_eq_true h)

theorem bltu_false (a b : BitVec 64) (h : zopz0zI_u a b = false) : b.toNat ≤ a.toNat := by
  unfold zopz0zI_u at h; simp only [Sail.BitVec.toNatInt] at h
  have h2 : ¬ (Int.ofNat a.toNat < Int.ofNat b.toNat) := of_decide_eq_false h
  rw [Int.not_lt] at h2; exact Int.ofNat_le.mp h2

theorem blez_true (a : BitVec 64) (h : zopz0zKzJ_s (0#64) a = true) : a.toInt ≤ 0 := by
  unfold zopz0zKzJ_s at h
  have := of_decide_eq_true h; simp only [BitVec.toInt_zero, ge_iff_le] at this; exact this

theorem blez_false (a : BitVec 64) (h : zopz0zKzJ_s (0#64) a = false) : 0 < a.toInt := by
  unfold zopz0zKzJ_s at h
  have h2 : ¬ (a.toInt ≤ 0) := by
    have := of_decide_eq_false h; simpa only [BitVec.toInt_zero, ge_iff_le] using this
  rw [Int.not_le] at h2; exact h2

/-- Classical case split for the `bgeu` guard (machine decides; logic is classical). -/
theorem bgeu_cases (a b : BitVec 64) : zopz0zKzJ_u a b = true ∨ zopz0zKzJ_u a b = false :=
  Bool.eq_false_or_eq_true (zopz0zKzJ_u a b)

theorem bltu_cases (a b : BitVec 64) : zopz0zI_u a b = true ∨ zopz0zI_u a b = false :=
  Bool.eq_false_or_eq_true (zopz0zI_u a b)

theorem blez_cases (a : BitVec 64) : zopz0zKzJ_s (0#64) a = true ∨ zopz0zKzJ_s (0#64) a = false :=
  Bool.eq_false_or_eq_true (zopz0zKzJ_s (0#64) a)

theorem bne_cases (a : BitVec 64) : (a != (0#64)) = true ∨ (a != (0#64)) = false :=
  Bool.eq_false_or_eq_true (a != (0#64))

theorem beq_cases (a : BitVec 64) : (a == (0#64)) = true ∨ (a == (0#64)) = false :=
  Bool.eq_false_or_eq_true (a == (0#64))

/-! ## Shift / top-bit arithmetic facts -/

/-- Left shift by 1 is exact multiplication when the top bit is clear. -/
theorem shl1_toNat (a : BitVec 64) (h : 2 * a.toNat < 2^64) :
    (a <<< (1:Nat)).toNat = a.toNat * 2 := by
  rw [BitVec.toNat_shiftLeft]; simp only [Nat.shiftLeft_eq]
  have hp : (2:Nat)^1 = 2 := by decide
  rw [hp]; omega

/-- Right shift by 1 is Nat division by 2. -/
theorem shr1_toNat (a : BitVec 64) : (a >>> (1:Nat)).toNat = a.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A `toInt ≤ 0`, nonzero `BitVec 64` has its top bit set (`≥ 2^63`). -/
theorem toInt_nonpos_top (a : BitVec 64) (h : a.toInt ≤ 0) (hne : a ≠ 0#64) : 2^63 ≤ a.toNat := by
  have hcond := BitVec.toInt_eq_toNat_cond a
  have hlt := a.isLt
  by_cases hb : 2 * a.toNat < 2^64
  · rw [if_pos hb] at hcond
    have hpos : 0 < a.toNat := by
      rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
      · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) hne
      · exact h0
    omega
  · omega

/-- Positive `toInt` means the top bit is clear (`2·toNat < 2^64`). -/
theorem toInt_pos_notop (a : BitVec 64) (h : 0 < a.toInt) : 2 * a.toNat < 2^64 := by
  have hcond := BitVec.toInt_eq_toNat_cond a
  have hlt := a.isLt
  by_cases hb : 2 * a.toNat < 2^64
  · exact hb
  · rw [if_neg hb] at hcond; omega

/-!
## Remaining: the two loops and the numeric division result (follow-up)

Everything above is fully proved (machine-stepping sites, all 24 config-level
one-step transitions `utr_*`, the guard-predicate bridges, and the shift/top-bit
arithmetic). What remains to reach the full `udivdi3_spec` postcondition
(`x10 = n / d`, `x11 = n % d`) is the pure-arithmetic loop reasoning, composed via
`Triple.loop`/`Triple.seq`. The invariants are:

**Prefix (ac → c0).** Compose `utr_ac_b0`, `utr_b0_b4`, `utr_b4_b8`,
`utr_b8_bc` (needs `d ≠ 0` ⇒ `(d == 0) = false`, from `beq_cases` + the `d ≠ 0`
hypothesis), `utr_bc_c0`. Establishes at `c0`: `a2 = d`, `a1 = n`, `a0 = -1`,
`a3 = 1`.

**Normalize loop (head `c4`, also entered from `c0`).** Guard `LoopN` = at `c0`
with `¬bgeu(a2,a1) ∧ ¬blez(a2)` (equivalently `a2.toNat < a1.toNat ∧ 0 < a2.toInt`).
Invariant: `∃ k, a2.toNat = d.toNat * 2^k ∧ a3.toNat = 2^k ∧ d.toNat * 2^k < 2^64`.
Measure: `2^64 - a2.toNat` (strictly decreases because a non-top-bit `a2` doubles
exactly, via `shl1_toNat` guarded by `toInt_pos_notop` from the `blez`-false
branch). Exit: at `d4` with `a2 = d·2^K` where `K` is minimal such that
`d·2^K ≥ n` or the top bit is set (the exact stop condition, from `bgeu`/`blez`
being true, bridged by `bgeu_true`/`blez_true`+`toInt_nonpos_top`).

**Divide loop (head `d8`).** After `utr_d4_d8` sets `a0 = 0`. Guard `LoopD` = at
`d8` with `a3 ≠ 0`. Invariant (`∃ j`):
  `a2.toNat = d.toNat * 2^j`, `a3.toNat = 2^j`, `d.toNat * 2^j < 2^64`,
  `a0.toNat % 2^(j+1) = 0`  (quotient bits so far are all above position j),
  `n.toNat = d.toNat * a0.toNat + a1.toNat`  (division progress), and
  `a1.toNat < 2 * a2.toNat`  (remainder bound).
Measure: `a3.toNat` (halves via `shr1_toNat`; `shr_lt` gives strict decrease).
The `or a0,a0,a3` step uses that bit `j` of `a0` is clear (`a0 % 2^(j+1) = 0`) to
turn the BitVec `|||` into `+ 2^j` — this needs a `Nat` lemma
`a % 2^(j+1) = 0 → a ||| 2^j = a + 2^j` (provable by `Nat.eq_of_testBit_eq` using
`Nat.testBit_two_pow_add_eq` / `_add_gt` and a `lowbits_clear`-style helper;
it was the one auxiliary not completed here). One body iteration splits on the
`bltu a1,a2` guard (`bltu_true`/`bltu_false`) and re-establishes the invariant with
`j ↦ j-1` (both loop-preserving cases verified by the arithmetic identities above).
Exit (`a3 = 0`, i.e. after the `j = 0` iteration): `a1.toNat < d.toNat` (from the
bound with `a2 = d`), so `a0 = n / d` and `a1 = n % d` by `Nat.div_mod_unique`
composed with `BitVec.toNat_udiv`/`toNat_umod`.

**Epilogue (`f0 → r`).** `utr_f0_ret` (proved) delivers `PC = r`, GPRs preserved,
`x1 = r`, mem unchanged, `GoodState`. The final `udivdi3_post` conjoins the numeric
result with the blanket-preservation conjunct (every GPR outside a0/a1/a2/a3 reads
as at entry — surfaced through the `obs_*_other` reads already threaded in each
`utr_*`).
-/

end Vsa.Sim

