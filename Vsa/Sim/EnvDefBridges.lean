import Vsa.Sim.EnvDefCompose
import Vsa.Sim.StrlenSpec
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvNewSites
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch10Part15
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch12Part06

/-!
# `EnvDefBridges` — the Shape-A straight-line machine bridges of `EnvDefCompose`

`Vsa/Sim/EnvDefCompose.lean` composed the whole `env_define` function over the real
callee contracts (`strlen`/`malloc`/`memcpy`/`realloc`), leaving its `*Contract`
theorems parameterised by NAMED machine-bridge hypotheses (`bridgeStrlenPre`,
`bridgeMallocPre`, …).  Each bridge is a straight-line `mv`/`addi`/`sd`/`ld` +
`jal callee` segment: NO call composition (that is `callSeg`'s job upstream), just the
per-instruction `StepObs` threading carrying the entry semantic facts across the arg
marshalling into the callee's entry predicate.

## The shared `mv rd,rs ; jal callee` prefix sub-shape

EVERY append/grow call prefix is the same 2-instruction idiom: one `addi`-class move
that marshals an argument into `a0`, then a `jal` that links the return address and
jumps to the callee entry.  `mvJalPrefix` factors that idiom into a reusable lemma:
given the entry state (PC at the `mv`, source register value, callee byte pins,
decode facts), it runs both steps and delivers the post-`jal` state (PC = callee
entry, `x10 = marshalled arg`, `x1 = link`, all other pins framed through).  Each
concrete bridge instantiates it and packages the callee's entry predicate.

The `jal`-marshalling helpers (`obs_jal_*`, `frame_jal_env`, `frame_alu_env`) are
reused verbatim from `EnvNewSpec` — env_new's single-malloc splice IS this same shape
(the ledger's fan-out note).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (Env_defineLoaded StrlenLoaded env_define_at_80002b1c env_define_at_80002b20
  env_define_at_80002b24 env_define_at_80002b28 env_define_at_80002b2c)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site step lemmas for the strlen prefix (`0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen`) -/

/-- Site `0x80002b1c` (`mv a0,s2` = `addi x10,x18,0`): `x10 := s2`. -/
theorem site_80002b1c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b1c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v18 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b1c hmem
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002b1c#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002b1c#64) _ (by decide) (by decide)]; exact hx18
  exact stepObs_alu σ i u (0x80002b1c#64) vminstret (0x00090513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x12#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v18 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x09#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00090513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x12#5) (regidx.Regidx 0x0a#5) v18
      (afterNextPC (afterPrelude σ) (0x80002b1c#64))
      (sigma3_alu σ (0x80002b1c#64) Register.x10 (v18 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x18 _ v18 hx18₂) (wX_bits_x10 _ (v18 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002b20` (`jal strlen`): `x1 := 0x80002b24`, `PC := 0x80006cf0`. -/
theorem site_80002b20_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b20#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x0041d0#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b20 hmem
  exact stepObs_jal σ i u (0x80002b20#64) vminstret (0x1d0040ef#32) (0x0041d0#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002b20#64) 4)
    (0xef#8) (0x40#8) (0x00#8) (0x1d#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_1d0040ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80002b20#64) 4)) hi

/-! ## Site step lemmas for the malloc prefix
(`0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal malloc`) -/

/-- Site `0x80002b24` (`addi s0,a0,1`): `x8 := a0 + 1`. -/
theorem site_80002b24_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b24#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 (v10 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b24 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002b24#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002b24#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002b24#64) vminstret (0x00150413#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v10 + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x04#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00150413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x08#5) v10
      (afterNextPC (afterPrelude σ) (0x80002b24#64))
      (sigma3_alu σ (0x80002b24#64) Register.x8 (v10 + sign_extend (m := 64) (0x001#12)))
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x8 _ (v10 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002b28` (`mv a0,s0` = `addi x10,x8,0`): `x10 := s0`. -/
theorem site_80002b28_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b28#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v8 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b28 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002b28#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002b28#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80002b28#64) vminstret (0x00040513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v8 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00040513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5) v8
      (afterNextPC (afterPrelude σ) (0x80002b28#64))
      (sigma3_alu σ (0x80002b28#64) Register.x10 (v8 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x10 _ (v8 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002b2c` (`jal malloc`): `x1 := 0x80002b30`, `PC := 0x80004790`. -/
theorem site_80002b2c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b2c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x001c64#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b2c hmem
  exact stepObs_jal σ i u (0x80002b2c#64) vminstret (0x465010ef#32) (0x001c64#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002b2c#64) 4)
    (0xef#8) (0x10#8) (0x50#8) (0x46#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_465010ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80002b2c#64) 4)) hi

/-! ## The strlen-prefix run: `0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen`

Chains the two site steps.  From a state at `0x80002b1c` with `x18 = namePtr`, runs to a
state at the strlen entry `0x80006cf0` with `x10 = namePtr`, `x1 = 0x80002b24` (the link),
memory unchanged, and `minstret` defined.  `x18` is preserved by both steps (the `mv`
writes `x10`, the `jal` writes `x1`), and memory is untouched, so all entry semantic facts
carry through unchanged. -/
theorem strlenPrefix_run
    (σ : MState) (i u : Nat) (vminstret namePtr : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x80002b1c#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx18 : σ.regs.get? Register.x18 = some namePtr)
    (hmem : Env_defineLoaded σ.mem) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 1 + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      σ'.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64) ∧
      σ'.regs.get? Register.x10 = some namePtr ∧
      σ'.regs.get? Register.x1 = some (0x80002b24#64 : BitVec 64) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      -- FRAME (x2/sp, x8/s0 preserved explicitly — `NotWrittenEnv` conservatively
      -- excludes both, but the two-step prefix writes only `x10` (mv) and `x1` (jal)):
      σ'.regs.get? Register.x2 = σ.regs.get? Register.x2 ∧
      σ'.regs.get? Register.x8 = σ.regs.get? Register.x8 ∧
      -- FRAME (blanket): every `NotWrittenEnv` register — `x3`/gp and every callee-saved
      -- register `s1..s11` (x9,x19..x27) — is preserved by the two-step prefix.
      (∀ (R : Register), NotWrittenEnv R → σ'.regs.get? R = σ.regs.get? R) := by
  -- step 1: mv a0,s2
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002b1c_ed σ i u (0x80002b1c#64) vminstret namePtr hG hpc hminstret hx18 hmem rfl hi
  have hstep1 : Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ := hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002b20#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002b1c#64 : BitVec 64) 4 = (0x80002b20#64 : BitVec 64) from by decide] at this
  have hx10_1 : σ1.regs.get? Register.x10 = some namePtr := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (namePtr + sign_extend (m := 64) (0x000#12) : BitVec 64) = namePtr from by
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
      rw [this, BitVec.add_zero]] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hmem1e : σ1.mem = σ.mem := hmem1
  have hloaded1 : Env_defineLoaded σ1.mem := hmem1e ▸ hmem
  -- step 2: jal strlen
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002b20_ed σ1 i1 (u + 1) (0x80002b20#64) vmi1 hG1 hpc1 hmi1 hloaded1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, u + 1⟩ ⟨σ2, i2, u + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64) := by
    have := obs_jal_pc_env hobs2
    rwa [show (0x80002b20#64 : BitVec 64) + sign_extend (m := 64) (0x0041d0#21)
      = (0x80006cf0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some namePtr :=
    obs_jal_other_env hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_1
  have hra_2 : σ2.regs.get? Register.x1 = some (0x80002b24#64 : BitVec 64) := by
    have := obs_jal_rd_env hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002b20#64 : BitVec 64) 4 = (0x80002b24#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hmi2 : ∃ w, σ2.regs.get? Register.minstret = some w := obs_jal_minstret_env hobs2
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2, hmem1e]
  -- Per-register frame across the two prefix steps, for ANY register the prefix does
  -- not write (alu writes x10; jal writes x1).  `x2`/`x8` are excluded by
  -- `NotWrittenEnv`, so we frame them directly through the two `sigmaPost` readbacks.
  have hstepframe : ∀ (R : Register),
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      (Register.x10 == R) = false → (Register.x1 == R) = false →
      σ2.regs.get? R = σ.regs.get? R := by
    intro R hmc hmt hmip hmis hpc' hnpc hmii hne10 hne1
    have e2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc hmt hmip).trans
        (get?_sigmaPost_jal σ1 (0x80002b20#64) vmi1 (0x0041d0#21) Register.x1
          (BitVec.addInt (0x80002b20#64) 4) R hmis hpc' hne1 hnpc hmii)
    have e1 : σ1.regs.get? R = σ.regs.get? R :=
      (hobs1.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ (0x80002b1c#64) vminstret Register.x10
          (namePtr + sign_extend (m := 64) (0x000#12)) R hmis hpc' hne10 hnpc hmii)
    exact e2.trans e1
  have hx2 : σ2.regs.get? Register.x2 = σ.regs.get? Register.x2 :=
    hstepframe Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hx8 : σ2.regs.get? Register.x8 = σ.regs.get? Register.x8 :=
    hstepframe Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  -- blanket NotWrittenEnv frame (specialises `hstepframe`).
  have hframe : ∀ (R : Register), NotWrittenEnv R → σ2.regs.get? R = σ.regs.get? R := by
    intro R hR
    obtain ⟨h1, h2, h8, h10, hpc', hnpc, hmis, hmii, hmc, hmt, hmip⟩ := hR
    exact hstepframe R hmc hmt hmip hmis hpc' hnpc hmii h10 h1
  refine ⟨σ2, i2, Steps.trans (Steps.single hstep1) (Steps.single hstep2), hi2, hG2, hmem2e,
    hpc2, hx10_2, hra_2, hmi2, hx2, hx8, hframe⟩

/-! ## `bridgeStrlenPre` discharged — FRAME-CARRYING

The append-path entry predicate `AppendStrlenEntry` supplies exactly what `strlen_pre`
needs about the `name` argument (`StrlenLoaded`, `StrRegions`, 8-alignment, `CString`)
plus the machine entry state at `0x80002b1c` (`x18 = namePtr`, `mem = m0`, tick, minstret),
AND the **carried caller-frame** (`EnvDefFrame`: sp/`StackOK`, gp, ABI callee-saved tie,
`AInv`) that the downstream malloc entry will need — the assertion-carried framing the
composed contract's strlen seam now demands.

`bridgeStrlenPre_closed` runs the two-instruction prefix (`strlenPrefix_run`), repackaging
the post-state as `strlen_pre namePtr 0x80002b24 nameStr m0 ∧ EnvDefFrame …`.  The frame
survives because the prefix writes only `x10` (mv) and `x1` (jal): sp/gp/callee-saveds are
framed through by `strlenPrefix_run`'s frame clauses, and `AInv` survives by its
stability under (mem-agree ∧ gp-agree) — the same `MallocContract`-interface property
`env_new` draws on (`EnvNewSpec` line 496).  This discharges `envDefAppendContract`'s
frame-carrying `bridgeStrlenPre` hypothesis. -/

/-- Append-path entry predicate at `0x80002b1c`: the `strlen` argument facts PLUS the
carried caller-frame ghosts (`sp`/`gpv`/`gm`/`exts`/`AInv`, with `StackOK`). -/
def AppendStrlenEntry (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (namePtr : BitVec 64) (nameStr : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Env_defineLoaded c.σ.mem ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80002b1c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x18 = some namePtr ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  StrRegions namePtr nameStr.length ∧ namePtr.toNat % 8 = 0 ∧
  CString m0 namePtr.toNat nameStr ∧
  EnvDefFrame SL gpv headroom AInv exts sp gm c

/-- **`bridgeStrlenPre` discharged (frame-carrying).**  From `AppendStrlenEntry` (args +
carried frame), the `mv a0,s2 ; jal strlen` prefix lands
`strlen_pre namePtr 0x80002b24 nameStr m0 ∧ EnvDefFrame …` at the strlen entry.  The
`hAInvStable` hypothesis is `AInv`'s stability under (mem-agree ∧ gp-agree) — the
`MallocContract`-interface property; the prefix preserves both, so `AInv` survives. -/
theorem bridgeStrlenPre_closed (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (namePtr : BitVec 64) (nameStr : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) → AInv σa exts → AInv σb exts) :
    Triple (AppendStrlenEntry SL gpv headroom AInv exts sp gm namePtr nameStr m0)
      (fun c => strlen_pre namePtr (0x80002b24#64 : BitVec 64) nameStr m0 c ∧
        EnvDefFrame SL gpv headroom AInv exts sp gm c) := by
  intro c hpre
  obtain ⟨hG, hloadedD, hloadedS, hmem, hpc, hx18, ⟨vmi, hmi⟩, htick, hreg, halign8, hcstr,
    hFrame⟩ := hpre
  obtain ⟨hsp, hstackOK, hgp, hAbi, hAInv, htickF⟩ := hFrame
  have hloadedD' : Env_defineLoaded c.σ.mem := hloadedD
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hpc', hx10', hra', hmi', hx2', hx8', hframe'⟩ :=
    strlenPrefix_run c.σ c.tick c.steps vmi namePtr hG hpc hmi hx18 hloadedD' htick
  -- gp (x3) is `NotWrittenEnv`; frame it through the prefix.
  have hgp' : σ'.regs.get? Register.x3 = some gpv := by
    rw [hframe' Register.x3 (by decide)]; exact hgp
  refine ⟨⟨σ', i', c.steps + 1 + 1⟩, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · -- strlen_pre
    refine ⟨hG', ?_, ?_, hpc', hx10', hra', hmi', ?_, hreg, halign8, ?_, ?_⟩
    · rw [hmem', hmem]; rw [hmem] at hloadedS; exact hloadedS
    · rw [hmem', hmem]
    · exact hi'
    · exact hcstr
    · decide
  · -- EnvDefFrame : sp/StackOK/gp preserved (register frame); AInv survives by stability
    refine ⟨?_, hstackOK, hgp', ?_, ?_, hi'⟩
    · -- x2 = sp
      rw [hx2']; exact hsp
    · -- ABI callee-saved tie: each AbiPreserved R is either x2 (sp), x8 (s0), or NotWrittenEnv
      intro R hR
      by_cases h2 : R = Register.x2
      · subst h2; rw [hx2']; exact hAbi Register.x2 hR
      by_cases h8 : R = Register.x8
      · subst h8; rw [hx8']; exact hAbi Register.x8 hR
      -- R is an AbiPreserved register other than x2/x8 ⇒ NotWrittenEnv R
      have hNW : NotWrittenEnv R :=
        ⟨abi_ne (by decide) hR, beq_false_of_ne' h2, beq_false_of_ne' h8,
          abi_ne (by decide) hR, abi_ne (by decide) hR, abi_ne (by decide) hR,
          abi_ne (by decide) hR, abi_ne (by decide) hR, abi_ne (by decide) hR,
          abi_ne (by decide) hR, abi_ne (by decide) hR⟩
      rw [hframe' R hNW]; exact hAbi R hR
    · -- AInv survives: mem unchanged, gp preserved ⇒ stability applies
      refine hAInvStable c.σ σ' ?_ ?_ hAInv
      · rw [hgp', hgp]
      · intro a; rw [hmem']

#print axioms bridgeStrlenPre_closed

/-! ## The malloc-prefix run:
`0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal malloc`

Chains the three site steps.  From a state at `0x80002b24` with `x10 = len` (the strlen
result), runs to a state at `mallocEntry = 0x80004790` with `x10 = len+1`, `x8 = len+1`
(`s0`, the saved size), `x1 = 0x80002b30` (link), memory unchanged, minstret defined, and a
FRAME clause: every register the three steps do not write (`x8` by the addi, `x10` by the
mv, `x1` by the jal) is preserved — in particular `x2`/sp and `x3`/gp and every OTHER
callee-saved.  `x8` is the one callee-saved the prefix rewrites (to the malloc size), so the
malloc-entry ABI ghost differs from the entry ghost only there. -/
theorem mallocPrefix_run
    (σ : MState) (i u : Nat) (vminstret vlen : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x80002b24#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vlen)
    (hmem : Env_defineLoaded σ.mem) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 1 + 1 + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      σ'.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
      σ'.regs.get? Register.x10 = some (vlen + 1#64) ∧
      σ'.regs.get? Register.x8 = some (vlen + 1#64) ∧
      σ'.regs.get? Register.x1 = some (0x80002b30#64 : BitVec 64) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      -- FRAME: any register outside the write set {x8, x10, x1} + control is preserved.
      (∀ (R : Register),
        (Register.mcycle == R) = false → (Register.mtime == R) = false →
        (Register.mip == R) = false → (Register.minstret == R) = false →
        (Register.PC == R) = false → (Register.nextPC == R) = false →
        (Register.minstret_increment == R) = false →
        (Register.x8 == R) = false → (Register.x10 == R) = false →
        (Register.x1 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  have hsext1 : (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hsext0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  -- step 1: addi s0,a0,1  ⇒ x8 := len+1
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002b24_ed σ i u (0x80002b24#64) vminstret vlen hG hpc hminstret hx10 hmem rfl hi
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002b28#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002b24#64 : BitVec 64) 4 = (0x80002b28#64 : BitVec 64) from by decide] at this
  have hx8_1 : σ1.regs.get? Register.x8 = some (vlen + 1#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hsext1] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hloaded1 : Env_defineLoaded σ1.mem := hmem1 ▸ hmem
  -- step 2: mv a0,s0  ⇒ x10 := s0 = len+1
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002b28_ed σ1 i1 (u + 1) (0x80002b28#64) vmi1 (vlen + 1#64) hG1 hpc1 hmi1 hx8_1 hloaded1 rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002b2c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80002b28#64 : BitVec 64) 4 = (0x80002b2c#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some (vlen + 1#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hsext0, BitVec.add_zero] at this
  have hx8_2 : σ2.regs.get? Register.x8 = some (vlen + 1#64) := by
    have := obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
    exact this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hloaded2 : Env_defineLoaded σ2.mem := hmem2 ▸ hloaded1
  -- step 3: jal malloc  ⇒ x1 := 0x80002b30, PC := mallocEntry
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002b2c_ed σ2 i2 (u + 1 + 1) (0x80002b2c#64) vmi2 hG2 hpc2 hmi2 hloaded2 rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) := by
    have := obs_jal_pc_env hobs3
    rwa [show (0x80002b2c#64 : BitVec 64) + sign_extend (m := 64) (0x001c64#21)
      = (BitVec.ofNat 64 mallocEntry) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_3 : σ3.regs.get? Register.x10 = some (vlen + 1#64) :=
    obs_jal_other_env hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_2
  have hx8_3 : σ3.regs.get? Register.x8 = some (vlen + 1#64) :=
    obs_jal_other_env hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx8_2
  have hra_3 : σ3.regs.get? Register.x1 = some (0x80002b30#64 : BitVec 64) := by
    have := obs_jal_rd_env hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002b2c#64 : BitVec 64) 4 = (0x80002b30#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hmi3 : ∃ w, σ3.regs.get? Register.minstret = some w := obs_jal_minstret_env hobs3
  have hmem3e : σ3.mem = σ.mem := by rw [hmem3, hmem2, hmem1]
  -- frame across the three steps
  have hframe : ∀ (R : Register),
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      (Register.x8 == R) = false → (Register.x10 == R) = false →
      (Register.x1 == R) = false →
      σ3.regs.get? R = σ.regs.get? R := by
    intro R hmc hmt hmip hmis hpc' hnpc hmii hne8 hne10 hne1
    have e3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmc hmt hmip).trans
        (get?_sigmaPost_jal σ2 (0x80002b2c#64) vmi2 (0x001c64#21) Register.x1
          (BitVec.addInt (0x80002b2c#64) 4) R hmis hpc' hne1 hnpc hmii)
    have e2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ1 (0x80002b28#64) vmi1 Register.x10
          ((vlen + 1#64) + sign_extend (m := 64) (0x000#12)) R hmis hpc' hne10 hnpc hmii)
    have e1 : σ1.regs.get? R = σ.regs.get? R :=
      (hobs1.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ (0x80002b24#64) vminstret Register.x8
          (vlen + sign_extend (m := 64) (0x001#12)) R hmis hpc' hne8 hnpc hmii)
    exact (e3.trans e2).trans e1
  exact ⟨σ3, i3, Steps.trans (Steps.single hs1) (Steps.trans (Steps.single hs2) (Steps.single hs3)),
    hi3, hG3, hmem3e, hpc3, hx10_3, hx8_3, hra_3, hmi3, hframe⟩

/-! ## `bridgeMallocPre` discharged — FRAME-CARRYING

`bridgeMallocPre`'s source is `strlen_post 0x80002b24 nameStr m0 ∧ EnvDefFrame …` (the
frame-carrying strlen seam).  The `addi;mv;jal malloc` prefix marshals `len+1` into `a0`
and lands `MallocContract.spec`'s entry predicate.  The malloc size is `nMalloc = len+1`
where `len = nameStr.length` (from `strlen_post`'s `x10 = ofNat len`); the return address
is `0x80002b30`; `sp`/`gp`/`AInv` come straight from the carried `EnvDefFrame`.  The one
callee-saved the prefix rewrites is `x8`/`s0` (holds the size across the malloc call), so the
malloc-entry ABI ghost `g'` agrees with the entry ghost `gm` everywhere except `x8`. -/
theorem bridgeMallocPre_closed (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm g' : (R : Register) → Option (RegisterType R))
    (nameStr : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- the malloc-entry ABI ghost `g'` agrees with the strlen-frame ghost `gm` on every
    -- callee-saved register EXCEPT `x8`/s0 (which the `addi` overwrites with the size):
    (hg'x8 : g' Register.x8 = some (BitVec.ofNat 64 (nameStr.length + 1)))
    (hg'other : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → g' R = gm R)
    (hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) → AInv σa exts → AInv σb exts)
    (hloaded : ∀ (mem : Std.ExtHashMap Nat (BitVec 8)), StrlenLoaded mem → Env_defineLoaded mem)
    (hstrlenLoaded : StrlenLoaded m0) :
    Triple
      (fun c => strlen_post (0x80002b24#64 : BitVec 64) nameStr m0 c ∧
        EnvDefFrame SL gpv headroom AInv exts sp gm c)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (nameStr.length + 1)) ∧
        c.σ.regs.get? Register.x1 = some (0x80002b30#64 : BitVec 64) ∧
          (0x80002b30#64 : BitVec 64).toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g' R) ∧
        AInv c.σ exts ∧ c.σ.mem = m0) := by
  intro c hpre
  obtain ⟨hpost, hFrame⟩ := hpre
  obtain ⟨hG, hpc, hx10, hra, hmem⟩ := hpost
  obtain ⟨hsp, hstackOK, hgp, hAbi, hAInv, htick⟩ := hFrame
  obtain ⟨vmi, hmi⟩ : ∃ v, c.σ.regs.get? Register.minstret = some v := hG.minstret
  have hloadedD : Env_defineLoaded c.σ.mem := by rw [hmem]; exact hloaded m0 hstrlenLoaded
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hpc', hx10', hx8', hra', hmi', hframe'⟩ :=
    mallocPrefix_run c.σ c.tick c.steps vmi (BitVec.ofNat 64 nameStr.length) hG hpc hmi hx10
      hloadedD htick
  -- gp (x3): frame through the prefix (x3 outside the {x8,x10,x1}+control write set).
  have hframeReg : ∀ (R : Register),
      (Register.x8 == R) = false → (Register.x10 == R) = false → (Register.x1 == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      σ'.regs.get? R = c.σ.regs.get? R :=
    fun R h8 h10 h1 hmc hmt hmip hmis hpc' hnpc hmii =>
      hframe' R hmc hmt hmip hmis hpc' hnpc hmii h8 h10 h1
  have hgp' : σ'.regs.get? Register.x3 = some gpv := by
    rw [hframeReg Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgp
  have hsp' : σ'.regs.get? Register.x2 = some sp := by
    rw [hframeReg Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp
  -- len = nameStr.length; the strlen result `x10 = ofNat len` gives `vlen + 1 = ofNat (len+1)`.
  have hlen1 : (BitVec.ofNat 64 nameStr.length + 1#64 : BitVec 64)
      = BitVec.ofNat 64 (nameStr.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  refine ⟨⟨σ', i', c.steps + 1 + 1 + 1⟩, ?_, ?_⟩
  · cases c; exact hsteps
  · refine ⟨hG', hi', hpc', ?_, ?_, ?_, hsp', hstackOK, hgp', ?_, ?_, ?_⟩
    · rw [hx10', hlen1]
    · rw [hra']
    · decide
    · -- ABI tie to `g'` (= `gm` off x8, = len+1 at x8)
      intro R hR
      by_cases hb : R = Register.x8
      · -- R = x8: value is len+1 = g' x8
        subst hb; rw [hx8', hlen1, hg'x8]
      · -- R ≠ x8: preserved through the prefix; g' R = gm R
        rw [hframeReg R (beq_false_of_ne' hb)
          (abi_ne (by decide) hR) (abi_ne (by decide) hR)
          (abi_ne (by decide) hR) (abi_ne (by decide) hR) (abi_ne (by decide) hR)
          (abi_ne (by decide) hR) (abi_ne (by decide) hR) (abi_ne (by decide) hR)
          (abi_ne (by decide) hR)]
        rw [hg'other R hR hb]; exact hAbi R hR
    · -- AInv survives (mem unchanged, gp preserved)
      refine hAInvStable c.σ σ' ?_ ?_ hAInv
      · rw [hgp', hgp]
      · intro a; rw [hmem']
    · -- mem = m0
      rw [hmem']; exact hmem

#print axioms bridgeMallocPre_closed

end Vsa.Sim
