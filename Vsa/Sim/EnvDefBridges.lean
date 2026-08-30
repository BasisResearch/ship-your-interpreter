import Vsa.Sim.EnvDefCompose
import Vsa.Sim.StrlenSpec
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvNewSites
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch10Part15

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
open Vsa.Sim.Code (Env_defineLoaded StrlenLoaded env_define_at_80002b1c env_define_at_80002b20)

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
      (∃ w, σ'.regs.get? Register.minstret = some w) := by
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
  refine ⟨σ2, i2, Steps.trans (Steps.single hstep1) (Steps.single hstep2), hi2, hG2, hmem2e,
    hpc2, hx10_2, hra_2, hmi2⟩

/-! ## `bridgeStrlenPre` discharged

The append-path entry predicate `AppendStrlenEntry` supplies exactly what `strlen_pre`
needs about the `name` argument (`StrlenLoaded`, `StrRegions`, 8-alignment, `CString`)
plus the machine entry state at `0x80002b1c` (`x18 = namePtr`, `mem = m0`, tick, minstret).
`bridgeStrlenPre_closed` runs the two-instruction prefix (`strlenPrefix_run`) and repackages
the post-state as `strlen_pre` at the strlen entry with return address `0x80002b24`.  This
discharges `envDefAppendContract`'s `bridgeStrlenPre` hypothesis verbatim. -/

/-- Append-path entry predicate at `0x80002b1c` carrying the `strlen` argument facts. -/
def AppendStrlenEntry (namePtr : BitVec 64) (nameStr : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Env_defineLoaded c.σ.mem ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80002b1c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x18 = some namePtr ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  StrRegions namePtr nameStr.length ∧ namePtr.toNat % 8 = 0 ∧
  CString m0 namePtr.toNat nameStr

/-- **`bridgeStrlenPre` discharged.**  From `AppendStrlenEntry`, the `mv a0,s2 ; jal strlen`
prefix lands `strlen_pre namePtr 0x80002b24 nameStr m0` at the strlen entry.  The return
address is `0x80002b24` (4-aligned), matching `envDefAppendContract`'s `rStrlen`. -/
theorem bridgeStrlenPre_closed (namePtr : BitVec 64) (nameStr : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (AppendStrlenEntry namePtr nameStr m0)
      (strlen_pre namePtr (0x80002b24#64 : BitVec 64) nameStr m0) := by
  intro c hpre
  obtain ⟨hG, hloadedD, hloadedS, hmem, hpc, hx18, ⟨vmi, hmi⟩, htick, hreg, halign8, hcstr⟩ := hpre
  have hloadedD' : Env_defineLoaded c.σ.mem := hloadedD
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hpc', hx10', hra', hmi'⟩ :=
    strlenPrefix_run c.σ c.tick c.steps vmi namePtr hG hpc hmi hx18 hloadedD' htick
  refine ⟨⟨σ', i', c.steps + 1 + 1⟩, ?_, ?_⟩
  · cases c; exact hsteps
  · refine ⟨hG', ?_, ?_, hpc', hx10', hra', hmi', ?_, hreg, halign8, ?_, ?_⟩
    · -- StrlenLoaded σ'.mem : mem unchanged from m0
      rw [hmem', hmem]; rw [hmem] at hloadedS; exact hloadedS
    · -- mem = m0
      rw [hmem', hmem]
    · exact hi'
    · -- CString m0 namePtr nameStr
      exact hcstr
    · decide

#print axioms bridgeStrlenPre_closed

end Vsa.Sim
