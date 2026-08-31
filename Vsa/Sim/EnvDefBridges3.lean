import Vsa.Sim.EnvDefCompose
import Vsa.Sim.EnvDefBridges
import Vsa.Sim.EnvDefBridges2
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvDefSpec4
import Vsa.Sim.ReallocSpec
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueSites
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.EnvGetSpec6
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch04Part01
import Vsa.Sim.DecodeTable.Batch05Part20
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch12Part29
import Vsa.Sim.DecodeTable.Batch03Part26
import Vsa.Sim.DecodeTable.Batch04Part02

/-!
# `EnvDefBridges3` — the grow-path `bridgeNamesToVals` machine bridge + the
`GrowEnvEntry` struct-field carrier

`Vsa/Sim/EnvDefCompose.lean`'s `envDefGrowContract` leaves the grow path's inter-call
staging as the named hypothesis `bridgeNamesToVals`, whose source is the FIRST realloc's
post (`ReallocPost(names) ∧ ReallocGrowResult(names)`) and whose target is the SECOND
realloc's entry predicate `ReallocPre(vals)`.  The prefix `0x80002ba4..0x80002bbc` reads
`Env`-struct fields, stores the new `names` pointer, and computes the `vals` realloc args:

```
80002ba4  lw   a5,4(s4)     -- x15 := env->cap   (= newcap, from bridgeCapCompute's sw)
80002ba8  sd   a0,8(s4)     -- env->names := a0  (the realloc(names) result pointer)
80002bac  ld   a0,16(s4)    -- x10 := env->vals  (pValsOld, the realloc(vals) arg p)
80002bb0  slli a1,a5,1      -- x11 := newcap*2
80002bb4  add  a1,a1,a5     -- x11 := newcap*3
80002bb8  slli a1,a1,3      -- x11 := newcap*24  (the realloc(vals) arg n)
80002bbc  jal  realloc      -- x1 := 0x80002bc0, PC := reallocEntry
```

## The `GrowEnvEntry` struct-field carrier (item 1)

`bridgeCapCompute`'s `GrowCapEntry` only pinned the cap REGISTER `x15`.  This staging
bridge additionally READS the `Env`-struct field CONTENTS (`env->cap` at `s4+4`,
`env->vals` at `s4+16`), which the cap-compute source did not expose.  `GrowEnvEntry`
is the additive frame-carrying carrier that pins those field contents (as `read64`/`read32`
facts) alongside the `EnvDefFrame` caller-frame — exactly the `envDefStrlenFramed`/
`bridgeCapCompute_closed` precedent.  The pinned struct words survived the first realloc
because they live in the caller's `Env` struct (public memory, disjoint from the realloc'd
extent), so the realloc post's `HeapPublicFrame` outside-clause preserves them; the carrier
takes them as data (the caller/dispatch knows the `Env` layout and its field values).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (Env_defineLoaded env_define_at_80002ba4 env_define_at_80002ba8
  env_define_at_80002bac env_define_at_80002bb0 env_define_at_80002bb4 env_define_at_80002bb8
  env_define_at_80002bbc)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site step lemmas for the names→vals staging prefix -/

/-- Site `0x80002ba4` (`lw a5,4(s4)`): `x15 := sign_extend(env->cap)` (4-byte load at s4+4). -/
theorem site_80002ba4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ba4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x004#12)).toNat)
    (hhiram : (v20 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (v20 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v20 + sign_extend (m := 64) (0x004#12)).toNat)
    (halign : (v20 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (h0 : σ.mem[(v20 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (h1 : σ.mem[(v20 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v20 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v20 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ba4 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002ba4#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002ba4#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_alu σ i u (0x80002ba4#64) vminstret (0x004a2783#32)
    (instruction.LOAD (0x004#12, regidx.Regidx 0x14#5, regidx.Regidx 0x0f#5, false, 4))
    Register.x15 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0x27#8) (0x4a#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_004a2783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80002ba4#64) (0x004#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002ba4#64) Register.x15
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      v20 b0 b1 b2 b3 hG (rX_bits_x20 _ v20 hx20₂)
      (wX_bits_x15 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002ba8` (`sd a0,8(s4)`): store `x10` (8 bytes) at `s4+8` = `env->names`. -/
theorem site_80002ba8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ba8#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v20 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v20 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v20 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002ba8#64)).mem
        (v20 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v10) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ba8#64)).mem
          (v20 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v10))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ba8 hmem
  exact stepObs_store σ i u (0x80002ba8#64) vminstret (0x00aa3423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x14#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ba8#64)).mem
      (v20 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v10))
    (0x23#8) (0x34#8) (0xaa#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00aa3423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002ba8#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x14#5)
      v20 v10 hG
      (rX_bits_x20 _ v20
        (by rw [get?_afterNextPC σ (0x80002ba8#64) _ (by decide) (by decide)]; exact hx20))
      (rX_bits_x10 _ v10
        (by rw [get?_afterNextPC σ (0x80002ba8#64) _ (by decide) (by decide)]; exact hx10))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002bac` (`ld a0,16(s4)`): `x10 := sign_extend(env->vals)` (8-byte load at s4+16). -/
theorem site_80002bac_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002bac#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v20 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v20 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v20 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v20 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (h1 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002bac hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002bac#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002bac#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_alu σ i u (0x80002bac#64) vminstret (0x010a3503#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x14#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x35#8) (0x0a#8) (0x01#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_010a3503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002bac#64) (0x010#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002bac#64) Register.x10
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v20 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x20 _ v20 hx20₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002bb0` (`slli a1,a5,1`): `x11 := x15 <<< 1`. -/
theorem site_80002bb0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002bb0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002bb0 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002bb0#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002bb0#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002bb0#64) vminstret (0x00179593#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0b#5, sop.SLLI))
    Register.x11 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x01#6) 5 0)) (0x93#8) (0x95#8) (0x17#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00179593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x01#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5) v15
      (afterNextPC (afterPrelude σ) (0x80002bb0#64))
      (sigma3_alu σ (0x80002bb0#64) Register.x11 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
      (rX_bits_x15 _ v15 hx15₂) (wX_bits_x11 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x01#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002bb4` (`add a1,a1,a5`): `x11 := x11 + x15`. -/
theorem site_80002bb4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002bb4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 (v11 + v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002bb4 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002bb4#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002bb4#64) _ (by decide) (by decide)]; exact hx11
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002bb4#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002bb4#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002bb4#64) vminstret (0x00f585b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, rop.ADD))
    Register.x11 (v11 + v15) (0xb3#8) (0x85#8) (0xf5#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00f585b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5)
      v11 v15 (afterNextPC (afterPrelude σ) (0x80002bb4#64))
      (sigma3_alu σ (0x80002bb4#64) Register.x11 (v11 + v15))
      (rX_bits_x11 _ v11 hx11₂) (rX_bits_x15 _ v15 hx15₂) (wX_bits_x11 _ (v11 + v15)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002bb8` (`slli a1,a1,3`): `x11 := x11 <<< 3`. -/
theorem site_80002bb8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002bb8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (shift_bits_left v11 (Sail.BitVec.extractLsb (0x03#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002bb8 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002bb8#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002bb8#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x80002bb8#64) vminstret (0x00359593#32)
    (instruction.SHIFTIOP (0x03#6, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, sop.SLLI))
    Register.x11 (shift_bits_left v11 (Sail.BitVec.extractLsb (0x03#6) 5 0)) (0x93#8) (0x95#8) (0x35#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00359593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x03#6) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
      (afterNextPC (afterPrelude σ) (0x80002bb8#64))
      (sigma3_alu σ (0x80002bb8#64) Register.x11 (shift_bits_left v11 (Sail.BitVec.extractLsb (0x03#6) 5 0)))
      (rX_bits_x11 _ v11 hx11₂) (wX_bits_x11 _ (shift_bits_left v11 (Sail.BitVec.extractLsb (0x03#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002bbc` (`jal realloc`): `x1 := 0x80002bc0`, `PC := reallocEntry`. -/
theorem site_80002bbc_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002bbc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x0026c0#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002bbc hmem
  exact stepObs_jal σ i u (0x80002bbc#64) vminstret (0x6c0020ef#32) (0x0026c0#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002bbc#64) 4)
    (0xef#8) (0x20#8) (0x00#8) (0x6c#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_6c0020ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80002bbc#64) 4)) hi

/-! ## The names→vals staging prefix run: `0x80002ba4..0x80002bbc`

Chains all seven steps.  From a state at `0x80002ba4` with `x20 = s4Ptr` (`env` base),
`x10 = pNamesNew` (the realloc(names) result), and the pinned struct fields
`env->cap = read32 m0 (s4+4)` / `env->vals = read64 m0 (s4+16)`, runs to `reallocEntry`
with:
* `x10 = pValsOld` (`env->vals`, the realloc(vals) arg `p`),
* `x11 = env->cap * 24` (the machine shift/add result, realloc(vals) arg `n`),
* `x1 = 0x80002bc0` (link),
* memory = the input memory with `env->names` (word at `s4+8`) overwritten by `pNamesNew`
  (`= writeMap8 m0 (s4+8) (sdData_val pNamesNew)`),
* every register outside the write set `{x15, x10, x11, x1}` + control preserved (in
  particular `x2`/sp, `x3`/gp and every other callee-saved).

The `env->vals` read at `s4+16` survives the intervening `sd` at `s4+8` because the two
8-byte windows `[s4+8,s4+16)` / `[s4+16,s4+24)` are disjoint (`read64_writeMap8_disjoint_eg6`).
The `env->cap` read at `s4+4` happens BEFORE the `sd`, so it reads `m0` directly. -/
theorem namesToValsPrefix_run
    (σ : MState) (i u : Nat) (vminstret s4Ptr pNamesNew : BitVec 64)
    (c0 c1 c2 c3 : BitVec 8) (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x80002ba4#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some s4Ptr)
    (hx10 : σ.regs.get? Register.x10 = some pNamesNew)
    (hmem : Env_defineLoaded σ.mem)
    -- the pinned struct-field CONTENTS (byte pins in the current memory):
    -- env->cap at s4+4 (4 bytes), env->vals at s4+16 (8 bytes).
    (hcapAddr : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat = s4Ptr.toNat + 4)
    (hvalsAddr : (s4Ptr + sign_extend (m := 64) (0x010#12)).toNat = s4Ptr.toNat + 16)
    (hnamesAddr : (s4Ptr + sign_extend (m := 64) (0x008#12)).toNat = s4Ptr.toNat + 8)
    (hcap0 : σ.mem[s4Ptr.toNat + 4]? = some c0) (hcap1 : σ.mem[s4Ptr.toNat + 5]? = some c1)
    (hcap2 : σ.mem[s4Ptr.toNat + 6]? = some c2) (hcap3 : σ.mem[s4Ptr.toNat + 7]? = some c3)
    (hvals0 : σ.mem[s4Ptr.toNat + 16]? = some d0) (hvals1 : σ.mem[s4Ptr.toNat + 17]? = some d1)
    (hvals2 : σ.mem[s4Ptr.toNat + 18]? = some d2) (hvals3 : σ.mem[s4Ptr.toNat + 19]? = some d3)
    (hvals4 : σ.mem[s4Ptr.toNat + 20]? = some d4) (hvals5 : σ.mem[s4Ptr.toNat + 21]? = some d5)
    (hvals6 : σ.mem[s4Ptr.toNat + 22]? = some d6) (hvals7 : σ.mem[s4Ptr.toNat + 23]? = some d7)
    -- store-target geometry for the `sd a0,8(s4)` write (`env->names`, in RAM, 8-aligned):
    (hnlo : 0x80000000 ≤ s4Ptr.toNat + 8)
    (hnhiram : s4Ptr.toNat + 8 + 8 ≤ 0x100000000)
    (hnhiwin : tohostAddr + 16 ≤ s4Ptr.toNat + 8)
    (hnalign : (s4Ptr.toNat + 8) % 8 = 0)
    -- load-target geometry for the `lw a5,4(s4)` (cap) and `ld a0,16(s4)` (vals) reads:
    (hclo : 0x80000000 ≤ s4Ptr.toNat + 4) (hchiram : s4Ptr.toNat + 4 + 4 ≤ 0x100000000)
    (hchtif : s4Ptr.toNat + 4 + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 4)
    (hcalign : (s4Ptr.toNat + 4) % 4 = 0)
    (hvlo : 0x80000000 ≤ s4Ptr.toNat + 16) (hvhiram : s4Ptr.toNat + 16 + 8 ≤ 0x100000000)
    (hvhtif : s4Ptr.toNat + 16 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 16)
    (hvalign : (s4Ptr.toNat + 16) % 8 = 0)
    -- the env->names word is disjoint from the env_define code (caller heap):
    (hnamesCode : s4Ptr.toNat + 8 + 8 ≤ 0x80002a5c ∨ 0x80002c10 ≤ s4Ptr.toNat + 8)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) ∧
      -- x10 = the loaded `env->vals` (raw byte reconstruction, tied to `ofNat pValsOld` by
      -- the caller via `ld_value_eq_read64`).
      σ'.regs.get? Register.x10 = some (sign_extend (m := 64)
        ((((((((d7.append d6).append d5).append d4).append d3).append d2).append d1).append d0)
          : BitVec (8 * 8))) ∧
      -- x11 = env->cap * 24, from the shift/add over the loaded cap.
      σ'.regs.get? Register.x11 = some
        (shift_bits_left
          ((shift_bits_left
              (sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
              (Sail.BitVec.extractLsb (0x01#6) 5 0))
            + sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
          (Sail.BitVec.extractLsb (0x03#6) 5 0)) ∧
      σ'.regs.get? Register.x1 = some (0x80002bc0#64 : BitVec 64) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      σ'.mem = writeMap8 σ.mem (s4Ptr.toNat + 8) (sdData_val pNamesNew) ∧
      (∀ (R : Register),
        (Register.mcycle == R) = false → (Register.mtime == R) = false →
        (Register.mip == R) = false → (Register.minstret == R) = false →
        (Register.PC == R) = false → (Register.nextPC == R) = false →
        (Register.minstret_increment == R) = false →
        (Register.x15 == R) = false → (Register.x10 == R) = false →
        (Register.x11 == R) = false → (Register.x1 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  let capVal : BitVec 64 :=
    sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4))
  let valsVal : BitVec 64 :=
    sign_extend (m := 64)
      ((((((((d7.append d6).append d5).append d4).append d3).append d2).append d1).append d0)
        : BitVec (8 * 8))
  -- step 1: lw a5,4(s4)  ⇒ x15 := env->cap
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002ba4_ed σ i u (0x80002ba4#64) vminstret s4Ptr c0 c1 c2 c3
      hG hpc hminstret hx20 hmem rfl
      (by rw [hcapAddr]; exact hclo) (by rw [hcapAddr]; exact hchiram)
      (by rw [hcapAddr]; exact hchtif) (by rw [hcapAddr]; exact hcalign)
      (by rw [hcapAddr]; exact hcap0) (by rw [hcapAddr]; exact hcap1)
      (by rw [hcapAddr]; exact hcap2) (by rw [hcapAddr]; exact hcap3) hi
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002ba8#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002ba4#64 : BitVec 64) 4 = (0x80002ba8#64 : BitVec 64) from by decide] at this
  have hx15_1 : σ1.regs.get? Register.x15 = some capVal :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx20_1 : σ1.regs.get? Register.x20 = some s4Ptr :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx20
  have hx10_1 : σ1.regs.get? Register.x10 = some pNamesNew :=
    obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hmem1e : σ1.mem = σ.mem := hmem1
  have hloaded1 : Env_defineLoaded σ1.mem := hmem1e ▸ hmem
  -- step 2: sd a0,8(s4)  ⇒ env->names := pNamesNew
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002ba8_ed σ1 i1 (u + 1) (0x80002ba8#64) vmi1 s4Ptr pNamesNew hG1 hpc1 hmi1 hx20_1 hx10_1
      hloaded1 rfl
      (by rw [hnamesAddr]; exact hnlo) (by rw [hnamesAddr]; exact hnhiram)
      (by rw [hnamesAddr]; exact hnhiwin) (by rw [hnamesAddr]; exact hnalign) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002bac#64 : BitVec 64) := by
    have := obs_store_pc hobs2
    rwa [show BitVec.addInt (0x80002ba8#64 : BitVec 64) 4 = (0x80002bac#64 : BitVec 64) from by decide] at this
  have hx15_2 : σ2.regs.get? Register.x15 = some capVal :=
    obs_store_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hx15_1
  have hx20_2 : σ2.regs.get? Register.x20 = some s4Ptr :=
    obs_store_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hx20_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret hobs2
  -- σ2.mem = writeMap8 σ.mem (s4+8) (sdData_val pNamesNew)
  have hbase2 : (afterNextPC (afterPrelude σ1) (0x80002ba8#64)).mem = σ.mem := by
    rw [mem_afterNextPC, mem_afterPrelude, hmem1e]
  have hmem2eq : σ2.mem = writeMap8 σ.mem (s4Ptr.toNat + 8) (sdData_val pNamesNew) := by
    rw [hmem2, hbase2, hnamesAddr]
  have hloaded2 : Env_defineLoaded σ2.mem := by
    rw [hmem2eq]
    exact loaded_envdef_writeMap8 σ.mem (s4Ptr.toNat + 8) (sdData_val pNamesNew) hnamesCode hmem
  -- the env->vals bytes at s4+16 survive the sd at s4+8 (disjoint windows)
  have hvalsRead : ∀ k, k < 8 → σ2.mem[s4Ptr.toNat + 16 + k]? = σ.mem[s4Ptr.toNat + 16 + k]? := by
    intro k hk
    rw [hmem2eq]; exact getElem_writeMap8_disjoint σ.mem (s4Ptr.toNat + 8) _ _ (by omega)
  -- step 3: ld a0,16(s4)  ⇒ x10 := env->vals
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002bac_ed σ2 i2 (u + 1 + 1) (0x80002bac#64) vmi2 s4Ptr d0 d1 d2 d3 d4 d5 d6 d7
      hG2 hpc2 hmi2 hx20_2 hloaded2 rfl
      (by rw [hvalsAddr]; exact hvlo) (by rw [hvalsAddr]; exact hvhiram)
      (by rw [hvalsAddr]; exact hvhtif) (by rw [hvalsAddr]; exact hvalign)
      (by rw [hvalsAddr]; have := hvalsRead 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hvals0)
      (by rw [hvalsAddr]; have := hvalsRead 1 (by omega); rw [this]; exact hvals1)
      (by rw [hvalsAddr]; have := hvalsRead 2 (by omega); rw [this]; exact hvals2)
      (by rw [hvalsAddr]; have := hvalsRead 3 (by omega); rw [this]; exact hvals3)
      (by rw [hvalsAddr]; have := hvalsRead 4 (by omega); rw [this]; exact hvals4)
      (by rw [hvalsAddr]; have := hvalsRead 5 (by omega); rw [this]; exact hvals5)
      (by rw [hvalsAddr]; have := hvalsRead 6 (by omega); rw [this]; exact hvals6)
      (by rw [hvalsAddr]; have := hvalsRead 7 (by omega); rw [this]; exact hvals7) hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002bb0#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80002bac#64 : BitVec 64) 4 = (0x80002bb0#64 : BitVec 64) from by decide] at this
  have hx10_3 : σ3.regs.get? Register.x10 = some valsVal :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_3 : σ3.regs.get? Register.x15 = some capVal :=
    obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx15_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hloaded3 : Env_defineLoaded σ3.mem := hmem3 ▸ hloaded2
  -- step 4: slli a1,a5,1  ⇒ x11 := capVal <<< 1
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002bb0_ed σ3 i3 (u + 1 + 1 + 1) (0x80002bb0#64) vmi3 capVal hG3 hpc3 hmi3 hx15_3 hloaded3 rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002bb4#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80002bb0#64 : BitVec 64) 4 = (0x80002bb4#64 : BitVec 64) from by decide] at this
  have hx11_4 : σ4.regs.get? Register.x11 = some
      (shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_4 : σ4.regs.get? Register.x15 = some capVal :=
    obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx15_3
  have hx10_4 : σ4.regs.get? Register.x10 = some valsVal :=
    obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hloaded4 : Env_defineLoaded σ4.mem := hmem4 ▸ hloaded3
  -- step 5: add a1,a1,a5  ⇒ x11 := (capVal<<<1) + capVal
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002bb4_ed σ4 i4 (u + 1 + 1 + 1 + 1) (0x80002bb4#64) vmi4
      (shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) capVal hG4 hpc4 hmi4 hx11_4 hx15_4 hloaded4 rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002bb8#64 : BitVec 64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80002bb4#64 : BitVec 64) 4 = (0x80002bb8#64 : BitVec 64) from by decide] at this
  have hx11_5 : σ5.regs.get? Register.x11 = some
      ((shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) + capVal) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx10_5 : σ5.regs.get? Register.x10 = some valsVal :=
    obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hloaded5 : Env_defineLoaded σ5.mem := hmem5 ▸ hloaded4
  -- step 6: slli a1,a1,3  ⇒ x11 := x11 <<< 3  (= capVal*24)
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80002bb8_ed σ5 i5 (u + 1 + 1 + 1 + 1 + 1) (0x80002bb8#64) vmi5
      ((shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) + capVal) hG5 hpc5 hmi5 hx11_5 hloaded5 rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002bbc#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80002bb8#64 : BitVec 64) 4 = (0x80002bbc#64 : BitVec 64) from by decide] at this
  have hx11_6 : σ6.regs.get? Register.x11 = some
      (shift_bits_left ((shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) + capVal)
        (Sail.BitVec.extractLsb (0x03#6) 5 0)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx10_6 : σ6.regs.get? Register.x10 = some valsVal :=
    obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hloaded6 : Env_defineLoaded σ6.mem := hmem6 ▸ hloaded5
  -- step 7: jal realloc  ⇒ x1 := 0x80002bc0, PC := reallocEntry
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80002bbc_ed σ6 i6 (u + 1 + 1 + 1 + 1 + 1 + 1) (0x80002bbc#64) vmi6 hG6 hpc6 hmi6 hloaded6 rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) := by
    have := obs_jal_pc_env hobs7
    rwa [show (0x80002bbc#64 : BitVec 64) + sign_extend (m := 64) (0x0026c0#21)
      = (BitVec.ofNat 64 reallocEntry) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_7 : σ7.regs.get? Register.x10 = some valsVal :=
    obs_jal_other_env hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_6
  have hx11_7 : σ7.regs.get? Register.x11 = some
      (shift_bits_left ((shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) + capVal)
        (Sail.BitVec.extractLsb (0x03#6) 5 0)) :=
    obs_jal_other_env hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx11_6
  have hra_7 : σ7.regs.get? Register.x1 = some (0x80002bc0#64 : BitVec 64) := by
    have := obs_jal_rd_env hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002bbc#64 : BitVec 64) 4 = (0x80002bc0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hmi7 : ∃ w, σ7.regs.get? Register.minstret = some w := obs_jal_minstret_env hobs7
  -- memory: only the sd (step 2) changed memory; steps 1,3-7 preserve mem.
  have hmemeq : σ7.mem = writeMap8 σ.mem (s4Ptr.toNat + 8) (sdData_val pNamesNew) := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3]; exact hmem2eq
  -- register frame across all 7 steps.
  have hframe : ∀ (R : Register),
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      (Register.x15 == R) = false → (Register.x10 == R) = false →
      (Register.x11 == R) = false → (Register.x1 == R) = false →
      σ7.regs.get? R = σ.regs.get? R := by
    intro R hmc hmt hmip hmis hpc' hnpc hmii hne15 hne10 hne11 hne1
    have e7 : σ7.regs.get? R = σ6.regs.get? R :=
      (hobs7.1 R hmc hmt hmip).trans
        (get?_sigmaPost_jal σ6 (0x80002bbc#64) vmi6 (0x0026c0#21) Register.x1
          (BitVec.addInt (0x80002bbc#64) 4) R hmis hpc' hne1 hnpc hmii)
    have e6 : σ6.regs.get? R = σ5.regs.get? R :=
      (hobs6.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ5 (0x80002bb8#64) vmi5 Register.x11
          (shift_bits_left ((shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) + capVal)
            (Sail.BitVec.extractLsb (0x03#6) 5 0)) R hmis hpc' hne11 hnpc hmii)
    have e5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ4 (0x80002bb4#64) vmi4 Register.x11
          ((shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) + capVal) R hmis hpc' hne11 hnpc hmii)
    have e4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ3 (0x80002bb0#64) vmi3 Register.x11
          (shift_bits_left capVal (Sail.BitVec.extractLsb (0x01#6) 5 0)) R hmis hpc' hne11 hnpc hmii)
    have e3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ2 (0x80002bac#64) vmi2 Register.x10 valsVal R hmis hpc' hne10 hnpc hmii)
    have e2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc hmt hmip).trans
        (get?_sigmaPost_store σ1 (0x80002ba8#64) vmi1
          (writeMap8 (afterNextPC (afterPrelude σ1) (0x80002ba8#64)).mem
            (s4Ptr + sign_extend (m := 64) (0x008#12)).toNat (sdData_val pNamesNew)) R hmis hpc' hnpc hmii)
    have e1 : σ1.regs.get? R = σ.regs.get? R :=
      (hobs1.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ (0x80002ba4#64) vminstret Register.x15 capVal R hmis hpc' hne15 hnpc hmii)
    exact ((((((e7.trans e6).trans e5).trans e4).trans e3).trans e2).trans e1)
  refine ⟨σ7, i7, ?_, hi7, hG7, hpc7, hx10_7, hx11_7, hra_7, hmi7, hmemeq, hframe⟩
  exact Steps.trans (Steps.single hs1) (Steps.trans (Steps.single hs2)
    (Steps.trans (Steps.single hs3) (Steps.trans (Steps.single hs4)
      (Steps.trans (Steps.single hs5) (Steps.trans (Steps.single hs6) (Steps.single hs7))))))

/-! ## The `GrowEnvEntry` struct-field carrier (item 1)

The additive frame-carrying carrier for the grow path's inter-realloc staging.  Beyond the
`EnvDefFrame` caller-frame (sp/gp/ABI-callee-saveds/AInv) it pins the `Env`-struct field
CONTENTS the staging reads — `env->cap` (at `s4+4`) and `env->vals` (at `s4+16`) — as
`read32`/`read64` facts on the CURRENT memory, plus the machine state at `0x80002ba4`.  Those
struct words survived the first realloc: they live in the caller's `Env` struct (public
memory, disjoint from the realloc'd extent), so the realloc post's `HeapPublicFrame`
outside-clause preserved them; the dispatch/scan (which owns the `Env` layout) supplies their
values as data — exactly the `AppendStrlenEntry`/`GrowCapEntry` precedent.

`s4Ptr` = the `env` base; `pValsOld` = `env->vals` = the second realloc's arg `p`;
`pNamesNew` = the first realloc's result (stored into `env->names`).  This structure is what
the top-level dispatch builds and threads into `bridgeNamesToVals_closed`. -/
structure GrowEnvEntry (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List Extent → Prop) (exts : List Extent)
    (sp : BitVec 64) (g : (R : Register) → Option (RegisterType R))
    (s4Ptr pNamesNew : BitVec 64) (pValsOld capw : Nat) (mN : Vsa.MemRepr.Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  loadedD : Env_defineLoaded c.σ.mem
  memEq : c.σ.mem = mN
  pc : c.σ.regs.get? Register.PC = some (0x80002ba4#64 : BitVec 64)
  s4 : c.σ.regs.get? Register.x20 = some s4Ptr
  namesRes : c.σ.regs.get? Register.x10 = some pNamesNew
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  -- struct-field CONTENTS (survived realloc via HeapPublicFrame):
  capEq : read32 mN (s4Ptr.toNat + 4) = some capw
  valsEq : read64 mN (s4Ptr.toNat + 16) = some pValsOld
  frame : EnvDefFrame SL gpv headroom AInv exts sp g c

/-! ## `bridgeNamesToVals` discharged — FRAME-CARRYING

From the first realloc's post enriched with the struct-field pins (`GrowEnvEntry`), the
`lw;sd;ld;slli;add;slli;jal realloc` staging lands the SECOND realloc's entry predicate
`ReallocPre(vals)`.  The frame (sp/gp/callee-saveds) survives because the staging writes only
`{x15,x10,x11,x1}` (and one memory word, `env->names`); `AInv` survives the `env->names`
store via the named `hAInvStableNames` (store-analogue of `bridgeCapCompute`'s
`hAInvStableCap`: the `env->names` word is inside the caller-owned `Env` struct, disjoint from
every allocator extent).

Value ties supplied by the caller (dispatch/scan, which knows the concrete `cap`):
* `hpTie` : the loaded `env->vals` = `ofNat pValsOld` (via `ld_value_eq_read64`; supplied as a
  named premise packaging that bridge over the `valsEq` pin),
* `hnTie` : the machine shift/add result `env->cap*24` = `ofNat nValsNew`. -/
theorem bridgeNamesToVals_closed
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    {AInv : MState → List Extent → Prop}
    (extsV : List Extent) (spN : BitVec 64)
    (gN gV : (R : Register) → Option (RegisterType R))
    (s4Ptr pNamesNew : BitVec 64) (pValsOld nValsNew : Nat) (capw : Nat)
    (mN : Vsa.MemRepr.Mem)
    -- value ties (caller data):
    (hpTie : ∀ (m : Vsa.MemRepr.Mem), read64 m (s4Ptr.toNat + 16) = some pValsOld →
      ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8),
        m[s4Ptr.toNat + 16]? = some b0 → m[s4Ptr.toNat + 17]? = some b1 →
        m[s4Ptr.toNat + 18]? = some b2 → m[s4Ptr.toNat + 19]? = some b3 →
        m[s4Ptr.toNat + 20]? = some b4 → m[s4Ptr.toNat + 21]? = some b5 →
        m[s4Ptr.toNat + 22]? = some b6 → m[s4Ptr.toNat + 23]? = some b7 →
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 pValsOld)
    (hnTie : ∀ (c0 c1 c2 c3 : BitVec 8),
        c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * c3.toNat)) = capw →
        shift_bits_left
          ((shift_bits_left
              (sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
              (Sail.BitVec.extractLsb (0x01#6) 5 0))
            + sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
          (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 nValsNew)
    -- the second realloc's entry ghost/extent are supplied by the caller (post-names
    -- realloc ledger); `spV = spN` (sp unchanged), `rV = 0x80002bc0` (the jal link),
    -- and the entry memory `mV = writeMap8 mN (s4+8) (sdData_val pNamesNew)`.
    (hgVtie : ∀ R, AbiPreserved R = true → R ≠ Register.x15 → R ≠ Register.x10 →
      R ≠ Register.x11 → R ≠ Register.x1 → gV R = gN R)
    -- struct-field / store geometry:
    (hcapAddr : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat = s4Ptr.toNat + 4)
    (hvalsAddr : (s4Ptr + sign_extend (m := 64) (0x010#12)).toNat = s4Ptr.toNat + 16)
    (hnamesAddr : (s4Ptr + sign_extend (m := 64) (0x008#12)).toNat = s4Ptr.toNat + 8)
    (hnlo : 0x80000000 ≤ s4Ptr.toNat + 8) (hnhiram : s4Ptr.toNat + 8 + 8 ≤ 0x100000000)
    (hnhiwin : tohostAddr + 16 ≤ s4Ptr.toNat + 8) (hnalign : (s4Ptr.toNat + 8) % 8 = 0)
    (hclo : 0x80000000 ≤ s4Ptr.toNat + 4) (hchiram : s4Ptr.toNat + 4 + 4 ≤ 0x100000000)
    (hchtif : s4Ptr.toNat + 4 + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 4)
    (hcalign : (s4Ptr.toNat + 4) % 4 = 0)
    (hvlo : 0x80000000 ≤ s4Ptr.toNat + 16) (hvhiram : s4Ptr.toNat + 16 + 8 ≤ 0x100000000)
    (hvhtif : s4Ptr.toNat + 16 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 16)
    (hvalign : (s4Ptr.toNat + 16) % 8 = 0)
    (hnamesCode : s4Ptr.toNat + 8 + 8 ≤ 0x80002a5c ∨ 0x80002c10 ≤ s4Ptr.toNat + 8)
    -- AInv survives the RAM `env->names` store (given gp preserved): the `env->names` word
    -- is inside the caller-owned `Env` struct, disjoint from every allocator extent in the
    -- post-names-realloc ledger `extsV`.
    (hAInvStableNames : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < s4Ptr.toNat + 8 ∨ s4Ptr.toNat + 8 + 8 ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      AInv σa extsV → AInv σb extsV) :
    Triple
      (GrowEnvEntry SL gpv headroom AInv extsV spN gN s4Ptr pNamesNew pValsOld capw mN)
      (ReallocPre SL gpv headroom AInv extsV pValsOld nValsNew spN
        (0x80002bc0#64 : BitVec 64)
        (writeMap8 mN (s4Ptr.toNat + 8) (sdData_val pNamesNew)) gV) := by
  intro c hpre
  obtain ⟨hG, hloadedD, hmemEq, hpc, hs4, hnamesRes, ⟨vmi, hmi⟩, htick, hcapEq, hvalsEq, hFrame⟩ := hpre
  obtain ⟨hsp, hstackOK, hgp, hAbi, hAInv, htickF⟩ := hFrame
  -- decompose the struct-field pins to bytes for the run (against the entry memory = mN)
  obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, hcRe⟩ := read32_bytes mN (s4Ptr.toNat + 4) capw hcapEq
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ :=
    ld64_bytes mN (s4Ptr.toNat + 16) pValsOld hvalsEq
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hx10', hx11', hra', hmi', hmemeq', hframe'⟩ :=
    namesToValsPrefix_run c.σ c.tick c.steps vmi s4Ptr pNamesNew c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7
      hG hpc hmi hs4 hnamesRes hloadedD hcapAddr hvalsAddr hnamesAddr
      (hmemEq ▸ hc0) (hmemEq ▸ hc1) (hmemEq ▸ hc2) (hmemEq ▸ hc3)
      (hmemEq ▸ hd0) (hmemEq ▸ hd1) (hmemEq ▸ hd2) (hmemEq ▸ hd3)
      (hmemEq ▸ hd4) (hmemEq ▸ hd5) (hmemEq ▸ hd6) (hmemEq ▸ hd7)
      hnlo hnhiram hnhiwin hnalign hclo hchiram hchtif hcalign
      hvlo hvhiram hvhtif hvalign hnamesCode htick
  -- register frame: only {x15,x10,x11,x1}+control written; sp/gp/callee-saveds survive.
  have hframeReg : ∀ (R : Register),
      (Register.x15 == R) = false → (Register.x10 == R) = false →
      (Register.x11 == R) = false → (Register.x1 == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      σ'.regs.get? R = c.σ.regs.get? R :=
    fun R h15 h10 h11 h1 hmc hmt hmip hmis hpc'' hnpc hmii =>
      hframe' R hmc hmt hmip hmis hpc'' hnpc hmii h15 h10 h11 h1
  have hsp' : σ'.regs.get? Register.x2 = some spN := by
    rw [hframeReg Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp
  have hgp' : σ'.regs.get? Register.x3 = some gpv := by
    rw [hframeReg Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgp
  refine ⟨⟨σ', i', c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, ?_⟩
  · cases c; exact hsteps
  · refine ⟨hG', hi', hpc', ?_, ?_, hra', by decide, hsp', hstackOK, hgp', ?_, ?_, ?_⟩
    · -- x10 = ofNat pValsOld (loaded env->vals, tied by hpTie over the valsEq pin)
      rw [hx10', hpTie mN hvalsEq d0 d1 d2 d3 d4 d5 d6 d7 hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7]
    · -- x11 = ofNat nValsNew (env->cap*24, tied by hnTie)
      rw [hx11', hnTie c0 c1 c2 c3 hcRe]
    · -- ABI tie to gV
      intro R hR
      by_cases h15 : R = Register.x15
      · subst h15; exact absurd hR (by decide)
      by_cases h10 : R = Register.x10
      · subst h10; exact absurd hR (by decide)
      by_cases h11 : R = Register.x11
      · subst h11; exact absurd hR (by decide)
      by_cases h1 : R = Register.x1
      · subst h1; exact absurd hR (by decide)
      rw [hframeReg R (beq_false_of_ne' h15) (beq_false_of_ne' h10) (beq_false_of_ne' h11)
        (beq_false_of_ne' h1) (abi_ne (by decide) hR) (abi_ne (by decide) hR)
        (abi_ne (by decide) hR) (abi_ne (by decide) hR) (abi_ne (by decide) hR)
        (abi_ne (by decide) hR) (abi_ne (by decide) hR)]
      rw [hgVtie R hR h15 h10 h11 h1]; exact hAbi R hR
    · -- AInv survives the env->names store (mem agrees off [s4+8,s4+16), gp preserved)
      refine hAInvStableNames c.σ σ' ?_ ?_ hAInv
      · rw [hgp', hgp]
      · intro a ha
        rw [hmemeq']
        exact (getElem_writeMap8_disjoint c.σ.mem (s4Ptr.toNat + 8) a (sdData_val pNamesNew) (by omega)).symm
    · -- mem = writeMap8 mN (s4+8) (sdData_val pNamesNew); c.σ.mem = mN
      rw [hmemeq', hmemEq]

/-! ## Wiring adapter: the contract's `bridgeNamesToVals` premise from `bridgeNamesToVals_closed`

`envDefGrowContract`'s `bridgeNamesToVals` premise is sourced at `ReallocPost(names) ∧
ReallocGrowResult(names)` (the first realloc's exact post), not at `GrowEnvEntry`.  This adapter
seqs the `ReallocPost ∧ ReallocGrowResult → GrowEnvEntry` construction (deriving the machine
state from `ReallocPost`, the new names pointer from `ReallocGrowResult`'s success case, and
the struct-field pins as caller data — they survived the realloc via `ReallocGrowResult`'s
`HeapPublicFrame`, so the dispatch knows their `mN`-values) into `bridgeNamesToVals_closed`,
producing the contract premise VERBATIM (with `rN := 0x80002ba4`, `spV := spN`, `rV := 0x80002bc0`,
`mV := writeMap8 mN (s4+8) (sdData_val pNamesNew)`).

The struct pins, geometry, ties, ABI-ghost tie, and AInv-stability are the named residuals the
dispatch/scan supplies — exactly the `AppendStrlenEntry`/`GrowCapEntry` discipline.  This makes
the grow-path names→vals seam a direct `Triple.seq` plug into `envDefGrowContract`, no gap in the
machine reasoning. -/
theorem bridgeNamesToVals_wired
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    {AInv : MState → List Extent → Prop} {Src : Config → Prop}
    (extsV : List Extent) (spN : BitVec 64)
    (gN gV : (R : Register) → Option (RegisterType R))
    (s4Ptr pNamesNew : BitVec 64) (pValsOld nValsNew : Nat) (capw : Nat)
    (mN : Vsa.MemRepr.Mem)
    -- the contract's `bridgeNamesToVals` source `Src` (= `ReallocPost(names) ∧
    -- ReallocGrowResult(names)`) supplies the machine state + new names pointer + struct pins:
    -- `hEntry` packages it into `GrowEnvEntry` (the dispatch's job — struct fields survived the
    -- realloc via `ReallocGrowResult`'s `HeapPublicFrame`, values known to the caller).
    (hEntry : ∀ c, Src c →
      GrowEnvEntry SL gpv headroom AInv extsV spN gN s4Ptr pNamesNew pValsOld capw mN c)
    (hpTie : ∀ (m : Vsa.MemRepr.Mem), read64 m (s4Ptr.toNat + 16) = some pValsOld →
      ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8),
        m[s4Ptr.toNat + 16]? = some b0 → m[s4Ptr.toNat + 17]? = some b1 →
        m[s4Ptr.toNat + 18]? = some b2 → m[s4Ptr.toNat + 19]? = some b3 →
        m[s4Ptr.toNat + 20]? = some b4 → m[s4Ptr.toNat + 21]? = some b5 →
        m[s4Ptr.toNat + 22]? = some b6 → m[s4Ptr.toNat + 23]? = some b7 →
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 pValsOld)
    (hnTie : ∀ (c0 c1 c2 c3 : BitVec 8),
        c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * c3.toNat)) = capw →
        shift_bits_left
          ((shift_bits_left
              (sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
              (Sail.BitVec.extractLsb (0x01#6) 5 0))
            + sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
          (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 nValsNew)
    (hgVtie : ∀ R, AbiPreserved R = true → R ≠ Register.x15 → R ≠ Register.x10 →
      R ≠ Register.x11 → R ≠ Register.x1 → gV R = gN R)
    (hcapAddr : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat = s4Ptr.toNat + 4)
    (hvalsAddr : (s4Ptr + sign_extend (m := 64) (0x010#12)).toNat = s4Ptr.toNat + 16)
    (hnamesAddr : (s4Ptr + sign_extend (m := 64) (0x008#12)).toNat = s4Ptr.toNat + 8)
    (hnlo : 0x80000000 ≤ s4Ptr.toNat + 8) (hnhiram : s4Ptr.toNat + 8 + 8 ≤ 0x100000000)
    (hnhiwin : tohostAddr + 16 ≤ s4Ptr.toNat + 8) (hnalign : (s4Ptr.toNat + 8) % 8 = 0)
    (hclo : 0x80000000 ≤ s4Ptr.toNat + 4) (hchiram : s4Ptr.toNat + 4 + 4 ≤ 0x100000000)
    (hchtif : s4Ptr.toNat + 4 + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 4)
    (hcalign : (s4Ptr.toNat + 4) % 4 = 0)
    (hvlo : 0x80000000 ≤ s4Ptr.toNat + 16) (hvhiram : s4Ptr.toNat + 16 + 8 ≤ 0x100000000)
    (hvhtif : s4Ptr.toNat + 16 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 16)
    (hvalign : (s4Ptr.toNat + 16) % 8 = 0)
    (hnamesCode : s4Ptr.toNat + 8 + 8 ≤ 0x80002a5c ∨ 0x80002c10 ≤ s4Ptr.toNat + 8)
    (hAInvStableNames : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < s4Ptr.toNat + 8 ∨ s4Ptr.toNat + 8 + 8 ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      AInv σa extsV → AInv σb extsV) :
    Triple Src
      (ReallocPre SL gpv headroom AInv extsV pValsOld nValsNew spN
        (0x80002bc0#64 : BitVec 64)
        (writeMap8 mN (s4Ptr.toNat + 8) (sdData_val pNamesNew)) gV) :=
  Triple.conseq
    (bridgeNamesToVals_closed SL gpv headroom extsV spN gN gV
      s4Ptr pNamesNew pValsOld nValsNew capw mN hpTie hnTie hgVtie hcapAddr hvalsAddr hnamesAddr
      hnlo hnhiram hnhiwin hnalign hclo hchiram hchtif hcalign hvlo hvhiram hvhtif hvalign
      hnamesCode hAInvStableNames)
    hEntry (fun _ h => h)

/-! ## `frameRepr_append` — the FrameRepr append core (item 3)

The append path's store block (`0x80002b44..0x80002b88`) writes the copied name pointer
into `names[count]`, the value into `vals[count]`, and `count+1` into `env->count`, turning
`FrameRepr … e f` into `FrameRepr … e (f` with `(x,v)` appended`)` — the append (name-absent)
case of `Store.define`.  `foundSt_of_storeRepr` (`EnvGetMarshal`) is the REVERSE direction
(`StoreRepr → FoundSt` for a HIT); this is the forward append.

This core lemma is stated purely on the post-store memory `m` (no machine steps): given the
readback facts for the EXTENDED structure — the new count `n+1`, the cap with `n+1 ≤ cap`, the
`names`/`vals` base pointers, the OLD `n` slots' name+value representations surviving, the NEW
slot's `CString`/`ValueRepr`, and the parent unchanged — it assembles `FrameRepr m N φf φc e f'`
for the frame `f'` whose `vars = f.vars ++ [(x,v)]`.  It is the shared spec-side reconstruction
the task flags: it serves `bridgeStore` (append path) AND the `env_define`-update append arm AND
`Call.closure`'s env-fold (each appends one bound slot to a `FrameRepr`).

The residual for the LIVE `bridgeStore` is only the MACHINE side (the store-block Steps chain
threading the four `sd`/`sw` sites + the count fold, delivering exactly these readback facts) —
named, not built here; this lemma discharges the FrameRepr-reconstruction content it feeds. -/
theorem frameRepr_append (m : Vsa.MemRepr.Mem) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value) (cap pn pv : Nat)
    -- header: count = n+1, cap with n+1 ≤ cap, names/vals base pointers.
    (hcount : read32 m e = some (vars.length + 1))
    (hcap : read32 m (e + 4) = some cap) (hcapLe : vars.length + 1 ≤ cap)
    (hpn : read64 m (e + 8) = some pn) (hpv : read64 m (e + 16) = some pv)
    -- OLD slots survive (their name pointer + CString + value representation).
    (hold : ∀ i, (h : i < vars.length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q (vars[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) (vars[i].2))
    -- parent unchanged (given explicitly to avoid a match-type motive capture).
    (hparentNone : parent = none → read64 m (e + 24) = some 0)
    (hparentSome : ∀ pa, parent = some pa →
      read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0)
    -- NEW slot (index vars.length): the copied name + the stored value.
    (hnewName : ∃ q, read64 m (pn + 8 * vars.length) = some q ∧ CString m q x)
    (hnewVal : ValueRepr m N φc (pv + 24 * vars.length) v) :
    FrameRepr m N φf φc e ⟨parent, vars ++ [(x, v)]⟩ := by
  -- the extended frame's `.vars` is `vars ++ [(x,v)]` and `.parent` is `parent`, both by rfl.
  refine ⟨?_, ⟨cap, hcap, ?_⟩, ⟨pn, pv, hpn, hpv, ?_⟩, ?_⟩
  · -- count = length of extended vars
    show read32 m e = some (vars ++ [(x, v)]).length
    rw [define_append_length]; exact hcount
  · -- length ≤ cap
    show (vars ++ [(x, v)]).length ≤ cap
    rw [define_append_length]; exact hcapLe
  · -- per-slot: split index into old (< length) vs the new appended slot (= length)
    show ∀ i, (h : i < (vars ++ [(x, v)]).length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q ((vars ++ [(x, v)])[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) ((vars ++ [(x, v)])[i].2)
    intro i hi
    rw [define_append_length] at hi
    by_cases hlt : i < vars.length
    · -- old slot i: getElem is vars[i]
      have hge : (vars ++ [(x, v)])[i] = vars[i]'hlt := define_append_getElem_old vars x v i hlt
      rw [hge]; exact hold i hlt
    · -- new slot: i = vars.length, getElem is (x, v)
      have hieq : i = vars.length := by omega
      subst hieq
      have hge : (vars ++ [(x, v)])[vars.length] = (x, v) := define_append_getElem_new vars x v
      rw [hge]; exact ⟨hnewName, hnewVal⟩
  · -- parent clause (the frame's `.parent` is `parent` by rfl)
    cases hpa : parent with
    | none => exact hparentNone hpa
    | some pa => exact hparentSome pa hpa

#print axioms site_80002ba4_ed
#print axioms site_80002ba8_ed
#print axioms site_80002bac_ed
#print axioms site_80002bb0_ed
#print axioms site_80002bb4_ed
#print axioms site_80002bb8_ed
#print axioms site_80002bbc_ed
#print axioms namesToValsPrefix_run
#print axioms bridgeNamesToVals_closed
#print axioms bridgeNamesToVals_wired
#print axioms frameRepr_append

end Vsa.Sim
