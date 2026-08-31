import Vsa.Sim.EnvDefCompose
import Vsa.Sim.EnvDefBridges
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvDefSpec4
import Vsa.Sim.ReallocSpec
import Vsa.Sim.ValueSpec
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch05Part06
import Vsa.Sim.DecodeTable.Batch02Part08
import Vsa.Sim.DecodeTable.Batch12Part29

/-!
# `EnvDefBridges2` — the grow-path `bridgeCapCompute` machine bridge

`Vsa/Sim/EnvDefCompose.lean`'s `envDefGrowContract` leaves the grow-path prefix as the
named hypothesis `bridgeCapCompute : Triple P (ReallocPre …)` — the cap-compute prefix
`0x80002b90..0x80002ba0`:

```
80002b90  slliw a5,a5,1      -- x15 := 2*cap        (32-bit doubling)
80002b94  slli  a1,a5,3      -- x11 := newcap*8     (the realloc arg n)
80002b98  sw    a5,4(s4)     -- env->cap := newcap  (store into env struct)
80002b9c  mv    a0,s6        -- x10 := s6 = env->names (pOld, the realloc arg p)
80002ba0  jal   realloc      -- x1 := 0x80002ba4, PC := reallocEntry
```

This lands `ReallocPre SL gpv headroom AInv extsN pOld nNew spN 0x80002ba4 mN gN` at the
realloc entry `0x8000527c`.

## Factored abstraction (the exponentiating deliverable)

The `mv rd,rs ; jal callee` tail is the SAME idiom the strlen/malloc prefixes end with
(`EnvDefBridges.strlenPrefix_run`/`mallocPrefix_run`).  `reallocMvJal_run` factors it into
a reusable two-step run keyed on (mv source register, callee entry, link) so this bridge
AND the future `bridgeNamesToVals`/`bridgeAppendHead` realloc calls all instantiate ONE
tail.  The `obs_jal_*`/`frame_*` readbacks are reused verbatim from `EnvNewSpec`.

## Store-memory / AInv threading

The `sw a5,4(s4)` writes `env->cap` — one word inside the caller's live `Env` struct, NOT
inside any allocator extent.  `AInv` (abstract in `ReallocOps`) therefore survives, but no
GENERIC store-frame lemma can exist for an abstract predicate; the survival is carried as
the named typed premise `hAInvStableCap` (the store-analogue of `EnvDefBridges`'s
`hAInvStable`).  The shift-result register values (`newcap = 2*cap`, `nNew = newcap*8`) and
the store-target geometry are supplied by the rich source predicate `GrowCapEntry` — the
dispatch/scan knows `cap` and the `Env` layout, so these are its data, exactly as the
append-path `AppendStrlenEntry` supplies the strlen argument facts.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (Env_defineLoaded env_define_at_80002b90 env_define_at_80002b94
  env_define_at_80002b98 env_define_at_80002b9c env_define_at_80002ba0)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `Env_defineLoaded` survives the `sw a5,4(s4)` cap store: the `env->cap` word is in
RAM, well above the `env_define` code region `[0x80002a5c, 0x80002c10)`, so it is disjoint
from every loaded code byte.  The `writeMap4` analogue of `loaded_envdef_writeMap8`. -/
theorem loaded_envdef_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 : Nat)
    (d : BitVec (8 * 4))
    (hdis : a4 + 4 ≤ 0x80002a5c ∨ 0x80002c10 ≤ a4) (h : Env_defineLoaded mem) :
    Env_defineLoaded (writeMap4 mem a4 d) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_defineChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk5] at c5 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk6] at c6 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## Site step lemmas for the cap-compute prefix -/

/-- Site `0x80002b90` (`slliw a5,a5,1`): `x15 := sext32(x15[31:0] << 1)`. -/
theorem site_80002b90_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b90#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v15 31 0) (0x01#5)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b90 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002b90#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002b90#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002b90#64) vminstret (0x0017979b#32)
    (instruction.SHIFTIWOP (0x01#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sopw.SLLIW))
    Register.x15 (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v15 31 0) (0x01#5)))
    (0x9b#8) (0x97#8) (0x17#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_0017979b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiwop_slliw_char (0x01#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
      (afterNextPC (afterPrelude σ) (0x80002b90#64))
      (sigma3_alu σ (0x80002b90#64) Register.x15
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v15 31 0) (0x01#5))))
      (rX_bits_x15 _ v15 hx15₂)
      (wX_bits_x15 _ (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v15 31 0) (0x01#5)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002b94` (`slli a1,a5,3`): `x11 := x15 <<< 3`. -/
theorem site_80002b94_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b94#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x03#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b94 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002b94#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002b94#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002b94#64) vminstret (0x00379593#32)
    (instruction.SHIFTIOP (0x03#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0b#5, sop.SLLI))
    Register.x11 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x03#6) 5 0)) (0x93#8) (0x95#8) (0x37#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_00379593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x03#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5) v15
      (afterNextPC (afterPrelude σ) (0x80002b94#64))
      (sigma3_alu σ (0x80002b94#64) Register.x11 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x03#6) 5 0)))
      (rX_bits_x15 _ v15 hx15₂) (wX_bits_x11 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x03#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002b98` (`sw a5,4(s4)`): store `x15` low 32 bits at `s4+4` = `env->cap`. -/
theorem site_80002b98_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b98#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x004#12)).toNat)
    (hahiram : (v20 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v20 + sign_extend (m := 64) (0x004#12)).toNat)
    (haalign : (v20 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x80002b98#64)).mem
        (v20 + sign_extend (m := 64) (0x004#12)).toNat (swData v15) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap4 (afterNextPC (afterPrelude σ) (0x80002b98#64)).mem
          (v20 + sign_extend (m := 64) (0x004#12)).toNat (swData v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b98 hmem
  exact stepObs_store σ i u (0x80002b98#64) vminstret (0x00fa2223#32)
    (instruction.STORE (0x004#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x14#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x80002b98#64)).mem
      (v20 + sign_extend (m := 64) (0x004#12)).toNat (swData v15))
    (0x23#8) (0x22#8) (0xfa#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00fa2223 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x80002b98#64) (0x004#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x14#5)
      v20 v15 hG
      (rX_bits_x20 _ v20
        (by rw [get?_afterNextPC σ (0x80002b98#64) _ (by decide) (by decide)]; exact hx20))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80002b98#64) _ (by decide) (by decide)]; exact hx15))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002b9c` (`mv a0,s6` = `addi x10,x22,0`): `x10 := s6`. -/
theorem site_80002b9c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b9c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v22 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b9c hmem
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80002b9c#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80002b9c#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_alu σ i u (0x80002b9c#64) vminstret (0x000b0513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x16#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v22 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x0b#8) (0x00#8)
    hG hpc hminstret (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_000b0513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x0a#5) v22
      (afterNextPC (afterPrelude σ) (0x80002b9c#64))
      (sigma3_alu σ (0x80002b9c#64) Register.x10 (v22 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x22 _ v22 hx22₂) (wX_bits_x10 _ (v22 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site `0x80002ba0` (`jal realloc`): `x1 := 0x80002ba4`, `PC := reallocEntry`. -/
theorem site_80002ba0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ba0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x0026dc#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ba0 hmem
  exact stepObs_jal σ i u (0x80002ba0#64) vminstret (0x6dc020ef#32) (0x0026dc#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002ba0#64) 4)
    (0xef#8) (0x20#8) (0xc0#8) (0x6d#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_6dc020ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80002ba0#64) 4)) hi

/-! ## The cap-compute prefix run

Chains all five steps `0x80002b90..0x80002ba0`.  From a state at `0x80002b90` with
`x15 = capReg` (the current capacity register), `x20 = s4Ptr` (`env` base), `x22 = s6Ptr`
(`env->names` = `pOld`), runs to a state at `reallocEntry` with:
* `x10 = s6Ptr` (the realloc arg `p`),
* `x11 = newcapx8` where `newcapx8 = (2*cap) <<< 3` (the realloc arg `n`),
* `x1 = 0x80002ba4` (link),
* memory = the input memory with `env->cap` (word at `s4Ptr+4`) overwritten by `newcap`
  (`= writeMap4 … (swData newcap)`),
* every register outside `{x10, x11, x15, x1}` + control preserved (in particular
  `x2`/sp, `x3`/gp and every other callee-saved).

`newcap = sext32(cap[31:0] << 1)`, `newcapx8 = newcap <<< 3` are the concrete machine
shift results; the caller ties them to `ofNat`-forms via `bridgeCapCompute`'s premises. -/
theorem capComputePrefix_run
    (σ : MState) (i u : Nat) (vminstret capReg s4Ptr s6Ptr : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x80002b90#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some capReg)
    (hx20 : σ.regs.get? Register.x20 = some s4Ptr)
    (hx22 : σ.regs.get? Register.x22 = some s6Ptr)
    (hmem : Env_defineLoaded σ.mem)
    -- the `sw` store-target geometry (word inside the `Env` struct, in RAM, aligned):
    (halo : 0x80000000 ≤ (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat)
    (hahiram : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat)
    (haalign : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    -- the cap word is disjoint from the `env_define` code (it is in the caller's heap):
    (hcapCode : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x80002a5c ∨
      0x80002c10 ≤ (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 1 + 1 + 1 + 1 + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) ∧
      σ'.regs.get? Register.x10 = some s6Ptr ∧
      σ'.regs.get? Register.x11 = some
        (shift_bits_left
          (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb capReg 31 0) (0x01#5)))
          (Sail.BitVec.extractLsb (0x03#6) 5 0)) ∧
      σ'.regs.get? Register.x1 = some (0x80002ba4#64 : BitVec 64) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      -- the memory after the cap store (env->cap := newcap): the full write-map equality.
      σ'.mem = writeMap4 σ.mem (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat
        (swData (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb capReg 31 0) (0x01#5)))) ∧
      -- FRAME: any register outside the write set {x15, x11, x10, x1} + control preserved.
      (∀ (R : Register),
        (Register.mcycle == R) = false → (Register.mtime == R) = false →
        (Register.mip == R) = false → (Register.minstret == R) = false →
        (Register.PC == R) = false → (Register.nextPC == R) = false →
        (Register.minstret_increment == R) = false →
        (Register.x15 == R) = false → (Register.x11 == R) = false →
        (Register.x10 == R) = false → (Register.x1 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  -- abbreviations for the two shift results (plain local definitions; no `set`/Mathlib)
  let newcap : BitVec 64 :=
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb capReg 31 0) (0x01#5))
  let newcapx8 : BitVec 64 :=
    shift_bits_left newcap (Sail.BitVec.extractLsb (0x03#6) 5 0)
  -- step 1: slliw a5,a5,1  ⇒ x15 := newcap
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002b90_ed σ i u (0x80002b90#64) vminstret capReg hG hpc hminstret hx15 hmem rfl hi
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002b94#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002b90#64 : BitVec 64) 4 = (0x80002b94#64 : BitVec 64) from by decide] at this
  have hx15_1 : σ1.regs.get? Register.x15 = some newcap :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hloaded1 : Env_defineLoaded σ1.mem := hmem1 ▸ hmem
  -- step 2: slli a1,a5,3  ⇒ x11 := newcapx8
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002b94_ed σ1 i1 (u + 1) (0x80002b94#64) vmi1 newcap hG1 hpc1 hmi1 hx15_1 hloaded1 rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002b98#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80002b94#64 : BitVec 64) 4 = (0x80002b98#64 : BitVec 64) from by decide] at this
  have hx11_2 : σ2.regs.get? Register.x11 = some newcapx8 :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_2 : σ2.regs.get? Register.x15 = some newcap :=
    obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx15_1
  have hx20_2 : σ2.regs.get? Register.x20 = some s4Ptr :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hx20)
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hloaded2 : Env_defineLoaded σ2.mem := hmem2 ▸ hloaded1
  -- step 3: sw a5,4(s4)  ⇒ env->cap := newcap  (writes memory, no GPR)
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002b98_ed σ2 i2 (u + 1 + 1) (0x80002b98#64) vmi2 s4Ptr newcap hG2 hpc2 hmi2 hx20_2 hx15_2
      hloaded2 rfl halo hahiram hahiwin haalign hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002b9c#64 : BitVec 64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x80002b98#64 : BitVec 64) 4 = (0x80002b9c#64 : BitVec 64) from by decide] at this
  have hx11_3 : σ3.regs.get? Register.x11 = some newcapx8 :=
    obs_store_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hx11_2
  -- s6 (x22) survives all of steps 1-3 (none writes x22)
  have hx22_1 : σ1.regs.get? Register.x22 = some s6Ptr :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx22
  have hx22_2 : σ2.regs.get? Register.x22 = some s6Ptr :=
    obs_alu_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx22_1
  have hx22_3 : σ3.regs.get? Register.x22 = some s6Ptr :=
    obs_store_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hx22_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  -- σ3.mem = writeMap4 (σ2.mem via afterNextPC/afterPrelude) …; Env_defineLoaded survives
  -- the RAM cap store (disjoint from code).
  have hbase3 : (afterNextPC (afterPrelude σ2) (0x80002b98#64)).mem = σ2.mem := by
    rw [mem_afterNextPC, mem_afterPrelude]
  have hloaded3 : Env_defineLoaded σ3.mem := by
    rw [hmem3, hbase3]
    exact loaded_envdef_writeMap4 σ2.mem (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat
      (swData newcap) hcapCode hloaded2
  -- step 4: mv a0,s6  ⇒ x10 := s6Ptr
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002b9c_ed σ3 i3 (u + 1 + 1 + 1) (0x80002b9c#64) vmi3 s6Ptr hG3 hpc3 hmi3 hx22_3 hloaded3 rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002ba0#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80002b9c#64 : BitVec 64) 4 = (0x80002ba0#64 : BitVec 64) from by decide] at this
  have hx10_4 : σ4.regs.get? Register.x10 = some s6Ptr := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (s6Ptr + sign_extend (m := 64) (0x000#12) : BitVec 64) = s6Ptr from by
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
      rw [this, BitVec.add_zero]] at this
  have hx11_4 : σ4.regs.get? Register.x11 = some newcapx8 :=
    obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx11_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hloaded4 : Env_defineLoaded σ4.mem := hmem4 ▸ hloaded3
  -- step 5: jal realloc  ⇒ x1 := 0x80002ba4, PC := reallocEntry
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002ba0_ed σ4 i4 (u + 1 + 1 + 1 + 1) (0x80002ba0#64) vmi4 hG4 hpc4 hmi4 hloaded4 rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) := by
    have := obs_jal_pc_env hobs5
    rwa [show (0x80002ba0#64 : BitVec 64) + sign_extend (m := 64) (0x0026dc#21)
      = (BitVec.ofNat 64 reallocEntry) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_5 : σ5.regs.get? Register.x10 = some s6Ptr :=
    obs_jal_other_env hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_4
  have hx11_5 : σ5.regs.get? Register.x11 = some newcapx8 :=
    obs_jal_other_env hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx11_4
  have hra_5 : σ5.regs.get? Register.x1 = some (0x80002ba4#64 : BitVec 64) := by
    have := obs_jal_rd_env hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002ba0#64 : BitVec 64) 4 = (0x80002ba4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hmi5 : ∃ w, σ5.regs.get? Register.minstret = some w := obs_jal_minstret_env hobs5
  -- register frame across all 5 steps (only the store step touches memory, no GPR)
  have hframe : ∀ (R : Register),
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      (Register.x15 == R) = false → (Register.x11 == R) = false →
      (Register.x10 == R) = false → (Register.x1 == R) = false →
      σ5.regs.get? R = σ.regs.get? R := by
    intro R hmc hmt hmip hmis hpc' hnpc hmii hne15 hne11 hne10 hne1
    have e5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmc hmt hmip).trans
        (get?_sigmaPost_jal σ4 (0x80002ba0#64) vmi4 (0x0026dc#21) Register.x1
          (BitVec.addInt (0x80002ba0#64) 4) R hmis hpc' hne1 hnpc hmii)
    have e4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ3 (0x80002b9c#64) vmi3 Register.x10
          (s6Ptr + sign_extend (m := 64) (0x000#12)) R hmis hpc' hne10 hnpc hmii)
    have e3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmc hmt hmip).trans
        (get?_sigmaPost_store σ2 (0x80002b98#64) vmi2
          (writeMap4 (afterNextPC (afterPrelude σ2) (0x80002b98#64)).mem
            (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat (swData newcap)) R hmis hpc' hnpc hmii)
    have e2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ1 (0x80002b94#64) vmi1 Register.x11 newcapx8 R hmis hpc' hne11 hnpc hmii)
    have e1 : σ1.regs.get? R = σ.regs.get? R :=
      (hobs1.1 R hmc hmt hmip).trans
        (get?_sigmaPost_alu σ (0x80002b90#64) vminstret Register.x15 newcap R hmis hpc' hne15 hnpc hmii)
    exact ((((e5.trans e4).trans e3).trans e2).trans e1)
  -- full memory equality: only the store step changed memory (env->cap := newcap).
  -- σ5.mem = σ4.mem = σ3.mem (jal/mv preserve mem); σ3.mem = writeMap4 σ2.mem-based …;
  -- σ2.mem = σ1.mem = σ.mem (both alu steps preserve mem).
  have hbase : (afterNextPC (afterPrelude σ2) (0x80002b98#64)).mem = σ.mem := by
    rw [mem_afterNextPC, mem_afterPrelude, hmem2, hmem1]
  have hmemeq : σ5.mem = writeMap4 σ.mem (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat
      (swData newcap) := by
    rw [hmem5, hmem4, hmem3, hbase]
  refine ⟨σ5, i5, ?_, hi5, hG5, hpc5, hx10_5, hx11_5, hra_5, hmi5, hmemeq, hframe⟩
  exact Steps.trans (Steps.single hs1) (Steps.trans (Steps.single hs2)
    (Steps.trans (Steps.single hs3) (Steps.trans (Steps.single hs4) (Steps.single hs5))))

/-! ## `bridgeCapCompute` discharged — FRAME-CARRYING

The grow-path entry predicate `GrowCapEntry` supplies the machine state at `0x80002b90`
(`x15 = cap` register, `x20`/`s4` = `env` base, `x22`/`s6` = `env->names` = `pOld`), the
`sw` store-target geometry, the carried caller-frame `EnvDefFrame`, AND the two
value-tie premises the caller (dispatch/scan) knows from the concrete `cap` value and
`Env` layout:

* `hpTie` : `s6Ptr = ofNat pNamesOld` (the names pointer register holds `pOld`),
* `hnTie` : the machine shift result `(2*cap) <<< 3` equals `ofNat nNamesNew` (`newcap*8`),
* `hmemTie` : the realloc-entry memory `mN` is the post-cap-store memory
  (`writeMap4 m0 capAddr (swData newcap)`).

`bridgeCapCompute_closed` runs `capComputePrefix_run` and repackages the post-state as
`ReallocPre …` at the realloc entry.  The register frame (`sp`/`gp`/callee-saveds)
survives because the prefix writes only `x15`/`x11`/`x10`/`x1`; `AInv` survives the RAM
cap store via the named `hAInvStableCap` (the store-analogue of `EnvDefBridges`'s
`hAInvStable`: mem-agree-off-the-cap-word ∧ gp-agree ⇒ `AInv`). -/

/-- **`bridgeCapCompute` discharged (frame-carrying).**  From `GrowCapEntry` (cap-compute
args + carried frame + caller value ties), the `slliw;slli;sw;mv;jal realloc` prefix lands
`ReallocPre SL gpv headroom AInv extsN pNamesOld nNamesNew spN 0x80002ba4 mN gN` at the
realloc entry.  This is the frame-carrying `bridgeCapCompute` premise of
`envDefGrowContract` (with `rN := 0x80002ba4`, `mN := writeMap4 m0 capAddr (swData newcap)`). -/
theorem bridgeCapCompute_closed (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List Extent → Prop) (extsN : List Extent)
    (spN : BitVec 64) (gN : (R : Register) → Option (RegisterType R))
    (capReg s4Ptr s6Ptr : BitVec 64) (pNamesOld nNamesNew : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- caller value ties: the names pointer holds `pOld`, and the machine shift result
    -- `(2*cap) <<< 3` equals `ofNat nNamesNew` (`newcap*8`):
    (hpTie : s6Ptr = BitVec.ofNat 64 pNamesOld)
    (hnTie : shift_bits_left
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb capReg 31 0) (0x01#5)))
        (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 nNamesNew)
    -- machine geometry of the cap word:
    (halo : 0x80000000 ≤ (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat)
    (hahiram : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat)
    (haalign : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (hcapCode : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x80002a5c ∨
      0x80002c10 ≤ (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat)
    -- AInv survives the RAM cap store (given gp preserved): the cap word is inside the
    -- caller-owned `Env` struct, disjoint from every allocator extent.
    (hAInvStableCap : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat ∨
        (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      AInv σa extsN → AInv σb extsN) :
    Triple
      (fun c =>
        GoodState c.σ ∧ Env_defineLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some (0x80002b90#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x15 = some capReg ∧
        c.σ.regs.get? Register.x20 = some s4Ptr ∧
        c.σ.regs.get? Register.x22 = some s6Ptr ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        EnvDefFrame SL gpv headroom AInv extsN spN gN c)
      (ReallocPre SL gpv headroom AInv extsN pNamesOld nNamesNew spN
        (0x80002ba4#64 : BitVec 64)
        (writeMap4 m0 (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat
          (swData (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb capReg 31 0) (0x01#5)))))
        gN) := by
  intro c hpre
  obtain ⟨hG, hloadedD, hmem, hpc, hx15, hx20, hx22, ⟨vmi, hmi⟩, htick, hFrame⟩ := hpre
  obtain ⟨hsp, hstackOK, hgp, hAbi, hAInv, htickF⟩ := hFrame
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hx10', hx11', hra', hmi', hmemeq', hframe'⟩ :=
    capComputePrefix_run c.σ c.tick c.steps vmi capReg s4Ptr s6Ptr hG hpc hmi hx15 hx20 hx22
      hloadedD halo hahiram hahiwin haalign hcapCode htick
  -- register frame: x2/sp and x3/gp survive (outside {x15,x11,x10,x1}+control write set)
  have hframeReg : ∀ (R : Register),
      (Register.x15 == R) = false → (Register.x11 == R) = false →
      (Register.x10 == R) = false → (Register.x1 == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → (Register.minstret == R) = false →
      (Register.PC == R) = false → (Register.nextPC == R) = false →
      (Register.minstret_increment == R) = false →
      σ'.regs.get? R = c.σ.regs.get? R :=
    fun R h15 h11 h10 h1 hmc hmt hmip hmis hpc'' hnpc hmii =>
      hframe' R hmc hmt hmip hmis hpc'' hnpc hmii h15 h11 h10 h1
  have hsp' : σ'.regs.get? Register.x2 = some spN := by
    rw [hframeReg Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp
  have hgp' : σ'.regs.get? Register.x3 = some gpv := by
    rw [hframeReg Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgp
  -- ABI callee-saved tie: each AbiPreserved R is x2, or NotWrittenEnv-covered.
  refine ⟨⟨σ', i', c.steps + 1 + 1 + 1 + 1 + 1⟩, ?_, ?_⟩
  · cases c; exact hsteps
  · refine ⟨hG', hi', hpc', ?_, ?_, hra', by decide, hsp', hstackOK, hgp', ?_, ?_, ?_⟩
    · -- x10 = ofNat pNamesOld
      rw [hx10', hpTie]
    · -- x11 = ofNat nNamesNew
      rw [hx11', hnTie]
    · -- ABI tie to gN: the entire write set {x15,x11,x10,x1} + control registers are
      -- NON-AbiPreserved, so any AbiPreserved R differs from all of them (`abi_ne`), hence
      -- is preserved through the prefix; then `gN R = c.σ R` by the entry tie.
      intro R hR
      rw [hframeReg R (abi_ne (by decide) hR) (abi_ne (by decide) hR)
        (abi_ne (by decide) hR) (abi_ne (by decide) hR) (abi_ne (by decide) hR)
        (abi_ne (by decide) hR) (abi_ne (by decide) hR) (abi_ne (by decide) hR)
        (abi_ne (by decide) hR) (abi_ne (by decide) hR) (abi_ne (by decide) hR)]
      exact hAbi R hR
    · -- AInv survives the RAM cap store (mem agrees off the cap word, gp preserved)
      refine hAInvStableCap c.σ σ' ?_ ?_ hAInv
      · rw [hgp', hgp]
      · intro a ha
        rw [hmemeq']
        exact (getElem_writeMap4_disjoint c.σ.mem
          (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat a _ (by omega)).symm
    · -- mem = mN = writeMap4 m0 capAddr (swData newcap); c.σ.mem = m0 (from `P`)
      rw [hmemeq', hmem]

#print axioms capComputePrefix_run
#print axioms bridgeCapCompute_closed

end Vsa.Sim
