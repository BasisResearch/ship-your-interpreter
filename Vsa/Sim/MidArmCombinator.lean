import Vsa.Sim.EvalBinSim
import Vsa.Sim.ArmSegSplitEval

/-!
# `MidArmCombinator` — the `SubEvalReturn → JalPreBundle` mid-arm re-cut (Task #79, priority 1)

The binary/logical arms of `eval_expr` evaluate the LEFT operand, RETURN into the spill
frame (`SubEvalReturn`), then run a MID-arm span (reload the RIGHT operand pointer, stage
the right sub-buffer, respill the env-reg) before the RIGHT `jal eval_expr`.  In
`EvalBinSim.blockB_binary` this mid-arm span is threaded BY HAND (lines 540–929): the
node-pointer transport `ment ↔ mcall1 ↔ cL.mem` (`hAgNode`), the frame-population
`hPopCL`, the node-24 byte readback, then the 7 machine sites 0x800034fc→0x80003518, then
the τ7 register/memory bundle that IS the RIGHT `armTail_rec` precondition.

This file factors that shape ONCE as `binaryR_midStagePre`: from the config `cL` at
`SubEvalReturn` (the post-left-return bundle) PLUS the carried node/geometry facts (all
stated over `cL.σ.mem` directly, so no reference to the left span's `mcall1`/`ment`), the
7 sites reach a config satisfying `JalPreBundle er` at the post-left store `st'`.  Then
`binaryR`/`logicalR` (and, with the analogous entry, `callC`-mid / `argsTail`-mid) each
instantiate it cheaply, sharing this ONE re-cut just as `binaryL` shares the ONE
marshalling bridge `evalEntry_of_jalPrefix`.

## Combinator verdict

**Factorable.**  The hand threading's ONLY entanglement with the left span is the
node-pointer transport (`ment↔mcall1↔cL.mem`) and frame-population (`hPopCL`).  Both are
consumed only as facts ABOUT `cL.σ.mem` (`read64 cL.σ.mem (aExpr+24) = aROp`, and
frame-presence on `[sp-1120, sp)`), which `SubEvalReturn`'s memframe + `MemExtends` clause
ALREADY establishes at the caller — so they are honest carried premises here, not
re-derived internals.  The 7 sites + the `mcall2` marshalling (StoreRepr / ExprRepr /
Value_intLoaded / IntSlotPinned survival, spill-slot survival, the ghost frame) are
op-independent (the arm PC is op-generic; the op only matters at the value-combine tail
AFTER the right returns), so ONE combinator serves every binary/logical operator.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

set_option linter.unusedVariables false

/-- **The binary/logical mid-arm re-cut, `SubEvalReturn → JalPreBundle`.**

From the config `cL` at the post-left-return `SubEvalReturn` bundle (over the left store
`st'`, sub-result `vl` — both irrelevant to the mid-arm, so ∃-absorbed by the caller),
run the 7 mid-arm sites 0x800034fc→0x80003518 and land at the RIGHT `jal eval_expr` PC
(`0x80003518`) with `JalPreBundle er` at store `st'`.  Delivered as `LandedN 7`; the
divergence-fold consumer only needs `≥ 1`.

The precondition mirrors `SubEvalReturn`'s fields (already unpacked by the caller) PLUS
the carried node/geometry facts that the left span established over `cL.σ.mem`:
* `hpc/ha0/hs1/hsp` — PC/regs at `cL` (from `SubEvalReturn`);
* `hx8/hx18` — `s0 = aExpr` / `s2 = aEnv` restored by the left call's ABI frame;
* `hnode` — the RIGHT operand pointer `read64 cL.σ.mem (aExpr+24) = aROp` (transported);
* `hpop` — the RIGHT sub-frame region `[sp-1120, sp)` is present in `cL.σ.mem`;
* `hexprSurv` — `ExprRepr … aROp er` survives any write outside `[SL.lo, sp)`;
* `hstoreSurv` — `st'.store` re-represents under the same survival window;
* `hviCL` / `hviSlotCL` — `Value_intLoaded` / `IntSlotPinned` at `cL.σ.mem`;
* `hslot*` — the four OUTER spill slots at `[sp-32, sp)`;
* geometry (`BinExtras`-shaped disjointness / alignment / RAM / windows). -/
theorem binaryR_midStagePre
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf1 φc1 : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (cL : Config)
    -- SubEvalReturn-supplied register/state facts at cL:
    (hGL : GoodState cL.σ) (htickL : cL.tick < 2)
    (hpcL : cL.σ.regs.get? Register.PC = some (0x800034fc#64))
    (hs1L : cL.σ.regs.get? Register.x9 = some sret)
    (hspL : cL.σ.regs.get? Register.x2 = some (sp - 1088#64))
    (hmiL : ∃ w, cL.σ.regs.get? Register.minstret = some w)
    (houtStrL : String.join cL.σ.sailOutput.toList = st'.out)
    (hframeL : ∀ R : Register, AbiPreservedNoise R → cL.σ.regs.get? R = gpre R)
    (hx8L : cL.σ.regs.get? Register.x8 = some aExpr)
    (hx18L : cL.σ.regs.get? Register.x18 = some aEnv)
    (hgx8v : gpre Register.x8 = some aExpr) (hgx18v : gpre Register.x18 = some aEnv)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    -- the transported right-operand pointer + node bytes present:
    (hnode : read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat)
    -- the right sub-frame region present (frame-population, from SubEvalReturn's memframe):
    (hpop : ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, cL.σ.mem[a]? = some b))
    -- StoreRepr / ExprRepr / Value_intLoaded / IntSlotPinned survival at cL.σ.mem:
    (hstoreCL : StoreRepr cL.σ.mem N A φf1 φc1 st'.store)
    (hstoreSurvCL : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        cL.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store)
    (hexprSurvCL : ∀ m : Mem,
      (∀ k, aROp.toNat ≤ k → k < aROp.toNat + 16 → cL.σ.mem[k]? = m[k]?) →
      ExprRepr m aROp.toNat er)
    (hviCL : Value_intLoaded cL.σ.mem) (hviSlotCL : IntSlotPinned cL.σ.mem)
    (hnbsCL : NBSPins cL.σ.mem)
    (hslotRaL : read64 cL.σ.mem (sp.toNat - 8) = some r.toNat)
    (hslotS0L : read64 cL.σ.mem (sp.toNat - 16) = some v8.toNat)
    (hslotS1L : read64 cL.σ.mem (sp.toNat - 24) = some v9.toNat)
    (hslotS2L : read64 cL.σ.mem (sp.toNat - 32) = some v18.toNat)
    -- geometry (BinExtras-shaped):
    (hnode_hi : aExpr.toNat + 32 ≤ 0x100000000)
    (hnode_lo : 0x80000000 ≤ aExpr.toNat)
    (hnode_align : aExpr.toNat % 8 = 0)
    (hnode_win : tohostAddr + 32 ≤ aExpr.toNat)
    (hrop_align : aROp.toNat % 8 = 0)
    (hrop_ram : 0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000)
    (hrop_win : tohostAddr + 16 ≤ aROp.toNat)
    (hrop_stk : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat)
    (hrop_stkfull : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat)
    (hsp1088 : 1088 ≤ sp.toNat)
    (hsproom : SL.lo + 3264 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi)
    (hsp16 : sp.toNat % 16 = 0) (hsphi : sp.toNat ≤ 0x100000000)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLhiRam : SL.hi ≤ 0x100000000)
    (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo)
    (hviStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec)
    (htableStk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
    -- ITEM ZERO B1: the RIGHT operand's recursion-sound budget at `sp - 1088`,
    -- its `.fn`-bodies bound, and the post-LEFT store-bodies invariant
    -- (threaded; the caller derives them at the arm entry).
    (hstackBudgetR : StackOK SL (sp - 1088#64)
      (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088))
    (hexprBodiesR : Expr.bodiesBound Vsa.While.perCallBudget er = true)
    (hstoreBodiesR : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    -- WAVE 47i: the RIGHT child's entry-ground bundle at `cL.σ.mem`, carried at
    -- the PARENT windows (re-cut to the child windows below via `child_at`).
    (hGroundR_CL : EvalGround cL.σ.mem SL A sp sret aROp.toNat er) :
    LandedN 7 cL (fun c' => JalPreBundle er c' st' d env) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  obtain ⟨vmiL, hmiLw⟩ := hmiL
  obtain ⟨rp0, rp1, rp2, rp3, rp4, rp5, rp6, rp7, hrp0, hrp1, hrp2, hrp3, hrp4, hrp5, hrp6, hrp7, hrpsext⟩ :=
    spill_roundtrip_ee cL.σ.mem (aExpr.toNat + 24) aROp hnode
  -- addresses for the intermediate reads/stores
  have hoff24_s0 : (aExpr + sign_extend (m := 64) (0x018#12)).toNat = aExpr.toNat + 24 := by
    have hs : (sign_extend (m := 64) (0x018#12) : BitVec 64) = 24#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (24#64 : BitVec 64).toNat = 24 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  have haddr0' : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by omega) hsp1088
  have haddr144' : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  -- present bytes for the reads (env @sp-1088, lw @sp-968, s3 @sp-960)
  obtain ⟨eb0, heb0⟩ := hpop (sp.toNat - 1088) (by omega) (by omega)
  obtain ⟨eb1, heb1⟩ := hpop (sp.toNat - 1088 + 1) (by omega) (by omega)
  obtain ⟨eb2, heb2⟩ := hpop (sp.toNat - 1088 + 2) (by omega) (by omega)
  obtain ⟨eb3, heb3⟩ := hpop (sp.toNat - 1088 + 3) (by omega) (by omega)
  obtain ⟨eb4, heb4⟩ := hpop (sp.toNat - 1088 + 4) (by omega) (by omega)
  obtain ⟨eb5, heb5⟩ := hpop (sp.toNat - 1088 + 5) (by omega) (by omega)
  obtain ⟨eb6, heb6⟩ := hpop (sp.toNat - 1088 + 6) (by omega) (by omega)
  obtain ⟨eb7, heb7⟩ := hpop (sp.toNat - 1088 + 7) (by omega) (by omega)
  obtain ⟨wb0, hwb0⟩ := hpop (sp.toNat - 968) (by omega) (by omega)
  obtain ⟨wb1, hwb1⟩ := hpop (sp.toNat - 968 + 1) (by omega) (by omega)
  obtain ⟨wb2, hwb2⟩ := hpop (sp.toNat - 968 + 2) (by omega) (by omega)
  obtain ⟨wb3, hwb3⟩ := hpop (sp.toNat - 968 + 3) (by omega) (by omega)
  obtain ⟨sb0, hsb0⟩ := hpop (sp.toNat - 960) (by omega) (by omega)
  obtain ⟨sb1, hsb1⟩ := hpop (sp.toNat - 960 + 1) (by omega) (by omega)
  obtain ⟨sb2, hsb2⟩ := hpop (sp.toNat - 960 + 2) (by omega) (by omega)
  obtain ⟨sb3, hsb3⟩ := hpop (sp.toNat - 960 + 3) (by omega) (by omega)
  obtain ⟨sb4, hsb4⟩ := hpop (sp.toNat - 960 + 4) (by omega) (by omega)
  obtain ⟨sb5, hsb5⟩ := hpop (sp.toNat - 960 + 5) (by omega) (by omega)
  obtain ⟨sb6, hsb6⟩ := hpop (sp.toNat - 960 + 6) (by omega) (by omega)
  obtain ⟨sb7, hsb7⟩ := hpop (sp.toNat - 960 + 7) (by omega) (by omega)
  -- ============ 0x800034fc: ld a2,24(s0) → x12 := aROp ============
  obtain ⟨τ1, j1, ht1', hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    site_800034fc_ee cL.σ cL.tick cL.steps (0x800034fc#64) vmiL aExpr rp0 rp1 rp2 rp3 rp4 rp5 rp6 rp7
      hGL hpcL hmiLw hx8L hcodeL rfl
      (by rw [hoff24_s0]; omega) (by rw [hoff24_s0]; omega)
      (by rw [hoff24_s0, htoh]; right; omega) (by rw [hoff24_s0]; omega)
      (by rw [hoff24_s0]; exact hrp0) (by rw [hoff24_s0]; exact hrp1)
      (by rw [hoff24_s0]; exact hrp2) (by rw [hoff24_s0]; exact hrp3)
      (by rw [hoff24_s0]; exact hrp4) (by rw [hoff24_s0]; exact hrp5)
      (by rw [hoff24_s0]; exact hrp6) (by rw [hoff24_s0]; exact hrp7) htickL
  have hstepτ1 : Step cL ⟨τ1, j1, cL.steps + 1⟩ := by cases cL; exact ht1'
  have hmemτ1e : τ1.mem = cL.σ.mem := hmemτ1
  have hpcτ1 : τ1.regs.get? Register.PC = some (0x80003500#64) := by
    have := obs_alu_pc hoτ1
    rwa [show BitVec.addInt (0x800034fc#64) 4 = (0x80003500#64 : BitVec 64) from by decide] at this
  have hx12τ1 : τ1.regs.get? Register.x12 = some aROp := by
    have := obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hrpsext] at this
  have hs1τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1L
  have hx18τ1 : τ1.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18L
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspL
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = cL.σ.sailOutput := by rw [hoτ1.out, sailOutput_sigmaPost_alu]
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcodeL
  -- ============ 0x80003500: ld a3,0(sp) → x13 := env (dead) ============
  obtain ⟨τ2, j2, ht2', hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    site_80003500_ee τ1 j1 (cL.steps + 1) (0x80003500#64) vmiτ1 (sp - 1088#64)
      eb0 eb1 eb2 eb3 eb4 eb5 eb6 eb7 hGτ1 hpcτ1 hmiτ1 hspτ1 hcodeτ1 rfl
      (by rw [haddr0']; omega) (by rw [haddr0']; omega)
      (by rw [haddr0', htoh]; right; omega) (by rw [haddr0']; omega)
      (by rw [haddr0', hmemτ1e]; exact heb0) (by rw [haddr0', hmemτ1e]; exact heb1)
      (by rw [haddr0', hmemτ1e]; exact heb2) (by rw [haddr0', hmemτ1e]; exact heb3)
      (by rw [haddr0', hmemτ1e]; exact heb4) (by rw [haddr0', hmemτ1e]; exact heb5)
      (by rw [haddr0', hmemτ1e]; exact heb6) (by rw [haddr0', hmemτ1e]; exact heb7) hj1
  have hstepτ2 : Step ⟨τ1, j1, cL.steps + 1⟩ ⟨τ2, j2, cL.steps + 1 + 1⟩ := ht2'
  have hmemτ2e : τ2.mem = cL.σ.mem := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some (0x80003504#64) := by
    have := obs_alu_pc hoτ2
    rwa [show BitVec.addInt (0x80003500#64) 4 = (0x80003504#64 : BitVec 64) from by decide] at this
  have hx12τ2 : τ2.regs.get? Register.x12 = some aROp := obs_alu_other hoτ2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ1
  have hx13τ2 : τ2.regs.get? Register.x13 = some
      (sign_extend (m := 64) ((((((((eb7.append eb6).append eb5).append eb4).append eb3).append eb2).append eb1).append eb0) : BitVec (8 * 8))) :=
    obs_alu_rd hoτ2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1τ2 : τ2.regs.get? Register.x9 = some sret := obs_alu_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ1
  have hx18τ2 : τ2.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ2 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_alu_minstret hoτ2
  have houtτ2 : τ2.sailOutput = cL.σ.sailOutput := by rw [hoτ2.out, sailOutput_sigmaPost_alu]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcodeL
  -- ============ 0x80003504: lw a6,120(sp) → x16 (dead) ============
  obtain ⟨τ3, j3, ht3', hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    site_80003504_ee τ2 j2 (cL.steps + 1 + 1) (0x80003504#64) vmiτ2 (sp - 1088#64)
      wb0 wb1 wb2 wb3 hGτ2 hpcτ2 hmiτ2 hspτ2 hcodeτ2 rfl
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmemτ2e]; exact hwb0) (by rw [haddr120, hmemτ2e]; exact hwb1)
      (by rw [haddr120, hmemτ2e]; exact hwb2) (by rw [haddr120, hmemτ2e]; exact hwb3) hj2
  have hstepτ3 : Step ⟨τ2, j2, cL.steps + 1 + 1⟩ ⟨τ3, j3, cL.steps + 1 + 1 + 1⟩ := ht3'
  have hmemτ3e : τ3.mem = cL.σ.mem := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x80003508#64) := by
    have := obs_alu_pc hoτ3
    rwa [show BitVec.addInt (0x80003504#64) 4 = (0x80003508#64 : BitVec 64) from by decide] at this
  have hx16τ3 : τ3.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12τ3 : τ3.regs.get? Register.x12 = some aROp := obs_alu_other hoτ3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ2
  have hx13τ3 := obs_alu_other hoτ3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ2
  have hs1τ3 : τ3.regs.get? Register.x9 = some sret := obs_alu_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ2
  have hx18τ3 : τ3.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ3 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_alu_minstret hoτ3
  have houtτ3 : τ3.sailOutput = cL.σ.sailOutput := by rw [hoτ3.out, sailOutput_sigmaPost_alu]; exact houtτ2
  have hcodeτ3 : Eval_exprLoaded τ3.mem := by rw [hmemτ3e]; exact hcodeL
  -- ============ 0x80003508: addi a0,sp,144 → x10 := sp-944 ============
  obtain ⟨τ4, j4, ht4', hj4, hGτ4, hmemτ4, hoτ4⟩ :=
    site_80003508_ee τ3 j3 (cL.steps + 1 + 1 + 1) (0x80003508#64) vmiτ3 (sp - 1088#64)
      hGτ3 hpcτ3 hmiτ3 hspτ3 hcodeτ3 rfl hj3
  have hstepτ4 : Step ⟨τ3, j3, cL.steps + 1 + 1 + 1⟩ ⟨τ4, j4, cL.steps + 1 + 1 + 1 + 1⟩ := ht4'
  have hmemτ4e : τ4.mem = cL.σ.mem := by rw [hmemτ4]; exact hmemτ3e
  have hpcτ4 : τ4.regs.get? Register.PC = some (0x8000350c#64) := by
    have := obs_alu_pc hoτ4
    rwa [show BitVec.addInt (0x80003508#64) 4 = (0x8000350c#64 : BitVec 64) from by decide] at this
  have ha0τ4 : τ4.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_rd hoτ4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12τ4 : τ4.regs.get? Register.x12 = some aROp := obs_alu_other hoτ4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ3
  have hx13τ4 := obs_alu_other hoτ4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ3
  have hs1τ4 : τ4.regs.get? Register.x9 = some sret := obs_alu_other hoτ4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ3
  have hx16τ4 : τ4.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_other hoτ4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ3
  have hx18τ4 : τ4.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ4 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ3
  have hspτ4 : τ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ3
  obtain ⟨vmiτ4, hmiτ4⟩ := obs_alu_minstret hoτ4
  have houtτ4 : τ4.sailOutput = cL.σ.sailOutput := by rw [hoτ4.out, sailOutput_sigmaPost_alu]; exact houtτ3
  have hcodeτ4 : Eval_exprLoaded τ4.mem := by rw [hmemτ4e]; exact hcodeL
  -- ============ 0x8000350c: mv a1,s2 → x11 := aEnv ============
  obtain ⟨τ5, j5, ht5', hj5, hGτ5, hmemτ5, hoτ5⟩ :=
    site_8000350c_ee τ4 j4 (cL.steps + 1 + 1 + 1 + 1) (0x8000350c#64) vmiτ4 aEnv
      hGτ4 hpcτ4 hmiτ4 hx18τ4 hcodeτ4 rfl hj4
  have hstepτ5 : Step ⟨τ4, j4, cL.steps + 1 + 1 + 1 + 1⟩ ⟨τ5, j5, cL.steps + 1 + 1 + 1 + 1 + 1⟩ := ht5'
  have hmemτ5e : τ5.mem = cL.σ.mem := by rw [hmemτ5]; exact hmemτ4e
  have hpcτ5 : τ5.regs.get? Register.PC = some (0x80003510#64) := by
    have := obs_alu_pc hoτ5
    rwa [show BitVec.addInt (0x8000350c#64) 4 = (0x80003510#64 : BitVec 64) from by decide] at this
  have hx11τ5 : τ5.regs.get? Register.x11 = some aEnv := by
    have := obs_alu_rd hoτ5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (aEnv + sign_extend (m := 64) (0x000#12)) = aEnv from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
      rw [this]; have := aEnv.isLt; omega] at this
  have ha0τ5 : τ5.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_other hoτ5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0τ4
  have hx12τ5 : τ5.regs.get? Register.x12 = some aROp := obs_alu_other hoτ5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ4
  have hx13τ5 := obs_alu_other hoτ5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ4
  have hs1τ5 : τ5.regs.get? Register.x9 = some sret := obs_alu_other hoτ5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ4
  have hx16τ5 : τ5.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_other hoτ5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ4
  have hspτ5 : τ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ4
  obtain ⟨vmiτ5, hmiτ5⟩ := obs_alu_minstret hoτ5
  have houtτ5 : τ5.sailOutput = cL.σ.sailOutput := by rw [hoτ5.out, sailOutput_sigmaPost_alu]; exact houtτ4
  have hcodeτ5 : Eval_exprLoaded τ5.mem := by rw [hmemτ5e]; exact hcodeL
  -- ============ 0x80003510: ld s3,128(sp) → x19 (dead) ============
  obtain ⟨τ6, j6, ht6', hj6, hGτ6, hmemτ6, hoτ6⟩ :=
    site_80003510_ee τ5 j5 (cL.steps + 1 + 1 + 1 + 1 + 1) (0x80003510#64) vmiτ5 (sp - 1088#64)
      sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 hGτ5 hpcτ5 hmiτ5 hspτ5 hcodeτ5 rfl
      (by rw [haddr128]; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, htoh]; right; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, hmemτ5e]; exact hsb0) (by rw [haddr128, hmemτ5e]; exact hsb1)
      (by rw [haddr128, hmemτ5e]; exact hsb2) (by rw [haddr128, hmemτ5e]; exact hsb3)
      (by rw [haddr128, hmemτ5e]; exact hsb4) (by rw [haddr128, hmemτ5e]; exact hsb5)
      (by rw [haddr128, hmemτ5e]; exact hsb6) (by rw [haddr128, hmemτ5e]; exact hsb7) hj5
  have hstepτ6 : Step ⟨τ5, j5, cL.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨τ6, j6, cL.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht6'
  have hmemτ6e : τ6.mem = cL.σ.mem := by rw [hmemτ6]; exact hmemτ5e
  have hpcτ6 : τ6.regs.get? Register.PC = some (0x80003514#64) := by
    have := obs_alu_pc hoτ6
    rwa [show BitVec.addInt (0x80003510#64) 4 = (0x80003514#64 : BitVec 64) from by decide] at this
  have ha0τ6 : τ6.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_other hoτ6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0τ5
  have hx11τ6 : τ6.regs.get? Register.x11 = some aEnv := obs_alu_other hoτ6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ5
  have hx12τ6 : τ6.regs.get? Register.x12 = some aROp := obs_alu_other hoτ6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ5
  have hx13τ6 := obs_alu_other hoτ6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ5
  have hs1τ6 : τ6.regs.get? Register.x9 = some sret := obs_alu_other hoτ6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ5
  have hx16τ6 : τ6.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_other hoτ6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ5
  have hspτ6 : τ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ5
  obtain ⟨vmiτ6, hmiτ6⟩ := obs_alu_minstret hoτ6
  have houtτ6 : τ6.sailOutput = cL.σ.sailOutput := by rw [hoτ6.out, sailOutput_sigmaPost_alu]; exact houtτ5
  have hcodeτ6 : Eval_exprLoaded τ6.mem := by rw [hmemτ6e]; exact hcodeL
  -- ============ 0x80003514: sd a6,0(sp) → mcall2 at sp-1088 ============
  let mcall2 : Mem := writeMap8 cL.σ.mem (sp.toNat - 1088)
    (sdData_val (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))))
  obtain ⟨τ7, j7, ht7', hj7, hGτ7, hmemτ7, hoτ7⟩ :=
    site_80003514_ee τ6 j6 (cL.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003514#64) vmiτ6 (sp - 1088#64)
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4)))
      hGτ6 hpcτ6 hmiτ6 hspτ6 hx16τ6 hcodeτ6 rfl
      (by rw [haddr0']; omega) (by rw [haddr0']; omega)
      (by rw [haddr0', htoh]; omega) (by rw [haddr0']; omega) hj6
  have hstepτ7 : Step ⟨τ6, j6, cL.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ7, j7, cL.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht7'
  have hmemτ7e : τ7.mem = mcall2 := by rw [hmemτ7, mem_afterNextPC, haddr0', hmemτ6e]
  have hpcτ7 : τ7.regs.get? Register.PC = some (0x80003518#64) := by
    have := obs_store_pc_val hoτ7
    rwa [show BitVec.addInt (0x80003514#64) 4 = (0x80003518#64 : BitVec 64) from by decide] at this
  have ha0τ7 := obs_store_other_val hoτ7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0τ6
  have hx11τ7 := obs_store_other_val hoτ7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ6
  have hx12τ7 := obs_store_other_val hoτ7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ6
  have hx13τ7 := obs_store_other_val hoτ7 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ6
  have hs1τ7 := obs_store_other_val hoτ7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ6
  have hspτ7 := obs_store_other_val hoτ7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ6
  obtain ⟨vmiτ7, hmiτ7⟩ := obs_store_minstret_val hoτ7
  have houtτ7 : τ7.sailOutput = cL.σ.sailOutput := by rw [hoτ7.out, sailOutput_sigmaPost_store]; exact houtτ6
  have hcodeτ7 : Eval_exprLoaded mcall2 :=
    loaded_eval_expr_agreeP cL.σ.mem mcall2
      (fun k hk => (getElem_writeMap8_disjoint cL.σ.mem (sp.toNat-1088) k _
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodeL
  -- agreement `cL.mem ↔ mcall2` outside the stack region `[SL.lo, sp)`.
  have hAgMcall2 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → cL.σ.mem[k]? = mcall2[k]? := by
    intro k hk
    show cL.σ.mem[k]? = (writeMap8 cL.σ.mem (sp.toNat - 1088) _)[k]?
    rw [getElem_writeMap8_disjoint cL.σ.mem (sp.toNat - 1088) k _ (by omega)]
  -- `StoreRepr mcall2` + survival
  have hstore2 : StoreRepr mcall2 N A φf1 φc1 st'.store :=
    hstoreSurvCL mcall2 (fun k hk1 hk2 => hAgMcall2 k (fun ⟨ha, hb⟩ => hk1 ⟨ha, by omega⟩))
  have hstoreSurv2 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
        ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mcall2[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store := by
    intro m' hag
    refine hstoreSurvCL m' (fun k hk1 hk2 => ?_)
    have hk1' : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hspSLhi⟩
    rw [hAgMcall2 k hk1']; exact hag k hk1 hk2
  -- `ExprRepr mcall2 aROp er`.  The right operand node `[aROp, aROp+16)` may live
  -- INSIDE the stack window (`sp-1088 ≤ aROp`), so we cannot use `hAgMcall2` (which
  -- needs disjointness from all of `[SL.lo, sp)`).  Instead: `mcall2` differs from
  -- `cL.σ.mem` ONLY at the `sd a6,0(sp)` word `[sp-1088, sp-1080)`, and the arm's
  -- geometry (`rop_stkfull`: the right node sits ABOVE the callee's lowered frame,
  -- so above `sp-1088`) keeps the node disjoint from that single write.
  have hexprR2 : ExprRepr mcall2 aROp.toNat er := by
    refine hexprSurvCL mcall2 (fun k hk1 hk2 => ?_)
    show cL.σ.mem[k]? = (writeMap8 cL.σ.mem (sp.toNat - 1088) _)[k]?
    rw [getElem_writeMap8_disjoint cL.σ.mem (sp.toNat - 1088) k _
      (by rcases hrop_stkfull with h | h <;> omega)]
  have hnbs2 : NBSPins mcall2 :=
    hnbsCL.survive_stack hviStk htableStk hAgMcall2
  -- WAVE 47i: the RIGHT child's entry-ground bundle at `mcall2`, child windows —
  -- the carried parent-window ground re-cut by `child_at` (identity projection)
  -- across the single in-stack `sd` write.
  have hGroundR2 : EvalGround mcall2 SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aROp.toNat er :=
    hGroundR_CL.child_at (fun _ _ h => h) (fun a ha => (hAgMcall2 a ha).symm)
      htableStk hspSLhi (by rw [hspsub]; omega)
      (by rw [haddr144']; omega) (by rw [haddr144']; omega)
  -- `Value_intLoaded` / `IntSlotPinned` for mcall2
  have hviInt2 : Value_intLoaded mcall2 :=
    loaded_value_int_agreeP cL.σ.mem mcall2
      (fun a ha => hAgMcall2 a (by rcases hviStk with h | h <;> omega)) hviCL
  have hviSlot2 : IntSlotPinned mcall2 :=
    intSlot_writeMap8 cL.σ.mem (sp.toNat - 1088) _
      (by simp only [jumpTableBase]; rcases htableStk with h | h
          · right; omega
          · left; omega) hviSlotCL
  -- the RIGHT frame's four spill slots survive the sp-1088 store (disjoint below)
  have hslotRa2 : read64 mcall2 (sp.toNat - 8) = some r.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 8) (sp.toNat - 1088) _ (by omega)]; exact hslotRaL
  have hslotS02 : read64 mcall2 (sp.toNat - 16) = some v8.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 16) (sp.toNat - 1088) _ (by omega)]; exact hslotS0L
  have hslotS12 : read64 mcall2 (sp.toNat - 24) = some v9.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 24) (sp.toNat - 1088) _ (by omega)]; exact hslotS1L
  have hslotS22 : read64 mcall2 (sp.toNat - 32) = some v18.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 32) (sp.toNat - 1088) _ (by omega)]; exact hslotS2L
  -- the RIGHT ghost `gR7 := τ7.regs.get?`: agrees with gpre on AbiPreservedNoise\{x19}
  have hframeτ7_excl : ∀ R : Register, AbiPreservedNoise R → (Register.x19 == R) = false →
      τ7.regs.get? R = gpre R := by
    intro R hR h19R
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h13R : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h16R : (Register.x16 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have h11R : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have f1 : τ1.regs.get? R = cL.σ.regs.get? R :=
      (hoτ1.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : τ2.regs.get? R = τ1.regs.get? R :=
      (hoτ2.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h13R hnpcR hmiiR)
    have f3 : τ3.regs.get? R = τ2.regs.get? R :=
      (hoτ3.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h16R hnpcR hmiiR)
    have f4 : τ4.regs.get? R = τ3.regs.get? R :=
      (hoτ4.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    have f5 : τ5.regs.get? R = τ4.regs.get? R :=
      (hoτ5.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h11R hnpcR hmiiR)
    have f6 : τ6.regs.get? R = τ5.regs.get? R :=
      (hoτ6.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h19R hnpcR hmiiR)
    have f7 : τ7.regs.get? R = τ6.regs.get? R :=
      (hoτ7.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    rw [f7, f6, f5, f4, f3, f2, f1]; exact hframeL R hR'
  have hgR7_8 : τ7.regs.get? Register.x8 = some aExpr :=
    (hframeτ7_excl Register.x8 (by decide) (by decide)).trans hgx8v
  have hgR7_18 : τ7.regs.get? Register.x18 = some aEnv :=
    (hframeτ7_excl Register.x18 (by decide) (by decide)).trans hgx18v
  -- ============ land at τ7 (the RIGHT jal PC 0x80003518) as `JalPreBundle er` ============
  refine ⟨7, ⟨τ7, j7, cL.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, Nat.le_refl _,
    StepsN.succ hstepτ1 (StepsN.succ hstepτ2 (StepsN.succ hstepτ3 (StepsN.succ hstepτ4
      (StepsN.succ hstepτ5 (StepsN.succ hstepτ6 (StepsN.succ hstepτ7 (StepsN.zero _))))))), ?_⟩
  · exact ⟨(fun R => τ7.regs.get? R), N, A, SL, φf1, φc1,
      (0x80003518#64), (0x8000351c#64), (0x1ffc4c#21),
      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)), aEnv, aROp,
      v8, v9, v18, cL.σ.sailOutput, mcall2,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_80003518_ee σ i u (0x80003518#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ),
      hGτ7, hj7, hpcτ7, ha0τ7, hs1τ7, hx11τ7, ⟨_, hx13τ7⟩, hx12τ7, hspτ7, ⟨vmiτ7, hmiτ7⟩,
      houtτ7, houtStrL, hmemτ7e, hcodeτ7, hviInt2, hviSlot2, hnbs2, hGroundR2, hexprR2, hstore2, hstoreSurv2,
      (fun R hR => rfl), ⟨⟨aExpr, hgR7_8⟩, ⟨aEnv, hgR7_18⟩⟩,
      hslotRa2, hslotS02, hslotS12, hslotS22,
      hrop_align, hrop_ram.1, hrop_ram.2, hrop_win, hrop_stk,
      (by rw [haddr144']; omega), (by rw [haddr144']; omega), (by rw [haddr144']; omega),
      (by omega), hspSLhi, hsp16, (by omega), hSLlo, hSLhiRam, hSLwin,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩

#print axioms binaryR_midStagePre

/-- **The divergence-fold form of the mid-arm re-cut.**  `binaryR_midStagePre` lands
`LandedN 7`; the `EvalChildStages.binaryR` residual only needs `LandedN 1` to
`JalPreBundle r`.  `weakenCount` drops the count.  This is the exact shape a caller
threads: after `armTail_rec` produces the post-left `SubEvalReturn` at `cL`, unpack it
into this combinator's premises (all present in the arm's `BinExtras`/`SubEvalReturn`)
and get the `JalPreBundle r` landing that `binaryR_split`/`evalChildSplit_of_stage`
finishes into `EEntryC r`. -/
theorem binaryR_midStage1
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf1 φc1 : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (cL : Config)
    (hGL : GoodState cL.σ) (htickL : cL.tick < 2)
    (hpcL : cL.σ.regs.get? Register.PC = some (0x800034fc#64))
    (hs1L : cL.σ.regs.get? Register.x9 = some sret)
    (hspL : cL.σ.regs.get? Register.x2 = some (sp - 1088#64))
    (hmiL : ∃ w, cL.σ.regs.get? Register.minstret = some w)
    (houtStrL : String.join cL.σ.sailOutput.toList = st'.out)
    (hframeL : ∀ R : Register, AbiPreservedNoise R → cL.σ.regs.get? R = gpre R)
    (hx8L : cL.σ.regs.get? Register.x8 = some aExpr)
    (hx18L : cL.σ.regs.get? Register.x18 = some aEnv)
    (hgx8v : gpre Register.x8 = some aExpr) (hgx18v : gpre Register.x18 = some aEnv)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    (hnode : read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat)
    (hpop : ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, cL.σ.mem[a]? = some b))
    (hstoreCL : StoreRepr cL.σ.mem N A φf1 φc1 st'.store)
    (hstoreSurvCL : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        cL.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store)
    (hexprSurvCL : ∀ m : Mem,
      (∀ k, aROp.toNat ≤ k → k < aROp.toNat + 16 → cL.σ.mem[k]? = m[k]?) →
      ExprRepr m aROp.toNat er)
    (hviCL : Value_intLoaded cL.σ.mem) (hviSlotCL : IntSlotPinned cL.σ.mem)
    (hnbsCL : NBSPins cL.σ.mem)
    (hslotRaL : read64 cL.σ.mem (sp.toNat - 8) = some r.toNat)
    (hslotS0L : read64 cL.σ.mem (sp.toNat - 16) = some v8.toNat)
    (hslotS1L : read64 cL.σ.mem (sp.toNat - 24) = some v9.toNat)
    (hslotS2L : read64 cL.σ.mem (sp.toNat - 32) = some v18.toNat)
    (hnode_hi : aExpr.toNat + 32 ≤ 0x100000000)
    (hnode_lo : 0x80000000 ≤ aExpr.toNat)
    (hnode_align : aExpr.toNat % 8 = 0)
    (hnode_win : tohostAddr + 32 ≤ aExpr.toNat)
    (hrop_align : aROp.toNat % 8 = 0)
    (hrop_ram : 0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000)
    (hrop_win : tohostAddr + 16 ≤ aROp.toNat)
    (hrop_stk : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat)
    (hrop_stkfull : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat)
    (hsp1088 : 1088 ≤ sp.toNat)
    (hsproom : SL.lo + 3264 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi)
    (hsp16 : sp.toNat % 16 = 0) (hsphi : sp.toNat ≤ 0x100000000)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLhiRam : SL.hi ≤ 0x100000000)
    (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo)
    (hviStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec)
    (htableStk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
    -- ITEM ZERO B1: threaded to `binaryR_midStagePre`.
    (hstackBudgetR : StackOK SL (sp - 1088#64)
      (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088))
    (hexprBodiesR : Expr.bodiesBound Vsa.While.perCallBudget er = true)
    (hstoreBodiesR : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    -- WAVE 47i: threaded to `binaryR_midStagePre`.
    (hGroundR_CL : EvalGround cL.σ.mem SL A sp sret aROp.toNat er) :
    LandedN 1 cL (fun c' => JalPreBundle er c' st' d env) :=
  LandedN.weakenCount (by omega : 1 ≤ 7)
    (binaryR_midStagePre gpre N A SL φf1 φc1 st' d env er sp r sret aExpr aEnv aROp
      v8 v9 v18 cL hGL htickL hpcL hs1L hspL hmiL houtStrL hframeL hx8L hx18L hgx8v hgx18v
      hcodeL hnode hpop hstoreCL hstoreSurvCL hexprSurvCL hviCL hviSlotCL hnbsCL hslotRaL hslotS0L
      hslotS1L hslotS2L hnode_hi hnode_lo hnode_align hnode_win hrop_align hrop_ram hrop_win
      hrop_stk hrop_stkfull hsp1088 hsproom hspSLhi hsp16 hsphi hSLlo hSLhiRam hSLwin
      hcodeStk hviStk htableStk harenaStk harenaCode
      hstackBudgetR hexprBodiesR hstoreBodiesR hGroundR_CL)

#print axioms binaryR_midStage1

end Vsa.Sim
