import Vsa.Sim.MidArmCombinator
import Vsa.Sim.EvalRecCommon

/-!
# `MidArmFieldIH` — the IH-carrying mid-arm field combinator (Wave 35)

## Why the `binaryR`/`logicalR` fields need an IH

The `EvalChildStages.binaryR` field is typed
`EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) → LandedN 1 c (JalPreBundle r c' st')`.
Its input is the SPEC-level left evaluation `EvalE l st' lv` plus the ARM-ENTRY config
`c`; it must land the config at the RIGHT `jal eval_expr` (`JalPreBundle r`).

The landed mid-arm re-cut `MidArmCombinator.binaryR_midStage1` handles the LAST leg
only: it starts from a config `cL` ALREADY at `SubEvalReturn` (PC `0x800034fc`,
post-left-return) and runs the 7 mid-arm sites to `JalPreBundle r`.  Bridging the arm
entry `c` to `cL` requires actually RUNNING the left `jal eval_expr` and RETURNING —
i.e. `armTail_rec`, whose `hIH` premise is the MACHINE-level `EvalIH st d env l st' vl`
(the ∀-closed simulation Triple `EvalEntry l ⇒ EvalExitD`).  That IH is NOT one of the
`binaryR` field's parameters — it lives at the divergence-fold's strong-induction, not
in the per-field staging.

So `binaryR`/`logicalR` cannot close from the field inputs alone (observation
`2026-09-01 binaryR-field-lacks-machine-IH`).  This file builds the HONEST seam the
fold instantiates: `midArmField_of_IH` takes the machine IH for the left operand as an
EXPLICIT premise, applies `armTail_rec` (reaching `SubEvalReturn`), then
`binaryR_midStage1` (reaching `JalPreBundle r`).  It composes the TWO landed halves
(`armTail_rec` ≫ `binaryR_midStage1`) at the config level — the mid-arm's precondition
is `SubEvalReturn`'s content plus the RIGHT-operand geometry that survives the left
call, named ONCE as `MidArmRightMarshal` (the residual the fold discharges from its
`BinArmExtras`, exactly as `EvalBinSim.blockB_binary` does inline).

The payoff: when the fold re-types `binaryR`/`logicalR` to carry the IH (proposal (b)
in the observation), the whole `SubEvalReturn → JalPreBundle r` mid-arm is a ONE-call
composition — no re-derivation of the 7 sites or the node transport.

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

/-- **The mid-arm right-operand marshalling residual.**  `binaryR_midStage1` needs its
config `cL` to satisfy a precondition (`hpcL … harenaCode`) that is `SubEvalReturn`'s
content (PC/regs/frame/store/spills) PLUS the RIGHT-operand facts that survive the left
call: the transported node pointer `read64 cL.σ.mem (aExpr+24) = aROp`, the frame
population on `[sp-1120, sp)`, the `ExprRepr … aROp er` survival, `Value_intLoaded`/
`IntSlotPinned` at `cL.σ.mem`, and the `BinExtras`-shaped right-operand geometry.

`SubEvalReturn` DOES NOT carry these (it only knows the LEFT sub-result), so they are an
honest carried premise here — exactly the `hAgNode`/`hPopCL`/`hexprR2` transport that
`EvalBinSim.blockB_binary` derives inline from `BinArmExtras` + the left `memFrame`.
Named as a predicate on the reached `SubEvalReturn` config so the fold discharges it
once per arm (over its own `BinArmExtras`), not per operator.

This is a `def : Prop` naming precisely the delta between `SubEvalReturn`'s content and
`binaryR_midStagePre`'s precondition — the ONE residual the mid-arm field owes. -/
def MidArmRightMarshal
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf1 φc1 : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (cL : Config) : Prop :=
  -- register/output facts at cL (SubEvalReturn's retPC = 0x800034fc, s0/s2 restored):
  cL.σ.regs.get? Register.PC = some (0x800034fc#64) ∧
  cL.σ.regs.get? Register.x9 = some sret ∧
  cL.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
  String.join cL.σ.sailOutput.toList = st'.out ∧
  (∀ R : Register, AbiPreservedNoise R → cL.σ.regs.get? R = gpre R) ∧
  cL.σ.regs.get? Register.x8 = some aExpr ∧
  cL.σ.regs.get? Register.x18 = some aEnv ∧
  gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
  -- transported right-operand node + frame population:
  read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat ∧
  (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, cL.σ.mem[a]? = some b)) ∧
  -- store/expr/value survival + spills at cL.σ.mem:
  StoreRepr cL.σ.mem N A φf1 φc1 st'.store ∧
  (∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      cL.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf1 φc1 st'.store) ∧
  (∀ m : Mem,
    (∀ k, aROp.toNat ≤ k → k < aROp.toNat + 16 → cL.σ.mem[k]? = m[k]?) →
    ExprRepr m aROp.toNat er) ∧
  Value_intLoaded cL.σ.mem ∧ IntSlotPinned cL.σ.mem ∧ NBSPins cL.σ.mem ∧
  read64 cL.σ.mem (sp.toNat - 8) = some r.toNat ∧
  read64 cL.σ.mem (sp.toNat - 16) = some v8.toNat ∧
  read64 cL.σ.mem (sp.toNat - 24) = some v9.toNat ∧
  read64 cL.σ.mem (sp.toNat - 32) = some v18.toNat ∧
  -- BinExtras-shaped right-operand geometry:
  aExpr.toNat + 32 ≤ 0x100000000 ∧ 0x80000000 ≤ aExpr.toNat ∧
  aExpr.toNat % 8 = 0 ∧ tohostAddr + 32 ≤ aExpr.toNat ∧
  aROp.toNat % 8 = 0 ∧
  (0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000) ∧
  tohostAddr + 16 ≤ aROp.toNat ∧
  (aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat) ∧
  (aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat) ∧
  1088 ≤ sp.toNat ∧
  SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧
  sp.toNat % 16 = 0 ∧ sp.toNat ≤ 0x100000000 ∧
  0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
  (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
  ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
  ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
  (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
  (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
  -- ITEM ZERO B1: the RIGHT operand's recursion-sound budget at `sp - 1088`,
  -- its `.fn`-bodies bound, and the post-LEFT store-bodies invariant.
  StackOK SL (sp - 1088#64)
    (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
  Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
  Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget

/-- **`midStage1_of_marshal`** — feed a `SubEvalReturn`-reached config `cL` (via the
`MidArmRightMarshal` residual, which repackages the right-operand geometry) into the
landed mid-arm re-cut `binaryR_midStage1`, landing at `JalPreBundle er st'`.

This is the ONE point the two landed halves plug together: `MidArmRightMarshal` is the
delta `SubEvalReturn` does not carry; everything else is projected straight through.
`GoodState`/`tick` come from `SubEvalReturn` (passed separately, since they are shared
with `armTail_rec`'s exit and not part of the right-operand delta). -/
theorem midStage1_of_marshal
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf1 φc1 : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (cL : Config)
    (hGL : GoodState cL.σ) (htickL : cL.tick < 2)
    (hmiL : ∃ w, cL.σ.regs.get? Register.minstret = some w)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    (hM : MidArmRightMarshal gpre N A SL φf1 φc1 st' d env er
            sp r sret aExpr aEnv aROp v8 v9 v18 cL) :
    LandedN 1 cL (fun c' => JalPreBundle er c' st' d env) := by
  obtain ⟨hpcL, hs1L, hspL, houtStrL, hframeL, hx8L, hx18L, hgx8v, hgx18v,
    hnode, hpop, hstoreCL, hstoreSurvCL, hexprSurvCL, hviCL, hviSlotCL, hnbsCL,
    hslotRaL, hslotS0L, hslotS1L, hslotS2L,
    hnode_hi, hnode_lo, hnode_align, hnode_win, hrop_align, hrop_ram, hrop_win,
    hrop_stk, hrop_stkfull, hsp1088, hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam,
    hSLwin, hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩ := hM
  exact binaryR_midStage1 gpre N A SL φf1 φc1 st' d env er sp r sret aExpr aEnv aROp
    v8 v9 v18 cL hGL htickL hpcL hs1L hspL hmiL houtStrL hframeL hx8L hx18L hgx8v hgx18v
    hcodeL hnode hpop hstoreCL hstoreSurvCL hexprSurvCL hviCL hviSlotCL hnbsCL hslotRaL hslotS0L
    hslotS1L hslotS2L hnode_hi hnode_lo hnode_align hnode_win hrop_align hrop_ram hrop_win
    hrop_stk hrop_stkfull hsp1088 hsproom hspSLhi hsp16 hsphi hSLlo hSLhiRam hSLwin
    hcodeStk hviStk htableStk harenaStk harenaCode
    hstackBudgetR hexprBodiesR hstoreBodiesR

#print axioms midStage1_of_marshal

/-- **`midArmField_of_IH`** — the FULL mid-arm field combinator: `armTail_rec` (the
left recursive call, via the machine IH) ≫ `binaryR_midStage1` (the mid-arm re-cut).

From a config `c` at the LEFT `jal eval_expr` (`armTail_rec`'s precondition `Pleft`,
which is precisely `JalPreBundle l`'s content), plus the machine IH for the left
operand (`EvalIH st d env l st' vsub`), plus the right-operand marshalling residual
(`MidArmRightMarshal` on EVERY `SubEvalReturn`-reached config), land at
`JalPreBundle r st'` — the exact `binaryR`/`logicalR` staging obligation.

The composition: `armTail_rec` gives a `Triple Pleft (SubEvalReturn …)`; turned into a
landing at `c` (`Landed.of_triple`), it reaches a `SubEvalReturn` config `cL`.  From
`cL`, `midStage1_of_marshal` lands `JalPreBundle r`.  `LandedN.bind` (via the `Landed`
form + a `≥ 1` recovery) composes the two runs.

`hMarshalAll` is the honest residual: for every config satisfying `SubEvalReturn` at the
arm's ghosts, the right-operand geometry (`MidArmRightMarshal`) holds — the fold
supplies it from its `BinArmExtras`.  The `GoodState`/`tick`/`minstret`/`code`
projections come straight out of `SubEvalReturn`. -/
theorem midArmField_of_IH
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (l r : Expr) (vsub : Value)
    (sp rr sret subsret aIn aLOp aROp aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem) (c : Config)
    -- `armTail_rec` fixed-target facts (the LEFT jal at 0x800034f8, retPC 0x800034fc):
    (hjaltgt : ((0x800034f8#64 : BitVec 64) + sign_extend (m := 64) (0x1ffc6c#21))
      = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt (0x800034f8#64) 4) = (0x800034fc#64 : BitVec 64))
    (hretAl : (0x800034fc#64 : BitVec 64).toNat % 4 = 0)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some (0x800034f8#64) →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ (0x800034f8#64) vmi (0x1ffc6c#21) Register.x1
          (BitVec.addInt (0x800034f8#64) 4)))
    (hIH : EvalIH st d env l st' vsub)
    -- the honest right-operand marshalling residual on every SubEvalReturn config:
    (hMarshalAll : ∀ cL : Config,
      SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' vsub sp rr sret subsret (0x800034fc#64) v8 v9 v18 mcall cL →
      MidArmRightMarshal gpre N A SL φf φc st' d env r
        sp rr sret aExpr aEnv aROp v8 v9 v18 cL)
    -- `armTail_rec`'s precondition (= `JalPreBundle l`'s content) at the arm entry `c`:
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (0x800034f8#64) ∧
        c.σ.regs.get? Register.x10 = some subsret ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x12 = some aLOp ∧
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧ NBSPins mcall ∧
        ExprRepr mcall aLOp.toNat l ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
        read64 mcall (sp.toNat - 8) = some rr.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        aLOp.toNat % 8 = 0 ∧
        0x80000000 ≤ aLOp.toNat ∧ aLOp.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aLOp.toNat ∧
        (aLOp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLOp.toNat) ∧
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the LEFT operand's recursion-sound budget at `sp - 1088`,
        -- its `.fn`-bodies bound, and the store-bodies invariant (the amended
        -- `armTail_rec` pre-tail).
        StackOK SL (sp - 1088#64)
          (l.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget l = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 1 c (fun c' => JalPreBundle r c' st' d env) := by
  -- run the LEFT recursive call to `SubEvalReturn`
  have hTriple := armTail_rec gpre N A SL φf φc st st' d env l vsub
    (0x800034f8#64) (0x800034fc#64) (0x1ffc6c#21)
    sp rr sret subsret aIn aLOp v8 v9 v18 out0 mcall
    hjaltgt hlink hretAl hjalSite hIH
  obtain ⟨cL, hsL, hSER⟩ := hTriple c hpre
  -- the SubEvalReturn config `cL` supplies GoodState/tick/minstret/code + the marshal.
  -- Keep `hSER` intact for `hMarshalAll`; project the shared facts from a copy.
  obtain ⟨hGL, htickL, hpcL', ha0L, hraL, hs1L, hspL', hmiL, houtL, hframeL,
    _hvalL, _hstoreBundleL, hcodeL, _rest⟩ := id hSER
  -- land `JalPreBundle r` from `cL` via the mid-arm re-cut
  obtain ⟨m2, c2, hm2, hs2, hpb⟩ :=
    midStage1_of_marshal gpre N A SL φf φc st' d env r sp rr sret aExpr aEnv aROp
      v8 v9 v18 cL hGL htickL hmiL hcodeL
      (hMarshalAll cL hSER)
  -- compose the two runs (`hsL : Steps c cL`, `hs2 : StepsN m2 cL c2`, `m2 ≥ 1`)
  obtain ⟨n1, hn1⟩ := hsL.toN
  exact ⟨n1 + m2, c2, by omega, hn1.trans_add hs2, hpb⟩

#print axioms midArmField_of_IH

end Vsa.Sim
