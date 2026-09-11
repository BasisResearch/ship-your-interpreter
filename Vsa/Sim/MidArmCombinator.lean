import Vsa.Sim.EvalBinSim
import Vsa.Sim.ArmSegSplitEval
import Vsa.Sim.LoadSitesTotB
import Vsa.Sim.BinaryRightStage

/-!
# Staging the right binary child

`binaryR_midStagePre` projects `binaryR_midStaged` into `JalPreBundle`.
The reflected seven-step prefix reads the actual right pointer and left
result, stages the right result slot, and respills the left kind.
The staged result retains fixed call witnesses and the reached ghost frame.
`binaryR_midStage1` projects the counted run to ordinary reachability.
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
* `hexprSurv` — `ExprRepr … aROp er` survives any write outside `[SL.lo, sp)`;
* `hstoreSurv` — `st'.store` re-represents under the same survival window;
* `hviCL` / `hviSlotCL` — `Value_intLoaded` / `IntSlotPinned` at `cL.σ.mem`;
* `hslot*` — the four OUTER spill slots at `[sp-32, sp)`;
* geometry (`BinExtras`-shaped disjointness / RAM / windows). -/
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
    (henvValid : EnvValid st' env)
    (henvRead : read64 cL.σ.mem (sp.toNat - 1088) =
      some (BitVec.ofNat 64 (φf1 env)).toNat)
    (henvset : ∃ w19 w20 w21 : BitVec 64,
      gpre Register.x19 = some w19 ∧ gpre Register.x20 = some w20 ∧
        gpre Register.x21 = some w21)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    -- the transported right-operand pointer + node bytes present:
    (hnode : read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat)
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
    (hnode_win : tohostAddr + 32 ≤ aExpr.toNat)
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
  have staged := binaryR_midStaged gpre N A SL φf1 φc1 st' d env er sp r sret aExpr aEnv aROp
      v8 v9 v18 cL hGL htickL hpcL hs1L hspL hmiL houtStrL hframeL hx8L hx18L hgx8v hgx18v
      henvValid henvRead henvset
      hcodeL hnode hstoreCL hstoreSurvCL
      (fun m agree => hexprSurvCL m (fun k hlo hhi =>
        agree k (by rcases hrop_stkfull with outside | outside <;> omega)))
      hviCL hviSlotCL hnbsCL hslotRaL hslotS0L
      hslotS1L hslotS2L hnode_hi hnode_lo hnode_win hrop_ram hrop_win
      hrop_stk hrop_stkfull hsp1088 hsproom hspSLhi hsp16 hsphi hSLlo hSLhiRam hSLwin
      hcodeStk hviStk htableStk harenaStk harenaCode
      hstackBudgetR hexprBodiesR hstoreBodiesR hGroundR_CL
  exact staged.weaken (fun after h =>
    ⟨(fun R => after.σ.regs.get? R), N, A, SL, φf1, φc1,
      0x80003518#64, 0x8000351c#64, 0x1ffc4c#21,
      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)),
      aEnv, aROp, v8, v9, v18, cL.σ.sailOutput, after.σ.mem, h.call⟩)

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
    (henvValid : EnvValid st' env)
    (henvRead : read64 cL.σ.mem (sp.toNat - 1088) =
      some (BitVec.ofNat 64 (φf1 env)).toNat)
    (henvset : ∃ w19 w20 w21 : BitVec 64,
      gpre Register.x19 = some w19 ∧ gpre Register.x20 = some w20 ∧
        gpre Register.x21 = some w21)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    (hnode : read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat)
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
    (hnode_win : tohostAddr + 32 ≤ aExpr.toNat)
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
      henvValid henvRead henvset
      hcodeL hnode hstoreCL hstoreSurvCL hexprSurvCL hviCL hviSlotCL hnbsCL hslotRaL hslotS0L
      hslotS1L hslotS2L hnode_hi hnode_lo hnode_win hrop_ram hrop_win
      hrop_stk hrop_stkfull hsp1088 hsproom hspSLhi hsp16 hsphi hSLlo hSLhiRam hSLwin
      hcodeStk hviStk htableStk harenaStk harenaCode
      hstackBudgetR hexprBodiesR hstoreBodiesR hGroundR_CL)

#print axioms binaryR_midStage1

end Vsa.Sim
