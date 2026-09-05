import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.rows.CallCruxMarshal
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.EnvSetReturn
import Vsa.Sim.rows.AssignArmReturnGen
import Vsa.Sim.rows.AssignArmStageGen
import Vsa.Sim.DecodeTable.Batch13Part11
import Vsa.Sim.EnvSetPrologueHead
import Vsa.Sim.EnvSetComplete
import Vsa.Sim.BridgeSegOut

/-! The shared successful var/assign value-copy tail, starting exactly at
`0x80003448`.  The assign arm reaches this address from `0x800034b4`; it does
not execute the var arm's branch at `0x80003444`. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

#derive_case evalValueReturnTailSeg chain
  [(0x80003448#64, 0x0f013683#32),  -- ld a3,240(sp)
   (0x8000344c#64, 0x0f813703#32),  -- ld a4,248(sp)
   (0x80003450#64, 0x10013783#32),  -- ld a5,256(sp)
   (0x80003454#64, 0x43813083#32),  -- ld ra,1080(sp)
   (0x80003458#64, 0x43013403#32),  -- ld s0,1072(sp)
   (0x8000345c#64, 0x00d4b023#32),  -- sd a3,0(s1)
   (0x80003460#64, 0x00e4b423#32),  -- sd a4,8(s1)
   (0x80003464#64, 0x00f4b823#32),  -- sd a5,16(s1)
   (0x80003468#64, 0x42013903#32),  -- ld s2,1056(sp)
   (0x8000346c#64, 0x00048513#32),  -- mv a0,s1
   (0x80003470#64, 0x42813483#32),  -- ld s1,1064(sp)
   (0x80003474#64, 0x44010113#32)]  -- addi sp,sp,1088
    terminator ⟨0x80003478#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def evalValueReturnTailL (sp sret : BitVec 64) : GRegs := [(2, sp), (9, sret)]

def evalValueReturnTailLds
    (d0 d1 d2 ret r8 r18 r9 : BitVec 64) : List (List (BitVec 8)) :=
  [envSetWordBytes d0, envSetWordBytes d1, envSetWordBytes d2,
   envSetWordBytes ret, envSetWordBytes r8, envSetWordBytes r18,
   envSetWordBytes r9]

structure EvalValueReturnTailPost
    (sp sret d0 d1 d2 ret r8 r18 r9 : BitVec 64)
    (m0 : Mem) (out0 : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = writeLog m0
    (evalBlocks evalValueReturnTailSeg
      (SegEvalState.init (evalValueReturnTailL sp sret)
        (evalValueReturnTailLds d0 d1 d2 ret r8 r18 r9))).log
  output : c.σ.sailOutput = out0
  pc : c.σ.regs.get? Register.PC = some ret
  a0 : c.σ.regs.get? Register.x10 = some sret
  ra : c.σ.regs.get? Register.x1 = some ret
  sp : c.σ.regs.get? Register.x2 = some (sp + 1088#64)
  s0 : c.σ.regs.get? Register.x8 = some r8
  s1 : c.σ.regs.get? Register.x9 = some r9
  s2 : c.σ.regs.get? Register.x18 = some r18

theorem eval_value_return_tail_row
    (sp sret d0 d1 d2 ret r8 r18 r9 : BitVec 64)
    (m0 : Mem) (out0 : Array String)
    (hret : BitVec.update (ret + sign_extend (m := 64) (0x000#12)) 0 0#1 = ret) :
    Triple
      (SegPreO evalValueReturnTailSeg (evalValueReturnTailL sp sret)
        (evalValueReturnTailLds d0 d1 d2 ret r8 r18 r9)
        0x80003448#64 m0 out0)
      (EvalValueReturnTailPost sp sret d0 d1 d2 ret r8 r18 r9 m0 out0) := by
  apply segToTripleOut evalValueReturnTailSeg (evalValueReturnTailL sp sret)
    (evalValueReturnTailLds d0 d1 d2 ret r8 r18 r9) 0x80003448#64 m0 out0
    (EvalValueReturnTailPost sp sret d0 d1 d2 ret r8 r18 r9 m0 out0)
    (by show ChainOK 0x80003448#64 [2, 9] evalValueReturnTailSeg; decide)
  intro σ' i' u' hG hi hmem hout hpc _hmi hregs
  have hpc' := hpc
  change σ'.regs.get? Register.PC = some
    (BitVec.update
      (bytesVal MKind.ld (envSetWordBytes ret) + sign_extend (m := 64) (0x000#12))
      0 0#1) at hpc'
  rw [envSetWordBytes_val, hret] at hpc'
  have ha0' := gholds_lookup (n := 10)
    (v := sret + sign_extend (m := 64) (0x000#12)) _ hregs (by rfl)
  have ha0Eq : sret + sign_extend (m := 64) (0x000#12) = sret := by
    have hz : sign_extend (m := 64) (0x000#12) = (0#64 : BitVec 64) := by decide
    rw [hz, BitVec.add_zero]
  rw [ha0Eq] at ha0'
  have hra := gholds_lookup (n := 1)
    (v := bytesVal MKind.ld (envSetWordBytes ret)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hra
  have hsp := gholds_lookup (n := 2)
    (v := sp + sign_extend (m := 64) (0x440#12)) _ hregs (by rfl)
  have hspEq : sp + sign_extend (m := 64) (0x440#12) = sp + 1088#64 := by
    congr 1
  rw [hspEq] at hsp
  have hs0 := gholds_lookup (n := 8)
    (v := bytesVal MKind.ld (envSetWordBytes r8)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs0
  have hs1 := gholds_lookup (n := 9)
    (v := bytesVal MKind.ld (envSetWordBytes r9)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs1
  have hs2 := gholds_lookup (n := 18)
    (v := bytesVal MKind.ld (envSetWordBytes r18)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs2
  exact ⟨hG, hi, hmem, hout, hpc', ha0', hra, hsp, hs0, hs1, hs2⟩

#print axioms eval_value_return_tail_row

/-! The assign arm's successful `bnez` route.  Its live register list retains
the two registers consumed by the shared tail. -/

def assignArmReturnLiveL (a0 sp sret : BitVec 64) : GRegs :=
  [(10, a0), (2, sp), (9, sret)]

def AssignValueReturnPre
    (a0 sp sret d0 d1 d2 ret r8 r18 r9 : BitVec 64)
    (m0 : Mem) (out0 : Array String) (c : Config) : Prop :=
  SegPreO assignArmReturnSeg (assignArmReturnLiveL a0 sp sret) []
    0x800034b4#64 m0 out0 c ∧
  ChainFacts m0 m0 (evalValueReturnTailL sp sret)
    (evalValueReturnTailLds d0 d1 d2 ret r8 r18 r9) evalValueReturnTailSeg

structure AssignArmReturnLivePost
    (sp sret : BitVec 64) (m0 : Mem) (out0 : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m0
  output : c.σ.sailOutput = out0
  pc : c.σ.regs.get? Register.PC = some 0x80003448#64
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  sp : c.σ.regs.get? Register.x2 = some sp
  sret : c.σ.regs.get? Register.x9 = some sret

theorem assign_arm_return_live_row
    (a0 sp sret : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (SegPreO assignArmReturnSeg (assignArmReturnLiveL a0 sp sret) []
        0x800034b4#64 m0 out0)
      (AssignArmReturnLivePost sp sret m0 out0) := by
  apply segToTripleOut assignArmReturnSeg (assignArmReturnLiveL a0 sp sret) []
    0x800034b4#64 m0 out0 (AssignArmReturnLivePost sp sret m0 out0)
    (by show ChainOK 0x800034b4#64 [10, 2, 9] assignArmReturnSeg; decide)
  intro σ' i' u' hG hi hmem hout hpc hmi hregs
  have hmem' : σ'.mem = m0 := by simpa using hmem
  have hpc' : σ'.regs.get? Register.PC = some 0x80003448#64 := by
    simpa using hpc
  have hsp : σ'.regs.get? Register.x2 = some sp :=
    gholds_lookup (n := 2) (v := sp) _ hregs (by rfl)
  have hsret : σ'.regs.get? Register.x9 = some sret :=
    gholds_lookup (n := 9) (v := sret) _ hregs (by rfl)
  exact ⟨hG, hi, hmem', hout, hpc', hmi, hsp, hsret⟩

theorem assign_arm_return_to_value_tail
    (a0 sp sret d0 d1 d2 ret r8 r18 r9 : BitVec 64)
    (m0 : Mem) (out0 : Array String)
    (hret : BitVec.update (ret + sign_extend (m := 64) (0x000#12)) 0 0#1 = ret) :
    Triple
      (AssignValueReturnPre a0 sp sret d0 d1 d2 ret r8 r18 r9 m0 out0)
      (EvalValueReturnTailPost sp sret d0 d1 d2 ret r8 r18 r9 m0 out0) := by
  apply Triple.seq (Q := SegPreO evalValueReturnTailSeg
    (evalValueReturnTailL sp sret)
    (evalValueReturnTailLds d0 d1 d2 ret r8 r18 r9)
    0x80003448#64 m0 out0)
  · intro c hpre
    obtain ⟨c', hs, hp⟩ := assign_arm_return_live_row a0 sp sret m0 out0 c hpre.1
    refine ⟨c', hs, ⟨⟨hp.good, hp.mem, hp.pc, hp.minstret, ?_, ?_, ?_, hp.tick⟩,
      hp.output⟩⟩
    · exact ⟨hp.sp, hp.sret, trivial⟩
    · have hk : keysG (evalValueReturnTailL sp sret) = [2, 9] := rfl
      rw [hk]
      decide
    · simpa [hp.mem] using hpre.2
  · exact eval_value_return_tail_row sp sret d0 d1 d2 ret r8 r18 r9 m0 out0 hret

#print axioms assign_arm_return_to_value_tail

/-! Concrete `jal env_set` seam at `0x800034b0`. -/

theorem site_800034b0_assign_set
    (σ : Vsa.Machine.MState) (i u : Nat) (vminstret : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800034b0#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem) (hi : i < 2) :
    ∃ (σ' : Vsa.Machine.MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ 0x800034b0#64 vminstret 0x1ff82c#21 Register.x1
          0x800034b4#64) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800034b0 hmem
  refine stepObs_jal σ i u (0x800034b0#64) vminstret (0x82dff0ef#32)
    (0x1ff82c#21) (regidx.Regidx 0x01#5) Register.x1 (0x800034b4#64)
    (0xef#8) (0xf0#8) (0xdf#8) (0x82#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_82dff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (0x800034b4#64)

theorem assign_env_set_jal_step
    (σ : Vsa.Machine.MState) (i u : Nat)
    (hG : GoodState σ) (hi : i < 2)
    (hpc : σ.regs.get? Register.PC = some (0x800034b0#64 : BitVec 64))
    (hmi : ∃ w, σ.regs.get? Register.minstret = some w)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    JalStep 0x80002cdc#64 0x800034b4#64 σ i u := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨σ', i', hs, hi', hG', hm, ho⟩ :=
    site_800034b0_assign_set σ i u vm hG hpc hvm hmem hi
  exact jalStep_of_obs hs hi' hG' hm ho
    (by apply BitVec.eq_of_toNat_eq; decide)

#print axioms assign_env_set_jal_step

theorem assign_env_set_jal_step_o
    (σ : Vsa.Machine.MState) (i u : Nat)
    (hG : GoodState σ) (hi : i < 2)
    (hpc : σ.regs.get? Register.PC = some (0x800034b0#64 : BitVec 64))
    (hmi : ∃ w, σ.regs.get? Register.minstret = some w)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    JalStepO 0x80002cdc#64 0x800034b4#64 σ i u := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨σ', i', hs, hi', hG', hm, ho⟩ :=
    site_800034b0_assign_set σ i u vm hG hpc hvm hmem hi
  obtain ⟨σ2, i2, hs2, hi2, hG2, hm2, hpc', hra', hmi', hnonra, habi⟩ :=
    jalStep_of_obs (jalPC := 0x800034b0#64) (imm := 0x1ff82c#21)
      (calleeEntry := 0x80002cdc#64) (link := 0x800034b4#64) hs hi' hG' hm ho
      (by apply BitVec.eq_of_toNat_eq; decide)
  have heq := Vsa.Machine.Step.deterministic hs2 hs
  cases heq
  refine ⟨σ', i', hs, hi', hG', hm, ?_, hpc', hra', hmi', hnonra, habi⟩
  rw [ho.out, sailOutput_sigmaPost_jal]

def assignArmStageLds
    (name d0 d1 d2 env : BitVec 64) : List (List (BitVec 8)) :=
  [envSetWordBytes name, envSetWordBytes d0, envSetWordBytes d1,
   envSetWordBytes d2, envSetWordBytes env]

def assignArmStageMem
    (s0 sp name d0 d1 d2 env : BitVec 64) (m : Mem) : Mem :=
  writeLog m (evalBlocks assignArmStageSeg
    (SegEvalState.init (assignArmStageL s0 sp)
      (assignArmStageLds name d0 d1 d2 env))).log

/-- Exact facts that are external to the reflected staging span: its load
readbacks and the geometry/readbacks consumed by `env_set` at the computed
post-memory. -/
structure AssignEnvSetStageFacts
    (s0 sp sret name d0 d1 d2 env : BitVec 64)
    (r8 r18 r19 r20 r21 : BitVec 64) (len pn : Nat) (m : Mem) : Prop where
  chainFacts : ChainFacts m m (assignArmStageL s0 sp)
    (assignArmStageLds name d0 d1 d2 env) assignArmStageSeg
  postCode : Vsa.Sim.Code.Eval_exprLoaded
    (assignArmStageMem s0 sp name d0 d1 d2 env m)
  postSet : Vsa.Sim.Code.Env_setLoaded
    (assignArmStageMem s0 sp name d0 d1 d2 env m)
  readLen : read32 (assignArmStageMem s0 sp name d0 d1 d2 env m) env.toNat = some len
  readPn : read64 (assignArmStageMem s0 sp name d0 d1 d2 env m) (env.toNat + 8) = some pn
  envNe : (env == (0#64 : BitVec 64)) = false
  spDrop : 0x40 ≤ sp.toNat
  spLo : 0x80000000 ≤ sp.toNat - 64
  spHi : sp.toNat ≤ 0x100000000
  spWin : tohostAddr + 64 ≤ sp.toNat - 64
  spAlign : sp.toNat % 8 = 0
  spCode : sp.toNat ≤ 0x80002cdc ∨ 0x80002da8 ≤ sp.toNat - 64
  envHi : env.toNat + 24 ≤ 0x100000000
  envStackDisj : env.toNat + 24 ≤ sp.toNat - 64 ∨ sp.toNat ≤ env.toNat

structure AssignArmStageEntry
    (s0 sp sret name d0 d1 d2 env : BitVec 64)
    (r8 r18 r19 r20 r21 : BitVec 64) (m : Mem) (out0 : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x8000348c#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = m
  output : c.σ.sailOutput = out0
  s0 : c.σ.regs.get? Register.x8 = some s0
  sp : c.σ.regs.get? Register.x2 = some sp
  sret : c.σ.regs.get? Register.x9 = some sret
  cs18 : c.σ.regs.get? Register.x18 = some r18
  cs19 : c.σ.regs.get? Register.x19 = some r19
  cs20 : c.σ.regs.get? Register.x20 = some r20
  cs21 : c.σ.regs.get? Register.x21 = some r21

theorem assign_arm_stage_to_env_set_entry
    (s0 sp sret name d0 d1 d2 env : BitVec 64)
    (r8 r18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (m : Mem) (out0 : Array String) (c : Config)
    (hE : AssignArmStageEntry s0 sp sret name d0 d1 d2 env
      r8 r18 r19 r20 r21 m out0 c)
    (hF : AssignEnvSetStageFacts s0 sp sret name d0 d1 d2 env
      r8 r18 r19 r20 r21 len pn m) :
    ∃ c', Vsa.Machine.Steps c c' ∧
      SetPrologueHeadSt env name (sp + 64#64) sp 0x800034b4#64
        s0 sret r18 r19 r20 r21 len pn
        (assignArmStageMem s0 sp name d0 d1 d2 env m) c' ∧
      c'.σ.sailOutput = out0 := by
  obtain ⟨vm, hvm⟩ := hE.minstret
  obtain ⟨σ', i', hs, hi, hG, hpc, hra, hmi, hregs, hmem, hout, habi⟩ :=
    bridgeOfSegOut assignArmStageSeg (assignArmStageL s0 sp)
      (assignArmStageLds name d0 d1 d2 env) c.σ c.tick c.steps
      0x8000348c#64 0x80002cdc#64 0x800034b4#64 vm m
      hE.good hE.pc hvm hE.mem ⟨hE.s0, hE.sp, trivial⟩
      (by show KeysOK [8, 2]; decide)
      (by simpa [hE.mem] using hF.chainFacts) hE.tick
      (by show ChainOK 0x8000348c#64 [8, 2] assignArmStageSeg; decide)
      (by show WrChainAvoidAbi assignArmStageSeg; decide)
      (by
        have hk : keysG (evalBlocks assignArmStageSeg
          (SegEvalState.init (assignArmStageL s0 sp)
            (assignArmStageLds name d0 d1 d2 env))).regs =
            [12, 10, 15, 14, 16, 11, 8, 2] := rfl
        rw [hk]
        decide)
      (by
        have hk : keysG (evalBlocks assignArmStageSeg
          (SegEvalState.init (assignArmStageL s0 sp)
            (assignArmStageLds name d0 d1 d2 env))).regs =
            [12, 10, 15, 14, 16, 11, 8, 2] := rfl
        unfold KeysAvoidRa
        rw [hk]
        decide)
      (fun σp ip up hg hip hp hm hmp hr =>
        assign_env_set_jal_step_o σp ip up hg hip hp hm
          (by rw [hmp]; exact hF.postCode))
  let c' : Config := ⟨σ', i', c.steps + evalBlocksFuel assignArmStageSeg + 1⟩
  have hmem' : σ'.mem = assignArmStageMem s0 sp name d0 d1 d2 env m := hmem
  have ha0 : σ'.regs.get? Register.x10 = some env :=
    gholds_lookup (n := 10) (v := bytesVal MKind.ld (envSetWordBytes env)) _ hregs (by rfl)
      |>.trans (by rw [envSetWordBytes_val])
  have ha1 : σ'.regs.get? Register.x11 = some name :=
    gholds_lookup (n := 11) (v := bytesVal MKind.ld (envSetWordBytes name)) _ hregs (by rfl)
      |>.trans (by rw [envSetWordBytes_val])
  have ha2 : σ'.regs.get? Register.x12 = some (sp + 64#64) := by
    have hh := gholds_lookup (n := 12)
      (v := sp + sign_extend (m := 64) (0x040#12)) _ hregs (by rfl)
    simpa using hh
  refine ⟨c', hs, ?_, hout.trans hE.output⟩
  exact
    { good := hG
      loadedG := by rw [hmem']; exact hF.postSet
      mem := hmem'
      pc := hpc
      a0 := ha0
      a1 := ha1
      a2 := ha2
      ra := hra
      sp := habi Register.x2 (by decide) |>.trans hE.sp
      cs8 := habi Register.x8 (by decide) |>.trans hE.s0
      cs9 := habi Register.x9 (by decide) |>.trans hE.sret
      cs18 := habi Register.x18 (by decide) |>.trans hE.cs18
      cs19 := habi Register.x19 (by decide) |>.trans hE.cs19
      cs20 := habi Register.x20 (by decide) |>.trans hE.cs20
      cs21 := habi Register.x21 (by decide) |>.trans hE.cs21
      minstret := hmi
      tick := hi
      envNe := hF.envNe
      read_len := hF.readLen
      read_pn := hF.readPn
      spDrop := hF.spDrop
      spLo := hF.spLo
      spHi := hF.spHi
      spWin := hF.spWin
      spAlign := hF.spAlign
      spCode := hF.spCode
      envHi := hF.envHi
      envStackDisj := hF.envStackDisj }

#print axioms assign_arm_stage_to_env_set_entry

structure AssignReturnChainFacts
    (sp sret d0 d1 d2 ret r8 r18 r9 : BitVec 64) (m : Mem) : Prop where
  branch : ChainFacts m m (assignArmReturnLiveL 1#64 sp sret) [] assignArmReturnSeg
  tail : ChainFacts m m (evalValueReturnTailL sp sret)
    (evalValueReturnTailLds d0 d1 d2 ret r8 r18 r9) evalValueReturnTailSeg

/-- Concrete post-RHS staging, the complete recursive `env_set`, the successful
assign branch, and the exact shared value-copy tail. -/
theorem assign_arm_stage_env_set_value_tail
    (store store' : Vsa.While.Store) (start : Vsa.While.Addr)
    (nameStr : String) (newValue : Vsa.While.Value)
    (bridge : AssignStoreBridge store store' start nameStr newValue)
    (s0 sp sret name d0 d1 d2 env : BitVec 64)
    -- `interp18` is the live interpreter pointer saved/restored by `env_set`.
    -- `saved18` is the outer caller's x18 image at `[sp+1056]`, restored only
    -- by the final `eval_expr` tail.  They are not interchangeable.
    (r8 interp18 saved18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (m : Mem) (out0 : Array String) (c : Config)
    (hE : AssignArmStageEntry s0 sp sret name d0 d1 d2 env
      r8 interp18 r19 r20 r21 m out0 c)
    (hF : AssignEnvSetStageFacts s0 sp sret name d0 d1 d2 env
      r8 interp18 r19 r20 r21 len pn m)
    (henv : env = BitVec.ofNat 64 (φf start))
    (hStoreSurv : ∀ m',
      (∀ k, ¬ ((sp - 64#64).toNat ≤ k ∧ k < (sp - 64#64).toNat + 64) →
        m'[k]? = (assignArmStageMem s0 sp name d0 d1 d2 env m)[k]?) →
      StoreRepr m' N A φf φc store)
    (hFactsSurv : ∀ m',
      (∀ k, ¬ ((sp - 64#64).toNat ≤ k ∧ k < (sp - 64#64).toNat + 64) →
        m'[k]? = (assignArmStageMem s0 sp name d0 d1 d2 env m)[k]?) →
      EnvSetChainFacts name (sp + 64#64) (sp - 64#64) 0x800034b4#64
        s0 sret interp18 r19 r20 r21 nameStr newValue N A φf φc m' store)
    (hStrcmpSurv : ∀ m',
      (∀ k, ¬ ((sp - 64#64).toNat ≤ k ∧ k < (sp - 64#64).toNat + 64) →
        m'[k]? = (assignArmStageMem s0 sp name d0 d1 d2 env m)[k]?) →
      Vsa.Sim.Code.StrcmpLoaded m')
    (hretSet : BitVec.update
      (0x800034b4#64 + sign_extend (m := 64) (0x000#12)) 0 0#1 = 0x800034b4#64)
    (hReturnFacts : ∀ m' target,
      StoreSetAdvance N A φf φc store store' start nameStr newValue
        bridge target m' →
      AssignReturnChainFacts sp sret d0 d1 d2 0x800034b4#64 s0 saved18 sret m') :
    ∃ c' mSet target, Vsa.Machine.Steps c c' ∧
      StoreSetAdvance N A φf φc store store' start nameStr newValue
        bridge target mSet ∧
      EvalValueReturnTailPost sp sret d0 d1 d2 0x800034b4#64 s0 saved18 sret
        mSet out0 c' := by
  subst env
  obtain ⟨cSetEntry, hsStage, hSetEntry, hSetOut⟩ :=
    assign_arm_stage_to_env_set_entry s0 sp sret name d0 d1 d2
      (BitVec.ofNat 64 (φf start))
      r8 interp18 r19 r20 r21 len pn m out0 c hE hF
  obtain ⟨cSet, _m9, hsSet, hSetPost, ⟨target, hAdvance⟩, _hframe⟩ :=
    env_set_from_entry store store' start nameStr newValue bridge name (sp + 64#64)
      sp 0x800034b4#64 s0 sret interp18 r19 r20 r21 N A φf φc
      (assignArmStageMem s0 sp name d0 d1 d2 (BitVec.ofNat 64 (φf start)) m)
      cSetEntry len pn
      hSetEntry hStoreSurv hFactsSurv hStrcmpSurv hretSet
  have hspRestore : (sp - 64#64) + 64#64 = sp := by
    have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
    have hsubNat : (sp - 64#64).toNat = sp.toNat - 64 := by
      rw [BitVec.toNat_sub, h64]
      have hlt := sp.isLt
      have hdrop := hF.spDrop
      rw [show 2^64 - 64 + sp.toNat = (sp.toNat - 64) + 2^64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsubNat, h64]
    have hlt := sp.isLt
    have hdrop := hF.spDrop
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hCF := hReturnFacts cSet.σ.mem target hAdvance
  have hReturnPre : AssignValueReturnPre 1#64 sp sret d0 d1 d2
      0x800034b4#64 s0 saved18 sret cSet.σ.mem out0 cSet := by
    refine ⟨?_, hCF.tail⟩
    refine ⟨?_, hSetPost.output.trans hSetOut⟩
    refine ⟨hSetPost.good, rfl, hSetPost.pc, hSetPost.minstret, ?_, ?_,
      hCF.branch, hSetPost.tick⟩
    · exact ⟨hSetPost.found, hspRestore ▸ hSetPost.sp, hSetPost.s1, trivial⟩
    · change KeysOK [10, 2, 9]
      decide
  obtain ⟨c', hsReturn, hTail⟩ :=
    assign_arm_return_to_value_tail 1#64 sp sret d0 d1 d2 0x800034b4#64
      s0 saved18 sret cSet.σ.mem out0 hretSet cSet hReturnPre
  exact ⟨c', cSet.σ.mem, target, (hsStage.trans hsSet).trans hsReturn, hAdvance, hTail⟩

#print axioms assign_arm_stage_env_set_value_tail

end Vsa.Sim
