import Vsa.Sim.HelperCallEnvDefine
import Vsa.Sim.HelperCallSites
import Vsa.Sim.Exec_stmtSites3
import Vsa.Sim.rows.ExecDispatchRows

/-!
# `EnvDefineCall` — the declaration tail on the helper-call layer

Both declaration forms rejoin at `0x800040f0` with the value in the slot at
`esp+104` (the initializer's result, or `.null` from the bridge):

```
800040f0  ld   a1,8(s0)        -- the name
800040f4  ld   a3,104(sp)      -- the three value words
800040f8  ld   a4,112(sp)
800040fc  ld   a5,120(sp)
80004100  mv   a0,s3           -- env
80004104  addi a2,sp,16        -- the value buffer
80004108  sd   a3,16(sp)
8000410c  sd   a4,24(sp)
80004110  sd   a5,32(sp)
80004114  jal  env_define
80004118  li   a0,0 ; j 0x8000409c
```

`envDefineTail_run` runs this tail from any route-ready state at the rejoin,
given the `env_define` contract: the copy, the parametric call, the contract,
and the normal exit.  It is the resume of `hSVarInit` and the tail of
`hSVarNull`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case envDefineCopySeg chain
  [(0x800040f0#64, 0x00843583#32),  -- discipline: allow(R12-helper-call-arm) the HelperCall instance's own prefix
   (0x800040f4#64, 0x06813683#32),
   (0x800040f8#64, 0x07013703#32),
   (0x800040fc#64, 0x07813783#32),
   (0x80004100#64, 0x00098513#32),
   (0x80004104#64, 0x01010613#32),
   (0x80004108#64, 0x00d13823#32),
   (0x8000410c#64, 0x00e13c23#32),
   (0x80004110#64, 0x02f13023#32)]

/-- The `env_define` call of the declaration tail. -/
def envDefineCall : HelperCall :=
  { headPC := 0x800040f0#64
    seg := envDefineCopySeg
    jalPC := 0x80004114#64
    jalImm := 0x1fe948#21
    entry := 0x80002a5c#64 }

theorem envDefineCall_cert : envDefineCall.Cert where
  ret_align := by decide
  ret_clean := by decide
  jal_tgt := by decide
  avoid_abi := by change WrChainAvoidAbi envDefineCopySeg; decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004114_hc σ i u _ vmi hG hpc hmi hmem rfl hi

/-- The four loads of the tail: the name pointer and the three value words. -/
def envDefineLds (m : Mem) (aStmt esp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (aStmt.toNat + 8),
   EvalChildArm.wordLds8 m (esp.toNat + 104),
   EvalChildArm.wordLds8 m (esp.toNat + 104 + 8),
   EvalChildArm.wordLds8 m (esp.toNat + 104 + 16)]

/-- The tail's write log is the three-word copy from `esp+104` to `esp+16`. -/
theorem envDefineCopy_log (a0 esp s0 s1 s2 s3 : BitVec 64) (m : Mem) (aStmt : BitVec 64)
    (hesp : esp.toNat + 40 < 2 ^ 64) :
    writeLog m (envDefineCall.out (HelperCall.callL a0 esp s0 s1 s2 s3)
      (envDefineLds m aStmt esp)).log =
    copy3Log m (esp.toNat + 104) (esp.toNat + 16) := by
  have h16 := off_toNat esp 0x010#12 16 (by omega) (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have h24 : (esp + sign_extend (m := 64) (0x018#12)).toNat = esp.toNat + 16 + 8 := by
    rw [off_toNat esp 0x018#12 24 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)]
  have h32 : (esp + sign_extend (m := 64) (0x020#12)).toNat = esp.toNat + 16 + 16 := by
    rw [off_toNat esp 0x020#12 32 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)]
  show writeMap8 (writeMap8 (writeMap8 m
      (esp + sign_extend (m := 64) (0x010#12)).toNat
      (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + 104)))))
      (esp + sign_extend (m := 64) (0x018#12)).toNat
      (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + 104 + 8)))))
      (esp + sign_extend (m := 64) (0x020#12)).toNat
      (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + 104 + 16)))) = _
  rw [h16, h24, h32]
  rfl

/-- Chain facts of the tail from the lowered-frame geometry. -/
theorem envDefineCopy_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64} {s : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat s)
    (hcode : Exec_stmtLoaded m)
    (esp : BitVec 64)
    (hlo : SL.lo ≤ esp.toNat) (hhi : esp.toNat + 136 ≤ SL.hi)
    (hram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ SL.lo) (halign : esp.toNat % 16 = 0)
    (a0 s1 s2 s3 : BitVec 64) :
    ChainFacts m m (HelperCall.callL a0 esp aStmt s1 s2 s3)
      (envDefineLds m aStmt esp) envDefineCopySeg := by
  have hhi32 : esp.toNat + 136 ≤ 0x100000000 := Nat.le_trans hhi hram.2
  have htohost : tohostAddr + 16 ≤ esp.toNat := Nat.le_trans hwin hlo
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 120)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (esp + sign_extend (m := 64) off).toNat = esp.toNat + n :=
    off_toNat esp off n (by omega) (by omega) hoff
  have ha16 := haddr 0x010#12 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha24 := haddr 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha32 := haddr 0x020#12 32 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha104 := haddr 0x068#12 104 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha112 := haddr 0x070#12 112 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha120 := haddr 0x078#12 120 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  unfold envDefineCopySeg envDefineLds ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact hg.node_ld_facts (0x008#12) 8 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x068#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x068#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x068#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 104)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha104]; omega
    · rw [ha104]; omega
    · right; rw [ha104]; omega
    · rw [ha104]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x070#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x070#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x070#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 104 + 8)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha112]; omega
    · rw [ha112]; omega
    · right; rw [ha112]; omega
    · rw [ha112, show esp.toNat + 112 = esp.toNat + 104 + 8 by omega]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x078#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x078#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x078#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 104 + 16)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha120]; omega
    · rw [ha120]; omega
    · right; rw [ha120]; omega
    · rw [ha120, show esp.toNat + 120 = esp.toNat + 104 + 16 by omega]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha16] <;> omega
  · change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha24] <;> omega
  · change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha32] <;> omega

/-- The `li a0,0` site of the declaration tail. -/
theorem envDefine_liSite : LiZeroSite 0x80004118#64 :=
  fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004118_es σ i u _ vmi hG hpc hmi hmem rfl hi

/-- The `j 0x8000409c` site of the declaration tail. -/
theorem envDefine_jSite : JumpSite (BitVec.addInt 0x80004118#64 4) (0x1fff80#21) :=
  fun σ i u vmi hG hpc hmi hmem htgt hi =>
    site_8000411c_es σ i u _ vmi hG hpc hmi hmem (by decide) htgt hi

/-- `Store.define` keeps the frame count. -/
theorem define_frames_size (s : Store) (a : Addr) (x : String) (v : Value) :
    (s.define a x v).frames.size = s.frames.size := by
  simp [Store.define, Array.size_modify]

/-- The declaration tail from the rejoin: copy the value into the call
buffer, call `env_define`, and complete normally.  The payload premise
(`PayloadOffWindow`: a string payload lies outside the call buffer) is the
same class as the value return's. -/
theorem envDefineTail_run {s : Stmt}
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St} {d : Nat} {env : Addr} {x : String} {v : Value}
    {sp r aInterp aStmt aEnv aRet a0 ra : BitVec 64} {m0 mX : Mem}
    {out : Array String} {cfgX : Config}
    (hED : EnvDefineContract)
    (F : FrameFacts s g N A SL φf' φc' st' d env sp r aInterp aStmt aEnv aRet gC mX)
    (hname : ∀ m' : Mem, StmtRepr m' aStmt.toNat s →
      ∃ p, read64 m' (aStmt.toNat + 8) = some p ∧ CString m' p x)
    (hR : TruthyCopy.RouteReady gC 0x800040f0#64 a0 (sp - 176#64) ra
      aStmt aInterp aRet aEnv mX out cfgX)
    (hpf : PhiExtends φf φf' nf) (hpc : PhiExtends φc φc' nc)
    (hv : ValueRepr mX N φc' ((sp - 176#64).toNat + 104) v)
    (hpay : PayloadOffWindow mX ((sp - 176#64).toNat + 104) ((sp - 176#64).toNat + 16) v)
    (hext : MemExtends m0 mX)
    (hframe0 : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ mX[a]? = m0[a]?)
    (hout : String.join out.toList = st'.out) :
    ∃ cfgD : Config, Steps cfgX cfgD ∧
      ExecExitD g N A SL φf φc nf nc ⟨st'.store.define env x v, st'.out⟩ .normal
        sp r aRet m0 cfgD := by
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hram := F.stack_ram
  have hwin := F.stack_win
  have hesp40 : (sp - 176#64).toNat + 40 < 2 ^ 64 := by rw [hesp]; have := sp.isLt; omega
  have hstack := F.espStack
  have harena := F.espArena
  have hlog := envDefineCopy_log a0 (sp - 176#64) aStmt aInterp aRet aEnv mX aStmt hesp40
  -- the copy changes only the call buffer
  have hfootC : ∀ k, ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 16 + 24) →
      SL.lo ≤ k ∧ k < sp.toNat - 40 := by
    intro k hk; rw [hesp] at hk; omega
  have hframeC : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 16 + 24) →
      (writeLog mX (envDefineCall.out (HelperCall.callL a0 (sp - 176#64) aStmt aInterp aRet aEnv)
        (envDefineLds mX aStmt (sp - 176#64))).log)[k]? = mX[k]? := by
    rw [hlog]; exact copy3_frame mX _ _
  have hextC : MemExtends mX (writeLog mX (envDefineCall.out
      (HelperCall.callL a0 (sp - 176#64) aStmt aInterp aRet aEnv)
      (envDefineLds mX aStmt (sp - 176#64))).log) := by
    rw [hlog]; exact copy3_memExtends mX _ _
  have FP := F.afterStackHelper hfootC hframeC hextC
  -- park at `env_define`
  obtain ⟨cP, hsP, hP⟩ := envDefineCall.parked_of_ready envDefineCall_cert hR
    (envDefineLds mX aStmt (sp - 176#64))
    (by change ChainOK 0x800040f0#64 [10, 2, 8, 9, 18, 19] envDefineCopySeg; decide) rfl
    (by change KeysOK [12, 10, 15, 14, 13, 11, 2, 8, 9, 18, 19]; decide)
    (by change ∀ n ∈ [12, 10, 15, 14, 13, 11, 2, 8, 9, 18, 19], n ≠ 1; decide)
    FP.code
    (envDefineCopy_facts F.ground F.code (sp - 176#64) (by rw [hesp]; omega)
      (by rw [hesp]; omega) hram hwin (by rw [hesp]; omega) a0 aInterp aRet aEnv)
  -- the name pointer read by the tail
  obtain ⟨pName, hpName, hcstr⟩ := hname _ FP.stmt
  have hnode : ∀ k, k < 8 → ¬ ((sp - 176#64).toNat + 16 ≤ aStmt.toNat + 8 + k ∧
      aStmt.toNat + 8 + k < (sp - 176#64).toNat + 16 + 24) := by
    obtain ⟨lo, hi, hr⟩ := F.ground.ast.region
    have hn := stmtIn_node hr.nodes
    have hsd := hr.stack_disjoint
    intro k hk
    rw [hesp]
    have := hn.lo_le; have := hn.hi_ge
    omega
  have hpNameX : read64 mX (aStmt.toNat + 8) = some pName := by
    rw [read64_agreeP (P := fun k => ¬ ((sp - 176#64).toNat + 16 ≤ k ∧
        k < (sp - 176#64).toNat + 16 + 24)) (fun k hk => (hframeC k hk).symm) hnode]
    exact hpName
  have hpNameLt : pName < 2 ^ 64 := read64_lt_eg4 mX (aStmt.toNat + 8) pName hpNameX
  have ha1 : bytesVal MKind.ld (EvalChildArm.wordLds8 mX (aStmt.toNat + 8)) =
      BitVec.ofNat 64 pName :=
    EvalChildArm.bytesVal_ld_wordLds mX (aStmt.toNat + 8) (BitVec.ofNat 64 pName)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpNameLt]; exact hpNameX)
  have hpv : ((sp - 176#64) + sign_extend (m := 64) (0x010#12)).toNat = (sp - 176#64).toNat + 16 :=
    off_toNat _ 0x010#12 16 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  -- the entry facts at the copied memory
  have hM : EnvDefineMem N A SL φf' φc' st' env x v (aEnv + sign_extend (m := 64) (0#12))
      (BitVec.ofNat 64 pName) ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) (sp - 176#64)
      (writeLog mX (envDefineCall.out (HelperCall.callL a0 (sp - 176#64) aStmt aInterp aRet aEnv)
        (envDefineLds mX aStmt (sp - 176#64))).log) :=
    { text := FP.ground.eval_call.image.text
      store := FP.store_survives _ (fun _ _ => rfl)
      store_survives := FP.store_survives
      store_bodies := FP.store_bodies
      env_valid := FP.env_valid
      env_addr := by
        rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
        exact FP.env_addr
      name := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpNameLt]
        exact hcstr
      value := by
        rw [hpv, hlog]
        exact valueRepr_copy_total_exact (copy3_total mX _ _) (hpay.covered (copy3_frame mX _ _)) hv
      stack := hstack
      stack_ram := hram
      stack_win := hwin
      stack_bytes := FP.ground.stack_bytes
      arena_stack := harena
      pv_frame := hpv
      slot_in_stack := by rw [hesp]; omega
      value_words := by
        rw [hpv, hlog]
        refine valueWordsTotal_of_interval (lo := (sp - 176#64).toNat + 16)
          (hi := (sp - 176#64).toNat + 16 + 24) ?_ (Nat.le_refl _) (Nat.le_refl _)
        intro k hk1 hk2
        have hb := copy3_total mX ((sp - 176#64).toNat + 104) ((sp - 176#64).toNat + 16)
          (k - ((sp - 176#64).toNat + 16)) (by omega)
        rw [show (sp - 176#64).toNat + 16 + (k - ((sp - 176#64).toNat + 16)) = k by omega] at hb
        exact ⟨_, hb⟩
      arena_image := FP.ground.eval_call.image.arena }
  -- the callee
  have h11 : lookupG 11 (envDefineCall.out (HelperCall.callL a0 (sp - 176#64) aStmt aInterp aRet aEnv)
      (envDefineLds mX aStmt (sp - 176#64))).regs =
      some (bytesVal MKind.ld (EvalChildArm.wordLds8 mX (aStmt.toNat + 8))) := rfl
  rw [ha1] at h11
  obtain ⟨cR, a0', hsR, hRet, hStore, hSurv⟩ :=
    envDefineCall.envDefineReturn_of_parked envDefineCall_cert rfl hED hP
      rfl h11 rfl rfl rfl rfl rfl rfl hM
  -- the frame after the callee
  have hframeR : ∀ a, ¬ (SL.lo ≤ a ∧ a < (sp - 176#64).toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cR.σ.mem[a]? =
        (writeLog mX (envDefineCall.out
          (HelperCall.callL a0 (sp - 176#64) aStmt aInterp aRet aEnv)
          (envDefineLds mX aStmt (sp - 176#64))).log)[a]? := by
    intro a hstk hA
    right
    exact hRet.mem_frame a (fun h => h.elim hA hstk)
  have FR := FP.afterExit (st' := ⟨st'.store.define env x v, st'.out⟩) hframeR
    hRet.mem_extends (PhiExtends.refl φf' _) hSurv
    (by
      show env < (st'.store.define env x v).frames.size
      rw [define_frames_size]
      exact FP.env_valid)
    (fun a cd h => FP.store_bodies a cd h)
  -- the normal exit
  obtain ⟨cH, hsH, hHead⟩ := TruthyCopy.route_of_ready [] 0x80004118#64 [] hRet.ready
    (by change ChainOK envDefineCall.retPC [10, 2, 1, 8, 9, 18, 19] []; trivial) rfl
    (by change WrChainAvoids TruthyCopy.abiButS0 []; decide)
    (by change ChainFacts _ _ _ _ []; trivial)
  have hPre := normalExitPre_of_routeHead hHead rfl rfl FR hpf hpc hout
  obtain ⟨cE, hsE, hExit⟩ :=
    normalExitTail 0x80004118#64 (0x1fff80#21) envDefine_liSite envDefine_jSite (by decide)
      cH hPre
  refine ⟨cE, (hsP.trans (hsR.trans (hsH.trans hsE))), ?_⟩
  clear ha1 h11 hpNameX hpName hcstr hM
  refine Rows.execExitD_rebaseMem g N A SL φf φc nf nc _ .normal sp r aRet m0 cR.σ.mem cE
    ((hext.trans hextC).trans hRet.mem_extends) ?_ hExit
  intro a hstk hA
  rw [hRet.mem_frame a (fun h => h.elim hA (fun hs => hstk ⟨hs.1, by rw [hesp] at hs; omega⟩)),
    hframeC a (fun hf => hstk ⟨(hfootC a hf).1, by have := (hfootC a hf).2; omega⟩)]
  exact hframe0 a hstk hA

#print axioms envDefineCall_cert
#print axioms envDefineCopy_facts
#print axioms envDefineTail_run

end Vsa.Sim
