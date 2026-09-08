import Vsa.Sim.StmtChildArm

/-!
# `HelperCall` — the parametric in-frame runtime-helper call of `exec_stmt`

Every remaining statement leaf calls a runtime helper from inside the
`exec_stmt` frame and continues at the helper's return: `value_null` at the
two null bridges (`ret;`, `var x;`), `env_define` at the declaration tail,
`env_new` at the block and for arms.  This file states that seam once:

* a descriptor `HelperCall` (head PC, reflected prefix, `jal` site, callee
  entry) and its decided certificate `Cert`;
* `parked_of_gholds` runs the prefix and the `jal` from any parked state and
  lands at the callee entry (`Parked`: link register, reflected registers and
  write log, ABI frame); `parked_of_ready` enters from a `RouteReady`,
  `parked_of_armState` from an `ArmState`;
* `Return` is the helper's return as a route-ready state plus its memory
  footprint; each callee supplies one adapter `xReturn_of_parked` from its
  contract (`HelperCallNull.lean` for `value_null`);
* `RouteHead.toRouteReady`, `ArmState.frameFacts`, and
  `FrameFacts.afterStackHelper` connect the return to the existing
  continuation kit (`route_of_ready`, `ArmState.of_routeHead`,
  `normalExitPre_of_routeHead`, the retslot resume).

An instance is one `#derive_case` prefix, one descriptor, a certificate of
`decide`s, and a chain-facts theorem.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-- An in-frame call of a runtime helper: the reflected prefix from the
parked PC up to (excluding) the `jal`, the `jal` site, and the callee entry. -/
structure HelperCall where
  /-- The parked PC the prefix starts at. -/
  headPC : BitVec 64
  /-- The reflected prefix (loads, moves, stores, decided branches). -/
  seg : List BBlock
  /-- PC of the `jal`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21
  /-- The callee entry. -/
  entry : BitVec 64

namespace HelperCall

/-- The link PC written by the `jal`. -/
def retPC (H : HelperCall) : BitVec 64 := BitVec.addInt H.jalPC 4

/-- The reflected outcome of the prefix from the pinned registers `L`. -/
def out (H : HelperCall) (L : GRegs) (lds : List (List (BitVec 8))) : SegEvalState :=
  evalBlocks H.seg (SegEvalState.init L lds)

/-- Facts about the descriptor alone: every field of an instance closes by
`decide` or the generated `jal` site lemma. -/
structure Cert (H : HelperCall) : Prop where
  ret_align : H.retPC.toNat % 4 = 0
  ret_clean : BitVec.update (H.retPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = H.retPC
  jal_tgt : H.jalPC + sign_extend (m := 64) H.jalImm = H.entry
  avoid_abi : WrChainAvoidAbi H.seg
  jal_site : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some H.jalPC →
    σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ H.jalPC vmi H.jalImm Register.x1
        (BitVec.addInt H.jalPC 4))

/-! ## Parked at the callee entry -/

/-- The state after the prefix and the `jal`: at the callee entry with the
link register set, the reflected registers and write log, and the ABI frame
of the parked state. -/
structure Parked (H : HelperCall) (L : GRegs) (lds : List (List (BitVec 8)))
    (mR : Mem) (out : Array String)
    (gC : (R : Register) → Option (RegisterType R)) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some H.entry
  ra : cfg.σ.regs.get? Register.x1 = some H.retPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = writeLog mR (H.out L lds).log
  out : cfg.σ.sailOutput = out
  regs : GHolds cfg.σ (H.out L lds).regs
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R

/-- Run the prefix and the `jal` from any parked state whose pinned
registers hold `L`. -/
theorem parked_of_gholds (H : HelperCall) (C : H.Cert) (L : GRegs)
    (lds : List (List (BitVec 8)))
    {gC : (R : Register) → Option (RegisterType R)}
    {mR : Mem} {out : Array String} {cfg : Config}
    (hgood : GoodState cfg.σ) (htick : cfg.tick < 2)
    (hpc : cfg.σ.regs.get? Register.PC = some H.headPC)
    (hmi : ∃ w, cfg.σ.regs.get? Register.minstret = some w)
    (hmem : cfg.σ.mem = mR) (hout : cfg.σ.sailOutput = out)
    (hL : GHolds cfg.σ L) (hkeys : KeysOK (keysG L))
    (hframe : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R)
    (hwf : ChainOK H.headPC (keysG L) H.seg)
    (hend : evalBlocksPC H.headPC (SegEvalState.init L lds) H.seg = H.jalPC)
    (hkeysOut : KeysOK (keysG (H.out L lds).regs))
    (hraOut : KeysAvoidRa (H.out L lds).regs)
    (hcode : Exec_stmtLoaded (writeLog mR (H.out L lds).log))
    (hfacts : ChainFacts mR mR L lds H.seg) :
    ∃ cfg' : Config, Steps cfg cfg' ∧ H.Parked L lds mR out gC cfg' := by
  obtain ⟨vm, hvm⟩ := hmi
  have hfactsT : ChainFacts cfg.σ.mem cfg.σ.mem L lds H.seg := by
    rw [hmem]; exact hfacts
  obtain ⟨σ2, i2, hs2, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hout2, hframe2⟩ :=
    bridgeOfSegOut H.seg L lds cfg.σ cfg.tick cfg.steps H.headPC H.entry H.retPC vm
      cfg.σ.mem hgood hpc hvm rfl hL hkeys hfactsT htick hwf C.avoid_abi hkeysOut hraOut
      (by
        intro σ i u hG hi hpc' hmi' hm _
        obtain ⟨vm', hvm'⟩ := hmi'
        rw [hend] at hpc'
        have hc : Exec_stmtLoaded σ.mem := by rw [hm, hmem]; exact hcode
        obtain ⟨σ', i', hs', hi', hG', hm', ho'⟩ := C.jal_site σ i u vm' hG hpc' hvm' hc hi
        exact jalStepO_of_obs hs' hi' hG' hm' ho' C.jal_tgt)
  refine ⟨⟨σ2, i2, cfg.steps + evalBlocksFuel H.seg + 1⟩, hs2, ?_⟩
  exact
    { good := hG2
      tick := hi2
      pc := hpc2
      ra := hra2
      minstret := hmi2
      mem := by rw [hmem2, hmem]; rfl
      out := by rw [hout2, hout]
      regs := hregs2
      frame := fun R hR => (hframe2 R hR).trans (hframe R hR) }

/-- The pinned registers of a call from a route-ready state: the six the
prefix may read; the link register is rewritten by the `jal`. -/
def callL (a0 esp s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(10, a0), (2, esp), (8, s0), (9, s1), (18, s2), (19, s3)]

/-- Enter from a route-ready state (a parked return keyed by `a0`). -/
theorem parked_of_ready (H : HelperCall) (C : H.Cert)
    {gC : (R : Register) → Option (RegisterType R)}
    {a0 esp ra s0 s1 s2 s3 : BitVec 64} {mR : Mem} {out : Array String} {cfg : Config}
    (hR : TruthyCopy.RouteReady gC H.headPC a0 esp ra s0 s1 s2 s3 mR out cfg)
    (lds : List (List (BitVec 8)))
    (hwf : ChainOK H.headPC [10, 2, 8, 9, 18, 19] H.seg)
    (hend : evalBlocksPC H.headPC
      (SegEvalState.init (callL a0 esp s0 s1 s2 s3) lds) H.seg = H.jalPC)
    (hkeysOut : KeysOK (keysG (H.out (callL a0 esp s0 s1 s2 s3) lds).regs))
    (hraOut : KeysAvoidRa (H.out (callL a0 esp s0 s1 s2 s3) lds).regs)
    (hcode : Exec_stmtLoaded (writeLog mR (H.out (callL a0 esp s0 s1 s2 s3) lds).log))
    (hfacts : ChainFacts mR mR (callL a0 esp s0 s1 s2 s3) lds H.seg) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      H.Parked (callL a0 esp s0 s1 s2 s3) lds mR out gC cfg' := by
  have hL : GHolds cfg.σ (callL a0 esp s0 s1 s2 s3) := by
    simp only [callL, GHolds, gprGet]
    exact ⟨hR.a0, hR.sp, hR.s0, hR.s1, hR.s2, hR.s3, True.intro⟩
  exact H.parked_of_gholds C _ lds hR.good hR.tick hR.pc hR.minstret hR.mem hR.out hL
    (by change KeysOK [10, 2, 8, 9, 18, 19]; decide) hR.frame hwf hend hkeysOut hraOut
    hcode hfacts

/-- Enter from an arm state (the five frame registers). -/
theorem parked_of_armState (H : HelperCall) (C : H.Cert) {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    (hA : Vsa.Sim.ArmState H.headPC s g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 ment cfg)
    (lds : List (List (BitVec 8)))
    (hwf : ChainOK H.headPC [2, 8, 9, 18, 19] H.seg)
    (hend : evalBlocksPC H.headPC
      (SegEvalState.init (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) lds)
      H.seg = H.jalPC)
    (hkeysOut : KeysOK (keysG
      (H.out (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) lds).regs))
    (hraOut : KeysAvoidRa
      (H.out (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) lds).regs)
    (hcode : Exec_stmtLoaded (writeLog ment
      (H.out (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) lds).log))
    (hfacts : ChainFacts ment ment (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv)
      lds H.seg) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      H.Parked (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) lds ment
        cfg.σ.sailOutput (fun R => cfg.σ.regs.get? R) cfg' := by
  have hL : GHolds cfg.σ (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) := by
    simp only [EvalChildArm.regs, GHolds, gprGet]
    exact ⟨hA.spReg, hA.s0, hA.s1, hA.s2, hA.s3, True.intro⟩
  exact H.parked_of_gholds C _ lds hA.good hA.tick hA.pc hA.minstret hA.mem rfl hL
    (by change KeysOK [2, 8, 9, 18, 19]; decide) (fun _ _ => rfl) hwf hend hkeysOut hraOut
    hcode hfacts

/-! ## The helper's return -/

/-- The helper's return: route-ready at the link PC (the result in `a0`),
with the memory changed only inside the helper's footprint. -/
structure Return (H : HelperCall) (gC : (R : Register) → Option (RegisterType R))
    (a0 esp s0 s1 s2 s3 : BitVec 64) (mIn mOut : Mem) (foot : Nat → Prop)
    (out : Array String) (cfg : Config) : Prop where
  ready : TruthyCopy.RouteReady gC H.retPC a0 esp H.retPC s0 s1 s2 s3 mOut out cfg
  mem_frame : ∀ k, ¬ foot k → mOut[k]? = mIn[k]?
  mem_extends : MemExtends mIn mOut

end HelperCall

/-! ## Connecting to the continuation kit -/

/-- The end of a memory-pure route is route-ready at its end PC. -/
theorem TruthyCopy.RouteHead.toRouteReady {bs : List BBlock} {endPC : BitVec 64} {L : GRegs}
    {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfg : Config}
    {a0 esp ra s0 s1 s2 s3 : BitVec 64}
    (h : TruthyCopy.RouteHead bs endPC L lds mR out gC cfg)
    (hlog : (evalBlocks bs (SegEvalState.init L lds)).log = [])
    (h10 : lookupG 10 (evalBlocks bs (SegEvalState.init L lds)).regs = some a0)
    (h2 : lookupG 2 (evalBlocks bs (SegEvalState.init L lds)).regs = some esp)
    (h1 : lookupG 1 (evalBlocks bs (SegEvalState.init L lds)).regs = some ra)
    (h8' : lookupG 8 (evalBlocks bs (SegEvalState.init L lds)).regs = some s0)
    (h9 : lookupG 9 (evalBlocks bs (SegEvalState.init L lds)).regs = some s1)
    (h18 : lookupG 18 (evalBlocks bs (SegEvalState.init L lds)).regs = some s2)
    (h19 : lookupG 19 (evalBlocks bs (SegEvalState.init L lds)).regs = some s3)
    (hg8 : gC Register.x8 = some s0) :
    TruthyCopy.RouteReady gC endPC a0 esp ra s0 s1 s2 s3 mR out cfg :=
  { good := h.good
    tick := h.tick
    pc := h.pc
    a0 := gholds_lookup _ h.regs h10
    ra := gholds_lookup _ h.regs h1
    minstret := h.minstret
    mem := by rw [h.mem, hlog]; rfl
    out := h.out
    sp := gholds_lookup _ h.regs h2
    s0 := gholds_lookup _ h.regs h8'
    s1 := gholds_lookup _ h.regs h9
    s2 := gholds_lookup _ h.regs h18
    s3 := gholds_lookup _ h.regs h19
    frame := by
      intro R hR
      by_cases h8 : R = Register.x8
      · subst h8
        exact (gholds_lookup _ h.regs h8').trans hg8.symm
      · exact h.frame R (by
          unfold TruthyCopy.abiButS0
          rw [hR, beq_eq_false_iff_ne.mpr (Ne.symm h8)]
          rfl) }

/-- An arm state carries the frame facts relative to its own registers. -/
theorem ArmState.frameFacts {armPC : BitVec 64} {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    (hA : Vsa.Sim.ArmState armPC s g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 ment cfg) :
    FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet
      (fun R => cfg.σ.regs.get? R) ment :=
  { s0 := hA.s0
    s1 := hA.s1
    s2 := hA.s2
    s3 := hA.s3
    spReg := hA.spReg
    parentSp := hA.parentSp
    code := hA.code
    code_stack_disjoint := hA.code_stack_disjoint
    stack_ram := hA.stack_ram
    stack_win := hA.stack_win
    ra_align := hA.ra_align
    stmt := hA.stmt
    env_addr := hA.env_addr
    env_valid := hA.env_valid
    store_survives := hA.store_survives
    saved_ra := hA.saved_ra
    saved_s0 := hA.saved_s0
    saved_s1 := hA.saved_s1
    saved_s2 := hA.saved_s2
    saved_s3 := hA.saved_s3
    stack_budget := hA.stack_budget
    stmt_bodies := hA.stmt_bodies
    store_bodies := hA.store_bodies
    envset_defined := hA.envset
    ground := hA.ground
    frame := by
      intro R hR
      by_cases h8 : R = Register.x8
      · exact Or.inl (Or.inl h8)
      by_cases h9 : R = Register.x9
      · exact Or.inl (Or.inr (Or.inl h9))
      by_cases h18 : R = Register.x18
      · exact Or.inl (Or.inr (Or.inr (Or.inl h18)))
      by_cases h19 : R = Register.x19
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h19))))
      by_cases h2 : R = Register.x2
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h2))))
      right
      exact hA.frame R hR (beq_eq_false_iff_ne.mpr (Ne.symm h8))
        (beq_eq_false_iff_ne.mpr (Ne.symm h9)) (beq_eq_false_iff_ne.mpr (Ne.symm h18))
        (beq_eq_false_iff_ne.mpr (Ne.symm h19)) (beq_eq_false_iff_ne.mpr (Ne.symm h2)) }

/-- The `exec_stmt` code survives any change confined to the stack window
below the frame. -/
theorem FrameFacts.code_of_frame {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR mR' : Mem}
    (F : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR)
    (hoff : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mR'[k]? = mR[k]?) :
    Exec_stmtLoaded mR' := by
  have hcs := F.code_stack_disjoint
  simp only [execStmtEntry, execStmtEnd] at hcs
  apply loaded_exec_stmt_agreeP mR mR' _ F.code
  intro a ha
  exact (hoff a (by intro hs; rcases hcs with hd | hd <;> omega)).symm

/-- The frame facts survive a helper whose footprint lies inside the lowered
frame below the saved registers. -/
theorem FrameFacts.afterStackHelper {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR mR' : Mem}
    (F : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR)
    {foot : Nat → Prop}
    (hfoot : ∀ k, foot k → SL.lo ≤ k ∧ k < sp.toNat - 40)
    (hframe : ∀ k, ¬ foot k → mR'[k]? = mR[k]?)
    (hext : MemExtends mR mR') :
    FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR' := by
  have hoff : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mR'[k]? = mR[k]? := by
    intro k hk
    exact hframe k (fun hf => hk ⟨(hfoot k hf).1, by have := (hfoot k hf).2; omega⟩)
  have hpop : StackBytesPresent mR' SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := F.ground.stack_bytes k hlo hhi
    exact hext k b hb
  exact F.transport hoff
    (fun k hlo hhi => hframe k (fun hf => by have := (hfoot k hf).2; omega))
    (F.code_of_frame hoff) hpop

/-- A statement-node field is a readable eight-byte window (the load facts of
any node-field `ld` in a prefix). -/
theorem ExecGround.node_ld_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64} {s : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat s) (off : BitVec 12) (n : Nat)
    (hn : n + 8 ≤ 40)
    (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
    (0x80000000 ≤ (aStmt + sign_extend (m := 64) off).toNat ∧
      (aStmt + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000 ∧
      ((aStmt + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) off).toNat)) ∧
    LPins8 m (aStmt + sign_extend (m := 64) off).toNat
      (EvalChildArm.wordLds8 m (aStmt.toNat + n)) := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hnode := stmtIn_node hr.nodes
  have haddr : (aStmt + sign_extend (m := 64) off).toNat = aStmt.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hnode.hi_ge
    have := hr.hi_ram
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := hr.lo_ram; have := hnode.lo_le; omega
  · have := hr.hi_ram; have := hnode.hi_ge; omega
  · right; have := hr.win; have := hnode.lo_le; omega
  · simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
    trivial

#print axioms HelperCall.parked_of_gholds
#print axioms HelperCall.parked_of_ready
#print axioms HelperCall.parked_of_armState
#print axioms TruthyCopy.RouteHead.toRouteReady
#print axioms ArmState.frameFacts
#print axioms FrameFacts.afterStackHelper
#print axioms ExecGround.node_ld_facts

/-! ## Byte-level facts of a three-word copy

Every in-frame value copy is three `ld`s followed by three `sd`s; its
reflected write log is three `writeMap8`s of the loaded words.  The facts
below hold for any source and destination. -/

/-- The reflected write log of a three-word copy from `src` to `dst`. -/
def copy3Log (m : Mem) (src dst : Nat) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m dst
    (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m src))))
    (dst + 8) (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (src + 8)))))
    (dst + 16) (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (src + 16))))

/-- The copy fills the destination with the source bytes. -/
theorem copy3_total (m : Mem) (src dst : Nat) :
    ∀ j, j < 24 → (copy3Log m src dst)[dst + j]? = some ((m[src + j]?).getD 0) := by
  let k0 := (m[src]?).getD 0
  let k1 := (m[src + 1]?).getD 0
  let k2 := (m[src + 2]?).getD 0
  let k3 := (m[src + 3]?).getD 0
  let k4 := (m[src + 4]?).getD 0
  let k5 := (m[src + 5]?).getD 0
  let k6 := (m[src + 6]?).getD 0
  let k7 := (m[src + 7]?).getD 0
  let p0 := (m[src + 8]?).getD 0
  let p1 := (m[src + 8 + 1]?).getD 0
  let p2 := (m[src + 8 + 2]?).getD 0
  let p3 := (m[src + 8 + 3]?).getD 0
  let p4 := (m[src + 8 + 4]?).getD 0
  let p5 := (m[src + 8 + 5]?).getD 0
  let p6 := (m[src + 8 + 6]?).getD 0
  let p7 := (m[src + 8 + 7]?).getD 0
  let q0 := (m[src + 16]?).getD 0
  let q1 := (m[src + 16 + 1]?).getD 0
  let q2 := (m[src + 16 + 2]?).getD 0
  let q3 := (m[src + 16 + 3]?).getD 0
  let q4 := (m[src + 16 + 4]?).getD 0
  let q5 := (m[src + 16 + 5]?).getD 0
  let q6 := (m[src + 16 + 6]?).getD 0
  let q7 := (m[src + 16 + 7]?).getD 0
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ :=
    TruthyCopy.sdData_sext_bytes k0 k1 k2 k3 k4 k5 k6 k7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ :=
    TruthyCopy.sdData_sext_bytes p0 p1 p2 p3 p4 p5 p6 p7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ :=
    TruthyCopy.sdData_sext_bytes q0 q1 q2 q3 q4 q5 q6 q7
  intro j hj
  unfold copy3Log
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
      j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
      j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨
      j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [EvalChildArm.wordLds8, bytesVal, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_0, eK0]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_1, eK1]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_2, eK2]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_3, eK3]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_4, eK4]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_5, eK5]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_6, eK6]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (dst + 8) _ _ (by omega), getElem_writeMap8_7, eK7]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_0, eP0]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_1, eP1]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_2, eP2]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_3, eP3]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_4, eP4]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_5, eP5]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_6, eP6]
  · rw [getElem_writeMap8_disjoint _ (dst + 16) _ _ (by omega), getElem_writeMap8_7, eP7]
  · rw [getElem_writeMap8_0, eQ0]
  · rw [getElem_writeMap8_1, eQ1]
  · rw [getElem_writeMap8_2, eQ2]
  · rw [getElem_writeMap8_3, eQ3]
  · rw [getElem_writeMap8_4, eQ4]
  · rw [getElem_writeMap8_5, eQ5]
  · rw [getElem_writeMap8_6, eQ6]
  · rw [getElem_writeMap8_7, eQ7]

/-- The copy changes only its 24-byte destination. -/
theorem copy3_frame (m : Mem) (src dst : Nat) :
    ∀ k, ¬ (dst ≤ k ∧ k < dst + 24) → (copy3Log m src dst)[k]? = m[k]? := by
  intro k hk
  unfold copy3Log
  rw [getElem_writeMap8_disjoint _ (dst + 16) k _ (by omega),
    getElem_writeMap8_disjoint _ (dst + 8) k _ (by omega),
    getElem_writeMap8_disjoint _ dst k _ (by omega)]

/-- The copy preserves memory presence. -/
theorem copy3_memExtends (m : Mem) (src dst : Nat) : MemExtends m (copy3Log m src dst) := by
  unfold copy3Log
  exact ((memExtends_writeMap8 m _ _).trans (memExtends_writeMap8 _ _ _)).trans
    (memExtends_writeMap8 _ _ _)

/-- A small positive frame offset, as a number. -/
theorem off_toNat (b : BitVec 64) (off : BitVec 12) (n : Nat)
    (hn : n ≤ 2047) (hb : b.toNat + n < 2 ^ 64)
    (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
    (b + sign_extend (m := 64) off).toNat = b.toNat + n := by
  rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## A copied value's payload

A 24-byte value copy moves the tag and the payload pointer, not the payload.
The copy represents the value at the destination when the payload (a string,
if any) lies outside the copied window. -/

/-- The string payload of the value at `src` lies outside `[dst, dst + 24)`. -/
def PayloadOffWindow (m : Mem) (src dst : Nat) (v : Value) : Prop :=
  ∀ (p : Nat) (s : String), read64 m (src + 8) = some p → ValuePayload v s →
    ∀ k, k ≤ s.length → (p + k < dst ∨ dst + 24 ≤ p + k)

theorem PayloadOffWindow.covered {m m' : Mem} {src dst : Nat} {v : Value}
    (h : PayloadOffWindow m src dst v)
    (hframe : ∀ k, ¬ (dst ≤ k ∧ k < dst + 24) → m'[k]? = m[k]?) :
    ValuePayloadCovered (fun a => m[a]? = m'[a]?) m src v := by
  cases v with
  | str s =>
    intro p hp k hk
    exact (hframe (p + k) (by
      rcases h p s hp rfl k hk with hlt | hge <;> omega)).symm
  | native f =>
    intro p hp k hk
    exact (hframe (p + k) (by
      rcases h p (nativeName f) hp rfl k hk with hlt | hge <;> omega)).symm
  | null => trivial
  | bool _ => trivial
  | int _ => trivial
  | closure _ => trivial

/-- A null, boolean, integer, or closure value has no string payload. -/
theorem PayloadOffWindow.of_no_payload {m : Mem} {src dst : Nat} {v : Value}
    (h : ∀ s : String, ¬ ValuePayload v s) : PayloadOffWindow m src dst v :=
  fun _ s _ hs => absurd hs (h s)

/-- The lowered frame keeps the callee headroom every runtime helper needs.
(The budget hypothesis is re-associated first: `omega` exhausts its recursion
budget on `SL.lo + (… + 1088)` in this toolchain.) -/
theorem FrameFacts.espStack {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR : Mem}
    (F : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR) :
    StackOK SL (sp - 176#64) 1088 := by
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hneed := Stmt.stackNeed_ge s
  simp only [execFrame] at hneed
  obtain ⟨hlo, hhi, hal'⟩ := F.stack_budget
  rw [← Nat.add_assoc, ← Nat.add_assoc] at hlo
  generalize (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget = k at hlo
  generalize s.stackNeed = n at hlo hneed
  refine ⟨?_, ?_, ?_⟩ <;> rw [hesp]
  · apply Nat.le_sub_of_add_le
    omega
  · omega
  · omega

/-- The arena lies beside the lowered frame. -/
theorem FrameFacts.espArena {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR : Mem}
    (F : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR) :
    A.hi ≤ SL.lo ∨ (sp - 176#64).toNat + 176 ≤ A.lo := by
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  rcases F.ground.arena_stack with h | h
  · exact Or.inl h
  · right; rw [hesp]; omega

#print axioms FrameFacts.espStack

/-! ## Four-byte loads and routes that rewrite `s3`

The block arm reads the statement count with `lw` and rewrites `s3` to the
fresh scope before its loop head; both fall outside the eight-byte and
`abiButS0` conventions of the earlier layers. -/

/-- One total 32-bit machine read, as the four positional bytes the reflected
evaluator consumes. -/
def wordLds4 (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a + 1]?).getD 0, (m[a + 2]?).getD 0, (m[a + 3]?).getD 0]

/-- A non-negative 32-bit word sign-extends to its value. -/
theorem sext32_of_lt (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 2 ^ 31)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k := by
  have hw : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat = k := by
    simp only [BitVec.append_eq, BitVec.toNat_append]
    have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [Nat.shiftLeft_eq, Nat.reducePow]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  have hmsb : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth]
  rw [hw, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

/-- The value of a signed 32-bit load of a small count. -/
theorem bytesVal_lw_wordLds4 (m : Mem) (a k : Nat) (hk : k < 2 ^ 31)
    (hread : read32 m a = some k) :
    bytesVal MKind.lw (wordLds4 m a) = BitVec.ofNat 64 k := by
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m a k hread
  simp only [wordLds4, bytesVal, List.getD_cons_zero, List.getD_cons_succ,
    hb0, hb1, hb2, hb3, Option.getD_some]
  exact sext32_of_lt b0 b1 b2 b3 k hk hrec

/-- A statement-node word is a readable four-byte window. -/
theorem ExecGround.node_lw_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64} {s : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat s) (off : BitVec 12) (n : Nat)
    (hn : n + 4 ≤ 40)
    (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
    (0x80000000 ≤ (aStmt + sign_extend (m := 64) off).toNat ∧
      (aStmt + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000 ∧
      ((aStmt + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) off).toNat)) ∧
    LPins4 m (aStmt + sign_extend (m := 64) off).toNat (wordLds4 m (aStmt.toNat + n)) := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hnode := stmtIn_node hr.nodes
  have haddr : (aStmt + sign_extend (m := 64) off).toNat = aStmt.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hnode.hi_ge
    have := hr.hi_ram
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := hr.lo_ram; have := hnode.lo_le; omega
  · have := hr.hi_ram; have := hnode.hi_ge; omega
  · right; have := hr.win; have := hnode.lo_le; omega
  · simp only [wordLds4, LPins4, List.getD_cons_zero, List.getD_cons_succ]
    trivial

/-- The `blez` guard on a small count: taken exactly at zero. -/
theorem blez_guard_zero : zopz0zKzJ_s (0#64) (BitVec.ofNat 64 0) = true := by
  unfold zopz0zKzJ_s
  decide

theorem blez_guard_pos (n : Nat) (h0 : 0 < n) (hn : n < 2 ^ 63) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 n) = false := by
  unfold zopz0zKzJ_s
  apply decide_eq_false
  intro h
  have hcond := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 64 n)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hcond
  rw [if_pos (by omega)] at hcond
  simp only [BitVec.toInt_zero, ge_iff_le, hcond] at h
  omega

/-- The end of a reflected route keeping the registers `keep` fixed. -/
structure RouteHeadK (keep : Register → Bool) (bs : List BBlock) (endPC : BitVec 64)
    (L : GRegs) (lds : List (List (BitVec 8))) (mR : Mem) (out : Array String)
    (gC : (R : Register) → Option (RegisterType R)) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some endPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = writeLog mR (evalBlocks bs (SegEvalState.init L lds)).log
  out : cfg.σ.sailOutput = out
  regs : GHolds cfg.σ (evalBlocks bs (SegEvalState.init L lds)).regs
  frame : ∀ R, keep R = true → cfg.σ.regs.get? R = gC R

/-- Run a reflected route from a route-ready state, keeping `keep` (a subset
of the ABI-preserved registers the route does not write). -/
theorem routeK_of_ready (keep : Register → Bool)
    (hnoise : ∀ rr ∈ noiseRegs, keep rr = false)
    (habi : ∀ R, keep R = true → AbiPreserved R = true)
    (bs : List BBlock) (endPC : BitVec 64) (lds : List (List (BitVec 8)))
    {gC : (R : Register) → Option (RegisterType R)}
    {pcR a0 esp ra s0 s1 s2 s3 : BitVec 64} {mR : Mem} {out : Array String} {cfg : Config}
    (hR : TruthyCopy.RouteReady gC pcR a0 esp ra s0 s1 s2 s3 mR out cfg)
    (hwf : ChainOK pcR [10, 2, 1, 8, 9, 18, 19] bs)
    (hend : evalBlocksPC pcR (SegEvalState.init (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) lds) bs
      = endPC)
    (havoid : WrChainAvoids keep bs)
    (hfacts : ChainFacts mR mR (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) lds bs) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      RouteHeadK keep bs endPC (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) lds mR out gC cfg' := by
  have hL : GHolds cfg.σ (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) := by
    simp only [TruthyCopy.routeL, GHolds, gprGet]
    exact ⟨hR.a0, hR.sp, hR.ra, hR.s0, hR.s1, hR.s2, hR.s3, True.intro⟩
  obtain ⟨vm, hvm⟩ := hR.minstret
  have hfactsT : ChainFacts cfg.σ.mem cfg.σ.mem (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) lds bs := by
    rw [hR.mem]; exact hfacts
  obtain ⟨σB, iB, hsB, hiB, hGB, hmemB, houtB, hpcB, hmiB, hregsB, hframeB⟩ :=
    segEval_sound bs cfg.σ cfg.tick cfg.steps pcR vm _ lds hR.good hR.pc hvm hL
      (by change KeysOK [10, 2, 1, 8, 9, 18, 19]; decide) hfactsT hwf hR.tick
  refine ⟨⟨σB, iB, cfg.steps + evalBlocksFuel bs⟩, hsB, ?_⟩
  exact
    { good := hGB
      tick := hiB
      pc := by rw [hpcB, hend]
      minstret := hmiB
      mem := by rw [hmemB, hR.mem]
      out := by rw [houtB, hR.out]
      regs := hregsB
      frame := fun R hR' =>
        (hframeB R (noise_avoids hnoise hR') (wrChain_avoids havoid hR')).trans
          (hR.frame R (habi R hR')) }

#print axioms bytesVal_lw_wordLds4
#print axioms blez_guard_pos
#print axioms routeK_of_ready

#print axioms copy3_total
#print axioms copy3_frame
#print axioms copy3_memExtends

end Vsa.Sim
