import Vsa.Sim.EvalChildArm
import Vsa.Sim.TruthyCopy
import Vsa.Sim.ExecRecCommon
import Vsa.Sim.rows.InitSomeReturnReady
import Vsa.Sim.ExecRetEpilogue

/-!
# `StmtChildArm` — the parametric in-frame call of a child statement

An `exec_stmt` loop arm calls `exec_stmt` recursively on a child statement
through a four-instruction prefix (`ld a1,off(s0); mv a3,s2; mv a2,s3;
mv a0,s1`) and a `jal` in the same 176-byte frame.  This file states that
call once over a descriptor: `dispatch_of_armState` lands the child's
`ExecEntry` with the parent `Carrier`; `exitKit_of_exit` recovers the parent
at the child's widened `ExecExitD`; `ExitKit.toRouteReady` hands the status
in `a0` to a reflected route (`TruthyCopy.route_of_ready`); the normal-exit
and return-propagation heads after a route are `normalExitPre_of_route` and
`retExit_of_route`.
-/

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) every `∃` here is the fixed StepObs site post
-- shape (`Cert.jal_site`), a saved-register witness inside a named-field structure, or
-- the reached-config existential of a run; all are consumed through named fields.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St


/-! ## The parent frame at an in-frame point

The facts a parent `exec_stmt` frame carries at any in-frame point after a
child returned: the ghost register image `gC`, and the memory-indexed AST,
code, store-survival, and saved-register facts at the current memory `mR`
with the current maps and source state.  Both child kits project it; routes,
copies, and the loop re-entry consume it. -/
structure FrameFacts (s : Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (gC : (R : Register) → Option (RegisterType R)) (mR : Mem) : Prop where
  s0 : gC Register.x8 = some aStmt
  s1 : gC Register.x9 = some aInterp
  s2 : gC Register.x18 = some aRet
  s3 : gC Register.x19 = some aEnv
  spReg : gC Register.x2 = some (sp - 176#64)
  parentSp : g Register.x2 = some sp
  code : Exec_stmtLoaded mR
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ra_align : r.toNat % 4 = 0
  stmt : StmtRepr mR aStmt.toNat s
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  env_valid : EnvValid st env
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mR[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  saved_ra : read64 mR (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 mR (sp.toNat - 16) = some v.toNat ∧ g Register.x8 = some v
  saved_s1 : ∃ v, read64 mR (sp.toNat - 24) = some v.toNat ∧ g Register.x9 = some v
  saved_s2 : ∃ v, read64 mR (sp.toNat - 32) = some v.toNat ∧ g Register.x18 = some v
  saved_s3 : ∃ v, read64 mR (sp.toNat - 40) = some v.toNat ∧ g Register.x19 = some v
  stack_budget : StackOK SL sp
    (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget s = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  envset_defined : (∃ v, gC Register.x20 = some v) ∧ (∃ v, gC Register.x21 = some v)
  ground : ExecGround mR SL A sp aRet aStmt.toNat s
  frame : ∀ R : Register, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ gC R = g R

namespace FrameFacts

/-- Geometry of the lowered frame. -/
theorem geom {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR : Mem}
    (h : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR) :
    176 ≤ sp.toNat ∧ (sp - 176#64).toNat = sp.toNat - 176 ∧
    SL.lo + 176 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 := by
  have hneed := Stmt.stackNeed_ge s
  simp only [execFrame] at hneed
  obtain ⟨hlo, hhi, hal⟩ := h.stack_budget
  have h176 : 176 ≤ sp.toNat := by omega
  exact ⟨h176, EvalChildArm.esp_toNat sp h176, by omega, hhi, hal⟩

/-- The frame facts survive a memory change that touches only the lowered
frame below the saved registers (a value copy or a reflected route). -/
theorem transport {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR mR' : Mem}
    (h : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR)
    (hoff : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mR'[k]? = mR[k]?)
    (hsaved : ∀ k, sp.toNat - 40 ≤ k → k < sp.toNat → mR'[k]? = mR[k]?)
    (hcode : Exec_stmtLoaded mR')
    (hpop : StackBytesPresent mR' SL) :
    FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR' := by
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := h.geom
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mR mR' :=
    fun k hk => (hsaved k hk.1 hk.2).symm
  obtain ⟨v8, hr8, hg8⟩ := h.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := h.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := h.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := h.saved_s3
  obtain ⟨hra, hs0, hs1, hs2, hs3⟩ := ScaffoldRows.initSomeReturn_saved_reads
    (by omega) hag h.saved_ra hr8 hr9 hr18 hr19
  exact
    { h with
      code := hcode
      stmt := h.ground.stmtRepr_offstack h.stmt hSLhi hoff
      ground := h.ground.transport_offstack hSLhi hpop hoff
      store_survives := fun m' hag' => h.store_survives m' (fun k hk =>
        ((hoff k (fun hs => hk ⟨hs.1, Nat.lt_of_lt_of_le hs.2 hSLhi⟩)).symm).trans (hag' k hk))
      saved_ra := hra
      saved_s0 := ⟨v8, hs0, hg8⟩
      saved_s1 := ⟨v9, hs1, hg9⟩
      saved_s2 := ⟨v18, hs2, hg18⟩
      saved_s3 := ⟨v19, hs3, hg19⟩ }

/-- The frame facts at a child's widened exit: the memory changed outside the
stack only in the arena and the retslot, and the maps extended on the entry
prefix. -/
theorem afterExit {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    {gC : (R : Register) → Option (RegisterType R)} {mR mR' : Mem}
    (h : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR)
    (hframe : ∀ a, ¬ (SL.lo ≤ a ∧ a < (sp - 176#64).toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ mR'[a]? = mR[a]?)
    (hext : MemExtends mR mR')
    (hpf : PhiExtends φf φf' st.store.frames.size)
    (hstore : ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mR'[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store)
    (henv : EnvValid st' env)
    (hbodies : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget) :
    FrameFacts s g N A SL φf' φc' st' d env sp r aInterp aStmt aEnv aRet gC mR' := by
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := h.geom
  have hframeP : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ mR'[a]? = mR[a]? :=
    fun a hstk hA => hframe a (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA
  have hpop : StackBytesPresent mR' SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := h.ground.stack_bytes k hlo hhi
    exact hext k b hb
  have hcode : Exec_stmtLoaded mR' := by
    have hcs := h.code_stack_disjoint
    have hac := h.ground.arena_code
    simp only [execStmtEntry, execStmtEnd] at hcs hac
    apply loaded_exec_stmt_agreeP mR mR' _ h.code
    intro a ha
    rcases hframe a (by rw [hesp]; intro hs; rcases hcs with hd | hd <;> omega)
        (by intro hA; rcases hac with hd | hd <;> omega) with hr | heq
    · exfalso
      have hret := h.ground.aret.inSL
      have hwin := h.stack_win
      rw [tohostAddr_val] at hwin
      omega
    · exact heq.symm
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mR mR' := by
    intro k hk
    rcases hframe k (by rw [hesp]; intro hs; omega)
        (by rcases h.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · exact absurd hr (by rcases h.ground.aret.scribble_disjoint with hd | hd <;> omega)
    · exact heq.symm
  obtain ⟨v8, hr8, hg8⟩ := h.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := h.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := h.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := h.saved_s3
  obtain ⟨hra, hs0, hs1, hs2, hs3⟩ := ScaffoldRows.initSomeReturn_saved_reads
    (by omega) hag h.saved_ra hr8 hr9 hr18 hr19
  exact
    { h with
      code := hcode
      stmt := h.ground.stmtRepr_execExit h.stmt hSLhi hframeP
      ground := h.ground.transport_execExit hSLhi hpop hframeP
      env_addr := by rw [hpf env h.env_valid]; exact h.env_addr
      env_valid := henv
      store_survives := hstore
      store_bodies := hbodies
      saved_ra := hra
      saved_s0 := ⟨v8, hs0, hg8⟩
      saved_s1 := ⟨v9, hs1, hg9⟩
      saved_s2 := ⟨v18, hs2, hg18⟩
      saved_s3 := ⟨v19, hs3, hg19⟩ }

end FrameFacts

/-- The frame facts carried by an expression-child carrier. -/
theorem EvalChildArm.Carrier.frameFacts {D : EvalChildArm} {s : Stmt} {e : Expr}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (h : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mC :=
  { h with }

/-- A route-ready state from an expression child's widened exit: the result
pointer is the key. -/
theorem EvalChildArm.routeReady_of_exit (D : EvalChildArm) (C : D.Cert) {s : Stmt} {e : Expr}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (cfg : Config)
    (hExitD : EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC cfg) :
    TruthyCopy.RouteReady gC D.retPC (D.sret (sp - 176#64)) (sp - 176#64) D.retPC
      aStmt aInterp aRet aEnv cfg.σ.mem cfg.σ.sailOutput cfg :=
  { good := hExitD.1.good
    tick := hExitD.1.tick
    pc := by rw [hExitD.1.pc, C.ret_pc_clean]
    a0 := hExitD.1.a0
    ra := hExitD.1.ra
    minstret := hExitD.1.minstret
    mem := rfl
    out := rfl
    sp := hExitD.1.spReg
    s0 := (hExitD.1.frame Register.x8 (by decide)).trans hCarrier.s0
    s1 := (hExitD.1.frame Register.x9 (by decide)).trans hCarrier.s1
    s2 := (hExitD.1.frame Register.x18 (by decide)).trans hCarrier.s2
    s3 := (hExitD.1.frame Register.x19 (by decide)).trans hCarrier.s3
    frame := fun R hR => hExitD.1.frame R (by
      cases R <;> simp [AbiPreserved, AbiPreservedNoise] at hR ⊢) }

/-- An in-frame `exec_stmt` arm that runs one child statement through
`jal exec_stmt` at the lowered frame `esp = sp - 176`. -/
structure StmtChildArm where
  /-- Arm entry PC; the prefix starts here. -/
  armPC : BitVec 64
  /-- The reflected prefix from `armPC` up to (excluding) the `jal`. -/
  seg : List BBlock
  /-- PC of `jal exec_stmt`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21
  /-- The child pointer field offset inside the statement node. -/
  childOff : Nat

namespace StmtChildArm

/-- The link PC written by the `jal`. -/
def retPC (D : StmtChildArm) : BitVec 64 := BitVec.addInt D.jalPC 4

/-- The load data of the prefix: the child pointer word. -/
def lds (D : StmtChildArm) (m : Mem) (aStmt : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (aStmt.toNat + D.childOff)]

/-- The reflected outcome of the prefix. -/
def out (D : StmtChildArm) (esp aStmt aInterp aRet aEnv : BitVec 64) (m : Mem) :
    SegEvalState :=
  evalBlocks D.seg
    (SegEvalState.init (EvalChildArm.regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt))

/-! ## The decidable certificate -/

/-- Decided facts about the descriptor. -/
structure Cert (D : StmtChildArm) : Prop where
  arm_align : D.armPC.toNat % 4 = 0
  ret_align : D.retPC.toNat % 4 = 0
  ret_pc_clean : BitVec.update (D.retPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = D.retPC
  jal_tgt : D.jalPC + sign_extend (m := 64) D.jalImm = BitVec.ofNat 64 execStmtEntry
  child_off : D.childOff + 8 ≤ 40
  chain_ok : ChainOK D.armPC [2, 8, 9, 18, 19] D.seg
  avoid_abi : WrChainAvoidAbi D.seg
  keys_out : ∀ esp aStmt aInterp aRet aEnv m,
    KeysOK (keysG (D.out esp aStmt aInterp aRet aEnv m).regs)
  ra_out : ∀ esp aStmt aInterp aRet aEnv m,
    KeysAvoidRa (D.out esp aStmt aInterp aRet aEnv m).regs
  end_pc : ∀ esp aStmt aInterp aRet aEnv m,
    evalBlocksPC D.armPC
      (SegEvalState.init (EvalChildArm.regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt))
      D.seg = D.jalPC
  log_nil : ∀ esp aStmt aInterp aRet aEnv m, (D.out esp aStmt aInterp aRet aEnv m).log = []
  a0_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 10 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (aInterp + sign_extend (m := 64) (0#12))
  a1_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 11 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + D.childOff)))
  a2_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 12 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (aEnv + sign_extend (m := 64) (0#12))
  a3_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 13 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (aRet + sign_extend (m := 64) (0#12))
  sp_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 2 (D.out esp aStmt aInterp aRet aEnv m).regs = some esp
  jal_site : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some D.jalPC →
    σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ D.jalPC vmi D.jalImm Register.x1
        (BitVec.addInt D.jalPC 4))

/-! ## The semantic certificate -/

/-- How the arm's statement constructor exposes its child statement. -/
structure Sem (D : StmtChildArm) (s sc : Stmt) : Prop where
  child_of_repr : ∀ (m : Mem) (a : Nat), StmtRepr m a s →
    ∃ p, read64 m (a + D.childOff) = some p ∧ StmtRepr m p sc
  in_proj : ∀ (m : Mem) (lo hi a : Nat), StmtIn m lo hi a s →
    ∀ p, read64 m (a + D.childOff) = some p → StmtIn m lo hi p sc
  need : sc.stackNeed + execFrame ≤ s.stackNeed
  bodies : ∀ P, Stmt.bodiesBound P s = true → Stmt.bodiesBound P sc = true
  facts : ∀ (m : Mem) (SL : StackLayout) (A : Arena)
    (sp aRet aStmt esp aInterp aEnv aChild : BitVec 64),
    ExecGround m SL A sp aRet aStmt.toNat s → Exec_stmtLoaded m →
    read64 m (aStmt.toNat + D.childOff) = some aChild.toNat →
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt) D.seg

/-! ## The prefix run -/

/-- Exact state after the prefix and its `jal`. -/
structure CallState (D : StmtChildArm)
    (g : (R : Register) → Option (RegisterType R))
    (esp aInterp aChild aEnv aRet : BitVec 64) (m : Mem) (out : Array String)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry)
  ra : cfg.σ.regs.get? Register.x1 = some D.retPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  spReg : cfg.σ.regs.get? Register.x2 = some esp
  a0 : cfg.σ.regs.get? Register.x10 = some aInterp
  a1 : cfg.σ.regs.get? Register.x11 = some aChild
  a2 : cfg.σ.regs.get? Register.x12 = some aEnv
  a3 : cfg.σ.regs.get? Register.x13 = some aRet
  mem : cfg.σ.mem = m
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R

/-- Run the reflected prefix and the `jal` from the arm entry. -/
theorem prefix_run (D : StmtChildArm) (C : D.Cert)
    {m : Mem} {aStmt aInterp aEnv aRet aChild esp : BitVec 64} {cfg : Config}
    (hfacts : ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (D.lds m aStmt) D.seg)
    (hcode : Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + D.childOff) = some aChild.toNat)
    (hgood : GoodState cfg.σ) (htick : cfg.tick < 2)
    (hpc : cfg.σ.regs.get? Register.PC = some D.armPC)
    (hmi : ∃ w, cfg.σ.regs.get? Register.minstret = some w)
    (hmem : cfg.σ.mem = m)
    (hregs : GHolds cfg.σ (EvalChildArm.regs esp aStmt aInterp aRet aEnv)) :
    ∃ cfg', Steps cfg cfg' ∧
      D.CallState (fun R => cfg.σ.regs.get? R) esp aInterp aChild aEnv aRet m
        cfg.σ.sailOutput cfg' := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨σ', i', hs, hi, hG, hPC, hRA, hMI, hRegs, hMem, hOut, hFrame⟩ :=
    bridgeOfSegOut D.seg (EvalChildArm.regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt)
      cfg.σ cfg.tick cfg.steps D.armPC (BitVec.ofNat 64 execStmtEntry) D.retPC vm m
      hgood hpc hvm hmem hregs (by change KeysOK [2, 8, 9, 18, 19]; decide)
      (hmem.symm ▸ hfacts) htick C.chain_ok C.avoid_abi
      (C.keys_out _ _ _ _ _ _) (C.ra_out _ _ _ _ _ _)
      (by
        intro σ i u hG hi hpc hmi hm _
        obtain ⟨vm, hvm⟩ := hmi
        rw [C.end_pc] at hpc
        have hc : Exec_stmtLoaded σ.mem := by
          rw [hm]
          have hl := C.log_nil esp aStmt aInterp aRet aEnv m
          unfold out at hl
          rw [hl]
          exact hcode
        obtain ⟨σ2, i2, hs2, hi2, hG2, hm2, ho2⟩ := C.jal_site σ i u vm hG hpc hvm hc hi
        exact jalStepO_of_obs hs2 hi2 hG2 hm2 ho2 C.jal_tgt)
  have hload := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + D.childOff) aChild hread
  have hzero : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  have hRegs' : GHolds σ' (D.out esp aStmt aInterp aRet aEnv m).regs := hRegs
  refine ⟨⟨σ', i', cfg.steps + evalBlocksFuel D.seg + 1⟩, hs, ?_⟩
  refine
    { good := hG
      tick := hi
      pc := hPC
      ra := hRA
      minstret := hMI
      spReg := gholds_lookup _ hRegs' (C.sp_out _ _ _ _ _ _)
      a0 := ?_
      a1 := ?_
      a2 := ?_
      a3 := ?_
      mem := ?_
      out := hOut
      frame := hFrame }
  · have h := gholds_lookup _ hRegs' (C.a0_out esp aStmt aInterp aRet aEnv m)
    rw [hzero, BitVec.add_zero] at h
    exact h
  · have h := gholds_lookup _ hRegs' (C.a1_out esp aStmt aInterp aRet aEnv m)
    rw [hload] at h
    exact h
  · have h := gholds_lookup _ hRegs' (C.a2_out esp aStmt aInterp aRet aEnv m)
    rw [hzero, BitVec.add_zero] at h
    exact h
  · have h := gholds_lookup _ hRegs' (C.a3_out esp aStmt aInterp aRet aEnv m)
    rw [hzero, BitVec.add_zero] at h
    exact h
  · rw [hMem]
    have hl := C.log_nil esp aStmt aInterp aRet aEnv m
    unfold out at hl
    rw [hl]
    rfl

/-! ## The carrier -/

/-- Static identity of the parent `exec_stmt` frame carried across the child
`exec_stmt` call. -/
structure Carrier (D : StmtChildArm) (s sc : Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R))
    (aC : BitVec 64) (mC : Mem) : Prop where
  s0 : gC Register.x8 = some aStmt
  s1 : gC Register.x9 = some aInterp
  s2 : gC Register.x18 = some aRet
  s3 : gC Register.x19 = some aEnv
  spReg : gC Register.x2 = some (sp - 176#64)
  parentSp : g Register.x2 = some sp
  code : Exec_stmtLoaded mC
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ra_align : r.toNat % 4 = 0
  stmt : StmtRepr mC aStmt.toNat s
  child_read : read64 mC (aStmt.toNat + D.childOff) = some aC.toNat
  child_stmt : StmtRepr mC aC.toNat sc
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  store : StoreRepr mC N A φf φc st.store
  env_valid : EnvValid st env
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mC[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  saved_ra : read64 mC (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 mC (sp.toNat - 16) = some v.toNat ∧ g Register.x8 = some v
  saved_s1 : ∃ v, read64 mC (sp.toNat - 24) = some v.toNat ∧ g Register.x9 = some v
  saved_s2 : ∃ v, read64 mC (sp.toNat - 32) = some v.toNat ∧ g Register.x18 = some v
  saved_s3 : ∃ v, read64 mC (sp.toNat - 40) = some v.toNat ∧ g Register.x19 = some v
  stack_budget : StackOK SL sp
    (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget s = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  envset_defined : (∃ v, gC Register.x20 = some v) ∧ (∃ v, gC Register.x21 = some v)
  ground : ExecGround mC SL A sp aRet aStmt.toNat s
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mC[a]? = m0[a]?
  mem_extends : MemExtends m0 mC
  frame : ∀ R : Register, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ gC R = g R

/-- The child entry reached by the arm, with the parent carrier. -/
def DispatchPost (D : StmtChildArm) (s sc : Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (cfg : Config) : Prop :=
  ∃ (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem),
    D.Carrier s sc g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC ∧
    ExecEntry gC N A SL φf φc st d env sc (sp - 176#64) D.retPC aInterp aC aEnv aRet mC cfg

private theorem child_headroom (sc : Stmt) (extra : Nat) :
    176 + 1088 ≤ sc.stackNeed + extra + 1088 := by
  have hneed := Stmt.stackNeed_ge sc
  simp only [execFrame] at hneed
  omega

/-- Geometry of the lowered frame. -/
theorem Carrier.geom {D : StmtChildArm} {s sc : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (h : D.Carrier s sc g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    176 ≤ sp.toNat ∧ (sp - 176#64).toNat = sp.toNat - 176 ∧
    SL.lo + 176 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 := by
  have hneed := Stmt.stackNeed_ge s
  simp only [execFrame] at hneed
  obtain ⟨hlo, hhi, hal⟩ := h.stack_budget
  have h176 : 176 ≤ sp.toNat := by omega
  exact ⟨h176, EvalChildArm.esp_toNat sp h176, by omega, hhi, hal⟩

/-- **The parametric child call from the arm state.**  Run the arm prefix and
the `jal`; land at the child's `ExecEntry` with the parent carrier. -/
theorem dispatch_of_armState (D : StmtChildArm) (C : D.Cert) {s sc : Stmt}
    (S : D.Sem s sc)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    (hA : Vsa.Sim.ArmState D.armPC s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet
      m0 ment cfg) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      D.DispatchPost s sc g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 cfg' := by
  have hsp176 : 176 ≤ sp.toNat := by
    have hneed := Stmt.stackNeed_ge s
    simp only [execFrame] at hneed
    have := hA.stack_budget.1
    omega
  obtain ⟨p, hread, hrepr⟩ := S.child_of_repr _ _ hA.stmt
  let aChild := BitVec.ofNat 64 p
  have hp : aChild.toNat = p :=
    Nat.mod_eq_of_lt (read64_lt_eg4 ment (aStmt.toNat + D.childOff) p hread)
  have hreadB : read64 ment (aStmt.toNat + D.childOff) = some aChild.toNat := hp ▸ hread
  have hreprB : StmtRepr ment aChild.toNat sc := hp ▸ hrepr
  have hfacts := S.facts ment SL A sp aRet aStmt (sp - 176#64) aInterp aEnv aChild
    hA.ground hA.code hreadB
  obtain ⟨cC, hsC, hc⟩ := D.prefix_run C hfacts hA.code hreadB hA.good hA.tick hA.pc
    hA.minstret hA.mem ⟨hA.spReg, hA.s0, hA.s1, hA.s2, hA.s3, True.intro⟩
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := EvalChildArm.esp_toNat sp hsp176
  have hneed := S.need
  simp only [execFrame] at hneed
  have hbudget : StackOK SL (sp - 176#64)
      (sc.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) := by
    obtain ⟨hlo, hhi, halign⟩ := hA.stack_budget
    simp only [StackOK, hesp]
    omega
  have hground : ExecGround ment SL A (sp - 176#64) aRet aChild.toNat sc :=
    hA.ground.child_sameRet
      (fun lo hi hin => S.in_proj ment lo hi aStmt.toNat hin _ hreadB) (by rw [hesp]; omega)
  obtain ⟨lo, hi, hr⟩ := hground.ast.region
  have hn := stmtIn_node hr.nodes
  have h8 := (hc.frame Register.x8 (by decide)).trans hA.s0
  have h9 := (hc.frame Register.x9 (by decide)).trans hA.s1
  have h18 := (hc.frame Register.x18 (by decide)).trans hA.s2
  have h19 := (hc.frame Register.x19 (by decide)).trans hA.s3
  have hDefined : (∃ v, cC.σ.regs.get? Register.x20 = some v) ∧
      (∃ v, cC.σ.regs.get? Register.x21 = some v) := by
    obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := hA.envset
    exact ⟨⟨v20, (hc.frame Register.x20 (by decide)).trans hv20⟩,
      ⟨v21, (hc.frame Register.x21 (by decide)).trans hv21⟩⟩
  refine ⟨cC, hsC, (fun R => cC.σ.regs.get? R), aChild, ment, ?_, ?_⟩
  · refine
      { s0 := h8
        s1 := h9
        s2 := h18
        s3 := h19
        spReg := hc.spReg
        parentSp := hA.parentSp
        code := hA.code
        code_stack_disjoint := hA.code_stack_disjoint
        stack_ram := hA.stack_ram
        stack_win := hA.stack_win
        ra_align := hA.ra_align
        stmt := hA.stmt
        child_read := hreadB
        child_stmt := hreprB
        env_addr := hA.env_addr
        store := hA.store
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
        envset_defined := hDefined
        ground := hA.ground
        mem_frame := hA.mem_frame
        mem_extends := hA.mem_extends
        frame := ?_ }
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
    exact Or.inr ((hc.frame R hR.1).trans (hA.frame R hR
      (beq_eq_false_iff_ne.mpr (Ne.symm h8)) (beq_eq_false_iff_ne.mpr (Ne.symm h9))
      (beq_eq_false_iff_ne.mpr (Ne.symm h18)) (beq_eq_false_iff_ne.mpr (Ne.symm h19))
      (beq_eq_false_iff_ne.mpr (Ne.symm h2))))
  · refine
      { good := hc.good
        tick := hc.tick
        pc := hc.pc
        a0 := hc.a0
        a1 := hc.a1
        a2 := hc.a2
        envPtr := hA.env_addr
        a3 := hc.a3
        ra := hc.ra
        ra_align := C.ret_align
        spReg := hc.spReg
        stackOK := StackOK.mono (child_headroom sc _) hbudget
        stackBudget := hbudget
        stmt_bodies := S.bodies _ hA.stmt_bodies
        store_bodies := hA.store_bodies
        minstret := hc.minstret
        mem := hc.mem
        code := hc.mem ▸ hA.code
        stmt := hc.mem ▸ hreprB
        store := hc.mem ▸ hA.store
        env_valid := hA.env_valid
        store_survives := ?_
        out := ?_
        frame := fun _ _ => rfl
        code_stack_disjoint := ?_
        stack_ram := hA.stack_ram
        stack_win := hA.stack_win
        stmt_stack_disjoint := ?_
        stmt_ram := ?_
        stmt_win := ?_
        spill_defined := ⟨⟨_, h8⟩, ⟨_, h9⟩, ⟨_, h18⟩, ⟨_, h19⟩⟩
        envset_defined := hDefined
        ground := hc.mem ▸ hground }
    · intro m' hag
      apply hA.store_survives m'
      intro k hk
      exact hc.mem ▸ hag k hk
    · change String.join cC.σ.sailOutput.toList = st.out
      rw [hc.out]
      exact hA.out
    · rcases hA.code_stack_disjoint with hd | hd
      · left; rw [hesp]; omega
      · exact Or.inr hd
    · have := hn.lo_le; have := hn.hi_ge
      have := hbudget.2.1
      rcases hr.stack_disjoint with hd | hd
      · left; omega
      · right; omega
    · have := hr.lo_ram; have := hr.hi_ram
      have := hn.lo_le; have := hn.hi_ge
      constructor <;> omega
    · have := hr.win; have := hn.lo_le; omega

/-! ## The child exit -/

/-- Parent facts recovered at the child's widened exit. -/
structure ExitKit (D : StmtChildArm) (s : Stmt)
    (g gC : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc' : Addr → Nat)
    (st' : SpecSt) (d : Nat) (env : Addr) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some D.retPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  a0 : cfg.σ.regs.get? Register.x10 = some (StatusCode status)
  ra : cfg.σ.regs.get? Register.x1 = some D.retPC
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R
  out : OutRepr cfg.σ st'
  stack_bytes : ∀ k, SL.lo ≤ k → k < SL.hi → ∃ b : BitVec 8, cfg.σ.mem[k]? = some b
  ff : FrameFacts s g N A SL φf' φc' st' d env sp r aInterp aStmt aEnv aRet gC cfg.σ.mem

private theorem abiPreservedNoise_of_abi {R : Register}
    (hR : AbiPreserved R = true) : AbiPreservedNoise R := by
  cases R <;> simp [AbiPreserved, AbiPreservedNoise] at hR ⊢

/-- The frame facts carried by a statement-child carrier. -/
theorem Carrier.frameFacts {D : StmtChildArm} {s sc : Stmt}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (h : D.Carrier s sc g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mC :=
  { h with }

/-- Recover the parent at the child's widened exit. -/
theorem exitKit_of_exit (D : StmtChildArm) (C : D.Cert) {s sc : Stmt} (S : D.Sem s sc)
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {status : Status}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem}
    (hCarrier : D.Carrier s sc g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hBody : ExecS st d env sc st' status)
    (cfg : Config)
    (hChild : ExecExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' status (sp - 176#64) D.retPC aRet mC cfg) :
    ∃ (φf' φc' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      D.ExitKit s g gC N A SL φf' φc' st' d env status sp r aInterp aStmt aEnv aRet cfg := by
  obtain ⟨φf', φc', hc⟩ := ScaffoldRows.initSomeChildExitView_of_exitD hChild
  have hpop : StackBytesPresent cfg.σ.mem SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := hCarrier.ground.stack_bytes k hlo hhi
    exact hc.memExtends k b hb
  refine ⟨φf', φc', hc.frames, hc.closures, ?_⟩
  exact
    { good := hc.exit.good
      tick := hc.exit.tick
      pc := by rw [hc.exit.pc, C.ret_pc_clean]
      minstret := hc.exit.minstret
      a0 := hc.exit.a0
      ra := hc.exit.ra
      spReg := hc.exit.spReg
      frame := fun R hR => hc.exit.frame R (abiPreservedNoise_of_abi hR)
      out := hc.exit.out
      stack_bytes := hpop
      ff := hCarrier.frameFacts.afterExit hc.exit.memFrame hc.memExtends hc.frames
        hc.storeSurvives (hCarrier.env_valid.afterExecS hBody)
        (StoreBodiesBound.afterExecS hBody (S.bodies _ hCarrier.stmt_bodies)
          hCarrier.store_bodies) }

/-- The child's return is route-ready with the status code as the key. -/
theorem ExitKit.toRouteReady {D : StmtChildArm} {s : Stmt}
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc' : Addr → Nat}
    {st' : SpecSt} {d : Nat} {env : Addr} {status : Status}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {cfg : Config}
    (K : D.ExitKit s g gC N A SL φf' φc' st' d env status sp r aInterp aStmt aEnv aRet cfg) :
    TruthyCopy.RouteReady gC D.retPC (StatusCode status) (sp - 176#64) D.retPC
      aStmt aInterp aRet aEnv cfg.σ.mem cfg.σ.sailOutput cfg :=
  { good := K.good, tick := K.tick, pc := K.pc, a0 := K.a0, ra := K.ra
    minstret := K.minstret, mem := rfl, out := rfl, sp := K.spReg
    s0 := (K.frame Register.x8 (by decide)).trans K.ff.s0
    s1 := (K.frame Register.x9 (by decide)).trans K.ff.s1
    s2 := (K.frame Register.x18 (by decide)).trans K.ff.s2
    s3 := (K.frame Register.x19 (by decide)).trans K.ff.s3
    frame := K.frame }

end StmtChildArm

/-! ## After a route -/

/-- The arm state at the end of a memory-pure reflected route whose register
image keeps the five frame registers. -/
theorem ArmState.of_routeHead {bs : List BBlock} {endPC : BitVec 64} {L : GRegs}
    {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfgR : Config}
    {s : Stmt} {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    (hHead : TruthyCopy.RouteHead bs endPC L lds mR out gC cfgR)
    (hlog : (evalBlocks bs (SegEvalState.init L lds)).log = [])
    (h8 : lookupG 8 (evalBlocks bs (SegEvalState.init L lds)).regs = some aStmt)
    (h9 : lookupG 9 (evalBlocks bs (SegEvalState.init L lds)).regs = some aInterp)
    (h18 : lookupG 18 (evalBlocks bs (SegEvalState.init L lds)).regs = some aRet)
    (h19 : lookupG 19 (evalBlocks bs (SegEvalState.init L lds)).regs = some aEnv)
    (h2 : lookupG 2 (evalBlocks bs (SegEvalState.init L lds)).regs = some (sp - 176#64))
    (F : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mR)
    (hout : String.join out.toList = st.out) :
    ArmState endPC s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet mR mR cfgR := by
  have hmem : cfgR.σ.mem = mR := by rw [hHead.mem, hlog]; rfl
  exact
    { good := hHead.good
      tick := hHead.tick
      pc := hHead.pc
      s0 := gholds_lookup _ hHead.regs h8
      s1 := gholds_lookup _ hHead.regs h9
      s2 := gholds_lookup _ hHead.regs h18
      s3 := gholds_lookup _ hHead.regs h19
      spReg := gholds_lookup _ hHead.regs h2
      minstret := hHead.minstret
      out := by
        change String.join cfgR.σ.sailOutput.toList = st.out
        rw [hHead.out]
        exact hout
      mem := hmem
      code := F.code
      store := F.store_survives mR (fun _ _ => rfl)
      saved_ra := F.saved_ra
      saved_s0 := F.saved_s0
      saved_s1 := F.saved_s1
      saved_s2 := F.saved_s2
      saved_s3 := F.saved_s3
      parentSp := F.parentSp
      frame := by
        intro R hR he8 he9 he18 he19 he2
        have hP : TruthyCopy.abiButS0 R = true := by
          unfold TruthyCopy.abiButS0; rw [hR.1, he8]; rfl
        rcases F.frame R hR with hspecial | heq
        · rcases hspecial with rfl | rfl | rfl | rfl | rfl
          · simp at he8
          · simp at he9
          · simp at he18
          · simp at he19
          · simp at he2
        · exact (hHead.frame R hP).trans heq
      mem_frame := fun _ _ => rfl
      mem_extends := MemExtends.refl mR
      ra_align := F.ra_align
      spSL := F.geom.2.2.2.1
      stack_budget := F.stack_budget
      stmt_bodies := F.stmt_bodies
      store_bodies := F.store_bodies
      store_survives := F.store_survives
      env_valid := F.env_valid
      env_addr := F.env_addr
      code_stack_disjoint := F.code_stack_disjoint
      stack_ram := F.stack_ram
      stack_win := F.stack_win
      ground := F.ground
      stmt := F.stmt
      envset := by
        obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := F.envset_defined
        exact ⟨⟨v20, (hHead.frame Register.x20 (by decide)).trans hv20⟩,
          ⟨v21, (hHead.frame Register.x21 (by decide)).trans hv21⟩⟩ }

/-- The normal-exit head at the end of a memory-pure route that lands on an
arm's `li a0,0`. -/
theorem normalExitPre_of_routeHead {bs : List BBlock} {liPC : BitVec 64} {L : GRegs}
    {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfgR : Config}
    {s : Stmt} {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64}
    (hHead : TruthyCopy.RouteHead bs liPC L lds mR out gC cfgR)
    (hlog : (evalBlocks bs (SegEvalState.init L lds)).log = [])
    (h2 : lookupG 2 (evalBlocks bs (SegEvalState.init L lds)).regs = some (sp - 176#64))
    (F : FrameFacts s g N A SL φf' φc' st' d env sp r aInterp aStmt aEnv aRet gC mR)
    (hpf : PhiExtends φf φf' nf) (hpc : PhiExtends φc φc' nc)
    (hout : String.join out.toList = st'.out) :
    NormalExitTailPre liPC g N A SL φf φc φf' φc' nf nc st' sp r aRet mR cfgR := by
  have hmem : cfgR.σ.mem = mR := by rw [hHead.mem, hlog]; rfl
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hram := F.stack_ram
  have hwin := F.stack_win
  exact
    { good := hHead.good
      tick := hHead.tick
      pc := hHead.pc
      minstret := hHead.minstret
      spReg := gholds_lookup _ hHead.regs h2
      code := by rw [hmem]; exact F.code
      out := by
        change String.join cfgR.σ.sailOutput.toList = st'.out
        rw [hHead.out]
        exact hout
      frames := hpf
      closures := hpc
      storeSurvives := by rw [hmem]; exact F.store_survives
      saved_ra := by rw [hmem]; exact F.saved_ra
      saved_s0 := by rw [hmem]; exact F.saved_s0
      saved_s1 := by rw [hmem]; exact F.saved_s1
      saved_s2 := by rw [hmem]; exact F.saved_s2
      saved_s3 := by rw [hmem]; exact F.saved_s3
      parentSp := F.parentSp
      frame := by
        intro R hR he8 he9 he18 he19 he2
        have hP : TruthyCopy.abiButS0 R = true := by
          unfold TruthyCopy.abiButS0; rw [hR.1, he8]; rfl
        rcases F.frame R hR with hspecial | heq
        · rcases hspecial with rfl | rfl | rfl | rfl | rfl
          · simp at he8
          · simp at he9
          · simp at he18
          · simp at he19
          · simp at he2
        · exact (hHead.frame R hP).trans heq
      memExtends := by rw [hmem]; exact MemExtends.refl mR
      memFrame := by rw [hmem]; exact fun _ _ _ => Or.inr rfl
      spRoom := h176
      spHi := by omega
      spLo := by omega
      spWin := by omega
      spAlign := by omega
      retAlign := F.ra_align }

/-- Propagate a returning child's value through the memory-pure parent
epilogue at `0x80004150`, reached by a route from the child's return. -/
theorem StmtChildArm.retExit_of_routeHead (D : StmtChildArm) {s sc : Stmt}
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {rv : Value}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem} {cfgX : Config}
    (hCarrier : D.Carrier s sc g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hChild : ExecExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' (.ret rv) (sp - 176#64) D.retPC aRet mC cfgX)
    (K : D.ExitKit s g gC N A SL φf' φc' st' d env (.ret rv) sp r aInterp aStmt aEnv aRet cfgX)
    {bs : List BBlock} {L : GRegs} {lds : List (List (BitVec 8))} {cfgR : Config}
    (hHead : TruthyCopy.RouteHead bs 0x80004150#64 L lds cfgX.σ.mem cfgX.σ.sailOutput gC cfgR)
    (hlog : (evalBlocks bs (SegEvalState.init L lds)).log = [])
    (h2 : lookupG 2 (evalBlocks bs (SegEvalState.init L lds)).regs = some (sp - 176#64)) :
    ∃ cfgE : Config, Steps cfgR cfgE ∧
      ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.ret rv) sp r aRet mC cfgE := by
  have hmR : cfgR.σ.mem = cfgX.σ.mem := by rw [hHead.mem, hlog]; rfl
  have hspR : cfgR.σ.regs.get? Register.x2 = some (sp - 176#64) := gholds_lookup _ hHead.regs h2
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := K.ff.geom
  have hram := K.ff.stack_ram
  have hwin := K.ff.stack_win
  obtain ⟨v8, hr8, hg8⟩ := K.ff.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := K.ff.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := K.ff.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := K.ff.saved_s3
  have hpre : ExecRetEpiloguePre (sp - 176#64) r v8 v9 v18 v19 cfgR := by
    refine ⟨hHead.good, hHead.tick, hHead.pc, hHead.minstret, hspR, ?_, ?_, ?_, ?_, ?_,
      K.ff.ra_align, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmR]; exact K.ff.code
    · rw [hesp]; omega
    · rw [hesp]; omega
    · rw [hesp]; have := tohostAddr_val; omega
    · rw [hesp]; omega
    · rw [hmR, hesp, show sp.toNat - 176 + 168 = sp.toNat - 8 by omega]
      exact K.ff.saved_ra
    · rw [hmR, hesp, show sp.toNat - 176 + 160 = sp.toNat - 16 by omega]
      exact hr8
    · rw [hmR, hesp, show sp.toNat - 176 + 152 = sp.toNat - 24 by omega]
      exact hr9
    · rw [hmR, hesp, show sp.toNat - 176 + 144 = sp.toNat - 32 by omega]
      exact hr18
    · rw [hmR, hesp, show sp.toNat - 176 + 136 = sp.toNat - 40 by omega]
      exact hr19
  obtain ⟨cD, hp, htail⟩ := execRetEpilogue_run hpre
  have hmD : cD.σ.mem = cfgX.σ.mem := hp.mem.trans hmR
  have hspD : cD.σ.regs.get? Register.x2 = some sp := by
    simpa only [BitVec.sub_add_cancel] using hp.sp
  obtain ⟨φf'', φc'', hc⟩ := ScaffoldRows.initSomeChildExitView_of_exitD hChild
  refine ⟨cD, htail.steps, ?_, ?_, φf'', φc'', hc.frames, hc.closures, ?_⟩
  · exact
      { good := hp.good
        tick := hp.tick
        pc := by
          simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64
            from by decide, BitVec.add_zero] using hp.pc
        a0 := hp.status
        ra := hp.ra
        spReg := hspD
        minstret := hp.minstret
        store := ⟨φf'', φc'', hc.frames, hc.closures, by
          rw [hmD]; exact hc.storeSurvives _ (fun _ _ => rfl)⟩
        out := by
          change String.join cD.σ.sailOutput.toList = st'.out
          rw [hp.output, hHead.out]
          exact K.out
        retval := by
          intro value hvalue
          obtain ⟨φcv, hcv, hv⟩ := hChild.1.retval value hvalue
          exact ⟨φcv, hcv, hmD.symm ▸ hv⟩
        frame := by
          intro R hR
          by_cases h2 : R = Register.x2
          · subst R; exact hspD.trans hCarrier.parentSp.symm
          by_cases h8 : R = Register.x8
          · subst R; exact hp.s0.trans hg8.symm
          by_cases h9 : R = Register.x9
          · subst R; exact hp.s1.trans hg9.symm
          by_cases h18 : R = Register.x18
          · subst R; exact hp.s2.trans hg18.symm
          by_cases h19 : R = Register.x19
          · subst R; exact hp.s3.trans hg19.symm
          have hkeep : execRetEpilogueKeep R = true := by
            simp [execRetEpilogueKeep, hR.1, h2, h8, h9, h18, h19]
          have hP : TruthyCopy.abiButS0 R = true := by
            have h8' : (Register.x8 == R) = false := beq_eq_false_iff_ne.mpr (Ne.symm h8)
            unfold TruthyCopy.abiButS0; rw [hR.1, h8']; rfl
          have hg : gC R = g R := by
            rcases hCarrier.frame R hR with hs | heq
            · rcases hs with hs | hs | hs | hs | hs
              · exact False.elim (h8 hs)
              · exact False.elim (h9 hs)
              · exact False.elim (h18 hs)
              · exact False.elim (h19 hs)
              · exact False.elim (h2 hs)
            · exact heq
          exact (htail.frame.regs.eq R hkeep).trans ((hHead.frame R hP).trans hg)
        memFrame := by
          intro a hstk hA
          rw [hmD]
          rcases hChild.1.memFrame a
              (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
          · exact Or.inl hr
          · exact Or.inr heq }
  · rw [hmD]
    exact hChild.2.1
  · rw [hmD]
    exact hc.storeSurvives

/-! ## The parent frame at an expression child's exit -/

/-- The frame facts at an expression child's widened exit, for any maps the
exit's store survives with (the exit kit carries no map). -/
theorem EvalChildArm.frameFacts_at_exit_of_store (D : EvalChildArm) (C : D.Cert) {s : Stmt}
    {e : Expr} (S : D.Sem s e)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hE : EvalE st d env e st' v)
    (cfg : Config)
    (hExitD : EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC cfg)
    (hpf : PhiExtends φf φf' st.store.frames.size)
    (hSurv : ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store)
    {φf0 φc0 : Addr → Nat}
    (hKit : D.ExitKit s gC N A SL φf0 φc0 st' v sp aStmt aRet mC cfg) :
    FrameFacts s g N A SL φf' φc' st' d env sp r aInterp aStmt aEnv aRet gC cfg.σ.mem := by
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom C
  have hsretRoom := C.sret_room
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mC cfg.σ.mem := by
    intro k hk
    rcases hExitD.1.memFrame k (by rw [hesp]; intro hs; omega)
        (by rcases hCarrier.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · rw [hsret] at hr
      omega
    · exact heq.symm
  obtain ⟨v8, hr8, hg8⟩ := hCarrier.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := hCarrier.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := hCarrier.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := hCarrier.saved_s3
  obtain ⟨hra, hs0, hs1, hs2, hs3⟩ := ScaffoldRows.initSomeReturn_saved_reads
    (by omega) hag hCarrier.saved_ra hr8 hr9 hr18 hr19
  exact
    { hCarrier.frameFacts with
      code := hKit.code
      stmt := hKit.parent_stmt
      ground := hKit.ground
      env_addr := by rw [hpf env hCarrier.env_valid]; exact hCarrier.env_addr
      env_valid := hCarrier.env_valid.afterEvalE hE
      store_survives := hSurv
      store_bodies := StoreBodiesBound.afterEvalE hE (S.bodies _ hCarrier.stmt_bodies)
        hCarrier.store_bodies
      saved_ra := hra
      saved_s0 := ⟨v8, hs0, hg8⟩
      saved_s1 := ⟨v9, hs1, hg9⟩
      saved_s2 := ⟨v18, hs2, hg18⟩
      saved_s3 := ⟨v19, hs3, hg19⟩ }

/-- The frame facts at an expression child's widened exit, with the extended
maps and the reached source state. -/
theorem EvalChildArm.frameFacts_at_exit (D : EvalChildArm) (C : D.Cert) {s : Stmt} {e : Expr}
    (S : D.Sem s e)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hE : EvalE st d env e st' v)
    (cfg : Config)
    (hExitD : EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC cfg) :
    ∃ (φf' φc' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      D.ExitKit s gC N A SL φf' φc' st' v sp aStmt aRet mC cfg ∧
      FrameFacts s g N A SL φf' φc' st' d env sp r aInterp aStmt aEnv aRet gC cfg.σ.mem := by
  obtain ⟨φf', φc', hpf, hpc, hSurv, hKit⟩ := D.exitKit_at_exit C hCarrier cfg hExitD
  exact ⟨φf', φc', hpf, hpc, hKit,
    D.frameFacts_at_exit_of_store C S hCarrier hE cfg hExitD hpf hSurv hKit⟩

/-! ## Memory bookkeeping across an iteration -/

/-- Memory change tolerated by the loop's exit: presence is preserved, and
outside the stack window and the arena only the retslot may differ. -/
def LoopFrame (SL : StackLayout) (A : Arena) (sp aRet : BitVec 64) (m m' : Mem) : Prop :=
  MemExtends m m' ∧
  ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ m'[a]? = m[a]?

namespace LoopFrame

theorem refl (SL : StackLayout) (A : Arena) (sp aRet : BitVec 64) (m : Mem) :
    LoopFrame SL A sp aRet m m :=
  ⟨MemExtends.refl m, fun _ _ _ => Or.inr rfl⟩

theorem trans {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {m m' m'' : Mem}
    (h1 : LoopFrame SL A sp aRet m m') (h2 : LoopFrame SL A sp aRet m' m'') :
    LoopFrame SL A sp aRet m m'' := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro a hstk hA
  rcases h2.2 a hstk hA with hr | heq
  · exact Or.inl hr
  · rcases h1.2 a hstk hA with hr' | heq'
    · exact Or.inl hr'
    · exact Or.inr (heq.trans heq')

/-- A change confined to the stack window. -/
theorem of_offstack {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {m m' : Mem}
    (hext : MemExtends m m')
    (hoff : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m'[a]? = m[a]?) :
    LoopFrame SL A sp aRet m m' :=
  ⟨hext, fun a hstk _ => Or.inr (hoff a hstk)⟩

/-- A statement child's widened exit at the lowered frame. -/
theorem of_execExit {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {m : Mem}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {φf φc : Addr → Nat} {nf nc : Nat} {st' : SpecSt} {status : Status}
    {r : BitVec 64} {cfg : Config} (hsp : 176 ≤ sp.toNat)
    (hExit : ExecExitD g N A SL φf φc nf nc st' status (sp - 176#64) r aRet m cfg) :
    LoopFrame SL A sp aRet m cfg.σ.mem := by
  have hesp := EvalChildArm.esp_toNat sp hsp
  refine ⟨hExit.2.1, ?_⟩
  intro a hstk hA
  exact hExit.1.memFrame a (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA

/-- An expression child's widened exit at the lowered frame with an in-frame
result slot. -/
theorem of_evalExit {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {m : Mem}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {φf φc : Addr → Nat} {nf nc : Nat} {st' : SpecSt} {v : Value}
    {r sret : BitVec 64} {cfg : Config} (hsp : SL.lo + 176 ≤ sp.toNat)
    (hsret : sret.toNat + 24 ≤ sp.toNat)
    (hsretLo : (sp - 176#64).toNat ≤ sret.toNat)
    (hExit : EvalExitD g N A SL φf φc nf nc st' v (sp - 176#64) r sret m cfg) :
    LoopFrame SL A sp aRet m cfg.σ.mem := by
  have hesp := EvalChildArm.esp_toNat sp (by omega)
  refine ⟨hExit.2.1, ?_⟩
  intro a hstk hA
  rcases hExit.1.memFrame a (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
  · exfalso
    rw [hesp] at hsretLo
    exact hstk ⟨by omega, by omega⟩
  · exact Or.inr heq

end LoopFrame

end Vsa.Sim
