import Vsa.Sim.rows.InitSomeReturn
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.ExecRecCommon
import Vsa.While.StoreBodiesBoundPreservation

/-! # Present-initializer return adapter

Compose an arbitrary-status recursive initializer exit with the concrete
`j 0x8000426c`, selecting the child's coherent extended allocation maps for
the ensuing for-loop boundary.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

/-- Named view of the conjunction-based recursive statement exit. -/
structure InitSomeChildExitView
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' : SpecSt) (status : Status)
    (sp r aRet : BitVec 64) (m0 : Mem) (cfg : Config)
    (frameMap closureMap : Addr → Nat) : Prop where
  exit : ExecExit g N A SL φf φc nf nc st' status sp r aRet m0 cfg
  memExtends : MemExtends m0 cfg.σ.mem
  frames : PhiExtends φf frameMap nf
  closures : PhiExtends φc closureMap nc
  storeSurvives : ∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A frameMap closureMap st'.store

/-- Destructure `ExecExitD` once into named fields. -/
theorem initSomeChildExitView_of_exitD
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {status : Status}
    {sp r aRet : BitVec 64} {m0 : Mem} {cfg : Config}
    (h : ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0 cfg) :
    ∃ frameMap closureMap,
      InitSomeChildExitView g N A SL φf φc nf nc st' status sp r aRet m0 cfg
        frameMap closureMap := by
  obtain ⟨hexit, hext, φf', φc', hpf, hpc, hsurv⟩ := h
  exact ⟨φf', φc', hexit, hext, hpf, hpc, hsurv⟩

/-- Registers untouched by the `j x0` return adapter. -/
structure InitSomeJumpFrame (R : Register) : Prop where
  mcycle : (Register.mcycle == R) = false
  mtime : (Register.mtime == R) = false
  mip : (Register.mip == R) = false
  minstret : (Register.minstret == R) = false
  pc : (Register.PC == R) = false
  nextPC : (Register.nextPC == R) = false
  minstretIncrement : (Register.minstret_increment == R) = false

/-- Return from the initializer child and land at the loop head.  The child
status is intentionally unrestricted: `ExecInit.some` ignores it. -/
theorem initSomeReturnReady
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d outer : Nat} {s : Stmt} {status : Status}
    {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem}
    {cfgCall cfgRet : Config}
    (h : InitSomeBodyLanding g N A SL φf φc st d outer s cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfgCall)
    (hChild : ExecExitD (fun R => cfgCall.σ.regs.get? R) N A SL φf φc
      st.store.frames.size st.store.closures.size st' status
      (sp - 176#64) (0x80004258#64) aRet ment cfgRet)
    (hExec : ExecS st d outer s st' status)
    (hStoreBodies : StoreBodiesBound st'.store perCallBudget) :
    ∃ cfg : Config, Steps cfgRet cfg ∧
      ExecInitExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' d outer (some s) cnd step body sp r aInterp aStmt aOuter aRet m0 cfg := by
  obtain ⟨φf', φc', hc⟩ := initSomeChildExitView_of_exitD hChild
  have hsp176 : 176 ≤ sp.toNat := by
    have := h.stage.stack_budget.1
    omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hspHi : sp.toNat ≤ SL.hi := h.stage.stack_budget.2.1
  have hGround : ExecGround cfgRet.σ.mem SL A sp aRet aStmt.toNat
      (.forStmt (some s) cnd step body) :=
    h.stage.ground.transport_execExit hspHi
      (fun k hlo hhi => by
        obtain ⟨b, hb⟩ := h.stage.ground.stack_bytes k hlo hhi
        exact hc.memExtends k b hb)
      (fun a hstk hA => hc.exit.memFrame a (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA)
  have hStmt : StmtRepr cfgRet.σ.mem aStmt.toNat
      (.forStmt (some s) cnd step body) :=
    h.stage.ground.stmtRepr_execExit h.stage.stmt hspHi
      (fun a hstk hA => hc.exit.memFrame a (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA)
  have hCode : Exec_stmtLoaded cfgRet.σ.mem := by
    have hcodeStack := h.stage.code_stack_disjoint
    have harenaCode := h.stage.ground.arena_code
    simp only [execStmtEntry, execStmtEnd] at hcodeStack harenaCode
    apply loaded_exec_stmt_agreeP ment cfgRet.σ.mem _ h.stage.code
    intro a ha
    rcases hc.exit.memFrame a (by
        rw [hspsub]
        intro hs
        rcases hcodeStack with hd | hd <;> omega)
        (by intro hA; rcases harenaCode with hd | hd <;> omega) with hr | heq
    · exfalso
      have hret := h.stage.ground.aret.inSL
      have hwin := h.stage.stack_win
      rw [tohostAddr_val] at hwin
      omega
    · exact heq.symm
  obtain ⟨vmi, hvmi⟩ := hc.exit.minstret
  obtain ⟨cfg, hs, htick, hgood, hmem, hobs⟩ :=
    initSomeReturn_j cfgRet vmi hc.exit.good hc.exit.tick hc.exit.pc hvmi hCode
  have hreg (R : Register) (hdis : InitSomeJumpFrame R) :
      cfg.σ.regs.get? R = cfgRet.σ.regs.get? R := by
    rw [hobs.1 R hdis.mcycle hdis.mtime hdis.mip]
    exact get?_sigmaPost_jump_x0 cfgRet.σ 0x80004258#64 vmi 0x8000426c#64 R
      hdis.minstret hdis.pc hdis.nextPC hdis.minstretIncrement
  have hag := initSomeReturn_spill_agree h.stage hc.exit
  obtain ⟨v8, hr8, hg8⟩ := h.stage.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := h.stage.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := h.stage.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := h.stage.saved_s3
  obtain ⟨hra, hs0, hs1, hs2, hs3⟩ := initSomeReturn_saved_reads
    (by have := h.stage.stack_budget.1; omega) hag h.stage.saved_ra
    hr8 hr9 hr18 hr19
  refine ⟨cfg, Steps.single hs, ⟨⟨φf', φc', 0x80004258#64,
    ⟨hc.frames, hc.closures, ?_⟩⟩⟩⟩
  refine
    { good := hgood
      tick := htick
      pc := by
        rw [hobs.1 Register.PC (by decide) (by decide) (by decide)]
        simp [sigmaPost_jump_x0, Std.ExtDHashMap.get?_insert]
      s0 := (hreg _ (by constructor <;> decide)).trans (hc.exit.frame Register.x8 (by decide) |>.trans
        (h.frame Register.x8 (by decide) |>.trans h.stage.s0))
      s1 := (hreg _ (by constructor <;> decide)).trans (hc.exit.frame Register.x9 (by decide) |>.trans
        (h.frame Register.x9 (by decide) |>.trans h.stage.s1))
      s2 := (hreg _ (by constructor <;> decide)).trans (hc.exit.frame Register.x18 (by decide) |>.trans
        (h.frame Register.x18 (by decide) |>.trans h.stage.s2))
      s3 := (hreg _ (by constructor <;> decide)).trans (hc.exit.frame Register.x19 (by decide) |>.trans
        (h.frame Register.x19 (by decide) |>.trans h.stage.s3))
      spReg := (hreg _ (by constructor <;> decide)).trans hc.exit.spReg
      ra := (hreg _ (by constructor <;> decide)).trans hc.exit.ra
      mem := rfl
      code := by rw [hmem]; exact hCode
      stmt := by rw [hmem]; exact hStmt
      outer_addr := (hc.frames outer h.stage.env_valid).trans h.stage.outer_addr
      store := by rw [hmem]; exact hc.storeSurvives _ (fun _ _ => rfl)
      env_valid := h.stage.env_valid.afterExecS hExec
      store_survives := by
        intro m' hagree
        apply hc.storeSurvives m'
        intro k hk
        exact (hmem.symm ▸ hagree k hk)
      stack_ram := h.stage.stack_ram
      stack_win := h.stage.stack_win
      code_stack_disjoint := h.stage.code_stack_disjoint
      out := by
        change Machine.output cfg.σ = st'.out
        change String.join cfg.σ.sailOutput.toList = st'.out
        rw [hobs.2, sailOutput_sigmaPost_jump_x0]
        exact hc.exit.out
      saved_ra := by rw [hmem]; exact hra
      saved_s0 := ⟨v8, by rw [hmem]; exact hs0, hg8⟩
      saved_s1 := ⟨v9, by rw [hmem]; exact hs1, hg9⟩
      saved_s2 := ⟨v18, by rw [hmem]; exact hs2, hg18⟩
      saved_s3 := ⟨v19, by rw [hmem]; exact hs3, hg19⟩
      x20_defined := by
        obtain ⟨v, hv⟩ := h.stage.x20_defined
        exact ⟨v, (hreg _ (by constructor <;> decide)).trans
          (hc.exit.frame Register.x20 (by decide) |>.trans
            (h.frame Register.x20 (by decide) |>.trans hv))⟩
      x21_defined := by
        obtain ⟨v, hv⟩ := h.stage.x21_defined
        exact ⟨v, (hreg _ (by constructor <;> decide)).trans
          (hc.exit.frame Register.x21 (by decide) |>.trans
            (h.frame Register.x21 (by decide) |>.trans hv))⟩
      stack_budget := h.stage.stack_budget
      stmt_bodies := h.stage.stmt_bodies
      store_bodies := hStoreBodies
      ground := by rw [hmem]; exact hGround
      mem_frame := by
        intro a hstk hA
        rcases hc.exit.memFrame a (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
        · exact Or.inl hr
        · rcases h.stage.mem_frame a hstk hA with hr | heq0
          · exact Or.inl hr
          · exact Or.inr (by rw [hmem]; exact heq.trans heq0)
      frame := by
        intro R hR
        by_cases hspecial : R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
            R = Register.x19 ∨ R = Register.x2
        · exact Or.inl hspecial
        · right
          obtain ⟨habi, hPC, hNextPC, hMinstret, hMinstretIncrement,
            hMcycle, hMtime, hMip⟩ := hR
          have hcall : cfgCall.σ.regs.get? R = g R := by
            rcases h.stage.frame R ⟨habi, hPC, hNextPC, hMinstret,
                hMinstretIncrement, hMcycle, hMtime, hMip⟩ with hbad | heq
            · exact False.elim (hspecial hbad)
            · exact (h.frame R habi).trans heq
          exact (hreg R ⟨hMcycle, hMtime, hMip, hMinstret, hPC,
            hNextPC, hMinstretIncrement⟩).trans
            ((hc.exit.frame R ⟨habi, hPC, hNextPC, hMinstret,
              hMinstretIncrement, hMcycle, hMtime, hMip⟩).trans hcall)
      minstret := hgood.minstret
      parentSp := h.stage.parentSp
      ra_align := h.stage.ra_align
      mem_extends := by rw [hmem]; exact h.stage.mem_extends.trans hc.memExtends }

end Vsa.Sim.ScaffoldRows

#print axioms Vsa.Sim.ScaffoldRows.initSomeChildExitView_of_exitD
#print axioms Vsa.Sim.ScaffoldRows.initSomeReturnReady
