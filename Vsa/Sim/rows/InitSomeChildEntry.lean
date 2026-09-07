import Vsa.Sim.rows.Field_hInitSome
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.WhileBodyDispatch

/-! # Present-initializer child entry

Marshal the output-preserving `jal exec_stmt` landing into the exact recursive
`ExecEntry` for the initializer statement.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

/-- The selected body landing is the initializer's recursive `exec_stmt` entry. -/
theorem initSomeChildEntry_of_landing
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d outer : Nat} {s : Stmt}
    {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem}
    {cfg : Config}
    (h : InitSomeBodyLanding g N A SL φf φc st d outer s cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg) :
    ExecEntry (fun R => cfg.σ.regs.get? R) N A SL φf φc st d outer s
      (sp - 176#64) (0x80004258#64) aInterp h.p aOuter aRet ment cfg := by
  have hsp176 : 176 ≤ sp.toNat := by
    have hroom := h.stage.stack_budget.1
    omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have hspRam := sp.isLt
    omega
  have hbudget : StackOK SL (sp - 176#64)
      (s.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) := by
    obtain ⟨hlo, hhi, halign⟩ := h.stage.stack_budget
    simp only [StackOK, hspsub]
    simp only [Stmt.stackNeed, Stmt.stackNeedOpt, execFrame] at hlo
    omega
  have hground : ExecGround ment SL A (sp - 176#64) aRet h.p.toNat s :=
    h.stage.ground.child_sameRet
      (fun _ _ hin => hin.2.1.2 h.p.toNat h.stage.init_ptr)
      (by rw [hspsub]; omega)
  have hregs : GHolds cfg.σ
      [(10, aInterp), (13, aRet), (12, aOuter), (2, sp - 176#64),
       (18, aRet), (9, aInterp), (11, h.p)] := by
    have hregs := h.regs
    change GHolds cfg.σ
      [(10, aInterp + 0#64), (13, aRet + 0#64), (12, aOuter + 0#64),
       (2, sp - 176#64), (18, aRet), (9, aInterp), (11, h.p)] at hregs
    simpa only [BitVec.add_zero] using hregs
  have h8 : cfg.σ.regs.get? Register.x8 = some aStmt :=
    (h.frame Register.x8 (by decide)).trans h.stage.s0
  have h9 : cfg.σ.regs.get? Register.x9 = some aInterp :=
    (h.frame Register.x9 (by decide)).trans h.stage.s1
  have h18 : cfg.σ.regs.get? Register.x18 = some aRet :=
    (h.frame Register.x18 (by decide)).trans h.stage.s2
  have h19 : cfg.σ.regs.get? Register.x19 = some aOuter :=
    (h.frame Register.x19 (by decide)).trans h.stage.s3
  have h20 : RegDefined cfg Register.x20 := by
    obtain ⟨v, hv⟩ := h.stage.x20_defined
    exact ⟨v, (h.frame Register.x20 (by decide)).trans hv⟩
  have h21 : RegDefined cfg Register.x21 := by
    obtain ⟨v, hv⟩ := h.stage.x21_defined
    exact ⟨v, (h.frame Register.x21 (by decide)).trans hv⟩
  obtain ⟨lo, hi, region⟩ := hground.ast.region
  have hnode := stmtIn_node region.nodes
  refine
    { good := h.good
      tick := h.tick
      pc := h.pc
      a0 := gholds_lookup (n := 10) _ hregs (by rfl)
      a1 := gholds_lookup (n := 11) _ hregs (by rfl)
      a2 := gholds_lookup (n := 12) _ hregs (by rfl)
      envPtr := by rw [h.stage.outer_addr]; simp
      a3 := gholds_lookup (n := 13) _ hregs (by rfl)
      ra := h.ra
      ra_align := by decide
      spReg := gholds_lookup (n := 2) _ hregs (by rfl)
      stackOK := Vsa.Alloc.StackOK.mono (exec_basic_headroom s _) hbudget
      stackBudget := hbudget
      stmt_bodies := by
        have hb := h.stage.stmt_bodies
        simp only [Stmt.bodiesBound, Stmt.bodiesBoundOpt, Bool.and_eq_true] at hb
        exact hb.1.1.1
      store_bodies := h.stage.store_bodies
      minstret := h.minstret
      mem := h.mem
      code := by rw [h.mem]; exact h.stage.code
      stmt := by rw [h.mem]; exact h.stage.child
      store := by rw [h.mem]; exact h.stage.store
      env_valid := h.stage.env_valid
      store_survives := by
        intro m' hagree
        apply h.stage.store_survives m'
        simpa only [h.mem] using hagree
      out := h.out
      frame := fun _ _ => rfl
      code_stack_disjoint := by
        rcases h.stage.code_stack_disjoint with hd | hd
        · left; rw [hspsub]; omega
        · exact Or.inr hd
      stack_ram := h.stage.stack_ram
      stack_win := h.stage.stack_win
      stmt_stack_disjoint := by
        have := hnode.lo_le
        have := hnode.hi_ge
        have := hbudget.2.1
        rcases region.stack_disjoint with hd | hd
        · left; omega
        · right; omega
      stmt_ram := by
        have := region.lo_ram
        have := region.hi_ram
        have := hnode.lo_le
        have := hnode.hi_ge
        constructor <;> omega
      stmt_win := by
        have := region.win
        have := hnode.lo_le
        omega
      spill_defined := ⟨⟨_, h8⟩, ⟨_, h9⟩, ⟨_, h18⟩, ⟨_, h19⟩⟩
      envset_defined := ⟨h20, h21⟩
      ground := by rw [h.mem]; exact hground }

end Vsa.Sim.ScaffoldRows

#print axioms Vsa.Sim.ScaffoldRows.initSomeChildEntry_of_landing
