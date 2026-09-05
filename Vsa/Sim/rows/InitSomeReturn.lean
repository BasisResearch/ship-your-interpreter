import Vsa.Sim.rows.Field_hInitSome
import Vsa.Sim.ExecWhileIndexed

/-!
# Present-initializer return seam

The child `exec_stmt` returns to `0x80004258`.  This file discharges the real
`j 0x8000426c` instruction which routes any initializer result to the
for-loop head.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

/-- A child execution cannot modify the enclosing `exec_stmt` spill window.
The lower child stack ends at `sp - 176`; the arena and return slot are both
disjoint from the enclosing stack scribble by `ExecGround`. -/
theorem initSomeReturn_spill_agree
    {g : (R : Register) → Option (RegisterType R)}
    {gchild : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d outer : Nat} {s : Stmt} {status : Status}
    {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Vsa.MemRepr.Mem}
    {cfg0 cfgRet : Config} {liveRA p : BitVec 64}
    (hparent : InitSomeStage g N A SL φf φc st d outer s cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg0 liveRA p)
    (hchild : ExecExit gchild N A SL φf φc
      st.store.frames.size st.store.closures.size st' status
      (sp - 176#64) (0x80004258#64) aRet ment cfgRet) :
    AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) ment cfgRet.σ.mem := by
  have hroom := hparent.stack_budget.1
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have hspRam := sp.isLt
    omega
  intro k hk
  have hf := hchild.memFrame k
    (by rw [hspsub]; intro ⟨_, hb⟩; omega)
    (by rcases hparent.ground.arena_stack with h | h <;> omega)
  rcases hf with hret | heq
  · exact absurd hret (by
      rcases hparent.ground.aret.scribble_disjoint with h | h <;> omega)
  · exact heq.symm

/-- The five enclosing callee-save slots retain their exact `read64` values. -/
theorem initSomeReturn_saved_reads
    {sp r v8 v9 v18 v19 : BitVec 64} {ment mret : Vsa.MemRepr.Mem}
    (hsp40 : 40 ≤ sp.toNat)
    (hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) ment mret)
    (hra : read64 ment (sp.toNat - 8) = some r.toNat)
    (hs0 : read64 ment (sp.toNat - 16) = some v8.toNat)
    (hs1 : read64 ment (sp.toNat - 24) = some v9.toNat)
    (hs2 : read64 ment (sp.toNat - 32) = some v18.toNat)
    (hs3 : read64 ment (sp.toNat - 40) = some v19.toNat) :
    read64 mret (sp.toNat - 8) = some r.toNat ∧
    read64 mret (sp.toNat - 16) = some v8.toNat ∧
    read64 mret (sp.toNat - 24) = some v9.toNat ∧
    read64 mret (sp.toNat - 32) = some v18.toNat ∧
    read64 mret (sp.toNat - 40) = some v19.toNat := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [← read64_agreeP hag (fun j hj => by omega)]
  · exact hra
  · exact hs0
  · exact hs1
  · exact hs2
  · exact hs3

/-- The concrete `j 0x8000426c` instruction at the initializer return link. -/
theorem initSomeReturn_j
    (c : Config) (vminstret : BitVec 64)
    (hG : GoodState c.σ)
    (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some (0x80004258#64))
    (hmi : c.σ.regs.get? Register.minstret = some vminstret)
    (hcode : Exec_stmtLoaded c.σ.mem) :
    ∃ c' : Config,
      Step c c' ∧ c'.tick < 2 ∧ GoodState c'.σ ∧
      c'.σ.mem = c.σ.mem ∧
      ReadsLikePost c'.σ
        (sigmaPost_jump_x0 c.σ 0x80004258#64 vminstret 0x8000426c#64) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := exec_stmt_at_80004258 hcode
  obtain ⟨σ', i', hs, hi', hG', hmem', hobs⟩ :=
    stepObs_j c.σ c.tick c.steps (0x80004258#64) vminstret
      (0x0140006f#32) (0x000014#21)
      (0x6f#8) (0x00#8) (0x40#8) (0x01#8)
      hG hpc hmi hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0140006f (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide) htick
  have htgt :
      (0x80004258#64 : BitVec 64) + sign_extend (m := 64) (0x000014#21) =
        (0x8000426c#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    decide
  rw [htgt] at hobs
  exact ⟨⟨σ', i', c.steps + 1⟩, hs, hi', hG', hmem', hobs⟩

end Vsa.Sim.ScaffoldRows

#print axioms Vsa.Sim.ScaffoldRows.initSomeReturn_j
#print axioms Vsa.Sim.ScaffoldRows.initSomeReturn_spill_agree
#print axioms Vsa.Sim.ScaffoldRows.initSomeReturn_saved_reads
