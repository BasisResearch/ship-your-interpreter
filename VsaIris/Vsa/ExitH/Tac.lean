import VsaIris.Vsa.ExitH.Loads
import VsaIris.Vsa.SymCompactTac

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.VsaHeap

/-- The exit run's stack window: the 256 bytes below the entry stack pointer. -/
theorem ExitSp.win {s : BitVec 64} (hs : ExitSp s) : StackWin (exitS s) s 256 0 :=
  ⟨⟨⟨fun k hk => .inr (.inr (by have := hs.lo; omega))⟩, by have := hs.lo; omega,
    by have := hs.hi; omega⟩, by have := hs.align; omega, hs.place⟩

/-- Facts every piece of the exit run normalises with: the entry registers, the FILE fields of
`CloseMt`, the tested bits of the console flags word (`ConFlags`), and the literal folders. -/
def xhFacts : Array Lean.Name := #[`h2, `h8, `h11, `hC.atexit, `hC.handler, `hC.glueNext, `hC.glueCount,
  `hC.glueFiles, `hC.sinit, `hC.in_flagsU, `hC.in_flags, `hC.in_fd, `hC.in_r, `hC.in_ur, `hC.in_cookie,
  `hC.in_close, `hC.in_ub, `hC.in_lb, `hC.in_lock, `hC.in_mode, `hC.out_flagsU, `hC.out_flags, `hC.out_fd,
  `hC.out_base, `hC.out_p, `hC.out_cookie, `hC.out_close, `hC.out_ub, `hC.out_lb, `hC.out_lock, `hC.out_mode,
  `hF.ne0, `hF.gt1, `hF.b200, `hF.b8, `hF.b3, `hF.b80,
  ``ne_eq, ``not_false_eq_true, ``BitVec.add_assoc, ``BitVec.reduceAnd, ``BitVec.reduceOr, ``BitVec.reduceSub, ``BitVec.reduceMul,
  ``BitVec.reduceShiftLeft, ``BitVec.reduceHShiftLeft, ``Nat.reducePow, ``Nat.reduceMod, ``BitVec.reduceOfNat]

set_option hygiene false in
open Lean in
/-- Run `n` instructions of the exit path with `xhFacts` plus the listed facts, then drop the
branch hypotheses of the explored prefix so the leftover states only the reached machine state.
Fails unless every branch was decided. -/
macro "xh_run " n:num " using " "[" fs:term,* "]" : tactic => do
  let all : Array Term := xhFacts.map (fun n => (mkIdent n : Term)) ++ fs.getElems
  `(tactic| (nx_run [$n] hlive using [$all,*] at 2147501960; all_goals nx_clean; nx_one))

set_option hygiene false in
/-- First piece: name the stack window and its geometry, then run. -/
macro "xh_start " n:num " using " "[" fs:term,* "]" : tactic => `(tactic| (
    have hs1 := hs.lo; have hs2 := hs.hi; have hs3 := hs.align; have hs4 := hs.place
    have hw := hs.win
    xh_run $n using [$fs,*]))

set_option hygiene false in
/-- Later pieces: forget the dead stack below `sp` (one merged layer), compact the register file, then run. -/
macro "xh_step " n:num " using " "[" fs:term,* "]" : tactic => `(tactic| (intros; nx_clean; nx_forget_sp (s.toNat - 256); nx_compactR; xh_run $n using [$fs,*]))

section Branch

open Lean Elab Command Term Meta

/-- `#ix_branch name (h : H) … from prev by tac`: a piece that starts at `prev`'s leftover state
under additional hypotheses. Two runs that agree up to `prev` share the pieces up to `prev`
and each continue with its own `#ix_branch`. -/
syntax (name := ixBranch) "#ix_branch " ident bracketedBinder+ " from " ident " by " tacticSeq : command

@[command_elab ixBranch] def elabIxBranch : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let prev ← liftCoreM <| realizeGlobalConstNoOverload stx[4]
  liftTermElabM do
    let info ← getConstInfo prev
    forallTelescope info.type fun xs _ => do
      let nv ← pieceVars xs
      let some hk := xs[nv]? | throwError "#ix_branch: {prev} has no leftover"
      forallTelescope (← inferType hk) fun ys T => do
        Term.elabBinders stx[2].getArgs fun zs => do
          Term.synthesizeSyntheticMVarsNoPostponing
          ixAddPiece declName (xs.extract 0 nv ++ ys ++ zs) T stx[6] true (xs.extract nv xs.size)

end Branch

set_option hygiene false in

macro "xh_end" : tactic => `(tactic| (intros; nx_clean; nx_compactR; exact hk _ _ ⟨by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero, h2, h8],
    by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2, h8],
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]⟩))

end VsaIris.Sym
