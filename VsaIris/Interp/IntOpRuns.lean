import VsaIris.Interp.BinErr
import VsaIris.Interp.ProofArith
import VsaIris.Interp.SymInterp
import VsaIris.Vsa.Dbm

/-!
Integer operators `+ - * / %` as one descriptor `IntOpDesc`: each operator's reflected path from
the dispatch to its `value_int` call (`IntOpRun`, including the `mul`/`divdi3`/`moddi3` helper
runs), and its epilogue.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- Post of an integer operator's path at its `value_int` call. -/
structure IntOpPost (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (s sret : BitVec 64) (res : Int) :
    Prop where
  keep : HiKeep R R'
  a0 : R' 10 = sret
  a1 : (R' 11).toInt = res
  saved : ∀ {ret v8 v9 v18 v19}, EvalSaved Mt s ret v8 v9 v18 v19 → EvalSaved Mt' s ret v8 v9 v18 v19

/-- The integer path of operator `op` (defined when `pre a b`), from the dispatch to the
`value_int` call at `vi`, computing `sem a b`. -/
def IntOpRun (op : BinOp) (pre : Int → Int → Prop) (sem : Int → Int → Int) (vi : BitVec 64) :
    Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {a b : Int} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok op) →
    BinMid s sret inp rv R Mt ret aX (.int a) (.int b) w0 w1 w2 u0 u1 u2 →
    w1.toInt = a → u1.toInt = b → pre a b →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64 vi R Mt
      (fun R' Mt' => IntOpPost R R' Mt Mt' s sret (sem a b))

/-- An integer operator: semantics, definedness, `value_int` site, reflected path, epilogue. -/
structure IntOpDesc where
  op : BinOp
  sem : Int → Int → Int
  pre : Int → Int → Prop
  vi : JalAt 0x8000280c#64
  run : IntOpRun op pre sem (BitVec.ofNat 64 vi.i)
  epi : EpiRun (BitVec.ofNat 64 (vi.i + 4))

set_option hygiene false in
macro "int_setup" : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt a b w0 w1 w2 u0 u1 u2 n g hn mid hw1 hu1 hpre Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have hKL : ldv .ld Mt (s.toNat - 1088) = 2#64 := mid.kl
  have hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64 := mid.kr
  have hU : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat = u1 := mid.q1
  clear g hn mid
  simp only [binOpTok] at hop))

set_option hygiene false in
macro "int_pre " pc:num : tactic => `(tactic| (
  int_setup
  sym_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc))

set_option hygiene false in
/-- `int_pre` for a divisor known to be non-zero. -/
macro "int_pre_nz " pc:num : tactic => `(tactic| (
  int_setup
  have hy : u1 ≠ 0#64 := fun h => hpre (by rw [← hu1, h]; rfl)
  have hb : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat ≠ 0#64 := by rw [hU]; exact hy
  sym_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc))

set_option hygiene false in
macro "int_post " wrap:ident : tactic => `(tactic| (
  have hoff := evalSP_off (s := s) hsf (by omega_dc)
  refine hk _ _ ⟨⟨by ix_reg, fun x hx => ?_⟩, by ix_reg, by ix_reg; rw [hU, $wrap:ident, hw1, hu1],
    fun h => ?_⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · ix_saved h using hoff))

set_option hygiene false in
/-- Close a register equation after a reflected segment, using the dispatch facts. -/
macro "reg_close" : tactic => `(tactic| (
  ix_reg <;> first | rfl | exact hU | exact h9 | exact h19 | exact h8))

set_option hygiene false in
/-- Rewrite a register through a helper's frame `hkeep` (`MulKeep` or `SDivKeep`). -/
macro "helper_keep" : tactic => `(tactic| (
  first
    | rw [hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    | rw [hkeep _ (by decide) (by decide) (by decide) (by decide)]
  reg_close))

set_option hygiene false in
/-- Close an `IntOpPost` after a helper call whose register frame is `hkeep`. -/
macro "int_helper_post " res:term : tactic => `(tactic| (
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨?_, fun x hx => ?_⟩, by reg_close, by ix_reg; exact $res, fun h => ?_⟩
  · ix_reg; helper_keep
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (ix_reg; helper_keep)
  · ix_saved h using hoff))

set_option hygiene false in
macro "zero_pre " pc1:num : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt a b w0 w1 w2 u0 u1 u2 n g hn mid hu Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have hKL : ldv .ld Mt (s.toNat - 1088) = 2#64 := mid.kl
  have hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64 := mid.kr
  have hZ : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat = 0#64 := mid.q1.trans hu
  clear g hn mid
  simp only [binOpTok] at hop
  sym_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hZ, hsf] at $pc1))

set_option hygiene false in
macro "zero_post " pc2:num : tactic => `(tactic| (
  sym_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hZ, hsf] at $pc2
  exact hk _ _ ⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg⟩))

open Lean in
def tree3' (a b c d : Ident) : MacroM (TSyntax `command) := do
  let l ← `(ixtree| $d:ident)
  let n ← `(ixtree| $c:ident [$l:ixtree])
  `(#ix_tree $a:ident := $b:ident [$n:ixtree])

set_option hygiene false in
open Lean in
/-- `#int_errs name op kn opn s1 sL sR` proves the two type-error paths of integer operator `op`
(value_kind_name call at `kn`, operator name `opn`, via `s1` and `sL`/`sR`) and its staging
segment to `rt_err`. -/
macro "#int_errs " nmI:ident op:ident kn:num opn:num s1:num sL:num sR:num rt:num : command => do
  let nm (s : String) : Ident := mkIdent (Name.mkStr (Name.mkStr .anonymous "IntOp") s!"{nmI.getId}{s}")
  let knp := Syntax.mkNumLit (toString (kn.getNat + 4))
  let cs : Array (TSyntax `command) := #[
    ← `(#ix_seg $(nm "ErrL1"):ident : BinErrRun $op:ident (BitVec.ofNat 64 $kn:num)
          (opnConst (BitVec.ofNat 64 $opn:num)) (BitVec.ofNat 64 $opn:num) true errIntL by
          bin_err_pre errIntL_facts $s1:num),
    ← `(#ix_piece $(nm "ErrL2"):ident from $(nm "ErrL1"):ident by bin_err_mid $sL:num),
    ← `(#ix_piece $(nm "ErrL3"):ident from $(nm "ErrL2"):ident by bin_err_post $kn:num),
    ← tree3' (nm "ErrL") (nm "ErrL1") (nm "ErrL2") (nm "ErrL3"),
    ← `(#ix_seg $(nm "ErrR1"):ident : BinErrRun $op:ident (BitVec.ofNat 64 $kn:num)
          (opnConst (BitVec.ofNat 64 $opn:num)) (BitVec.ofNat 64 $opn:num) false errIntR by
          bin_err_pre errIntR_facts $s1:num),
    ← `(#ix_piece $(nm "ErrR2"):ident from $(nm "ErrR1"):ident by bin_err_mid $sR:num),
    ← `(#ix_piece $(nm "ErrR3"):ident from $(nm "ErrR2"):ident by bin_err_post $kn:num),
    ← tree3' (nm "ErrR") (nm "ErrR1") (nm "ErrR2") (nm "ErrR3"),
    ← `(theorem $(nm "Rt"):ident : RtRun (BitVec.ofNat 64 $knp:num) (BitVec.ofNat 64 $rt:num)
          (opnConst (BitVec.ofNat 64 $opn:num)) := by rt_run)]
  return ⟨mkNullNode cs⟩

end VsaIris.Interp
