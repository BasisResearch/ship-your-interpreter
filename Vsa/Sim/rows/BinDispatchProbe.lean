import Vsa.Sim.rows.BinDispatchRow

/-!
# `BinDispatchProbe` — slot-verify that `eval_binary_row` fills `hBinary`

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open Vsa.Sim Vsa.Sim.TermSimAssembly Vsa.While
open Vsa.Machine (Config)


/-- **Slot-verify** (decisive): `eval_binary_row` applied to residual-slot
hypotheses of its declared types produces a term ASCRIBED to the verbatim
`hBinary` premise shape.  The ascription forces Lean to check that
`eval_binary_row`'s conclusion is DEFINITIONALLY the recursor's `hBinary` slot. -/
theorem binary_row_fills_hBinary
    (hIAdd : BinIntCell .add AddResid (fun _ _ => True))
    (hISub : BinIntCell .sub SubResid (fun _ _ => True))
    (hIMul : BinIntCell .mul MulResid (fun _ _ => True))
    (hIDiv : BinIntCell .div DivResid (fun a b => ¬(a = -2^63 ∧ b = -1)))
    (hIMod : BinIntCell .mod ModResid (fun _ _ => True))
    (hILt : BinIntCell .lt LtResid (fun _ _ => True))
    (hILe : BinIntCell .le LeResid (fun _ _ => True))
    (hIGt : BinIntCell .gt GtResid (fun _ _ => True))
    (hIGe : BinIntCell .ge GeResid (fun _ _ => True))
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hStrAddL : BinStrAddLCell)
    (hStrAddR : BinStrAddRCell)
    (hStrLt : BinStrCmpCell .lt (fun sl sr => sl < sr))
    (hStrLe : BinStrCmpCell .le (fun sl sr => sl < sr || sl == sr))
    (hStrGt : BinStrCmpCell .gt (fun sl sr => sr < sl))
    (hStrGe : BinStrCmpCell .ge (fun sl sr => sr < sl || sl == sr))
    (hDivOv : BinDivOverflowCell) :
    (∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : Vsa.While.St) (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv) (a_2 : binOpSem st''.store op lv rv = some v), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 → mEvalE st d env (Expr.binary op l r) st'' v (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2)) :=
  eval_binary_row hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe
    hStrAddL hStrAddR hStrLt hStrLe hStrGt hStrGe hDivOv
