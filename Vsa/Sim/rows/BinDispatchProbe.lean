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
    (hIAdd : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .add AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hISub : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .sub SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIMul : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .mul MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIDiv : ∀ g N A SL φf φc st st' st'' el er a b, ¬(a = -2^63 ∧ b = -1) →
        ∀ sp r sret aExpr m0,
        BinIntCellResid .div DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIMod : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .mod ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hILt : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .lt LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hILe : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .le LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIGt : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .gt GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIGe : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .ge GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hEq : ∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
        BinEqCellResid .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
          g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0)
    (hNe : ∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
        BinEqCellResid .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
          g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0)
    (hStrAddL : ∀ st d env el er st'' (sl : String) (rv : Value),
        EvalIH st d env (.binary .add el er) st'' (.str ((Value.str sl).display st''.store ++ rv.display st''.store)))
    (hStrAddR : ∀ st d env el er st'' (lv : Value) (sr : String),
        EvalIH st d env (.binary .add el er) st'' (.str (lv.display st''.store ++ (Value.str sr).display st''.store)))
    (hStrLt : ∀ st d env el er st'' (sl sr : String),
        EvalIH st d env (.binary .lt el er) st'' (.bool (sl < sr)))
    (hStrLe : ∀ st d env el er st'' (sl sr : String),
        EvalIH st d env (.binary .le el er) st'' (.bool (sl < sr || sl == sr)))
    (hStrGt : ∀ st d env el er st'' (sl sr : String),
        EvalIH st d env (.binary .gt el er) st'' (.bool (sr < sl)))
    (hStrGe : ∀ st d env el er st'' (sl sr : String),
        EvalIH st d env (.binary .ge el er) st'' (.bool (sr < sl || sl == sr)))
    (hDivOv : ∀ st d env el er st'',
        EvalIH st d env (.binary .div el er) st'' (.int (wrap64 ((-2^63 : Int).tdiv (-1))))) :
    (∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : Vsa.While.St) (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv) (a_2 : binOpSem st''.store op lv rv = some v), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 → mEvalE st d env (Expr.binary op l r) st'' v (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2)) :=
  eval_binary_row hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe
    hStrAddL hStrAddR hStrLt hStrLe hStrGt hStrGe hDivOv
