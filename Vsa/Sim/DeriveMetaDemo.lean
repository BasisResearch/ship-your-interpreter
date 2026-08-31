import Vsa.Sim.DeriveMeta
import Vsa.Sim.TermAssembly

/-!
# `DeriveMetaDemo` — `#verify_slots` run over the REAL row set

`#verify_slots` over the full current `TermCases` row set — a PASS re-derives, on
every build, the ~40 hand record-update probes in
`TermAssembly.termCases_of_residuals`.  A deliberate FAILURE mode is shown
(verbatim measured output) in the doc block at the bottom.

(`#derive_destructurer` on the real towers `ArmEntryK`/`TwoSubReturn` is demoed
in `Vsa/Sim/DeriveMetaTowers.lean`; `#derive_row` in `Vsa/Sim/DeriveRow.lean`.)
-/

open Vsa.Sim Vsa.Sim.Rows

namespace Vsa.Sim.DeriveMetaDemo

/-! ## `#verify_slots` over the real rows

Every `(field, row)` pair here is exactly a line of
`termCases_of_residuals` (`TermAssembly.lean`).  This command re-checks all of
them against the authoritative `TermCases` field types on every build — if a
row's conclusion drifts from its slot, THIS line breaks (pointing at the row),
rather than the 50-field record fill breaking opaquely. -/
#verify_slots Vsa.Sim.TermCaseBundle.TermCases
  [ (hInt, eval_int_row),
    (hStr, eval_str_row),
    (hBool, eval_bool_row),
    (hNull, eval_null_row),
    (hVar, eval_var_row),
    (hAssign, eval_assign_row),
    (hBinary, eval_binary_row),
    (hOrTrue, eval_orTrue_row),
    (hOrFalse, eval_orFalse_row),
    (hAndFalse, eval_andFalse_row),
    (hAndTrue, eval_andTrue_row),
    (hNeg, eval_neg_row),
    (hNot, eval_not_row),
    (hCall, eval_call_row),
    (hFn, eval_fn_row),
    (hArgsNil, eval_argsNil_row),
    (hArgsCons, eval_argsCons_row),
    (hCallPrint, eval_callPrint_row),
    (hCallPrintln, eval_callPrintln_row),
    (hCallAssertOk, eval_callAssertOk_row),
    (hSExpr, exec_expr_row),
    (hSVarInit, exec_varInit_row),
    (hSVarNull, exec_varNull_row),
    (hSBlock, exec_block_row),
    (hSIfTrue, exec_ifTrue_row),
    (hSIfFalse, exec_ifFalse_row),
    (hSIfNone, exec_ifNone_row),
    (hSWhileFalse, exec_whileFalse_row),
    (hSWhileBreak, exec_whileBreak_row),
    (hSWhileRet, exec_whileRet_row),
    (hSWhileLoop, exec_whileLoop_row),
    (hSForStart, exec_forStart_row),
    (hSRet, exec_ret_row),
    (hSRetNull, exec_retNull_row),
    (hSBrk, exec_brk_row),
    (hSCont, exec_cont_row) ] report

/-! ## The FAILURE mode (demonstrated, kept as documentation)

Routing a field to the WRONG row makes `#verify_slots` an ELABORATION ERROR that
names both types.  E.g. `#verify_slots … [ (hInt, eval_str_row) ]` produces
(verbatim, measured):

```
#verify_slots Vsa.Sim.TermCaseBundle.TermCases: 1 slot mismatch(es)
  ✗ hInt ⟵ eval_str_row
    field expects:
      ∀ (st : Vsa.While.St) (d : Nat) (env : Vsa.While.Addr) (n : Int),
        TermSimAssembly.mEvalE st d env (Vsa.While.Expr.int n) st (Vsa.While.Value.int n) ⋯
    row (full) type:
      (∀ (st : Vsa.While.St) (s : String), StrLeafResid st s) →
        ∀ (st : Vsa.While.St) (d : Nat) (env : Vsa.While.Addr) (s : String),
          TermSimAssembly.mEvalE st d env (Vsa.While.Expr.str s) st (Vsa.While.Value.str s) ⋯
```

i.e. the `.int`-node field cannot be filled by the `.str` row — the check catches
exactly the class of bug the positional `termCases_of_residuals` fill would
surface only as an opaque record-elaboration failure. -/

end Vsa.Sim.DeriveMetaDemo
