import Vsa.MemRepr
import Vsa.Sim.OutputAliasProgram

/-! The alias AST is derived from finite memory reads. No representation premise. -/

namespace Vsa.Sim.OutputAliasLoaded

open Vsa.MemRepr
open Vsa.While
open Vsa.While.LoadedOutputAlias

/-- Exact reads of the two-statement alias AST and its three string payloads. -/
structure ProgramReads (m : Mem) : Prop where
  array_first : read64 m 0x82000000 = some 0x82000020
  array_second : read64 m 0x82000008 = some 0x82000040
  print_tag : read32 m 0x82000020 = some 0
  print_expr : read64 m 0x82000028 = some 0x82000080
  if_tag : read32 m 0x82000040 = some 3
  if_cond : read64 m 0x82000048 = some 0x820000c0
  if_then : read64 m 0x82000050 = some 0x82000020
  if_else : read64 m 0x82000058 = some 0
  call_tag : read32 m 0x82000080 = some 9
  call_callee : read64 m 0x82000088 = some 0x820000a0
  call_args : read64 m 0x82000090 = some 0
  call_argc : read32 m 0x82000098 = some 0
  var_tag : read32 m 0x820000a0 = some 4
  var_name : read64 m 0x820000a8 = some 0x81000210
  equal_tag : read32 m 0x820000c0 = some 6
  equal_op : read32 m 0x820000c8 = some 19
  equal_left : read64 m 0x820000d0 = some 0x82000100
  equal_right : read64 m 0x820000d8 = some 0x82000120
  empty_tag : read32 m 0x82000100 = some 1
  empty_ptr : read64 m 0x82000108 = some 0x8001bb97
  newline_tag : read32 m 0x82000120 = some 1
  newline_ptr : read64 m 0x82000128 = some 0x82000140
  name_p : m[0x81000210]? = some 112#8
  name_r : m[0x81000211]? = some 114#8
  name_i : m[0x81000212]? = some 105#8
  name_n₁ : m[0x81000213]? = some 110#8
  name_t : m[0x81000214]? = some 116#8
  name_l : m[0x81000215]? = some 108#8
  name_n₂ : m[0x81000216]? = some 110#8
  name_zero : m[0x81000217]? = some 0
  empty_zero : m[0x8001bb97]? = some 0
  newline_byte : m[0x82000140]? = some 10#8
  newline_zero : m[0x82000141]? = some 0

namespace ProgramReads

variable {m : Mem} (h : ProgramReads m)
include h

theorem printlnCString : CString m 0x81000210 "println" := by
  refine ⟨['p', 'r', 'i', 'n', 't', 'l', 'n'], ?_, rfl⟩
  exact CStr.cons h.name_p (by decide) (by decide)
    (CStr.cons h.name_r (by decide) (by decide)
      (CStr.cons h.name_i (by decide) (by decide)
        (CStr.cons h.name_n₁ (by decide) (by decide)
          (CStr.cons h.name_t (by decide) (by decide)
            (CStr.cons h.name_l (by decide) (by decide)
              (CStr.cons h.name_n₂ (by decide) (by decide)
                (CStr.nil h.name_zero)))))))

theorem emptyCString : CString m 0x8001bb97 "" :=
  ⟨[], CStr.nil h.empty_zero, rfl⟩

theorem newlineCString : CString m 0x82000140 "\n" := by
  refine ⟨['\n'], ?_, rfl⟩
  exact CStr.cons h.newline_byte (by decide) (by decide) (CStr.nil h.newline_zero)

theorem printRepr : StmtRepr m 0x82000020 printLine := by
  apply StmtRepr.expr h.print_tag h.print_expr
  exact ExprRepr.call h.call_tag h.call_callee
    (ExprRepr.var h.var_tag h.var_name h.printlnCString)
    h.call_args h.call_argc (by decide) ExprArrayRepr.nil

theorem conditionRepr : ExprRepr m 0x820000c0 condition := by
  exact ExprRepr.binary h.equal_tag h.equal_op h.equal_left
    (ExprRepr.str h.empty_tag h.empty_ptr h.emptyCString)
    h.equal_right (ExprRepr.str h.newline_tag h.newline_ptr h.newlineCString)

theorem ifRepr : StmtRepr m 0x82000040 (.ifStmt condition printLine none) :=
  StmtRepr.ifNoElse h.if_tag h.if_cond h.conditionRepr
    h.if_then h.printRepr h.if_else

theorem stmtArrayRepr : StmtArrayRepr m 0x82000000 2 program :=
  StmtArrayRepr.cons h.array_first h.printRepr
    (StmtArrayRepr.cons h.array_second h.ifRepr StmtArrayRepr.nil)

theorem programRepr : ProgramRepr m 0x82000000 2 program :=
  ⟨h.stmtArrayRepr, rfl⟩

end ProgramReads

#print axioms ProgramReads.printlnCString
#print axioms ProgramReads.programRepr

end Vsa.Sim.OutputAliasLoaded
