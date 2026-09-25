import VsaIris.Interp.Case.AssignP
import VsaIris.Interp.Case.BinaryDivP
import VsaIris.Interp.Case.BinaryAddP
import VsaIris.Interp.Case.ExecBlockP
import VsaIris.Interp.Case.CallArmP
import VsaIris.Interp.Case.LeafBoolP
import VsaIris.Interp.Case.ExecVarNullP
import VsaIris.Interp.Case.BinaryGtP
import VsaIris.Interp.Case.BinaryNeP
import VsaIris.Interp.Case.FnLitP
import VsaIris.Interp.Case.ExecExprP
import VsaIris.Interp.Case.BinaryLeP
import VsaIris.Interp.Case.UnaryNegTypeP
import VsaIris.Interp.Case.ExecVarInitP
import VsaIris.Interp.Case.VarP
import VsaIris.Interp.Case.ExecWhileP
import VsaIris.Interp.Case.BinarySubP
import VsaIris.Interp.Case.LeafStrP
import VsaIris.Interp.Case.ExecForP
import VsaIris.Interp.Case.BinaryEqP
import VsaIris.Interp.Case.UnaryNotP
import VsaIris.Interp.Case.BinaryMulP
import VsaIris.Interp.Case.LogicalAndFalseP
import VsaIris.Interp.Case.ExecRetP
import VsaIris.Interp.Case.LogicalOrTrueP
import VsaIris.Interp.Case.ExecBrkP
import VsaIris.Interp.Case.ExecContP
import VsaIris.Interp.Case.BinaryModP
import VsaIris.Interp.Case.ExecIfP
import VsaIris.Interp.Case.BinaryLtP
import VsaIris.Interp.Case.ExecRetNullP
import VsaIris.Interp.Case.LeafNullP
import VsaIris.Interp.Case.LeafIntP
import VsaIris.Interp.Case.BinaryGeP
import VsaIris.Interp.CallCloP
import VsaIris.Interp.LoopWhile
import VsaIris.Interp.LoopFor
import VsaIris.Interp.LoopArgs
import VsaIris.Interp.SeqLoopInterp
import VsaIris.Interp.ExecDisp
import VsaIris.Interp.TermSim

/-!
# `stuck_sim`'s recursion: Löb over the partial specs (lane A)

INTERP_DESIGN.md §4.2, §5.3. One Löb induction proves `eval_expr`'s partial
spec (`evalSpecP_body`) and `exec_stmt`'s dispatch-point partial spec
(`execDispP_body`, E5) for every input at once. Each recursive `jal` inside a
case pays the later (`evalSpecsP`/`execDispsP` are the Löb hypothesis under
`□ ▷`). Each syntactic form goes to its generated `Case/*P` lemma; the abort
core is `evalCore` (the whole stack segment's landing core, `LeafErr.lean`).
The persistent `errCtx inp` (the binary image and the `jmp_buf` `interp_run`'s
`setjmp` wrote) is the context. Premises: `StuckSupply`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.Sym
open Vsa.While Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

local notation "Mv" live => vsaModel live
local notation "Lp" => vsaLayoutP
local notation "Rp" => vsaRoomB

/-- **The callee specs and named premises of the partial cases.** -/
structure StuckSupply (live : Nat → Prop) (N : NativeAddrs) (inp : Nat) : Prop where
  hlive : ∀ p ∈ interpText, live p.1
  errEnv : ErrEnv (GF := GF) N Lp Rp inp live (evalCore N Lp Rp inp)
  vint : ⊢ ∀ p n, valueIntSpec (GF := GF) (Mv live) N (wpW (Mv live)) p n
  vbool : ⊢ ∀ p b, valueBoolSpec (GF := GF) (Mv live) N (wpW (Mv live)) p b
  vnull : ⊢ ∀ p, valueNullSpec (GF := GF) (Mv live) N (wpW (Mv live)) p
  vstr : ⊢ ∀ p q x, valueStrSpec (GF := GF) (Mv live) N (wpW (Mv live)) p q x
  vtruthy : ⊢ ∀ p v, valueTruthySpec (GF := GF) (Mv live) N (wpW (Mv live)) p v
  vequal : ⊢ ∀ pa pb s a b st B, valueEqualSpec (GF := GF) (Mv live) N (wpW (Mv live)) pa pb s a b st B
  vkind : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (Mv live) (wpW (Mv live)) p Mt v
  strcmpV : ⊢ strcmpSpecV (GF := GF) (Mv live) (wpW (Mv live))
  strcmpOrd : ⊢ strcmpOrdSpec (GF := GF) (Mv live) (wpW (Mv live))
  envGet : ⊢ envGetSpec (GF := GF) (wpW (Mv live)) N
  envSet : ⊢ envSetSpec (GF := GF) (wpW (Mv live)) N
  envNew : ⊢ envNewSpec (GF := GF) (wpW (Mv live)) N
  envDefine : ⊢ envDefineSpec (GF := GF) (wpW (Mv live)) N
  nativeInj : NativeInj N
  nativeEntries : NativeEntries N
  cloSupply : CloSupply (GF := GF) N
  inpAl : inp % 8 = 0
  nPrint : ∀ (sret args s : BitVec 64) (vs : List Value) (st : Store) (o : String),
    ⊢ nativePrintSpec (GF := GF) (Mv live) N (wpW (Mv live)) sret args s vs st o
  nPrintln : ∀ (sret args s : BitVec 64) (vs : List Value) (st : Store) (o : String),
    ⊢ nativePrintlnSpec (GF := GF) (Mv live) N (wpW (Mv live)) sret args s vs st o
  nAssert : ∀ (sret inp args s line : BitVec 64) (vs : List Value) (ρ : Regime) (st : St) (d : Nat)
    (jb : Nat → BitVec 8),
    ⊢ nativeAssertSpec (GF := GF) (Mv live) N (wpW (Mv live)) Lp Rp sret inp args s line vs ρ st d jb
  /-- The `fn` literal's partial case, closed (its lemma takes `textOwn allocText`). -/
  fnLit : ∀ {st : St} {d env : Nat} {nm : Option String} {ps : List String} {body : List Stmt},
    leafErrCtx inp ∗ evalSpecsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ⊢
      evalSpecP_body (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env (.fn nm ps body)
  /-- `+`'s partial case, closed (its lemma takes `textOwn allocText`). -/
  add : ∀ {st : St} {d env : Nat} {l r : Expr},
    evalSpecsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ∗ errCtx inp ⊢
      evalSpecP_body (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env (.binary .add l r)

/-- The Löb conclusion, as one proposition. -/
abbrev specsPI (live : Nat → Prop) (N : NativeAddrs) (inp : Nat) : IProp GF :=
  iprop((∀ st d env e, evalSpecP_body (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env e) ∧
    (∀ st d env sm, execDispP_body (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env sm))

theorem specsP_split (live : Nat → Prop) (N : NativeAddrs) (inp : Nat) :
    ▷ □ specsPI (GF := GF) live N inp ⊢
      evalSpecsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ∗
        execDispsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) := by
  have hl : □ specsPI (GF := GF) live N inp ⊢
      ∀ st d env e, evalSpecP_body (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env e := by
    iintro #H; iapply and_elim_l $$ H
  have hr : □ specsPI (GF := GF) live N inp ⊢
      ∀ st d env sm, execDispP_body (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env sm := by
    iintro #H; iapply and_elim_r $$ H
  iintro #H
  unfold evalSpecsP execDispsP
  isplitl
  · imodintro
    iapply later_mono hl $$ H
  · imodintro
    iapply later_mono hr $$ H

/-- The expression cases. -/
theorem evalP_cases {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (S : StuckSupply (GF := GF) live N inp) (st : St) (d env : Nat) (e : Expr) :
    errCtx inp ∗ evalSpecsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ∗
        execDispsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ⊢
      evalSpecP_body (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env e := by
  iintro ⟨#Hctx, #HE, #HX⟩
  have hE := S.errEnv
  ihave #HL := leafErrCtx_of_errCtx hE.inpGeom hE.inpLt $$ Hctx
  cases e with
  | int n => iapply caseP_LeafInt S.hlive S.vint $$ HE
  | str x => iapply caseP_LeafStr S.hlive S.vstr $$ HE
  | bool b => iapply caseP_LeafBool S.hlive S.vbool $$ HE
  | null => iapply caseP_LeafNull S.hlive S.vnull $$ HE
  | var x =>
    iapply caseP_Var S.hlive hE.newlib hE.code (errRoom _ _) S.envGet
    iframe HL HE
  | assign x e =>
    iapply caseP_Assign S.hlive hE.newlib hE.code (errRoom _ _) S.envSet
    iframe HL HE
  | fn nm ps body =>
    iapply S.fnLit
    iframe HL HE
  | unary op e =>
    cases op with
    | neg =>
      iapply caseP_UnaryNeg S.hlive S.vint S.vkind hE
      iframe HE Hctx
    | not => iapply caseP_UnaryNot S.hlive S.vtruthy S.vbool $$ HE
  | logical op l r =>
    cases op with
    | and => iapply caseP_LogicalAnd S.hlive S.vtruthy S.vbool $$ HE
    | or => iapply caseP_LogicalOr S.hlive S.vtruthy S.vbool $$ HE
  | binary op l r =>
    cases op with
    | add => iapply S.add; iframe HE Hctx
    | sub => iapply caseP_BinarySub S.hlive hE S.vint S.vkind; iframe HE Hctx
    | mul => iapply caseP_BinaryMul S.hlive hE S.vint S.vkind; iframe HE Hctx
    | div => iapply caseP_BinaryDiv S.hlive hE S.vint S.vkind; iframe HE Hctx
    | mod => iapply caseP_BinaryMod S.hlive hE S.vint S.vkind; iframe HE Hctx
    | eq => iapply caseP_BinaryEq S.hlive S.vequal S.strcmpV S.vbool S.nativeInj; iframe HE Hctx
    | ne => iapply caseP_BinaryNe S.hlive S.vequal S.strcmpV S.vbool S.nativeInj; iframe HE Hctx
    | lt => iapply caseP_BinaryLt S.hlive hE S.vbool S.strcmpOrd S.vkind; iframe HE Hctx
    | le => iapply caseP_BinaryLe S.hlive hE S.vbool S.strcmpOrd S.vkind; iframe HE Hctx
    | gt => iapply caseP_BinaryGt S.hlive hE S.vbool S.strcmpOrd S.vkind; iframe HE Hctx
    | ge => iapply caseP_BinaryGe S.hlive hE S.vbool S.strcmpOrd S.vkind; iframe HE Hctx
  | call f args =>
    iapply caseP_CallArm S.hlive hE S.nativeEntries (dispSupply_of_cloSupply S.cloSupply)
      (evalArgsP_all S.hlive _ d env args) S.vkind S.nPrint S.nPrintln S.nAssert
      (hroomPrintln f args d)
      (callCloP_of S.hlive hE S.vnull S.envNew S.envDefine S.cloSupply S.inpAl)
    iframe HE Hctx HX

/-- The statement cases. -/
theorem execP_cases {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (S : StuckSupply (GF := GF) live N inp) (st : St) (d env : Nat) (sm : Stmt) :
    errCtx inp ∗ evalSpecsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ∗
        execDispsP (GF := GF) (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) ⊢
      execDispP_body (Mv live) N Lp Rp inp (evalCore N Lp Rp inp) st d env sm := by
  iintro ⟨#Hctx, #HE, #HX⟩
  have hE := S.errEnv
  cases sm with
  | expr e => iapply caseP_ExecExpr S.hlive $$ HE
  | varDecl x eo =>
    cases eo with
    | some e => iapply caseP_ExecVarInit S.hlive hE.newlib hE.code hE.core S.envDefine; iframe Hctx HE
    | none => iapply caseP_ExecVarNull S.hlive hE.newlib hE.code hE.core S.vnull S.envDefine $$ Hctx
  | block ss => iapply caseP_ExecBlock S.hlive hE.newlib hE.code hE.core S.envNew; iframe Hctx HX
  | ifStmt c t eo => iapply caseP_ExecIf S.hlive S.vtruthy; iframe HE HX
  | whileStmt c b =>
    iapply caseP_ExecWhile S.hlive (whileP_all S.hlive S.vtruthy _ d env c b); iframe HE HX
  | forStmt init cnd step b =>
    iapply caseP_ExecFor S.hlive hE.newlib hE.code hE.core S.envNew (execInitP_all S.hlive _ _ _ _)
      (forLoopP_all S.hlive S.vtruthy _ _ _ _ _ _)
    iframe Hctx HE HX
  | ret eo =>
    cases eo with
    | some e => iapply caseP_ExecRet S.hlive $$ HE
    | none => iapply caseP_ExecRetNull S.hlive S.vnull
  | brk => iapply caseP_ExecBrk S.hlive
  | cont => iapply caseP_ExecCont S.hlive

/-- **`stuck_sim`'s recursion (Löb)**: under the error context, every
expression and every statement meets its partial spec. -/
theorem specsP_all {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (S : StuckSupply (GF := GF) live N inp) :
    errCtx inp ⊢ □ specsPI (GF := GF) live N inp := by
  iintro #Hctx
  iapply loeb_wand
  imodintro
  iintro #IH
  ihave ⟨#HE, #HX⟩ := specsP_split live N inp $$ IH
  imodintro
  isplit
  · iintro %st %d %env %e
    iapply evalP_cases S st d env e
    iframe Hctx HE HX
  · iintro %st %d %env %sm
    iapply execP_cases S st d env sm
    iframe Hctx HE HX

end

end VsaIris.Interp
