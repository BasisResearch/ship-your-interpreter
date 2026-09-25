import VsaIris.Interp.Case.LeafNullT
import VsaIris.Interp.Case.LeafIntT
import VsaIris.Interp.Case.LeafStrT
import VsaIris.Interp.Case.LeafBoolT
import VsaIris.Interp.Case.VarT
import VsaIris.Interp.Case.AssignT
import VsaIris.Interp.Case.FnLitT
import VsaIris.Interp.Case.BinaryAddIntT
import VsaIris.Interp.Case.BinarySubIntT
import VsaIris.Interp.Case.BinaryMulIntT
import VsaIris.Interp.Case.BinaryDivIntT
import VsaIris.Interp.Case.BinaryModIntT
import VsaIris.Interp.Case.BinaryConcatT
import VsaIris.Interp.Case.BinaryEqT
import VsaIris.Interp.Case.BinaryNeT
import VsaIris.Interp.Case.BinaryLtIntT
import VsaIris.Interp.Case.BinaryLeIntT
import VsaIris.Interp.Case.BinaryGtIntT
import VsaIris.Interp.Case.BinaryGeIntT
import VsaIris.Interp.Case.BinaryLtStrT
import VsaIris.Interp.Case.BinaryLeStrT
import VsaIris.Interp.Case.BinaryGtStrT
import VsaIris.Interp.Case.BinaryGeStrT
import VsaIris.Interp.Case.LogicalAndFalseT
import VsaIris.Interp.Case.LogicalAndTrueT
import VsaIris.Interp.Case.LogicalOrFalseT
import VsaIris.Interp.Case.LogicalOrTrueT
import VsaIris.Interp.Case.UnaryNegT
import VsaIris.Interp.Case.UnaryNotT
import VsaIris.Interp.Case.CallClosureT
import VsaIris.Interp.Case.CallPrintT
import VsaIris.Interp.Case.CallPrintlnT
import VsaIris.Interp.Case.CallAssertT
import VsaIris.Interp.Case.ExecExprT
import VsaIris.Interp.Case.ExecVarInitT
import VsaIris.Interp.Case.ExecVarNullT
import VsaIris.Interp.Case.ExecBlockT
import VsaIris.Interp.Case.ExecIfTrueT
import VsaIris.Interp.Case.ExecIfFalseT
import VsaIris.Interp.Case.ExecIfNoneT
import VsaIris.Interp.Case.ExecWhileT
import VsaIris.Interp.Case.ExecForT
import VsaIris.Interp.Case.ExecRetT
import VsaIris.Interp.Case.ExecRetNullT
import VsaIris.Interp.Case.ExecBrkT
import VsaIris.Interp.Case.ExecContT
import VsaIris.Interp.LoopWhile
import VsaIris.Interp.LoopFor
import VsaIris.Interp.LoopArgs
import VsaIris.Interp.SeqLoopInterp
import VsaIris.Interp.ExecDisp

/-!
# `term_sim`'s recursion: every cost derivation meets its total spec (lane A)

INTERP_DESIGN.md §4.1, §5.2. The mutual recursor over the nine cost
companions (`EvalECost` … `ExecSeqCost`, `Vsa/While/Cost.lean`) with one motive
per relation, each the landed statement its consumers take:

| relation | motive |
|---|---|
| `EvalECost` | `⊢ evalSpecT_body D` |
| `EvalArgsCost` | E6's `evalArgsT_body` |
| `CallCost` | the call arm: any callee and argument derivations with their motives give the whole call's `evalSpecT_body` |
| `ExecSCost` | `⊢ execDispT_body D` (E5), and E6's `whileT_body` for a `while` |
| `ExecInitCost`, `ForLoopCost`, `ForCondCost`, `ExecStepCost` | E6's motives |
| `ExecSeqCost` | G's three `seqLoop` sites: block, closure body, `interp_run` |

Each recursor case applies its generated `Case/*T` lemma (or the loop lemma of
E6/G). The callee specs and the named premises of the cases are one record,
`TermSupply`, supplied once at the top (`Top.lean`).
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

/-- **The callee specs and named premises of the total cases**, at one
`live`, native table `N` and interpreter object `inp`. Every field is a
closed statement a helper proof (H1-H4, the string runs) or the boundary
supplies. -/
structure TermSupply (live : Nat → Prop) (N : NativeAddrs) (inp : Nat) : Prop where
  hlive : ∀ p ∈ interpText, live p.1
  vint : ⊢ ∀ p n, valueIntSpec (GF := GF) (Mv live) N (twpW (Mv live)) p n
  vbool : ⊢ ∀ p b, valueBoolSpec (GF := GF) (Mv live) N (twpW (Mv live)) p b
  vnull : ⊢ ∀ p, valueNullSpec (GF := GF) (Mv live) N (twpW (Mv live)) p
  vstr : ⊢ ∀ p q x, valueStrSpec (GF := GF) (Mv live) N (twpW (Mv live)) p q x
  vtruthy : ⊢ ∀ p v, valueTruthySpec (GF := GF) (Mv live) N (twpW (Mv live)) p v
  vequal : ⊢ ∀ pa pb s a b st B, valueEqualSpec (GF := GF) (Mv live) N (twpW (Mv live)) pa pb s a b st B
  strcmpV : ⊢ strcmpSpecV (GF := GF) (Mv live) (twpW (Mv live))
  strcmpOrd : ⊢ strcmpOrdSpec (GF := GF) (Mv live) (twpW (Mv live))
  envGet : ⊢ envGetSpec (GF := GF) (twpW (Mv live)) N
  envSet : ⊢ envSetSpec (GF := GF) (twpW (Mv live)) N
  envNew : ⊢ envNewSpec (GF := GF) (twpW (Mv live)) N
  envDefine : ⊢ envDefineSpec (GF := GF) (twpW (Mv live)) N
  nativeInj : NativeInj N
  nativeEntries : NativeEntries N
  cloSupply : CloSupply (GF := GF) N
  inpGeom : Newlib.RtErr.InpGeom (BitVec.ofNat 64 inp)
  inpLt : inp < 2 ^ 64
  inpAl : inp % 8 = 0
  nPrint : ∀ (sret args s : BitVec 64) (vs : List Value) (st : Store) (o : String),
    ⊢ nativePrintSpec (GF := GF) (Mv live) N (twpW (Mv live)) sret args s vs st o
  nPrintln : ∀ (sret args s : BitVec 64) (vs : List Value) (st : Store) (o : String),
    ⊢ nativePrintlnSpec (GF := GF) (Mv live) N (twpW (Mv live)) sret args s vs st o
  nAssert : ∀ (sret inp args s line : BitVec 64) (vs : List Value) (ρ : Regime) (st : St) (d : Nat)
    (jb : Nat → BitVec 8),
    ⊢ nativeAssertSpec (GF := GF) (Mv live) N (twpW (Mv live)) Lp Rp sret inp args s line vs ρ st d jb
  alloc : AllocSpecs live
  stringifyT : ⊢ ∀ p s v st k H c o, stringifySpecT (GF := GF) (Mv live) N (twpW (Mv live)) p s v st k H c o
  strlenHeap : ⊢ ∀ q x ρ H, strlenHeapSpec (GF := GF) (Mv live) (twpW (Mv live)) q x ρ H
  memcpyOwned : ⊢ memcpySpecOwned (GF := GF) (Mv live) (twpW (Mv live))
  strcpyHeap : ⊢ ∀ d q y ρ H, strcpyHeapSpec (GF := GF) (Mv live) (twpW (Mv live)) d q y ρ H

/-! ## The binary arm: one `binOpSem` outcome, one case lemma -/

theorem binOpSem_add_str (s : Store) {lv rv : Value} (h : valTag lv = 3 ∨ valTag rv = 3) :
    binOpSem s .add lv rv = some (.str (lv.catDisplay s ++ rv.catDisplay s)) := by
  cases lv <;> cases rv <;> simp [valTag] at h <;> rfl

theorem binaryT {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (S : TermSupply (GF := GF) live N inp) {st st1 st2 : St} {d env : Nat} {op : BinOp}
    {l r : Expr} {lv rv v : Value} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (Dr : EvalECost st1 d env r st2 rv nr)
    (hsem : binOpSem st2.store op lv rv = some v)
    (hl : ⊢ evalSpecT_body (GF := GF) (Mv live) N Lp Rp inp st d env l st1 lv nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (Mv live) N Lp Rp inp st1 d env r st2 rv nr Dr) :
    ⊢ evalSpecT_body (GF := GF) (Mv live) N Lp Rp inp st d env (.binary op l r) st2 v
      (nl + nr + binOpCost st2.store op lv rv) (.binary st d env op l r st1 st2 lv rv v nl nr Dl Dr hsem) := by
  cases op with
  | eq =>
    obtain rfl := Option.some.inj hsem
    exact caseT_BinaryEq S.hlive Dl Dr _ hl hr S.vequal S.strcmpV S.vbool S.nativeInj
  | ne =>
    obtain rfl := Option.some.inj hsem
    exact caseT_BinaryNe S.hlive Dl Dr _ hl hr S.vequal S.strcmpV S.vbool S.nativeInj
  | add =>
    by_cases hs : valTag lv = 3 ∨ valTag rv = 3
    · have e := (binOpSem_add_str st2.store hs).symm.trans hsem
      obtain rfl := Option.some.inj e
      exact caseT_BinaryConcat S.hlive Dl Dr _ hl hr rfl rfl hs S.alloc S.stringifyT S.strlenHeap
        S.memcpyOwned S.strcpyHeap S.vstr (dispSupply_of_cloSupply S.cloSupply)
    · cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem <;>
        simp [valTag] at hs
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryAddInt S.hlive Dl Dr _ hl hr S.vint
  | sub =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    obtain rfl := Option.some.inj hsem
    exact caseT_BinarySubInt S.hlive Dl Dr _ hl hr S.vint
  | mul =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    obtain rfl := Option.some.inj hsem
    exact caseT_BinaryMulInt S.hlive Dl Dr _ hl hr S.vint
  | div =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    rename_i a b
    by_cases hb : b = 0
    · simp [hb] at hsem
    · simp only [hb, beq_iff_eq, ite_false] at hsem
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryDivInt S.hlive Dl Dr _ hb hl hr S.vint
  | mod =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    rename_i a b
    by_cases hb : b = 0
    · simp [hb] at hsem
    · simp only [hb, beq_iff_eq, ite_false] at hsem
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryModInt S.hlive Dl Dr _ hb hl hr S.vint
  | lt =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    case int.int =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryLtInt S.hlive Dl Dr _ hl hr S.vbool
    case str.str =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryLtStr S.hlive Dl Dr _ hl hr S.strcmpOrd S.vbool
  | le =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    case int.int =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryLeInt S.hlive Dl Dr _ hl hr S.vbool
    case str.str =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryLeStr S.hlive Dl Dr _ hl hr S.strcmpOrd S.vbool
  | gt =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    case int.int =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryGtInt S.hlive Dl Dr _ hl hr S.vbool
    case str.str =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryGtStr S.hlive Dl Dr _ hl hr S.strcmpOrd S.vbool
  | ge =>
    cases lv <;> cases rv <;> simp only [binOpSem, reduceCtorEq] at hsem
    case int.int =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryGeInt S.hlive Dl Dr _ hl hr S.vbool
    case str.str =>
      obtain rfl := Option.some.inj hsem
      exact caseT_BinaryGeStr S.hlive Dl Dr _ hl hr S.strcmpOrd S.vbool

/-! ## The native calls' stack room (Q7's headroom) -/

theorem hroomPrint (f : Expr) (args : List Expr) (d : Nat) :
    nativePrintNeed + 1088 ≤ evalNeed (.call f args) d := by
  have := Expr.stackNeed_ge f
  unfold evalNeed stackBudget nativePrintNeed printNeed Newlib.fprintfNeed
    Vsa.Sim.LayoutInstance.helperHeadroom
  simp only [Expr.stackNeed]; unfold evalFrame at *; omega

theorem hroomPrintln (f : Expr) (args : List Expr) (d : Nat) :
    nativePrintlnNeed + 1088 ≤ evalNeed (.call f args) d := by
  have := Expr.stackNeed_ge f
  unfold evalNeed stackBudget nativePrintlnNeed nativePrintNeed printNeed Newlib.fprintfNeed
    Vsa.Sim.LayoutInstance.helperHeadroom
  simp only [Expr.stackNeed]; unfold evalFrame at *; omega

/-! ## The motives -/

section Motives

variable (live : Nat → Prop) (N : NativeAddrs) (inp : Nat)

/-- `CallCost`'s motive: the call arm, for any callee and argument derivations
with their motives. -/
def callT (st : St) (d : Nat) (fv : Value) (vs : List Value) (st' : St) (v : Value) (n : Nat)
    (Dc : CallCost st d fv vs st' v n) : Prop :=
  ∀ {st0 st1 : St} {env : Nat} {f : Expr} {args : List Expr} {nf na : Nat}
    (Df : EvalECost st0 d env f st1 fv nf) (hlen : args.length ≤ maxArgs)
    (Da : EvalArgsCost st1 d env args st vs na),
    (⊢ evalSpecT_body (GF := GF) (Mv live) N Lp Rp inp st0 d env f st1 fv nf Df) →
    evalArgsT_body (GF := GF) live N Lp Rp inp st1 d env args st vs na →
    ⊢ evalSpecT_body (GF := GF) (Mv live) N Lp Rp inp st0 d env (.call f args) st' v (nf + na + n)
      (.call st0 d env f args st1 st st' fv vs v nf na n Df hlen Da Dc)

/-- `ExecSCost`'s motive: E5's dispatch-point spec, and E6's `while` loop. -/
def execT (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (D : ExecSCost st d env sm st' status n) : Prop :=
  (⊢ execDispT_body (GF := GF) (Mv live) N Lp Rp inp st d env sm st' status n D) ∧
    ∀ c b, sm = .whileStmt c b → whileT_body (GF := GF) live N Lp Rp inp st d env c b st' status n

/-- `ExecSeqCost`'s motive: G's three sequence sites. -/
def seqT (st : St) (d env : Nat) (ss : List Stmt) (st' : St) (status : Status) (n : Nat)
    (D : ExecSeqCost st d env ss st' status n) : Prop :=
  blockSeqT_body (GF := GF) live N Lp Rp inp st d env ss st' status n D ∧
    closureSeqT_body (GF := GF) live N Lp Rp inp st d env ss st' status n D ∧
    interpSeqT_body (GF := GF) live N Lp Rp inp st d env ss st' status n D

end Motives

theorem execSpec_of {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (hlive : ∀ p ∈ interpText, live p.1) {st : St} {d env : Nat} {sm : Stmt} {st' : St}
    {status : Status} {n : Nat} {D : ExecSCost st d env sm st' status n}
    (h : ⊢ execDispT_body (GF := GF) (Mv live) N Lp Rp inp st d env sm st' status n D) :
    ⊢ execSpecT_body (GF := GF) (Mv live) N Lp Rp inp st d env sm st' status n D :=
  h.trans (execSpecT_of_disp hlive D)

set_option hygiene false in
/-- **The recursion** at one relation `R`: the nine motives and the fifty
cases. -/
local macro "term_rec " r:ident S:ident h:ident : tactic => `(tactic| (
  refine $r
    (motive_1 := fun st d env e st' v n D =>
      ⊢ evalSpecT_body (GF := GF) (Mv live) N Lp Rp inp st d env e st' v n D)
    (motive_2 := fun st d env es st' vs n _ =>
      evalArgsT_body (GF := GF) live N Lp Rp inp st d env es st' vs n)
    (motive_3 := fun st d fv vs st' v n D => callT (GF := GF) live N inp st d fv vs st' v n D)
    (motive_4 := fun st d env sm st' status n D => execT (GF := GF) live N inp st d env sm st' status n D)
    (motive_5 := fun st d env init st' n _ =>
      execInitT_body (GF := GF) live N Lp Rp inp st d env init st' n)
    (motive_6 := fun st d env cnd step b st' status n _ =>
      forLoopT_body (GF := GF) live N Lp Rp inp st d env cnd step b st' status n)
    (motive_7 := fun st d env cnd st' n _ => forCondT_body (GF := GF) live N Lp Rp inp st d env cnd st' n)
    (motive_8 := fun st d env step st' n _ =>
      execStepT_body (GF := GF) live N Lp Rp inp st d env step st' n)
    (motive_9 := fun st d env ss st' status n D => seqT (GF := GF) live N inp st d env ss st' status n D)
    ?int ?str ?bool ?null ?var ?assign ?binary ?orTrue ?orFalse ?andFalse ?andTrue ?neg ?not ?call ?fn
    ?argsNil ?argsCons
    ?cloClosure ?cloPrint ?cloPrintln ?cloAssert
    ?expr ?varInit ?varNull ?block ?ifTrue ?ifFalse ?ifNone ?whileFalse ?whileBreak ?whileRet
    ?whileLoop ?forStart ?ret ?retNull ?brk ?cont
    ?initNone ?initSome ?condFalse ?bodyBreak ?bodyRet ?loop ?condNone ?condSome ?stepNone ?stepSome
    ?seqNil ?seqCons ?seqAbrupt $h
  case int => intro st d env n; exact caseT_LeafInt ($S).hlive _ ($S).vint
  case str => intro st d env x; exact caseT_LeafStr ($S).hlive _ ($S).vstr
  case bool => intro st d env b; exact caseT_LeafBool ($S).hlive _ ($S).vbool
  case null => intro st d env; exact caseT_LeafNull ($S).hlive _ ($S).vnull
  case var => intro st d env x v _; exact caseT_Var ($S).hlive _ ($S).envGet
  case assign =>
    intro st d env x e st' v store'' n De hset ihe; exact caseT_Assign ($S).hlive De hset _ ihe ($S).envSet
  case binary =>
    intro st d env op l r st' st'' lv rv v nl nr Dl Dr hsem ihl ihr; exact binaryT $S Dl Dr hsem ihl ihr
  case orTrue =>
    intro st d env l r st' lv n Dl ht ihl
    exact caseT_LogicalOrTrue ($S).hlive Dl ht _ ihl ($S).vtruthy ($S).vbool
  case orFalse =>
    intro st d env l r st' st'' lv rv nl nr Dl hf Dr ihl ihr
    exact caseT_LogicalOrFalse ($S).hlive Dl hf Dr _ ihl ihr ($S).vtruthy ($S).vbool
  case andFalse =>
    intro st d env l r st' lv n Dl hf ihl
    exact caseT_LogicalAndFalse ($S).hlive Dl hf _ ihl ($S).vtruthy ($S).vbool
  case andTrue =>
    intro st d env l r st' st'' lv rv nl nr Dl ht Dr ihl ihr
    exact caseT_LogicalAndTrue ($S).hlive Dl ht Dr _ ihl ihr ($S).vtruthy ($S).vbool
  case neg => intro st d env e st' n m De ih; exact caseT_UnaryNeg ($S).hlive De _ ih ($S).vint
  case not => intro st d env e st' v m De ih; exact caseT_UnaryNot ($S).hlive De _ ih ($S).vtruthy ($S).vbool
  case call =>
    intro st d env f args st1 st2 st3 fv vs v nf na nc Df hlen Da Dc ihf iha ihc
    exact ihc Df hlen Da ihf iha
  case fn => intro st d env nm ps body store' a h; exact caseT_FnLit ($S).hlive ($S).alloc h _
  case argsNil => intro st d env; exact evalArgsT_nil live N Lp Rp inp st d env
  case argsCons =>
    intro st d env e es st1 st2 v vs ne nes De Des ihe ihes; exact evalArgsT_cons ($S).hlive De Des ihe ihes
  case cloClosure =>
    intro st d a cd vs store' frame st' status v nb hcl hvl hd halloc Dseq hst ihseq
    intro st0 st1 env f args nf na Df hlen Da hf ha
    exact caseT_CallClosure ($S).hlive ($S).cloSupply ($S).inpGeom ($S).inpLt ($S).inpAl Df hlen Da hcl hvl hd
      halloc Dseq hst hf ha ihseq.2.1 ($S).vnull ($S).envNew ($S).envDefine
  case cloPrint =>
    intro st d vs st0 st1 env f args nf na Df hlen Da hf ha
    exact caseT_CallPrint ($S).hlive ($S).nativeEntries (dispSupply_of_cloSupply ($S).cloSupply)
      ErrnoOwn.errnoLend_vsa Df hlen Da hf
      ha ($S).nPrint (hroomPrint f args d)
  case cloPrintln =>
    intro st d vs st0 st1 env f args nf na Df hlen Da hf ha
    exact caseT_CallPrintln ($S).hlive ($S).nativeEntries (dispSupply_of_cloSupply ($S).cloSupply)
      ErrnoOwn.errnoLend_vsa Df hlen Da
      hf ha ($S).nPrintln (hroomPrintln f args d)
  case cloAssert =>
    intro st d vs v m hvm htr st0 st1 env f args nf na Df hlen Da hf ha
    exact caseT_CallAssert ($S).hlive hvm htr ($S).nativeEntries ($S).inpGeom ($S).inpLt Df hlen Da hf ha
      ($S).nAssert
  case expr =>
    intro st d env e st' v n De ihe
    exact ⟨caseT_ExecExpr ($S).hlive De ihe, fun _ _ h => by cases h⟩
  case varInit =>
    intro st d env x e st' v n De ihe
    exact ⟨caseT_ExecVarInit ($S).hlive De ihe ($S).envDefine, fun _ _ h => by cases h⟩
  case varNull =>
    intro st d env x
    exact ⟨caseT_ExecVarNull ($S).hlive ($S).vnull ($S).envDefine, fun _ _ h => by cases h⟩
  case block =>
    intro st d env ss store' inner st' status n halloc Dseq ihseq
    exact ⟨caseT_ExecBlock ($S).hlive halloc Dseq ihseq.1 ($S).envNew, fun _ _ h => by cases h⟩
  case ifTrue =>
    intro st d env c t e st1 st2 v status nc nt Dc ht Dt ihc iht
    exact ⟨caseT_ExecIfTrue ($S).hlive Dc ht Dt ihc iht.1 ($S).vtruthy, fun _ _ h => by cases h⟩
  case ifFalse =>
    intro st d env c t e st1 st2 v status nc ne Dc hf De ihc ihe
    exact ⟨caseT_ExecIfFalse ($S).hlive Dc hf De ihc ihe.1 ($S).vtruthy, fun _ _ h => by cases h⟩
  case ifNone =>
    intro st d env c t st' v nc Dc hf ihc
    exact ⟨caseT_ExecIfNone ($S).hlive Dc hf ihc ($S).vtruthy, fun _ _ h => by cases h⟩
  case whileFalse =>
    intro st d env c b st' v nc Dc hf ihc
    have hw := whileT_false (b := b) ($S).hlive Dc hf ihc ($S).vtruthy
    exact ⟨caseT_ExecWhile ($S).hlive _ hw, fun _ _ h => by cases h; exact hw⟩
  case whileBreak =>
    intro st d env c b st1 st2 v nc nb Dc ht Db ihc ihb
    have hw := whileT_break ($S).hlive Dc ht Db ihc (execSpec_of ($S).hlive ihb.1) ($S).vtruthy
    exact ⟨caseT_ExecWhile ($S).hlive _ hw, fun _ _ h => by cases h; exact hw⟩
  case whileRet =>
    intro st d env c b st1 st2 v rv nc nb Dc ht Db ihc ihb
    have hw := whileT_ret ($S).hlive Dc ht Db ihc (execSpec_of ($S).hlive ihb.1) ($S).vtruthy
    exact ⟨caseT_ExecWhile ($S).hlive _ hw, fun _ _ h => by cases h; exact hw⟩
  case whileLoop =>
    intro st d env c b st1 st2 st3 v status status' nc nb nr Dc ht Db hst Dr ihc ihb ihr
    have hw := whileT_loop ($S).hlive Dc ht Db hst ihc (execSpec_of ($S).hlive ihb.1) (ihr.2 c b rfl)
      ($S).vtruthy
    exact ⟨caseT_ExecWhile ($S).hlive _ hw, fun _ _ h => by cases h; exact hw⟩
  case forStart =>
    intro st d env init cnd step b store' outer st1 st2 status ni nl halloc Di Dl ihi ihl
    exact ⟨caseT_ExecFor ($S).hlive halloc Di Dl ihi ihl ($S).envNew, fun _ _ h => by cases h⟩
  case ret =>
    intro st d env e st' v n De ihe
    exact ⟨caseT_ExecRet ($S).hlive De ihe, fun _ _ h => by cases h⟩
  case retNull =>
    intro st d env
    exact ⟨caseT_ExecRetNull ($S).hlive ($S).vnull, fun _ _ h => by cases h⟩
  case brk => intro st d env; exact ⟨caseT_ExecBrk ($S).hlive, fun _ _ h => by cases h⟩
  case cont => intro st d env; exact ⟨caseT_ExecCont ($S).hlive, fun _ _ h => by cases h⟩
  case initNone => intro st d env; exact execInitT_none ($S).hlive st d env
  case initSome =>
    intro st d env s st' status n Ds ihs; exact execInitT_some ($S).hlive Ds (execSpec_of ($S).hlive ihs.1)
  case condFalse =>
    intro st d env c step b st' v nc Dc hf ihc; exact forLoopT_condFalse ($S).hlive Dc hf ihc ($S).vtruthy
  case bodyBreak =>
    intro st d env cnd step b st1 st2 nc nb Dc Db ihc ihb
    exact forLoopT_bodyBreak ($S).hlive ihc Db (execSpec_of ($S).hlive ihb.1)
  case bodyRet =>
    intro st d env cnd step b st1 st2 rv nc nb Dc Db ihc ihb
    exact forLoopT_bodyRet ($S).hlive ihc Db (execSpec_of ($S).hlive ihb.1)
  case loop =>
    intro st d env cnd step b st1 st2 st3 st4 status status' nc nb ns nr Dc Db hst Ds Dr ihc ihb ihs ihr
    exact forLoopT_loop ($S).hlive ihc Db hst (execSpec_of ($S).hlive ihb.1) ihs ihr
  case condNone => intro st d env; exact forCondT_none ($S).hlive st d env
  case condSome =>
    intro st d env c st' v nc Dc ht ihc; exact forCondT_some ($S).hlive Dc ht ihc ($S).vtruthy
  case stepNone => intro st d env; exact execStepT_none ($S).hlive st d env
  case stepSome => intro st d env e st' v n De ihe; exact execStepT_some ($S).hlive De ihe
  case seqNil =>
    intro st d env
    exact ⟨blockSeqT_nil live N Lp Rp inp st d env, closureSeqT_nil live N Lp Rp inp st d env,
      interpSeqT_nil live N Lp Rp inp st d env⟩
  case seqCons =>
    intro st d env s ss st1 st2 status n1 n2 D1 D2 ih1 ih2
    have h1 := execSpec_of ($S).hlive ih1.1
    exact ⟨blockSeqT_consNormal ($S).hlive D1 D2 h1 ih2.1, closureSeqT_consNormal ($S).hlive D1 D2 h1 ih2.2.1,
      interpSeqT_consNormal ($S).hlive D1 D2 h1 ih2.2.2 ($S).vnull⟩
  case seqAbrupt =>
    intro st d env s ss st' status n D1 hne ih1
    have h1 := execSpec_of ($S).hlive ih1.1
    exact ⟨blockSeqT_consAbrupt (st'' := st') ($S).hlive D1 hne h1,
      closureSeqT_consAbrupt (st'' := st') ($S).hlive D1 hne h1,
      interpSeqT_consAbrupt ($S).hlive D1 hne h1 ($S).vnull⟩))

/-- **`term_sim`'s recursion, statement form**: every statement derivation
meets `exec_stmt`'s dispatch-point spec. -/
theorem execDispT_all {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (S : TermSupply (GF := GF) live N inp) {st : St} {d env : Nat} {sm : Stmt} {st' : St}
    {status : Status} {n : Nat} (D : ExecSCost st d env sm st' status n) :
    ⊢ execDispT_body (GF := GF) (Mv live) N Lp Rp inp st d env sm st' status n D := by
  have h : execT (GF := GF) live N inp st d env sm st' status n D := by term_rec ExecSCost.rec S D
  exact h.1

/-- **`term_sim`'s recursion, program form**: a whole-program derivation
meets `interp_run`'s loop motive. -/
theorem interpSeqT_all {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}
    (S : TermSupply (GF := GF) live N inp) {st : St} {d env : Nat} {ss : List Stmt} {st' : St}
    {status : Status} {n : Nat} (D : ExecSeqCost st d env ss st' status n) :
    interpSeqT_body (GF := GF) live N Lp Rp inp st d env ss st' status n D := by
  have h : seqT (GF := GF) live N inp st d env ss st' status n D := by term_rec ExecSeqCost.rec S D
  exact h.2.2

end

end VsaIris.Interp
