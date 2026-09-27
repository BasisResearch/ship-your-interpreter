import Vsa.Compiler.SimFor

/-!
# The forward simulation

`sim_all`: every cost derivation of the nine relations is simulated by its code,
by the mutual induction principle of the cost relations with the simulation
statements as motives; each case is one of the per-rule lemmas.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The forward simulation of each of the nine cost relations. -/
structure Sims (code : List Ins) (T : List String) : Prop where
  e : ∀ {st d a e st' v n}, EvalECost st d a e st' v n → ESpec code T st d a e st' v n
  a : ∀ {st d a es st' vs n}, EvalArgsCost st d a es st' vs n → ASpec code T st d a es st' vs n
  c : ∀ {st d fv vs st' v n}, CallCost st d fv vs st' v n → CSpec code T st d fv vs st' v n
  s : ∀ {st d a s st' t n}, ExecSCost st d a s st' t n → SSpec code T st d a s st' t n
  xi : ∀ {st d a i st' n}, ExecInitCost st d a i st' n → XISpec code T st d a i st' n
  fl : ∀ {st d a c s b st' t n}, ForLoopCost st d a c s b st' t n → FLSpec code T st d a c s b st' t n
  fc : ∀ {st d a c st' n}, ForCondCost st d a c st' n → FCSpec code T st d a c st' n
  xs : ∀ {st d a s st' n}, ExecStepCost st d a s st' n → XSSpec code T st d a s st' n
  q : ∀ {st d a ss st' t n}, ExecSeqCost st d a ss st' t n → QSpec code T st d a ss st' t n

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sim_all : Sims code T := by
  have c_int := fun st d env n => sInt (T := T) hR st d env n
  have c_str := fun st d env s => sStr (T := T) hR st d env s
  have c_bool := fun st d env b => sBool (T := T) hR st d env b
  have c_null := fun st d env => sNull (T := T) hR st d env
  have c_var := fun st d env x v hget => sVar (T := T) hR st d env x v hget
  have c_assign := fun (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St) (v : Value)
    (store'' : Store) (n : Nat) (_ : EvalECost st d env e st' v n) (hs : st'.store.set? env x v = some store'')
    (ih : ESpec code T st d env e st' v n) => sAssign hR ih hs
  have c_bin := fun (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : St) (lv rv v : Value)
    (nl nr : Nat) (_ : EvalECost st d env l st' lv nl) (_ : EvalECost st' d env r st'' rv nr)
    (hbin : binOpSem st''.store op lv rv = some v) (ihl : ESpec code T st d env l st' lv nl)
    (ihr : ESpec code T st' d env r st'' rv nr) => sBinary hR ihl ihr hbin
  have c_ort := fun (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St) (lv : Value) (n : Nat)
    (_ : EvalECost st d env l st' lv n) (ht : lv.truthy = true) (ih : ESpec code T st d env l st' lv n) =>
    sLogShort (r := r) (op := .or) hR ih ht
  have c_orf := fun (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St) (lv rv : Value) (nl nr : Nat)
    (_ : EvalECost st d env l st' lv nl) (hf : lv.truthy = false) (_ : EvalECost st' d env r st'' rv nr)
    (ihl : ESpec code T st d env l st' lv nl) (ihr : ESpec code T st' d env r st'' rv nr) =>
    sLogFull (op := .or) hR ihl hf ihr
  have c_anf := fun (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St) (lv : Value) (n : Nat)
    (_ : EvalECost st d env l st' lv n) (hf : lv.truthy = false) (ih : ESpec code T st d env l st' lv n) =>
    sLogShort (r := r) (op := .and) hR ih hf
  have c_ant := fun (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St) (lv rv : Value) (nl nr : Nat)
    (_ : EvalECost st d env l st' lv nl) (ht : lv.truthy = true) (_ : EvalECost st' d env r st'' rv nr)
    (ihl : ESpec code T st d env l st' lv nl) (ihr : ESpec code T st' d env r st'' rv nr) =>
    sLogFull (op := .and) hR ihl ht ihr
  have c_neg := fun (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (n : Int) (m : Nat)
    (_ : EvalECost st d env e st' (.int n) m) (ih : ESpec code T st d env e st' (.int n) m) => sNeg hR ih
  have c_not := fun (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (m : Nat)
    (_ : EvalECost st d env e st' v m) (ih : ESpec code T st d env e st' v m) => sNot hR ih
  have c_call := fun (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : St)
    (fv : Value) (vs : List Value) (v : Value) (nf na nc : Nat) (_ : EvalECost st d env f st' fv nf)
    (hmax : args.length ≤ maxArgs) (ha : EvalArgsCost st' d env args st'' vs na)
    (_ : CallCost st'' d fv vs st''' v nc) (ihf : ESpec code T st d env f st' fv nf)
    (iha : ASpec code T st' d env args st'' vs na) (ihc : CSpec code T st'' d fv vs st''' v nc) =>
    sCall hR ihf hmax iha (evalArgsCost_length ha) ihc
  have c_fn := fun (st : St) (d : Nat) (env : Addr) (name : Option String) (params : List String)
    (body : List Stmt) (store' : Store) (a : Addr)
    (halloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a)) => sFn (T := T) (d := d) hR halloc
  have c_anil := fun st d env => aNil (T := T) hR st d env
  have c_acons := fun (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) (st' st'' : St) (v : Value)
    (vs : List Value) (ne nes : Nat) (_ : EvalECost st d env e st' v ne) (_ : EvalArgsCost st' d env es st'' vs nes)
    (ihe : ESpec code T st d env e st' v ne) (ihes : ASpec code T st' d env es st'' vs nes) => aCons hR ihe ihes
  have c_clo : ∀ (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store)
      (frame : Addr) (st' : St) (status : Status) (v : Value) (nb : Nat),
      st.store.closures[a]? = some cd → vs.length = cd.params.length → d < maxCallDepth →
      st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeqCost ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩ (d + 1)
        frame cd.body st' status nb →
      (status = .normal ∧ v = .null ∨ status = .ret v) →
      QSpec code T ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩ (d + 1)
        frame cd.body st' status nb →
      CSpec code T st d (.closure a) vs st' v (envBytes + bindParamsCost store' frame (cd.params.zip vs) + nb) := by
    intro st d a cd vs store' frame st' status v nb hcd hlen hd halloc _ hst ih
    have e1 : store' = (st.store.allocFrame (some cd.env)).1 := by rw [halloc]
    have e2 : frame = st.store.frames.size := by
      have : frame = (st.store.allocFrame (some cd.env)).2 := by rw [halloc]
      rw [this]; rfl
    subst e1 e2
    refine cClosure hR hcd hlen hd ih hst ?_
    omega
  have c_pr := fun st d vs => cPrint (T := T) hR st d vs
  have c_prl := fun st d vs => cPrintln (T := T) hR st d vs
  have c_as := fun st d vs v m hvs ht => cAssert (T := T) hR st d vs v m hvs ht
  have c_sexpr := fun (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_ : EvalECost st d env e st' v n) (ih : ESpec code T st d env e st' v n) => sExpr hR ih
  have c_svi := fun (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_ : EvalECost st d env e st' v n) (ih : ESpec code T st d env e st' v n) => sVarInit (x := x) hR ih
  have c_svn := fun st d env x => sVarNull (T := T) hR st d env x
  have c_sblk := fun (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr) (st' : St)
    (status : Status) (n : Nat) (halloc : st.store.allocFrame (some env) = (store', inner))
    (_ : ExecSeqCost ⟨store', st.out⟩ d inner ss st' status n)
    (ih : QSpec code T ⟨store', st.out⟩ d inner ss st' status n) => sBlock hR halloc ih
  have c_sift := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt) (st' st'' : St)
    (v : Value) (status : Status) (nc nt : Nat) (_ : EvalECost st d env c st' v nc) (htr : v.truthy = true)
    (_ : ExecSCost st' d env t st'' status nt) (ihc : ESpec code T st d env c st' v nc)
    (iht : SSpec code T st' d env t st'' status nt) => sIfTrue (e := e) hR ihc htr iht
  have c_siff := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt) (st' st'' : St)
    (v : Value) (status : Status) (nc ne : Nat) (_ : EvalECost st d env c st' v nc) (hfa : v.truthy = false)
    (_ : ExecSCost st' d env e st'' status ne) (ihc : ESpec code T st d env c st' v nc)
    (ihe : SSpec code T st' d env e st'' status ne) => sIfFalse (t := t) hR ihc hfa ihe
  have c_sifn := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : St) (v : Value) (nc : Nat)
    (_ : EvalECost st d env c st' v nc) (hfa : v.truthy = false) (ihc : ESpec code T st d env c st' v nc) =>
    sIfNone (t := t) hR ihc hfa
  have c_swf := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : St) (v : Value) (nc : Nat)
    (_ : EvalECost st d env c st' v nc) (hfa : v.truthy = false) (ihc : ESpec code T st d env c st' v nc) =>
    sWhileFalse (b := b) hR ihc hfa
  have c_swb := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : St) (v : Value)
    (nc nb : Nat) (_ : EvalECost st d env c st' v nc) (htr : v.truthy = true) (_ : ExecSCost st' d env b st'' .brk nb)
    (ihc : ESpec code T st d env c st' v nc) (ihb : SSpec code T st' d env b st'' .brk nb) =>
    sWhileBreak hR ihc htr ihb
  have c_swr := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : St) (v rv : Value)
    (nc nb : Nat) (_ : EvalECost st d env c st' v nc) (htr : v.truthy = true)
    (_ : ExecSCost st' d env b st'' (.ret rv) nb)
    (ihc : ESpec code T st d env c st' v nc) (ihb : SSpec code T st' d env b st'' (.ret rv) nb) =>
    sWhileRet hR ihc htr ihb
  have c_swl := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : St) (v : Value)
    (status status' : Status) (nc nb nr : Nat) (_ : EvalECost st d env c st' v nc) (htr : v.truthy = true)
    (_ : ExecSCost st' d env b st'' status nb) (hst : status = .normal ∨ status = .cont)
    (_ : ExecSCost st'' d env (.whileStmt c b) st''' status' nr)
    (ihc : ESpec code T st d env c st' v nc) (ihb : SSpec code T st' d env b st'' status nb)
    (ihw : SSpec code T st'' d env (.whileStmt c b) st''' status' nr) => sWhileLoop hR ihc htr ihb hst ihw
  have c_sfor := fun (st : St) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt)
    (store' : Store) (outer : Addr) (st' st'' : St) (status : Status) (ni nl : Nat)
    (halloc : st.store.allocFrame (some env) = (store', outer))
    (_ : ExecInitCost ⟨store', st.out⟩ d outer init st' ni) (_ : ForLoopCost st' d outer cnd step b st'' status nl)
    (ihi : XISpec code T ⟨store', st.out⟩ d outer init st' ni)
    (ihl : FLSpec code T st' d outer cnd step b st'' status nl) => sForStart hR halloc ihi ihl
  have c_sret := fun (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_ : EvalECost st d env e st' v n) (ih : ESpec code T st d env e st' v n) => sRet hR ih
  have c_srn := fun st d env => sRetNull (T := T) hR st d env
  have c_sbrk := fun st d env => sBrk (T := T) hR st d env
  have c_scont := fun st d env => sCont (T := T) hR st d env
  have c_inone := fun st d env => xiNone (T := T) hR st d env
  have c_isome := fun (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) (status : Status) (n : Nat)
    (_ : ExecSCost st d env s st' status n) (ih : SSpec code T st d env s st' status n) => xiSome hR ih
  have c_lcf := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt) (st' : St)
    (v : Value) (nc : Nat) (_ : EvalECost st d env c st' v nc) (hfa : v.truthy = false)
    (ih : ESpec code T st d env c st' v nc) => flCondFalse (step := step) (b := b) hR ih hfa
  have c_lbb := fun (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : St)
    (nc nb : Nat) (_ : ForCondCost st d env cnd st' nc) (_ : ExecSCost st' d env b st'' .brk nb)
    (ihc : FCSpec code T st d env cnd st' nc) (ihb : SSpec code T st' d env b st'' .brk nb) =>
    flBodyBreak (step := step) hR ihc ihb
  have c_lbr := fun (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : St)
    (rv : Value) (nc nb : Nat) (_ : ForCondCost st d env cnd st' nc) (_ : ExecSCost st' d env b st'' (.ret rv) nb)
    (ihc : FCSpec code T st d env cnd st' nc) (ihb : SSpec code T st' d env b st'' (.ret rv) nb) =>
    flBodyRet (step := step) hR ihc ihb
  have c_lloop := fun (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : St)
    (status status' : Status) (nc nb ns nr : Nat) (_ : ForCondCost st d env cnd st' nc)
    (_ : ExecSCost st' d env b st'' status nb) (hst : status = .normal ∨ status = .cont)
    (_ : ExecStepCost st'' d env step st''' ns) (_ : ForLoopCost st''' d env cnd step b st'''' status' nr)
    (ihc : FCSpec code T st d env cnd st' nc) (ihb : SSpec code T st' d env b st'' status nb)
    (ihs : XSSpec code T st'' d env step st''' ns) (ihl : FLSpec code T st''' d env cnd step b st'''' status' nr) =>
    flLoop hR ihc ihb hst ihs ihl
  have c_cnone := fun st d env => fcNone (T := T) hR st d env
  have c_csome := fun (st : St) (d : Nat) (env : Addr) (c : Expr) (st' : St) (v : Value) (nc : Nat)
    (_ : EvalECost st d env c st' v nc) (htr : v.truthy = true) (ih : ESpec code T st d env c st' v nc) =>
    fcSome hR ih htr
  have c_stnone := fun st d env => xsNone (code := code) (T := T) st d env
  have c_stsome := fun (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_ : EvalECost st d env e st' v n) (ih : ESpec code T st d env e st' v n) => xsSome ih
  have c_qnil := fun st d env => qNil (T := T) hR st d env
  have c_qcn := fun (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : St) (status : Status)
    (n1 n2 : Nat) (_ : ExecSCost st d env s st' .normal n1) (_ : ExecSeqCost st' d env ss st'' status n2)
    (ihs : SSpec code T st d env s st' .normal n1) (ihss : QSpec code T st' d env ss st'' status n2) =>
    qConsNormal hR ihs ihss
  have c_qca := fun (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : St) (status : Status)
    (n : Nat) (_ : ExecSCost st d env s st' status n) (hne : status ≠ .normal)
    (ih : SSpec code T st d env s st' status n) => qConsAbrupt (ss := ss) hR ih hne
  exact ⟨fun h => EvalECost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => EvalArgsCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => CallCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => ExecSCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => ExecInitCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => ForLoopCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => ForCondCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => ExecStepCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
    fun h => ExecSeqCost.rec (motive_1 := fun st d a e st' v n _ => ESpec code T st d a e st' v n) (motive_2 := fun st d a es st' vs n _ => ASpec code T st d a es st' vs n) (motive_3 := fun st d fv vs st' v n _ => CSpec code T st d fv vs st' v n) (motive_4 := fun st d a s st' t n _ => SSpec code T st d a s st' t n) (motive_5 := fun st d a i st' n _ => XISpec code T st d a i st' n) (motive_6 := fun st d a c s b st' t n _ => FLSpec code T st d a c s b st' t n) (motive_7 := fun st d a c st' n _ => FCSpec code T st d a c st' n) (motive_8 := fun st d a s st' n _ => XSSpec code T st d a s st' n) (motive_9 := fun st d a ss st' t n _ => QSpec code T st d a ss st' t n)
      c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h⟩

end

end Vsa.Compiler
