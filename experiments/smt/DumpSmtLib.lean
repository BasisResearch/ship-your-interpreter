import Vsa.Sim.EvalSimCommon

/-!
# `dump_smt_lib` — a Lean-side SMT-LIB2 EXPORT tactic (encoder v2)

`dump_smt_lib "<path>" for <PropName>` walks the ELABORATED body of a
`Prop`-valued constant and writes an SMT-LIB2 encoding of its NEGATION
(the `--refute` query: `(∧ hyps) ∧ ¬concl` SAT ⟺ the statement has a
countermodel in the encoded fragment) to `<path>`.

It PROVES NOTHING — it is a pure exporter run as an `elab` COMMAND (never a
tactic that closes a goal, never wired into `Vsa.lean`), so Law 2 is untouched:
no `sorry`/`axiom`/`native_decide` anywhere.  Elaborated via `lake env lean`.

Metaprogram precedents: `Vsa/Sim/RepackTac.lean`, `Vsa/Sim/ChainFactsTac.lean`,
`Vsa/Sim/DeriveCase.lean`.

## Unfolding policy (the principled OPAQUE boundary)

Walking the real elaborated `Expr` — not a Python re-parse of the source — lets
the boundary between "unfold to arithmetic/array form" and "leave uninterpreted"
be a WHNF decision rather than a hand-maintained name list:

* REDUCIBLE arithmetic + window predicates are unfolded to their SMT forms:
  - `BitVec 64/32/8` binders → SMT `BitVec` of that width, plus an `Int`
    `.toNat` mirror pinned `0 ≤ v < 2^w`;
  - `Nat`/`Int` → `Int` (`Nat` carries `≥ 0`);
  - `Mem = Std.ExtHashMap Nat (BitVec 8)` → a `(def : Array Int Bool, val :
    Array Int (BitVec 8))` pair; `m[a]? = some b ↦ (select def a) ∧ (select
    val a) = b`; `m[a]? = m0[a]? ↦ defs agree ∧ vals agree`;
  - `MemExtends m0 m` WHNF-unfolds to `∀ a b, m0[a]? = some b → ∃ b', m[a]? =
    some b'` and is emitted as `∀ za, def0 za → def za`;
  - `StackOK SL sp k` WHNF-unfolds to `lo+k ≤ sp ∧ sp ≤ hi ∧ sp%16 = 0`;
  - `.lo`/`.hi` projections, `HAdd/HSub/HMod/HMul` (Nat `-` is TRUNCATED:
    `ite (≥) (-) 0`, honest so a VALIDATE UNSAT stays sound), `Nat.succ`,
    `OfNat` literals, `<`(= `succ ≤`), `≤`, `=`, `∧`, `∨`, `¬`, `∃`, `∀`.

* Everything whose head does NOT reduce into that vocabulary — the genuinely
  SEMANTIC predicates `ValueRepr`/`ExprRepr`/`CString`/`GoodState`/`StoreRepr`/
  `FoundSt`/`Approx`/`Loaded`/`InterpSim`/`frameRepr`/… — is left as an
  UNINTERPRETED 0-ary Bool symbol (one per distinct atom text).  A model that
  hinges on such a symbol ⇒ the Python driver reports REFUTED-MODULO-OPAQUE and
  does NOT auto-replay.  The exporter records the set of opaque heads it emitted
  as an SMT comment (`; OPAQUE: …`) so the driver can read it back.

If any atom cannot be encoded even as an opaque symbol (should not happen — the
fallback is total) the exporter writes `; ENCODE-GAP: <atom>` and the driver
falls back to its Python encoder for that file.
-/

open Lean Elab Meta Command

namespace Vsa.SmtExport

/-- Semantic-predicate head stems: an atom whose (un-whnf'd) head constant name
contains one of these is emitted as an uninterpreted Bool.  This mirrors the
Python `OPAQUE_HEADS` list but is only consulted AFTER whnf-unfolding failed to
produce arithmetic/array structure, so it is a backstop, not the primary
boundary. -/
def opaqueStems : List String :=
  ["ValueRepr", "ExprRepr", "CString", "GoodState", "Repr", "Loaded",
   "InterpSim", "FoundSt", "Approx", "StoreRepr", "frameRepr"]

/-- Accumulated exporter state. -/
structure St where
  decls    : Array String := #[]     -- (declare-fun …) lines, de-duplicated
  aux      : Array String := #[]     -- side pins (mirror ranges etc.)
  declared : Std.HashSet String := {} -- keys already declared
  opaqueHeads : Std.HashSet String := {} -- opaque heads emitted
  gaps     : Array String := #[]     -- atoms that could not be encoded
  fresh    : Nat := 0                 -- fresh-name counter (opaque symbols)
  deriving Inhabited

abbrev ExpM := StateRefT St MetaM

def emitDecl (line key : String) : ExpM Unit := do
  let s ← get
  if s.declared.contains key then return
  set { s with decls := s.decls.push line, declared := s.declared.insert key }

def emitAux (line : String) : ExpM Unit :=
  modify fun s => { s with aux := s.aux.push line }

def noteGap (atom : String) : ExpM Unit :=
  modify fun s => { s with gaps := s.gaps.push atom }

/-- SMT-safe token for an fvar / bound name. -/
def smtName (n : Name) : String :=
  let s := n.toString.replace "." "_"
  String.mk (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')

/-- A sort classification for a binder / fvar. -/
inductive VSort where
  | bv (w : Nat)       -- BitVec of width w (with an Int .toNat mirror _n)
  | int                -- Nat/Int → Int
  | mem                -- Mem → (def,val) array pair
  | sl                 -- StackLayout → _lo,_hi Ints
  | other              -- ghost structure / unknown
  deriving Inhabited, BEq

/-- Classify a binder TYPE expression into a `Sort`. -/
def classifyTy (ty : Expr) : MetaM VSort := do
  let ty ← whnf ty
  match ty with
  | .const ``Nat _ => return .int
  | .const ``Int _ => return .int
  | _ =>
    if ty.isAppOfArity ``BitVec 1 then
      match (← getNatValue? ty.appArg!) with
      | some w => return .bv w
      | none   => return .bv 64
    else if ty.isAppOfArity ``Std.ExtHashMap 4 then
      return .mem            -- Mem = ExtHashMap Nat (BitVec 8)
    else if ty.isConstOf ``Vsa.Alloc.StackLayout then
      return .sl
    else
      return .other

/-- Declare an fvar according to its sort; return the SMT sort tag. -/
def declFVar (fv : FVarId) : ExpM VSort := do
  let ty ← fv.getType
  let s ← liftM (classifyTy ty)
  let nm := smtName (← fv.getUserName)
  match s with
  | .bv w =>
    emitDecl s!"(declare-fun {nm} () (_ BitVec {w}))" nm
    emitDecl s!"(declare-fun {nm}_n () Int)" s!"{nm}_n"
    emitAux s!"(assert (= {nm}_n (bv2int {nm})))"
    emitAux s!"(assert (>= {nm}_n 0))"
  | .int =>
    emitDecl s!"(declare-fun {nm} () Int)" nm
    -- Nat carries ≥ 0
    if (← whnf ty).isConstOf ``Nat then emitAux s!"(assert (>= {nm} 0))"
  | .mem =>
    emitDecl s!"(declare-fun {nm}_def () (Array Int Bool))" s!"{nm}_def"
    emitDecl s!"(declare-fun {nm}_val () (Array Int (_ BitVec 8)))" s!"{nm}_val"
  | .sl =>
    emitDecl s!"(declare-fun {nm}_lo () Int)" s!"{nm}_lo"
    emitDecl s!"(declare-fun {nm}_hi () Int)" s!"{nm}_hi"
    emitAux s!"(assert (>= {nm}_lo 0))"
    emitAux s!"(assert (>= {nm}_hi 0))"
  | .other => pure ()
  return s

/-- Fresh opaque Bool symbol keyed on an atom's pretty text (so equal atoms
share a symbol). -/
def opaqueSym (head : String) (atom : Expr) : ExpM String := do
  let txt := (toString (← liftM (ppExpr atom)))
  let key := "op_" ++ String.mk ((txt.toList.filter (·.isAlphanum)).take 40)
  emitDecl s!"(declare-fun {key} () Bool)" key
  modify fun s => { s with opaqueHeads := s.opaqueHeads.insert head }
  return key

-- ==========================================================================
-- integer/Nat term encoding (over the .toNat / .lo mirrors)
-- ==========================================================================

/-- Encode an integer/Nat-valued `Expr` to an SMT Int term, or `none` if it is
not in the arithmetic fragment.  Does NOT whnf (projections/`.toNat` must be
matched syntactically). -/
partial def encInt (e : Expr) : ExpM (Option String) := do
  -- literal
  match (← getNatValue? e) with
  | some n => return some (toString n)
  | none => pure ()
  match e with
  | .fvar fv =>
    let nm := smtName (← fv.getUserName)
    let s ← liftM (classifyTy (← fv.getType))
    match s with
    | .int  => return some nm
    | .bv _ => return some s!"{nm}_n"
    | _     => return none
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    -- BitVec.toNat x   → x_n
    if e.isAppOfArity ``BitVec.toNat 2 then
      match args[1]! with
      | .fvar fv => return some s!"{smtName (← fv.getUserName)}_n"
      | _ => return none
    -- StackLayout.lo/.hi SL → SL_lo/_hi
    if let .const c _ := fn then
      if c == ``Vsa.Alloc.StackLayout.lo || c == ``Vsa.Alloc.StackLayout.hi then
        let proj := if c == ``Vsa.Alloc.StackLayout.lo then "lo" else "hi"
        match args[0]! with
        | .fvar fv => return some s!"{smtName (← fv.getUserName)}_{proj}"
        | _ => return none
      -- Nat.succ x → (+ x 1)
      if c == ``Nat.succ then
        match ← encInt args[0]! with
        | some t => return some s!"(+ {t} 1)"
        | none => return none
    -- OfNat.ofNat _ n _  (already caught by getNatValue? in most cases)
    -- binary HAdd/HSub/HMul/HMod: last two args are the operands
    let bin? : Option String :=
      if e.isAppOfArity ``HAdd.hAdd 6 then some "+"
      else if e.isAppOfArity ``HSub.hSub 6 then some "-"
      else if e.isAppOfArity ``HMul.hMul 6 then some "*"
      else if e.isAppOfArity ``HMod.hMod 6 then some "mod"
      else none
    match bin? with
    | some op =>
      let l ← encInt args[4]!
      let r ← encInt args[5]!
      match l, r with
      | some l, some r =>
        if op == "-" then
          -- TRUNCATED Nat subtraction: max(0, l-r)
          return some s!"(ite (>= {l} {r}) (- {l} {r}) 0)"
        else return some s!"({op} {l} {r})"
      | _, _ => return none
    | none => return none
  | _ => return none

/-- Encode a BitVec-8 value literal / bound var for a `some b` payload. -/
def encBv8 (e : Expr) (bound : Option (Name × String)) : ExpM (Option String) := do
  match (← getBitVecValue? e) with
  | some ⟨_, v⟩ => return some s!"(_ bv{v.toNat} 8)"
  | none =>
    match e, bound with
    | .fvar fv, some (bn, bsmt) => if (← fv.getUserName) == bn then return some bsmt else return none
    | _, _ => return none

/-- Get the collection + index of a `getElem?` application, as (memName, idxSmt),
or `none` if not a `Mem`-indexed lookup in the fragment.  `bound` threads the
inner-∀ address var. -/
def memLookup (e : Expr) (bound : Option (Name × String)) :
    ExpM (Option (String × String)) := do
  if e.isAppOfArity ``getElem? 7 then
    let args := e.getAppArgs
    let coll := args[5]!
    let idx  := args[6]!
    let memNm? : Option String := match coll with
      | .fvar fv => some (smtName fv.name)
      | _ => none
    match memNm? with
    | none => return none
    | some _ =>
      -- resolve fvar user name for the mem
      let .fvar cfv := coll | return none
      let memNm := smtName (← cfv.getUserName)
      let idxSmt ← match idx, bound with
        | .fvar ifv, some (bn, bsmt) =>
          if (← ifv.getUserName) == bn then pure (some bsmt)
          else encInt idx
        | _, _ => encInt idx
      match idxSmt with
      | some i => return some (memNm, i)
      | none => return none
  else return none

-- ==========================================================================
-- Prop encoding
-- ==========================================================================

mutual

/-- Encode a Prop-valued `Expr` (hypothesis, conclusion, atom, or nested
quantifier) to an SMT Bool term.  `bound` threads the innermost address ∀ var
(name, SMT symbol).  Returns `none` only on total failure (records a gap). -/
partial def encProp (e0 : Expr) (bound : Option (Name × String)) :
    ExpM (Option String) := do
  let e := e0
  -- ∀ …  (dependent arrow): non-Prop domain ⇒ quantifier; Prop domain ⇒ →
  match e with
  | .forallE nm dom body _ =>
    if (← liftM (Meta.isProp dom)) then
      -- implication  dom → body.  Open the hyp binder so `body` has no loose
      -- bvar (the hyp proof is unused in the encodable fragment).
      let eh ← encProp dom bound
      let ec ← controlAt MetaM fun runInBase =>
        Meta.withLocalDeclD nm dom fun fv => runInBase (encProp (body.instantiate1 fv) bound)
      match eh, ec with
      | some h, some c => return some s!"(=> {h} {c})"
      | _, _ => return none
    else
      -- genuine ∀.  Introduce as an SMT quantifier.
      -- Mem-typed → two Array-sorted qvars; else an Int qvar.
      let s ← liftM (classifyTy dom)
      let bn := smtName nm
      let (qdecl, newBound) : String × Option (Name × String) := match s with
        | .mem => (s!"({bn}_def (Array Int Bool)) ({bn}_val (Array Int (_ BitVec 8)))", bound)
        | _    => (s!"({bn} Int)", some (nm, bn))
      -- open the body under a temporary fvar so getElem?/arith see the binder
      let r ← controlAt MetaM fun runInBase =>
        Meta.withLocalDeclD nm dom fun fv => runInBase do
          encProp (body.instantiate1 fv) newBound
      match r with
      | some c => return some s!"(forall ({qdecl}) {c})"
      | none => return none
  | _ => encAtom e bound

/-- Encode a single atomic Prop (no leading ∀/→ at top level). -/
partial def encAtom (e0 : Expr) (bound : Option (Name × String)) :
    ExpM (Option String) := do
  let e := e0
  -- ¬ P
  if e.isAppOfArity ``Not 1 then
    match ← encProp e.appArg! bound with
    | some p => return some s!"(not {p})"
    | none => return none
  -- P ∧ Q
  if e.isAppOfArity ``And 2 then
    let a := e.getAppArgs
    match ← encProp a[0]! bound, ← encProp a[1]! bound with
    | some x, some y => return some s!"(and {x} {y})"
    | _, _ => return none
  -- P ∨ Q
  if e.isAppOfArity ``Or 2 then
    let a := e.getAppArgs
    match ← encProp a[0]! bound, ← encProp a[1]! bound with
    | some x, some y => return some s!"(or {x} {y})"
    | _, _ => return none
  -- ∃ x, P   (Exists α (fun x => P))
  if e.isAppOfArity ``Exists 2 then
    let a := e.getAppArgs
    let p := a[1]!
    match p with
    | .lam nm dom pb _ =>
      -- ∃ b, m[i]? = some b  ⇒  (select mem_def i)   (presence)
      -- general: introduce an Int/BV qvar; keep it simple — presence only.
      let r ← controlAt MetaM fun runInBase =>
        Meta.withLocalDeclD nm dom fun fv => runInBase do
        let pb' := pb.instantiate1 fv
        -- detect  <mem>[i]? = some <fv>
        match pb' with
        | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
          match ← memLookup lhs bound with
          | some (mem, idx) =>
            -- rhs = some fv ?
            if rhs.isAppOfArity ``Option.some 2 then
              match rhs.appArg! with
              | .fvar rfv => if (← rfv.getUserName) == nm then
                               return some s!"(select {mem}_def {idx})"
                             else return none
              | _ => return none
            else return none
          | none => return none
        | _ => return none
      match r with
      | some x => return some x
      | none => return none
    | _ => return none
  -- Eq : membership lookups first, then integer equality
  if e.isAppOfArity ``Eq 3 then
    let a := e.getAppArgs
    let lhs := a[1]!; let rhs := a[2]!
    -- m[i]? = some b
    match ← memLookup lhs bound with
    | some (mem, idx) =>
      if rhs.isAppOfArity ``Option.some 2 then
        match ← encBv8 rhs.appArg! bound with
        | some b => return some s!"(and (select {mem}_def {idx}) (= (select {mem}_val {idx}) {b}))"
        | none => pure ()
      -- m[i]? = m0[j]?   (defs + vals agree)
      match ← memLookup rhs bound with
      | some (m2, i2) =>
        return some s!"(and (= (select {mem}_def {idx}) (select {m2}_def {i2})) (= (select {mem}_val {idx}) (select {m2}_val {i2})))"
      | none => pure ()
      return none
    | none => pure ()
    -- integer equality
    match ← encInt lhs, ← encInt rhs with
    | some l, some r => return some s!"(= {l} {r})"
    | _, _ => pure ()
  -- ≤ / < (LE.le / LT.lt with 4 args: α inst lhs rhs)
  for (nm, sym, succTweak) in [(``LE.le, "<=", false), (``LT.lt, "<", false)] do
    if e.isAppOfArity nm 4 then
      let a := e.getAppArgs
      match ← encInt a[2]!, ← encInt a[3]! with
      | some l, some r =>
        let _ := succTweak
        return some s!"({sym} {l} {r})"
      | _, _ => pure ()
  -- Nat.le / Nat.lt (post-whnf 2-arg form; < is succ ≤)
  if e.isAppOfArity ``Nat.le 2 then
    let a := e.getAppArgs
    match ← encInt a[0]!, ← encInt a[1]! with
    | some l, some r => return some s!"(<= {l} {r})"
    | _, _ => pure ()
  if e.isAppOfArity ``Nat.lt 2 then
    let a := e.getAppArgs
    match ← encInt a[0]!, ← encInt a[1]! with
    | some l, some r => return some s!"(< {l} {r})"
    | _, _ => pure ()
  -- Ne a b  →  ¬ (a = b)
  if e.isAppOfArity ``Ne 3 then
    let a := e.getAppArgs
    match ← encInt a[1]!, ← encInt a[2]! with
    | some l, some r => return some s!"(not (= {l} {r}))"
    | _, _ => pure ()
  -- No syntactic match: try WHNF-unfolding a reducible predicate
  -- (StackOK, MemExtends, …) exactly ONCE, then re-encode.
  let head := e.getAppFn
  match head with
  | .const c _ =>
    let cn := c.toString
    -- opaque backstop: genuinely semantic heads are uninterpreted
    if opaqueStems.any (fun stem => (cn.splitOn stem).length > 1) then
      return some (← opaqueSym cn e)
    -- try to unfold the definition once and re-encode
    let e' ← whnf e
    if e' != e then
      return (← encProp e' bound)
    else
      return some (← opaqueSym cn e)   -- irreducible non-arith head ⇒ opaque
  | _ =>
    -- unknown non-const head that we could not reduce
    noteGap (toString (← liftM (ppExpr e)))
    return none

end   -- mutual encProp / encAtom

-- ==========================================================================
-- top-level: split the statement into (hyps, concl) and build the SMT file
-- ==========================================================================

/-- Split the body's top-level `→` chain into hyps + conclusion, encoding each
into the shared `ExpM` state.  A top-level `∀` (non-Prop domain) inside the BODY
means "the whole body is one conclusion" (no more top-level hyps). -/
partial def encStatement (bodyE : Expr) : ExpM (Array String × Option String) := do
  let rec go (e : Expr) (hyps : Array String) : ExpM (Array String × Option String) := do
    match e with
    | .forallE nm dom body _ =>
      let body0 := body.instantiate1 (mkConst ``True)  -- dummy; hyp proof unused
      if (← liftM (Meta.isProp dom)) && !body0.hasLooseBVars then
        match ← encProp dom none with
        | some h => go body0 (hyps.push h)
        | none => return (hyps, ← encProp e none)
      else
        return (hyps, ← encProp e none)
    | _ => return (hyps, ← encProp e none)
  go bodyE #[]

/-- Introduce the OUTER data telescope as fvars (declaring each in SMT), then
encode the remaining body — all in ONE shared `ExpM` state.  `withLocalDeclD`
runs the recursion INSIDE its callback so the fvar stays in scope, and the
`StateRefT` state (an `IO.Ref`) survives across the callback boundary. -/
partial def runExportM (e0 : Expr) : ExpM (Array String × Option String) := do
  match e0 with
  | .forallE nm dom body _ =>
    if (← liftM (Meta.isProp dom)) then
      encStatement e0
    else
      controlAt MetaM fun runInBase =>
        Meta.withLocalDeclD nm dom fun fv => runInBase do
          let _ ← declFVar fv.fvarId!
          runExportM (body.instantiate1 fv)
  | _ => encStatement e0

partial def runExport (name : Name) : MetaM (St × Array String × Option String) := do
  let info ← getConstInfo name
  let e := info.value!
  let ((hyps, concl), st) ← (runExportM e).run {}
  return (st, hyps, concl)

/-- Assemble the SMT-LIB2 file text (negated statement for refutation). -/
def buildSmt (st : St) (hyps : Array String) (concl : Option String) : String := Id.run do
  let mut lines := #["(set-logic ALL)"]
  for d in st.decls do lines := lines.push d
  for a in st.aux do lines := lines.push a
  -- negated statement:  (and hyps…) ∧ ¬concl
  match concl with
  | some c =>
    if hyps.isEmpty then
      lines := lines.push s!"(assert (not {c}))"
    else
      let conj := "(and " ++ String.intercalate " " hyps.toList ++ ")"
      lines := lines.push s!"(assert {conj})"
      lines := lines.push s!"(assert (not {c}))"
  | none => lines := lines.push "; ENCODE-GAP: conclusion unencodable"
  lines := lines.push "(check-sat)"
  lines := lines.push "(get-model)"
  -- metadata comments the Python driver reads back
  let opq := String.intercalate " " st.opaqueHeads.toList
  let gaps := String.intercalate " | " st.gaps.toList
  lines := lines.push s!"; OPAQUE: {opq}"
  if !st.gaps.isEmpty then lines := lines.push s!"; GAPS: {gaps}"
  return String.intercalate "\n" lines.toList ++ "\n"

end Vsa.SmtExport

open Vsa.SmtExport in
/-- `dump_smt_lib "<path>" for <PropName>` — write the SMT-LIB2 refutation query
for the named `Prop` constant to `<path>`.  Proves nothing. -/
elab "dump_smt_lib " pathStx:str " for " nameStx:ident : command => do
  let path := pathStx.getString
  liftTermElabM do
    let name ← resolveGlobalConstNoOverload nameStx
    let (st, hyps, concl) ← runExport name
    let txt := buildSmt st hyps concl
    IO.FS.writeFile path txt
    logInfo m!"dump_smt_lib → {path} ({st.decls.size} decls, {hyps.size} hyps, opaque={st.opaqueHeads.toList}, gaps={st.gaps.size})"
