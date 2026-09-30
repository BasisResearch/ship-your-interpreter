import VsaIris.Vsa.SymExec
import VsaIris.Interp.ITac

/-!
# The symbolic route for `IW` runs

* `codeAt_interp`: `interpText` pins its code and constant-table ranges to the binary image.
* `geomOf`: the `Geom` a run needs, read off its own obligations (per atom: the offset span,
  the store alignment, the `S`/`DA` cover ranges and the HTIF gap). `geom_auto` then proves it
  from the piece's hypotheses, so no piece writes a `Geom` by hand.
* `sym_run`: the `ix_run` surface (`sym_run [n] hlive using [facts] at pcs`). It runs the
  executor once, closes the checked obligations and the decode facts, prunes branches and
  normalises continuations exactly as `ix_run` does, and hands back the same leftover goals.
  Any failure falls back to `ix_run`.
-/

namespace VsaIris.SymExec.Interp

open VsaIris VsaIris.Sym VsaIris.SymExec Vsa.Sim Vsa.MemRepr Vsa.Sim.Code VsaIris.MallocFast
open LeanRV64DExecutable (bop)

/-- Byte function of the loaded binary (text, then read-only data). -/
def binByte (a : Nat) : BitVec 8 :=
  if a < 0x80018be0 then fixedTextByte (a - 0x80000000) else fixedRodataByte (a - 0x80018be0)

/-- The ranges of `interpText` (code, then constant tables). -/
def interpRanges : List (Nat × Nat) := interpCodeRanges ++ interpRORanges

theorem codeAt_interp : CodeAt interpText binByte interpRanges :=
  codeAt_of_pieces (ps := interpCodePieces) (qs := interpROPieces)
    (fun _ hm => ⟨TextIn.left hm, TextIn.right hm⟩) (by decide +kernel)

/-- Executor configuration for `IW` runs. -/
def cfgI (stops : List (BitVec 64)) (dbase : List SE := [])
    (kv : List (MKind × SE × BitVec 64) := []) : Cfg :=
  ⟨binByte, interpRanges, iRegs, stops, dbase, kv⟩

/-! ## The `Geom` of a run, from its obligations -/

def Tree.obs : Tree → List SOb
  | .leaf s => s.obs
  | .br _ _ _ _ t f => Tree.obs t ++ Tree.obs f
  | .jr s _ => s.obs

/-- Leaves with a literal continuation pc. -/
def Tree.leaves : Tree → List SS
  | .leaf s => [s]
  | .br _ _ _ _ t f => Tree.leaves t ++ Tree.leaves f
  | .jr _ _ => []

/-- Merge a list of half-open ranges. -/
def mergeR (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  let s := (rs.toArray.qsort fun a b => a.1 < b.1).toList
  s.foldl (fun acc r => match acc with
    | (l, h) :: t => if r.1 ≤ h then (l, max h r.2) :: t else r :: (l, h) :: t
    | [] => [r]) [] |>.reverse

/-- Kinds of address need: 0 owned read, 1 data-view read, 2 owned write, 3 alignment. -/
structure Need where
  atom : SE
  offs : List (BitVec 64 × Nat × Nat)

def needOf (o : SOb) : Option (SE × BitVec 64 × Nat × Nat) :=
  match o with
  | .ld e w => some ((base e).1, (base e).2, w, 0)
  | .ldD e w => some ((base e).1, (base e).2, w, 1)
  | .st e w => some ((base e).1, (base e).2, w, 2)
  | .al4 e => some ((base e).1, (base e).2, 0, 3)
  | _ => none

def addNeed (ns : List Need) (o : SOb) : List Need :=
  match needOf o with
  | none => ns
  | some (a, off, w, k) =>
    if a = .c 0 then ns else
    if ns.any (·.atom = a) then
      ns.map fun n => if n.atom = a then { n with offs := (off, w, k) :: n.offs } else n
    else ⟨a, [(off, w, k)]⟩ :: ns

def signedOf (o : BitVec 64) : Int := if o.toNat ≥ 2 ^ 63 then (o.toNat : Int) - 2 ^ 64 else o.toNat

def factOf (n : Need) : AFact :=
  let m := (n.offs.map fun e => signedOf e.1).foldl min 0
  let shift : BitVec 64 := BitVec.ofInt 64 m
  let rel (o : BitVec 64) : Nat := (o - shift).toNat
  let spans := (n.offs.filter (·.2.2 ≠ 3)).map fun e => (rel e.1, rel e.1 + e.2.1)
  let stores := (n.offs.filter (·.2.2 = 2)).map fun e => (rel e.1, rel e.1 + e.2.1)
  let al4 := n.offs.any (·.2.2 = 3)
  let maxRel := (n.offs.map fun e => rel e.1 + e.2.1).foldl max 0
  let omin := (spans.map (·.1)).foldl min (2 ^ 64)
  let omax := (spans.map (·.2)).foldl max 0
  let smin := (stores.map (·.1)).foldl min (2 ^ 64)
  let am0 := (stores.map fun r => r.2 - r.1).foldl max 1
  let am := if al4 then max am0 4 else am0
  let lo := if spans.isEmpty then 0 else
    max (0x80000000 - omin) (if stores.isEmpty then 0 else tohostAddr + 16 - smin)
  let hi := if spans.isEmpty then 2 ^ 64 - 1 - maxRel else 0x100000000 - omax
  { atom := n.atom, lo := lo, hi := hi, amod := am,
    sc := mergeR ((n.offs.filter fun e => e.2.2 = 0 ∨ e.2.2 = 2).map fun e => (rel e.1, rel e.1 + e.2.1)),
    dc := mergeR ((n.offs.filter (·.2.2 = 1)).map fun e => (rel e.1, rel e.1 + e.2.1)),
    gap := if spans.isEmpty then none else some (omax, 8 - omin), shift := shift }

def geomOf (obs : List SOb) : Geom := ((obs.foldl addNeed []).map factOf).reverse

/-- Atoms whose owned reads are needed. -/
def ownedReadAtoms (obs : List SOb) : List SE :=
  obs.filterMap fun o => match o with
    | .ld e _ => if (base e).1 = .c 0 then none else some (base e).1
    | _ => none

/-! ## Branch premises in the landed step-lemma form -/

theorem gF_beq (a b : BitVec 64) : guardB .BEQ a b = false ↔ ¬ (a = b) := guard_false (guard_beq a b)
theorem gF_bne (a b : BitVec 64) : guardB .BNE a b = false ↔ ¬ (a ≠ b) := guard_false (guard_bne a b)
theorem gF_blt (a b : BitVec 64) : guardB .BLT a b = false ↔ ¬ (a.toInt < b.toInt) :=
  guard_false (guard_blt a b)
theorem gF_bge (a b : BitVec 64) : guardB .BGE a b = false ↔ ¬ (b.toInt ≤ a.toInt) :=
  guard_false (guard_bge a b)
theorem gF_bltu (a b : BitVec 64) : guardB .BLTU a b = false ↔ ¬ (a.toNat < b.toNat) :=
  guard_false (guard_bltu a b)
theorem gF_bgeu (a b : BitVec 64) : guardB .BGEU a b = false ↔ ¬ (b.toNat ≤ a.toNat) :=
  guard_false (guard_bgeu a b)

/-! ## The driver -/

open Lean Meta Elab Tactic

register_option sym_run.trace : Bool := { defValue := false, descr := "report sym_run fallbacks" }

syntax "sym_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

def mkindOf? (n : Name) : Option MKind :=
  if n == ``MKind.lw then some .lw else if n == ``MKind.lwu then some .lwu
  else if n == ``MKind.ld then some .ld else if n == ``MKind.lbu then some .lbu
  else if n == ``MKind.lh then some .lh else if n == ``MKind.lhu then some .lhu else none

/-- Replace the last three arguments (pc, registers, memory) of the landed goal head. -/
def withState (ty0 pc R M : Expr) : Expr :=
  let args := ty0.getAppArgs
  mkAppN ty0.getAppFn (args.extract 0 (args.size - 3) ++ #[pc, R, M])

def headConsts (e : Expr) : Array Name :=
  match e.getAppFn with
  | .const n _ =>
    if n == ``accAddrs || n == ``HAppend.hAppend || n == ``List.nil then #[] else #[n]
  | _ => #[]

def contNorm (ty0 : Expr) (norm : Syntax) (l0facts : Array Term) (gk : MVarId) :
    TacticM MVarId := do
  let [gk] ← evalTacticAt (← `(tactic| (try simp only [regsDen, memDen, SE.den, aluVal]))) gk
    | throwError "sym_run: continuation"
  let kty ← whnfR (← instantiateMVars (← gk.getType))
  let a := kty.getAppArgs
  unless kty.getAppFn.isConstOf ``SWP && a.size == 8 do throwError "sym_run: not SWP"
  let gk ← gk.replaceTargetDefEq (withState ty0 a[5]! a[6]! a[7]!)
  let gk ← do
    let mut gk := gk
    for f in l0facts do
      let saved ← saveState
      try
        match ← evalTacticAt (← `(tactic| rw [upd_self_eq $f])) gk with
        | [g'] => gk := g'
        | _ => saved.restore
      catch _ => saved.restore
    pure gk
  let gk ← do
    let saved ← saveState
    try
      match ← evalTacticAt norm gk with
      | [g'] => pure g'
      | _ => saved.restore; pure gk
    catch _ => saved.restore; pure gk
  return gk

def symLeaf (ty0 : Expr) (norm : Syntax) (l0facts : Array Term) (go gk : MVarId)
    (withCont : Bool := true) : TacticM (List MVarId × List MVarId) := do
  -- obligations
  let mut pend : List MVarId := []
  let mut cur := go
  repeat
    let t ← instantiateMVars (← cur.getType)
    let l := t.getAppArgs.back!
    if l.isAppOf ``List.nil then
      let [] ← cur.apply (mkConst ``ObsOK_nil) | throwError "sym_run: obs"
      break
    let [ho, hr] ← cur.apply (mkConst ``ObsOK_cons) | throwError "sym_run: obs"
    let [ho] ← evalTacticAt (← `(tactic| simp only [SOb.den])) ho | throwError "sym_run: obs"
    let hty ← instantiateMVars (← ho.getType)
    if hty.isAppOfArity ``DecM 1 || hty.isAppOfArity ``DecT 1 then
      let [] ← evalTacticAt (← `(tactic| sym_dec)) ho | throwError "sym_run: dec"
    else
      let isAl4 := (← instantiateMVars (← ho.getType)).isAppOf ``Eq &&
        ((← instantiateMVars (← ho.getType)).getAppArgs[1]?.map (·.isAppOf ``HMod.hMod)).getD false
      let saved ← saveState
      try
        let gs ← evalTacticAt (← `(tactic| (simp only [SE.den, aluVal] <;> ($(⟨norm⟩) <;> sx_side)))) ho
        unless gs.isEmpty do throwError "open"
      catch _ =>
        saved.restore
        -- an unproved alignment of a return target is a pending side goal, as in `ix_run`;
        -- any other undecided memory obligation means the landed route used another rule
        unless isAl4 do
          if (← getOptions).getBool `sym_run.trace false then
            IO.eprintln s!"sym_run undecided: {← ppGoal ho}"
          throwError "sym_run: undecided memory obligation"
        let [ho'] ← evalTacticAt (← `(tactic| (try simp only [SE.den, aluVal]))) ho
          | throwError "sym_run: obligation"
        let ho' ← do
          let saved ← saveState
          try
            match ← evalTacticAt norm ho' with
            | [g'] => pure g'
            | _ => saved.restore; pure ho'
          catch _ => saved.restore; pure ho'
        pend := pend ++ [ho']
    cur := hr
  if withCont then return (pend, [← contNorm ty0 norm l0facts gk]) else return (pend, [])

/-- A branch that `ix_run1` would leave unexplored: both premises are returned with the
landed step-lemma premise (`P (R' r₁) (R' r₂) → …`) over the pre-branch register chain. -/
def branchStuck (ty0 : Expr) (norm : Syntax) (l0facts : Array Term) (g : MVarId)
    (op : bop) (r1 r2 : Nat) (taken : Bool) : TacticM MVarId := do
  -- g : guardB op (den a) (den b) = taken → Tree.WP … (Tree.leaf t0)
  let [g1] ← evalTacticAt (← `(tactic| intro hg)) g | throwError "sym_run1: intro"
  g1.withContext do
  let hg := (← getLCtx).lastDecl.get!.toExpr
  let [go, gk] ← g1.apply (mkConst ``Tree.WP_leaf) | throwError "sym_run1: leaf"
  let (pend, [gk']) ← symLeaf ty0 norm l0facts go gk | throwError "sym_run1: leaf"
  unless pend.isEmpty do throwError "sym_run1: pending"
  gk'.withContext do
  let N ← instantiateMVars (← gk'.getType)
  let w ← whnfR N
  let R' := w.getAppArgs[6]!
  let opnd (r : Nat) : Expr := if r = 0 then toExpr (0 : BitVec 64) else mkApp R' (mkNatLit r)
  let x := opnd r1
  let y := opnd r2
  let lem := match op, taken with
    | .BEQ, true => ``guard_beq | .BNE, true => ``guard_bne | .BLT, true => ``guard_blt
    | .BGE, true => ``guard_bge | .BLTU, true => ``guard_bltu | .BGEU, true => ``guard_bgeu
    | .BEQ, false => ``gF_beq | .BNE, false => ``gF_bne | .BLT, false => ``gF_blt
    | .BGE, false => ``gF_bge | .BLTU, false => ``gF_bltu | .BGEU, false => ``gF_bgeu
  let li := mkApp2 (mkConst lem) x y
  let some (_, P) := (← inferType li).iff? | throwError "sym_run1: guard"
  let G ← g.withContext do mkFreshExprMVar (← mkArrow P N)
  let pf ← mkAppM ``Iff.mp #[li, hg]
  gk'.assign (mkApp G pf)
  return G.mvarId!

/-- A branch side that reaches a stop point with no further step: as in `ix_run`, the branch
premise stays in the step-lemma form over the pre-branch register chain and only the
continuation is normalised. -/
def zeroStepChild (ty0 : Expr) (norm : Syntax) (l0facts : Array Term) (facts : Array Term)
    (cg : MVarId) (op : bop) (r1 r2 : Nat) (taken : Bool) : TacticM (List MVarId × MVarId) := do
  let outer ← cg.getDecl
  let [cg1] ← evalTacticAt (← `(tactic| intro hc)) cg | throwError "sym_run: intro"
  cg1.withContext do
  let hg := (← getLCtx).lastDecl.get!.toExpr
  let [go, gk] ← cg1.apply (mkConst ``Tree.WP_leaf) | throwError "sym_run: leaf"
  let (pend, []) ← symLeaf ty0 norm l0facts go gk (withCont := false) | throwError "sym_run: leaf"
  -- normalise the continuation in the outer context (without the branch premise)
  let m ← mkFreshExprMVarAt outer.lctx outer.localInstances (← instantiateMVars (← gk.getType))
  let m' ← contNorm ty0 norm l0facts m.mvarId!
  let N ← instantiateMVars (← m'.getType)
  let w ← whnfR N
  let R' := w.getAppArgs[6]!
  let opnd (r : Nat) : Expr := if r = 0 then toExpr (0 : BitVec 64) else mkApp R' (mkNatLit r)
  let lem := match op, taken with
    | .BEQ, true => ``guard_beq | .BNE, true => ``guard_bne | .BLT, true => ``guard_blt
    | .BGE, true => ``guard_bge | .BLTU, true => ``guard_bltu | .BGEU, true => ``guard_bgeu
    | .BEQ, false => ``gF_beq | .BNE, false => ``gF_bne | .BLT, false => ``gF_blt
    | .BGE, false => ``gF_bge | .BLTU, false => ``gF_bltu | .BGEU, false => ``gF_bgeu
  let li := mkApp2 (mkConst lem) (opnd r1) (opnd r2)
  let some (_, P) := (← inferType li).iff? | throwError "sym_run: guard"
  let G ← mkFreshExprMVarAt outer.lctx outer.localInstances (← mkArrow P N)
  let H ← withLocalDeclD `x N fun x => do
    m'.assign x
    mkLambdaFVars #[x] (← instantiateMVars m)
  let pfG ← mkFreshExprMVar P
  let mut lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
  let hgId := mkIdent (← hg.fvarId!.getUserName)
  let [] ← evalTacticAt (← `(tactic| simpa only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
      BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceToNat, Nat.reduceAdd, not_true_eq_false,
      $lems,*] using $hgId)) pfG.mvarId! | throwError "sym_run: branch premise"
  gk.assign (mkApp H (mkApp G pfG))
  return (pend, G.mvarId!)

partial def symWalk (ty0 : Expr) (norm : Syntax) (l0facts : Array Term) (facts : Array Term)
    (explore : Bool) (g : MVarId) : TacticM (Except (List Nat) (List MVarId × List MVarId)) := do
  let tgt ← instantiateMVars (← g.getType)
  let tr := tgt.getAppArgs.back!
  if tr.isAppOf ``Tree.leaf then
    let [go, gk] ← g.apply (mkConst ``Tree.WP_leaf) | throwError "sym_run: leaf"
    return .ok (← symLeaf ty0 norm l0facts go gk)
  else if tr.isAppOf ``Tree.jr then
    let [go, gk] ← g.apply (mkConst ``Tree.WP_jr) | throwError "sym_run: jr"
    return .ok (← symLeaf ty0 norm l0facts go gk)
  else if tr.isAppOf ``Tree.br then
    let args := tr.getAppArgs
    let [gt, gf] ← g.apply (mkConst ``Tree.WP_br) | throwError "sym_run: br"
    let prem := fun (g : MVarId) => do
      let [g] ← evalTacticAt (← `(tactic| simp only [SE.den, aluVal, guard_beq, guard_bne,
        guard_blt, guard_bge, guard_bltu, guard_bgeu, gF_beq, gF_bne, gF_blt, gF_bge, gF_bltu,
        gF_bgeu])) g | throwError "sym_run: guard"
      pure g
    let introHc (g : MVarId) : TacticM MVarId := do
      let [g] ← evalTacticAt (← `(tactic| intro hc)) g | throwError "sym_run: intro"
      pure g
    let gt' ← prem gt
    let gf' ← prem gf
    let some ⟨_, bpc⟩ ← getBitVecValue? args[0]! | throwError "sym_run: pc"
    let some (bop', br1, br2, bi13) := decB (wordAt binByte bpc.toNat) | throwError "sym_run: decode"
    let tpc := (bpc + bi13.signExtend 64).toNat
    let fpc := bpc.toNat + 4
    let zeroAt (child : Expr) (succ : Nat) : MetaM Bool := do
      unless child.isAppOf ``Tree.leaf do return false
      let st := child.appArg!
      unless st.isAppOf ``SS.mk do return false
      match ← getBitVecValue? st.getAppArgs[0]! with
      | some ⟨_, v⟩ => return v.toNat == succ
      | none => return false
    let side (g : MVarId) (child : Expr) (succ : Nat) (taken : Bool) :
        TacticM (Except (List Nat) (List MVarId × List MVarId)) := do
      if ← zeroAt child succ then
        let (p, st) ← zeroStepChild ty0 norm l0facts facts g bop' br1 br2 taken
        return .ok (p, [st])
      else
        -- the branch premise in the form `ix_run` reaches after one normalisation step
        let g ← do
          let saved ← saveState
          try
            match ← evalTacticAt norm g with
            | [g'] => pure g'
            | _ => saved.restore; pure g
          catch _ => saved.restore; pure g
        symWalk ty0 norm l0facts facts explore (← introHc g)
    if ← ixTryPrune norm gt' then
      side gf' args[5]! fpc false
    else if ← ixTryPrune norm gf' then
      side gt' args[4]! tpc true
    else if explore then
      match ← side gt' args[4]! tpc true with
      | .error c => return .error c
      | .ok (p1, s1) =>
        match ← side gf' args[5]! fpc false with
        | .error c => return .error c
        | .ok (p2, s2) => return .ok (p1 ++ p2, s1 ++ s2)
    else
      -- `ix_run1` stops at this branch
      let some ⟨_, pcv⟩ ← getBitVecValue? args[0]! | throwError "sym_run1: pc"
      let w := wordAt binByte pcv.toNat
      let some (op, r1, r2, i13) := decB w | throwError "sym_run1: decode"
      let tpc := (pcv + i13.signExtend 64).toNat
      let fpc := pcv.toNat + 4
      unless args[4]!.isAppOf ``Tree.leaf && args[5]!.isAppOf ``Tree.leaf do
        return .error [tpc, fpc]
      let st ← branchStuck ty0 norm l0facts gt op r1 r2 true
      let sf ← branchStuck ty0 norm l0facts gf op r1 r2 false
      return .ok ([], [st, sf])
  else throwError "sym_run: unexpected tree"

def symRunCore (explore : Bool) (fuel : Nat) (h : Syntax) (facts : Array Term) (stops : List Nat) :
    TacticM (Option (List Nat)) := do
  let dbg (m : String) : TacticM Unit := do
    if (← getOptions).getBool `sym_run.trace false then IO.eprintln s!"sym_run stage: {m}"
  let norm ← ixNorm facts
  let g ← getMainGoal
  let g ← do
    let saved ← saveState
    try
      match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) g with
      | [g'] => pure g'
      | _ => saved.restore; pure g
    catch _ => saved.restore; pure g
  g.withContext do
  let ty0 ← instantiateMVars (← g.getType)
  let w ← whnfR ty0
  let a := w.getAppArgs
  unless w.getAppFn.isConstOf ``SWP && a.size == 8 do throwError "sym_run: goal is not SWP"
  let some ⟨_, pcv⟩ ← getBitVecValue? a[5]! | throwError "sym_run: pc"
  let R := a[6]!
  -- data view and its bases
  let text ← whnfR a[1]!
  let DA := if text.getAppNumArgs == 6 then (text.getAppArgs[5]!).getAppArgs.back? else none
  let daF := match DA with
    | some e => (collectFVars {} e).fvarSet
    | none => {}
  let Rf := Id.run do
    let mut e := R
    while e.isAppOfArity ``upd 4 || e.isAppOfArity ``upd 3 do e := e.getAppArgs[0]!
    return e
  let regOf? (lhs : Expr) : Option Nat :=
    if lhs.isApp && (lhs.appFn! == R || lhs.appFn! == Rf) then lhs.appArg!.nat? else none
  let mut dbase : List SE := []
  let mut L0 : List (Nat × SE) := []
  let mut L0facts : Array Term := #[]
  let mut regEqs : Array (Nat × Expr) := #[]
  let mut ldFacts : Array (Expr × Expr) := #[]
  for f in facts do
    let fe ← Term.elabTerm f none
    let fty ← instantiateMVars (← inferType fe)
    if let some (_, lhs, rhs) := fty.eq? then
      if let some i := regOf? lhs then
        regEqs := regEqs.push (i, rhs)
        if let some ⟨64, v⟩ ← getBitVecValue? rhs then
          L0 := L0 ++ [(i, .c v)]; L0facts := L0facts.push f
        let rf := (collectFVars {} rhs).fvarSet
        if rf.toList.any daF.contains then dbase := dbase ++ [.r i]
      else if lhs.isAppOfArity ``ldv 3 then
        ldFacts := ldFacts.push (lhs, rhs)
  let Dt : Expr := if text.getAppNumArgs == 6 then
      ((text.getAppArgs[5]!).getAppArgs[0]?).getD (mkConst ``Std.ExtHashMap.emptyWithCapacity)
    else mkConst ``Unit.unit
  -- known data-view words: `ldv k Dt ADDR = lit`, ADDR = `x.toNat` or `(x + c).toNat`, `R i = x`
  let mut kv : List (MKind × SE × BitVec 64) := []
  for (lhs, rhs) in ldFacts do
    let args := lhs.getAppArgs
    let some ⟨64, v⟩ ← getBitVecValue? rhs | continue
    unless ← isDefEq args[1]! Dt do continue
    let kE ← whnfR args[0]!
    let some k := kE.constName?.bind mkindOf? | continue
    let ad := args[2]!
    unless ad.isAppOfArity ``BitVec.toNat 2 do continue
    let x := ad.appArg!
    let (xb, off) ← do
      if x.isAppOfArity ``HAdd.hAdd 6 then
        match ← getBitVecValue? x.appArg! with
        | some ⟨64, c⟩ => pure (x.appFn!.appArg!, c)
        | _ => pure (x, (0 : BitVec 64))
      else pure (x, (0 : BitVec 64))
    for (i, e) in regEqs do
      if e == xb then kv := kv ++ [(k, addC (.r i) off, v)]
  let DAe : Expr := DA.getD (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Nat))
  let ρ := mkApp3 (mkConst ``Env.mk) R a[7]! Dt
  let mut lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
  for n in headConsts a[3]! ++ (match DA with | some e => headConsts e | none => #[]) do
    lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
  lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| InExt))
  let geomTac ← `(tactic| (simp only [Geom.holds, List.mem_cons, forall_eq_or_imp,
    List.not_mem_nil, false_implies, implies_true, and_true, AFact.holds, SE.den, reduceCtorEq,
    Option.some.injEq, forall_eq', List.mem_append, mem_accAddrs_iff', Nat.mod_one, forall_const,
    BitVec.add_zero, upd_apply, Nat.reduceEqDiff, ite_true, ite_false, $lems,*, *] <;> and_intros <;>
    (try intros) <;> first | exact True.intro |
      (have _htoh : tohostAddr = 0x8001ad00 := rfl; omega)))
  let proveGeom (gg : MVarId) : TacticM Bool := do
    let saved ← saveState
    try
      let gs ← evalTacticAt geomTac gg
      if gs.isEmpty then return true
      saved.restore; return false
    catch _ => saved.restore; return false
  let stopsBV : List (BitVec 64) := stops.map (BitVec.ofNat 64)
  let s0 : SS := ⟨BitVec.ofNat 64 pcv.toNat, L0, [], []⟩
  -- choose the data-view bases: an atom whose owned-read cover fails moves to the data view
  let mut tree : Tree := .leaf s0
  let mut Γ : Geom := []
  let mut done := false
  let mut rounds := 0
  while !done && rounds < 6 do
    rounds := rounds + 1
    let C := mkApp3 (mkConst ``cfgI) (toExpr stopsBV) (toExpr dbase) (toExpr kv)
    let run := mkApp3 (mkConst ``symRun) C (mkNatLit fuel) (toExpr s0)
    tree ← unsafe evalExpr Tree (mkConst ``Tree) run
    if rounds == 1 then
      -- every literal leaf must be a stop point, or a pc with no landed step lemma
      for s in Tree.leaves tree do
        let p := s.pc.toNat
        unless (stops.contains p) do
          if ← StepGen.hasStep ixPre p then
            throwError "sym_run: leaf {p} is not a stop point"
    Γ := geomOf (Tree.obs tree)
    let reads := ownedReadAtoms (Tree.obs tree)
    let mut moved := false
    let mut kept : Geom := []
    for f in Γ do
      let gg ← mkFreshExprMVar (← mkAppM ``Geom.holds #[ρ, a[3]!, DAe, toExpr [f]])
      if ← proveGeom gg.mvarId! then
        kept := kept ++ [f]
      else if reads.contains f.atom && !(dbase.contains f.atom) && DA.isSome then
        dbase := dbase ++ [f.atom]; moved := true
      else
        dbg s!"geometry fact dropped: {← ppGoal gg.mvarId!}"
    Γ := kept
    done := !moved
  unless done do throwError "sym_run: geometry"
  let C := mkApp3 (mkConst ``cfgI) (toExpr stopsBV) (toExpr dbase) (toExpr kv)
  -- every literal leaf must be a stop point, or a pc with no landed step lemma
  for s in Tree.leaves tree do
    let p := s.pc.toNat
    unless stops.contains p do
      if ← StepGen.hasStep ixPre p then
        throwError "sym_run: leaf {p} is not a stop point"
  dbg "tree"
  let Cs ← Term.exprToSyntax C
  let Γs ← Term.exprToSyntax (toExpr Γ)
  let fuelS := Syntax.mkNumLit (toString fuel)
  let L0s ← Term.exprToSyntax (toExpr L0)
  let gs ← evalTacticAt (← `(tactic| refine symRun_auto $Cs codeAt_interp $(⟨h⟩) (by decide)
    (by decide) $Γs $fuelS _ _ _ $L0s ?_ ?_ ?_ ?_)) g
  let [gL, gK, gΓ, gw] := gs | throwError "sym_run: refine"
  let knownTac ← `(tactic| (simp only [cfgI, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    false_implies, implies_true, and_true, SE.den, addC, upd_apply, Nat.reduceEqDiff, ite_true,
    ite_false, BitVec.add_zero, $lems,*, *] <;> and_intros <;> first | rfl | assumption))
  for gg in [gL, gK] do
    let saved ← saveState
    let ok ← try pure (← evalTacticAt knownTac gg).isEmpty catch e => do
      dbg s!"known values: {← e.toMessageData.toString}"; pure false
    unless ok do saved.restore; throwError "sym_run: known values"
  dbg "refine"
  unless ← proveGeom gΓ do throwError "sym_run: geometry"
  dbg "geom"
  let [gw] ← evalTacticAt (← `(tactic| sym_eval)) gw | throwError "sym_run: eval"
  dbg "eval"
  match ← symWalk ty0 norm L0facts facts explore gw with
  | .error cuts => return some cuts
  | .ok (pend, stuck) =>
    replaceMainGoal (pend ++ stuck)
    return none

def symRunTac (explore : Bool) (n : Option (TSyntax `num)) (h : Syntax)
    (fs : Option (Syntax.TSepArray `term ",")) (stops : Option (Array (TSyntax `num))) :
    TacticM Unit := do
  let fuel := (n.map (·.getNat)).getD 400
  let facts : Array Term := match fs with | some fs => fs.getElems | none => #[]
  let stopPCs : List Nat := match stops with | some ss => ss.toList.map (·.getNat) | none => []
  let saved ← saveState
  let trace := (← getOptions).getBool `sym_run.trace false
  tryCatchRuntimeEx
    (do
      let mut extra : List Nat := []
      let mut fin := false
      let mut rounds := 0
      while !fin do
        rounds := rounds + 1
        if rounds > 8 then throwError "sym_run1: too many cuts"
        let s1 ← saveState
        match ← symRunCore explore fuel h facts (stopPCs ++ extra) with
        | none => fin := true
        | some cuts => s1.restore; extra := extra ++ cuts
      if trace then logInfo m!"sym_run: symbolic")
    (fun e => do
      let msg ← e.toMessageData.toString
      saved.restore
      if trace then logInfo m!"sym_run fallback: {msg}"
      ixRunCore explore n h fs stops)

syntax "sym_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| sym_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => symRunTac true n h fs stops
  | `(tactic| sym_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => ixRunCore false n h fs stops

end VsaIris.SymExec.Interp
