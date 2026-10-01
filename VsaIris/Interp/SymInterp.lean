import VsaIris.Vsa.SymExec
import VsaIris.Interp.ITac

/-!
# The symbolic route for `IW` runs

* `codeAt_interp`: `interpText` pins its code and constant-table ranges to the binary image.
* `geomOf`: the `Geom` a run needs, read off its own obligations (per atom: the offset span,
  the store alignment, the `S`/`DA` cover ranges and the HTIF gap). `geom_auto` then proves it
  from the piece's hypotheses, so no piece writes a `Geom` by hand.
* `sym_run [n] hlive using [facts] at pcs` runs the executor from the goal's state to the stop
  points, one segment per undecided branch, closes the checked obligations and the decode
  facts, prunes infeasible branch sides and normalises the continuations. `sym_run1` stops at
  the first branch it cannot prune.

The leftover goals are in *step-lemma form*, the form a run that applies the step table's
lemma of each instruction and normalises after every step would leave; the pieces' statements
are written against it. A branch premise reads a written register from the fact-rewritten
register chain of its step; an undecided access check or jump alignment is the side goal of
that instruction's step lemma (`hea`, `hLDS`, `hLDD`, `hS`, `hal`); a branch side that takes
no further step keeps its premise unnormalised; case tags are `hk` per load, store and
indirect jump and `hT`/`hF` per branch.
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

open Lean Elab Command in
/-- `#pc_list name := e` defines `name : List (BitVec 64)` as the literal value of `e : List Nat`. -/
elab "#pc_list " n:ident " := " e:term : command => do
  let v ← liftTermElabM do
    let e ← Term.elabTermEnsuringType e (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    let l ← unsafe Meta.evalExpr (List Nat) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat))
      (← instantiateMVars e)
    pure (l.map (BitVec.ofNat 64))
  let name := (← getCurrNamespace) ++ n.getId
  let ty := mkApp (mkConst ``List [Level.zero]) (mkApp (mkConst ``BitVec) (mkNatLit 64))
  let val := toExpr v
  liftCoreM <| addAndCompile
    (.defnDecl (mkDefinitionValEx name [] ty val .abbrev .safe [name]))

-- The interpreter's loads of bytes it does not own (value quantified), as the step table has
-- them: the `argc`/count words read through a pointer whose target is not in the frame or view.
#pc_list interpHavocPCs := (StepGen.interpTbl.variants.lookup "H").getD []

-- The interpreter's loads that read the data view (the AST and the input).
#pc_list interpDataPCs := (StepGen.interpTbl.variants.lookup "D").getD []

/-- Whether the interpreter's step table has a lemma at `pc` (a step-by-step run steps
exactly there): an instruction of the table's code, outside its skipped ranges, that one of its
step families (not the call family) covers. -/
def interpHasStep (pc : Nat) : Lean.MetaM Bool := do
  let t := StepGen.interpTbl
  unless 0x800027ec ≤ pc ∧ pc < 0x80004764 do return false
  if t.skip.any fun r => r.1 ≤ pc ∧ pc < r.2 then return false
  let some w ← StepGen.wordAt? t.pieces pc | return false
  return t.kinds.any fun kind =>
    kind != "jalx" && t.offers kind pc && (StepGen.lemOf t pc w kind).isSome

/-- Executor configuration for `IW` runs. -/
def cfgI (stops : List (BitVec 64)) (dbase : List SE := [])
    (kv : List (MKind × SE × BitVec 64) := []) (kvM : List (MKind × SE × BitVec 64) := [])
    (known : List (Nat × BitVec 64) := [])
    (dpcs : List (BitVec 64) := interpDataPCs) (hv : List (BitVec 64) := interpHavocPCs)
    (rawpcs : List (BitVec 64) := []) (forkStop : Bool := false) : Cfg :=
  { img := binByte, rT := interpRanges, rs := iRegs, stops, dbase, kv, kvM, known,
    hasB := bytesHasB interpCodePieces, dpcs, hv, rawpcs, forkStop }

/-! ## The `Geom` of a run, from its obligations -/

def Tree.obs : Tree → List SOb
  | .leaf s => s.obs
  | .br _ _ _ _ o t f => o ++ Tree.obs t ++ Tree.obs f
  | .jr s _ => s.obs
  | .hv _ t => Tree.obs t
  | .raw _ _ _ _ t => Tree.obs t

/-- The undecided forwarding checks of one node's loads, with the load's pc (`obs` is newest
first). Checks over a havoc slot are left to the walk, where the slot has its value. -/
def rawCandsOf (obs : List SOb) : List (BitVec 64 × SOb) :=
  (obs.reverse.foldl (fun (acc : Option (BitVec 64) × List (BitVec 64 × SOb)) o =>
    match o, acc.1 with
    | .decM pc _, _ => (some pc, acc.2)
    | .disj a _ b _, some pc => if a.noHv && b.noHv then (acc.1, acc.2 ++ [(pc, o)]) else acc
    | _, _ => acc) (none, [])).2

def Tree.rawCands : Tree → List (BitVec 64 × SOb)
  | .leaf s => rawCandsOf s.obs
  | .br _ _ _ _ o t f => rawCandsOf o ++ Tree.rawCands t ++ Tree.rawCands f
  | .jr s _ => rawCandsOf s.obs
  | .hv _ t => Tree.rawCands t
  | .raw _ _ _ _ t => Tree.rawCands t

/-- The state a segment's straight line ends in, when it ends at a leaf (not at a fork or an
indirect jump). -/
def Tree.endLeaf? : Tree → Option SS
  | .leaf s => some s
  | .br _ op a b _ t f => match a, b with
    | .c u, .c v => if guardB op u v then Tree.endLeaf? t else Tree.endLeaf? f
    | _, _ => none
  | .jr _ _ => none
  | .hv _ t => Tree.endLeaf? t
  | .raw _ _ _ _ t => Tree.endLeaf? t

/-- Whether an obligation is the decode fact of a step (one per step). -/
def isDec : SOb → Bool
  | .decM .. | .decT .. | .decO .. => true
  | _ => false

/-- Merge a list of half-open ranges. -/
def mergeR (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  let s := (rs.toArray.qsort fun a b => a.1 < b.1).toList
  s.foldl (fun acc r => match acc with
    | (l, h) :: t => if r.1 ≤ h then (l, max h r.2) :: t else r :: (l, h) :: t
    | [] => [r]) [] |>.reverse

/-- Kinds of address need: 0 owned read, 1 data-view read, 2 owned write, 3 alignment,
4 havoc read (access check only). -/
structure Need where
  atom : SE
  offs : List (BitVec 64 × Nat × Nat)

def needOf (o : SOb) : Option (SE × BitVec 64 × Nat × Nat) :=
  match o with
  | .ld e w => some ((base e).1, (base e).2, w, 0)
  | .ldD e w => some ((base e).1, (base e).2, w, 1)
  | .st e w => some ((base e).1, (base e).2, w, 2)
  | .ldH e w => some ((base e).1, (base e).2, w, 4)
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

def geomOf (obs : List SOb) : Geom :=
  (((obs.foldl addNeed []).map factOf).filter (·.atom.noHv)).reverse


/-- Atoms whose owned reads are needed. -/
def ownedReadAtoms (obs : List SOb) : List SE :=
  obs.filterMap fun o => match o with
    | .ld e _ => if (base e).1 = .c 0 then none else some (base e).1
    | _ => none

/-! ## Branch premises in step-lemma form -/

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

/-- Denotation normaliser: symbolic values, havoc slots, register and memory folds. -/
macro "sym_den" : tactic => `(tactic| simp (disch := decide) only [regsDen, memDen, SE.den, aluVal,
  Env.withH, hset_self, hset_ne, shamtOf, shamt5Of, imm20Of, BitVec.reduceExtractLsb'])

/-- `sx_norm` on the branch premise just introduced, while it is the last hypothesis (a
step-by-step run normalises it at the next step, before any later premise exists). -/
macro "sym_hnorm " h:ident : tactic =>
  `(tactic| simp_set sx_norm_set at $h:ident)

/-- Unfolding `rawR`, as a rewrite with a proof: a definitional change of a branch premise
leaves the kernel to compare the entry register chain against its unfolding. -/
theorem rawR_eq (R : Nat → BitVec 64) (i : Nat) : rawR R i = R i := Eq.trans rfl rfl

theorem geom_nil (ρ : Env) (S : Nat → Prop) (DA : List Nat) : Geom.holds ρ S DA [] :=
  fun _ h => nomatch h

theorem geom_cons {ρ : Env} {S : Nat → Prop} {DA : List Nat} {f : AFact} {Γ : Geom}
    (h1 : Geom.holds ρ S DA [f]) (h2 : Geom.holds ρ S DA Γ) : Geom.holds ρ S DA (f :: Γ) :=
  fun g hg => (List.mem_cons.1 hg).elim (fun e => h1 g (e ▸ List.mem_singleton.2 rfl)) (h2 g)

register_option sym_run.trace : Bool := { defValue := false, descr := "report each sym_run and its stages" }

register_option sym_run.maxSegs : Nat :=
  { defValue := 0, descr := "debugging: stop after this many segments (0 = no limit)" }

syntax "sym_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

def mkindOf? (n : Name) : Option MKind :=
  if n == ``MKind.lw then some .lw else if n == ``MKind.lwu then some .lwu
  else if n == ``MKind.ld then some .ld else if n == ``MKind.lbu then some .lbu
  else if n == ``MKind.lh then some .lh else if n == ``MKind.lhu then some .lhu else none

/-- Replace the last three arguments (pc, registers, memory) of the goal head. -/
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
  let [gk] ← evalTacticAt (← `(tactic| (try sym_den))) gk
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
    -- a step-by-step run normalises after every step, so a value is normalised again whenever a
    -- later step rewrites inside it: iterate to the fixed point
    let mut gk := gk
    for _ in [0:4] do
      let before ← instantiateMVars (← gk.getType)
      let saved ← saveState
      let g' ← try
          match ← evalTacticAt norm gk with
          | [g'] => pure g'
          | _ => saved.restore; pure gk
        catch _ => saved.restore; pure gk
      gk := g'
      if (← instantiateMVars (← gk.getType)) == before then break
    pure gk
  return gk

/-- What the obligation walk needs from the run: the goal head, the normaliser, the facts
and the register list of a leaf below the node (every earlier register list is a suffix). -/
structure ObCtx where
  ty0 : Expr
  norm : Syntax
  l0facts : Array Term
  facts : Array Term
  regs : List (Nat × SE)
  /-- forwarding checks already proved for the segment, at the environment `preEnv` -/
  pre : Array (Expr × Expr) := #[]
  preEnv : Option Expr := none

/-- The register list of a leaf below the node. -/
def Tree.anyRegs : Tree → List (Nat × SE)
  | .leaf s => s.regs
  | .br _ _ _ _ _ t _ => Tree.anyRegs t
  | .jr s _ => s.regs
  | .hv _ t => Tree.anyRegs t
  | .raw _ _ _ _ t => Tree.anyRegs t

/-- An undecided load/store check, handed back as the side goals the step lemma at that
pc leaves: `LdOK`/`StOK` of `(R' rs1 + sign_extend imm).toNat` over the register chain `R'` of
that step, then the cover. Each part that the side tactic proves is closed. -/
def pendingMem (cx : ObCtx) (ρ S DA : Expr) (ho : MVarId) (o : SOb) (pc : BitVec 64)
    (w : BitVec 32) (n : Nat) (tag : Name) : TacticM (List MVarId) := ho.withContext do
  let a := mkLine pc w
  unless a.rs1 ≠ 0 ∧ a.rs1 ≠ 3 do throwError "sym_run: pending check at a constant base"
  let snap := cx.regs.drop (cx.regs.length - n)
  let m ← mkFreshExprMVar (withState cx.ty0 (toExpr pc)
    (mkApp2 (mkConst ``regsDen) ρ (toExpr snap)) cx.ty0.getAppArgs.back!)
  let m' ← contNorm cx.ty0 cx.norm cx.l0facts m.mvarId!
  let R' := (← whnfR (← instantiateMVars (← m'.getType))).getAppArgs[6]!
  let Rs ← Term.exprToSyntax R'
  let Ss ← Term.exprToSyntax S
  let DAs ← Term.exprToSyntax DA
  let rs1 := Syntax.mkNumLit (toString a.rs1)
  let imm := Syntax.mkNumLit (toString a.imm.toNat)
  let wd := Syntax.mkNumLit (toString (widthOfM a.kind))
  let ea ← `((($Rs $rs1) + LeanRV64DExecutable.Functions.sign_extend (m := 64) (BitVec.ofNat 12 $imm)).toNat)
  -- the side goals carry the premise names of the step lemma
  let tys : List (Name × Term) ← match o with
    | .ld _ _ => pure [(`hea, ← `(LdOK $ea $wd)), (`hLDS, ← `(∀ b ∈ accAddrs $ea $wd, $Ss b))]
    | .ldD _ _ => pure [(`hea, ← `(LdOK $ea $wd)), (`hLDD, ← `(∀ b ∈ accAddrs $ea $wd, b ∈ $DAs))]
    | .ldH _ _ => pure [(`hea, ← `(LdOK $ea $wd))]
    | .st _ _ => pure [(`hea, ← `(StOK $ea $wd)), (`hS, ← `(∀ b ∈ accAddrs $ea $wd, $Ss b))]
    | _ => throwError "sym_run: undecided obligation"
  let mut pend : List MVarId := []
  let mut hs : Array Term := #[]
  for (nm, t) in tys do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let G ← mkFreshExprMVar (← instantiateMVars ty) (userName := tag ++ nm)
    unless ← ixTrySide cx.norm G.mvarId! do pend := pend ++ [G.mvarId!]
    hs := hs.push (← Term.exprToSyntax G)
  -- both sides in one normal form: the obligation's symbolic address and the chain's register
  let mut fl : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in cx.facts do fl := fl.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
  let close (h : Term) : TacticM (TSyntax `tactic) :=
    if fl.isEmpty then
      `(tactic| (have hG := $h; (try sym_den); (try sx_norm); first | exact hG | assumption | skip))
    else
      `(tactic| (have hG := $h; (try sym_den); (try simp only [$fl,*] at hG); (try simp only [$fl,*]); (try sx_norm); (try simp only [$fl,*] at hG); (try simp only [$fl,*]); (try sx_norm); first | exact hG | assumption | skip))
  let parts ← match hs with
    | #[_] => pure [ho]
    | #[_, _] => evalTacticAt (← `(tactic| refine ⟨?_, ?_⟩)) ho
    | _ => throwError "sym_run: pending"
  unless parts.length == hs.size do throwError "sym_run: pending"
  for (g, h) in parts.zip hs.toList do
    let gs ← evalTacticAt (← close h) g
    unless gs.isEmpty do
      if (← getOptions).getBool `sym_run.trace false then
        for g in gs do IO.eprintln s!"sym_run pending mismatch: {← ppGoal g}"
      throwError "sym_run: pending check does not match the side goal of the step lemma"
  return pend

/-- The alignment premise of an indirect jump, as the step lemma states it:
`(R' r).toNat % 4 = 0` over the register chain of that step. Closed when the side tactic proves
it, else returned pending. -/
def pendingAl4 (cx : ObCtx) (ρ : Expr) (ho : MVarId) (pc : BitVec 64) (r n : Nat) (tag : Name) :
    TacticM (List MVarId) := ho.withContext do
  let snap := cx.regs.drop (cx.regs.length - n)
  let m ← mkFreshExprMVar (withState cx.ty0 (toExpr pc)
    (mkApp2 (mkConst ``regsDen) ρ (toExpr snap)) cx.ty0.getAppArgs.back!)
  let m' ← contNorm cx.ty0 cx.norm cx.l0facts m.mvarId!
  let R' := (← whnfR (← instantiateMVars (← m'.getType))).getAppArgs[6]!
  let Rs ← Term.exprToSyntax R'
  let rs := Syntax.mkNumLit (toString r)
  let ty ← Term.elabType (← `((($Rs $rs)).toNat % 4 = 0))
  Term.synthesizeSyntheticMVarsNoPostponing
  let G ← mkFreshExprMVar (← instantiateMVars ty) (userName := tag ++ `hal)
  let pend ← if ← ixTrySide cx.norm G.mvarId! then pure [] else pure [G.mvarId!]
  let h ← Term.exprToSyntax G
  let mut fl : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in cx.facts do fl := fl.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
  let tac ← if fl.isEmpty then
      `(tactic| (have hG := $h; (try sym_den); (try sx_norm); first | exact hG | assumption | skip))
    else
      `(tactic| (have hG := $h; (try sym_den); (try simp only [$fl,*] at hG); (try simp only [$fl,*]); (try sx_norm); (try simp only [$fl,*] at hG); (try simp only [$fl,*]); (try sx_norm); first | exact hG | assumption | skip))
  let gs ← evalTacticAt tac ho
  unless gs.isEmpty do
    if (← getOptions).getBool `sym_run.trace false then
      for g in gs do IO.eprintln s!"sym_run pending mismatch: {← ppGoal g}"
    throwError "sym_run: alignment does not match the side goal of the step lemma"
  return pend

/-- Discharge an `ObsOK` list, oldest obligation first (the order a step-by-step run meets them).
`nw` counts the register writes before the node; an undecided check is returned pending. -/
def symObs (cx : ObCtx) (obs : List SOb) (nw : Nat) (tag : Name) (go : MVarId) :
    TacticM (List MVarId × Nat × Name × Nat) := do
  let trace := (← getOptions).getBool `sym_run.trace false
  let t0 ← instantiateMVars (← go.getType)
  let targs := t0.getAppArgs
  let (ρ, S, DA) := (targs[0]!, targs[1]!, targs[2]!)
  -- one goal per obligation, newest first
  let mut hos : Array MVarId := #[]
  let mut cur := go
  for _ in obs do
    let [ho, hr] ← cur.apply (mkConst ``ObsOK_cons) | throwError "sym_run: obs"
    hos := hos.push ho
    cur := hr
  let [] ← cur.apply (mkConst ``ObsOK_nil) | throwError "sym_run: obs"
  let mut pend : List MVarId := []
  let mut nw := nw
  -- the goal tag of the step-lemma form here: a step whose lemma has side premises (a load,
  -- a store, an indirect jump) adds `hk`; a fork adds `hT`/`hF` (in `symWalk`)
  let mut tag := tag
  let mut tagAt := tag
  let mut at? : Option (BitVec 64 × BitVec 32 × Nat) := none
  let mut jr? : Option (BitVec 64 × Nat × Nat) := none
  let obsA := obs.toArray
  for k in [0:obsA.size] do
    let i := obsA.size - 1 - k
    let some o := obsA[i]? | throwError "sym_run: obs"
    if o matches .disj .. then
      if let (some ρ0, some (_, pf)) := (cx.preEnv, cx.pre.find? (·.1 == toExpr o)) then
        if ρ0 == ρ then
          if ← isDefEq (← hos[i]!.getType) (← inferType pf) then
            hos[i]!.assign pf
            continue
    let [ho] ← evalTacticAt (← `(tactic| simp only [SOb.den])) hos[i]! | throwError "sym_run: obs"
    match o with
    | .decM pc w =>
      let [] ← evalTacticAt (← `(tactic| sym_dec)) ho | throwError "sym_run: dec"
      at? := some (pc, w, nw)
      let k := (mkLine pc w).kind
      unless isStoreK k do nw := nw + 1
      tagAt := tag
      if isStoreK k || isLoadK k then tag := tag ++ `hk
    | .decT t =>
      let [] ← evalTacticAt (← `(tactic| sym_dec)) ho | throwError "sym_run: dec"
      tagAt := tag
      if t.kind matches .jr then
        jr? := some (t.pc, t.rs1, nw)
        tag := tag ++ `hk
    | .decO .. =>
      let [] ← evalTacticAt (← `(tactic| sym_dec)) ho | throwError "sym_run: dec"
      nw := nw + 1
    | _ =>
      let saved ← saveState
      try
        let gs ← evalTacticAt (← `(tactic| (sym_den <;> ($(⟨cx.norm⟩) <;> sx_side)))) ho
        unless gs.isEmpty do throwError "open"
      catch _ =>
        saved.restore
        match o, at? with
        | .al4 _, _ =>
          -- the alignment premise of the `jr` step lemma, pending when its side tactic fails
          let some (pc, r, n) := jr? | throwError "sym_run: alignment"
          pend := pend ++ (← pendingAl4 cx ρ ho pc r n tagAt)
        | .disj .., some (pc, _, _) =>
          -- the normaliser cannot pass this store either: read the load unreduced
          throwError "sym_run: rawpc {pc.toNat}"
        | _, none =>
          if trace then IO.eprintln s!"sym_run undecided: {← ppGoal ho}"
          throwError "sym_run: undecided memory obligation"
        | _, some (pc, w, n) =>
          try
            pend := pend ++ (← pendingMem cx ρ S DA ho o pc w n tagAt)
          catch e =>
            if trace then IO.eprintln s!"sym_run undecided: {← ppGoal ho}"
            throw e
  return (pend, nw, tag, (obs.filter isDec).length)

def symLeaf (cx : ObCtx) (obs : List SOb) (nw : Nat) (tag : Name) (go gk : MVarId)
    (withCont : Bool := true) : TacticM (List MVarId × List MVarId × Name) := do
  let (pend, _, tag, _) ← symObs cx obs nw tag go
  if withCont then
    let gk ← contNorm cx.ty0 cx.norm cx.l0facts gk
    gk.setTag tag
    return (pend, [gk], tag)
  else return (pend, [], tag)

/-- A branch side that reaches a stop point with no further step (or a branch `sym_run1` leaves
unexplored): the branch premise stays in the step-lemma form over the pre-branch register chain and only the continuation is normalised. -/
def zeroStepChild (cx : ObCtx) (child : SS) (nw : Nat) (tag : Name)
    (cg : MVarId) (op : bop) (r1 r2 : Nat) (taken : Bool) (introHc : Bool := true) :
    TacticM (List MVarId × MVarId) := do
  let (ty0, norm, l0facts, facts) := (cx.ty0, cx.norm, cx.l0facts, cx.facts)
  let outer ← cg.getDecl
  let [cg1] ← evalTacticAt (← `(tactic| intro hc)) cg | throwError "sym_run: intro"
  cg1.withContext do
  let hg := (← getLCtx).lastDecl.get!.toExpr
  let [go, gk] ← cg1.apply (mkConst ``Tree.WP_leaf) | throwError "sym_run: leaf"
  let (pend, [], _) ← symLeaf cx child.obs nw tag go gk (withCont := false)
    | throwError "sym_run: leaf"
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
  let G ← mkFreshExprMVarAt outer.lctx outer.localInstances (← mkArrow P N) (userName := tag)
  let H ← withLocalDeclD `x N fun x => do
    m'.assign x
    mkLambdaFVars #[x] (← instantiateMVars m)
  let pfG ← mkFreshExprMVar P
  let mut lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
  let hgId := mkIdent (← hg.fvarId!.getUserName)
  let [] ← evalTacticAt (← `(tactic| simpa only [rawR_eq, upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
      BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceToNat, Nat.reduceAdd, not_true_eq_false,
      $lems,*] using $hgId)) pfG.mvarId! | throwError "sym_run: branch premise"
  gk.assign (mkApp H (mkApp G pfG))
  -- `sym_run` introduces the premise of the side it follows; `sym_run1` leaves both sides of a
  -- branch it stops at as implications
  if introHc then
    let [G'] ← evalTacticAt (← `(tactic| intro hc)) G.mvarId! | throwError "sym_run: intro"
    return (pend, G')
  return (pend, G.mvarId!)

/-- What a segment needs beyond the obligation context. -/
structure SegCtx where
  /-- the executor configuration (`cfgI …` with `forkStop`) -/
  C : Expr
  /-- proof of `RunCtx live interpText Dt C R Mt` -/
  hX : Expr
  fuel : Nat
  stops : List Nat
  explore : Bool
  /-- entry environment, frame predicate and data view of the goal -/
  env0 : Expr
  S : Expr
  DA : Expr
  proveGeom : MVarId → TacticM Bool
  dbg : String → TacticM Unit
  segs : IO.Ref Nat
  /-- geometry facts already tried at the entry environment, with their proofs -/
  gcache : IO.Ref (Array (Expr × Option Expr))

mutual

/-- One segment: run the executor from `s` up to the next undecided branch (`forkStop`), close
the checked obligations, and walk the residual tree. `gk` is the `SWP` goal at `s`. -/
partial def runSeg (sc : SegCtx) (cx0 : ObCtx) (s : SS) (ρE : Expr) (used nw : Nat) (tag : Name)
    (gk : MVarId) : TacticM (List MVarId × List MVarId) := gk.withContext do
  sc.segs.modify (· + 1)
  let lim := sym_run.maxSegs.get (← getOptions)
  if lim != 0 && (← sc.segs.get) > lim then return ([], [gk])
  let fuel := sc.fuel - used
  let run := mkApp3 (mkConst ``symRun) sc.C (mkNatLit fuel) (toExpr s)
  let tree ← unsafe evalExpr Tree (mkConst ``Tree) run
  -- a straight line ends at a stop point, at a fork, out of fuel, or where no step
  -- lemma applies
  if let some e := Tree.endLeaf? tree then
    let p := e.pc.toNat
    unless sc.stops.contains p || ((Tree.obs tree).filter isDec).length ≥ fuel do
      if (← interpHasStep p) && inRangesB interpCodeRanges p then
        throwError "sym_run: leaf {p} is not a stop point"
  let mut Γ : Geom := []
  let mut pfs : Array Expr := #[]
  for f in geomOf (Tree.obs tree) do
    let fE := toExpr f
    let pf? ← match (← sc.gcache.get).find? (·.1 == fE) with
      | some (_, r) => pure r
      | none =>
        let gg ← mkFreshExprMVar (← mkAppM ``Geom.holds #[sc.env0, sc.S, sc.DA, toExpr [f]])
        let r ← if ← sc.proveGeom gg.mvarId! then pure (some (← instantiateMVars gg)) else
          sc.dbg s!"geometry fact dropped: {← ppGoal gg.mvarId!}"
          pure none
        sc.gcache.modify (·.push (fE, r))
        pure r
    if let some pf := pf? then
      Γ := Γ ++ [f]
      pfs := pfs.push pf
  let hΓ ← pfs.foldrM (fun pf acc => mkAppM ``geom_cons #[pf, acc])
    (mkApp3 (mkConst ``geom_nil) sc.env0 sc.S sc.DA)
  sc.dbg "tree"
  -- a load whose forwarding through a store stays undecided is rerun unreduced (`rawpc`): find
  -- it before any other obligation of the segment is worked on
  let mut pre : Array (Expr × Expr) := #[]
  for (pc, o) in Tree.rawCands (Tree.prune Γ tree) do
    let oE := toExpr o
    if pre.any (·.1 == oE) then continue
    let g ← mkFreshExprMVar (← mkAppM ``SOb.den #[ρE, sc.S, sc.DA, oE])
    let ok ← try
        let [ho] ← evalTacticAt (← `(tactic| simp only [SOb.den])) g.mvarId! | throwError "obs"
        let gs ← evalTacticAt (← `(tactic| (sym_den <;> ($(⟨cx0.norm⟩) <;> sx_side)))) ho
        pure gs.isEmpty
      catch _ => pure false
    unless ok do throwError "sym_run: rawpc {pc.toNat}"
    pre := pre.push (oE, ← instantiateMVars g)
  let hXs ← Term.exprToSyntax sc.hX
  let Γs ← Term.exprToSyntax (toExpr Γ)
  let hΓs ← Term.exprToSyntax hΓ
  let ρs ← Term.exprToSyntax ρE
  let ss ← Term.exprToSyntax (toExpr s)
  let fuelS := Syntax.mkNumLit (toString fuel)
  let [gw] ← evalTacticAt (← `(tactic| refine symRun_cont $hXs $Γs (by decide) $hΓs $fuelS $ρs
    rfl rfl rfl $ss ?_)) gk | throwError "sym_run: refine"
  let [gw] ← evalTacticAt (← `(tactic| sym_eval)) gw | throwError "sym_run: eval"
  sc.dbg "eval"
  symWalk sc { cx0 with pre, preEnv := some ρE } (Tree.prune Γ tree) used nw tag gw

partial def symWalk (sc : SegCtx) (cx0 : ObCtx) (t : Tree) (used nw : Nat) (tag : Name)
    (g : MVarId) : TacticM (List MVarId × List MVarId) := do
  let cx : ObCtx := { cx0 with regs := Tree.anyRegs t }
  let (norm, facts) := (cx.norm, cx.facts)
  match t with
  | .leaf s =>
    let [go, gk] ← g.apply (mkConst ``Tree.WP_leaf) | throwError "sym_run: leaf"
    let (p, st, _) ← symLeaf cx s.obs nw tag go gk
    return (p, st)
  | .hv _ t' =>
    let [g1] ← g.apply (mkConst ``Tree.WP_hv) | throwError "sym_run: hv"
    let [g2] ← evalTacticAt (← `(tactic| intro _)) g1 | throwError "sym_run: hv intro"
    symWalk sc cx0 t' used nw tag g2
  | .raw _ _ _ _ t' =>
    let [g1] ← g.apply (mkConst ``Tree.WP_raw) | throwError "sym_run: raw"
    symWalk sc cx0 t' used nw tag g1
  | .jr s _ =>
    let [go, gk] ← g.apply (mkConst ``Tree.WP_jr) | throwError "sym_run: jr"
    let (p, st, _) ← symLeaf cx s.obs nw tag go gk
    return (p, st)
  | .br bpc _ ba bb obs tt ff =>
    let [go, gt, gf] ← g.apply (mkConst ``Tree.WP_br) | throwError "sym_run: br"
    let (pend0, nw, tag, n) ← symObs cx obs nw tag go
    let used := used + n
    -- a fork: the operands do not decide the branch and the executor stopped at both successors
    let isFork := !(ba matches .c _) || !(bb matches .c _)
    let tagOf (taken : Bool) : Name := tag ++ (if taken then `hT else `hF)
    let prem := fun (g : MVarId) => show TacticM (Option MVarId) from do
      let [g] ← evalTacticAt (← `(tactic| simp (disch := decide) only [regsDen, memDen, SE.den, aluVal, Env.withH,
        hset_self, hset_ne, shamtOf, shamt5Of, imm20Of, BitVec.reduceExtractLsb', guard_beq, guard_bne,
        guard_blt, guard_bge, guard_bltu, guard_bgeu, gF_beq, gF_bne, gF_blt, gF_bge, gF_bltu,
        gF_bgeu])) g | throwError "sym_run: guard"
      -- step-lemma form: the premise reads a written register from the fact-rewritten chain and normalise the
      -- premise at the next step: introduce, normalise, rewrite with the facts, revert
      let mut fl : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
      for f in facts do
        -- only term equations: the chain holds terms, never a proposition to rewrite
        let isEq ← g.withContext do
          try
            let ty ← whnfR (← instantiateMVars (← inferType (← Term.elabTerm f none)))
            pure ty.isEq
          catch _ => pure false
        if isEq then fl := fl.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
      let saved ← saveState
      try
        let [g1] ← evalTacticAt (← `(tactic| intro hc)) g | throwError "intro"
        let hcId ← g1.withContext do
          pure (mkIdent (← (← getLCtx).lastDecl.get!.fvarId.getUserName))
        let tac ← if fl.isEmpty then
            `(tactic| ((try simp only [rawR_eq] at $hcId:ident) <;> (try sym_hnorm $hcId)))
          else `(tactic| ((try sym_hnorm $hcId) <;> (try simp only [$fl,*] at $hcId:ident) <;>
            (try simp only [rawR_eq] at $hcId:ident) <;> (try sym_hnorm $hcId)))
        match ← evalTacticAt tac g1 with
        | [] => pure none  -- the normalised premise is contradictory: this side is closed
        | [g2] =>
          let [g3] ← evalTacticAt (← `(tactic| revert $hcId)) g2 | throwError "revert"
          pure (some g3)
        | _ => throwError "norm"
      catch e =>
        if sym_run.trace.get (← getOptions) then IO.eprintln s!"sym_run prem: {← e.toMessageData.toString}"
        saved.restore; pure (some g)
    let introHc (g : MVarId) : TacticM MVarId := do
      let [g] ← evalTacticAt (← `(tactic| intro hc)) g | throwError "sym_run: intro"
      pure g
    let gt' ← prem gt
    let gf' ← prem gf
    let some (bop', br1, br2, bi13) := decB (wordAt binByte bpc.toNat) | throwError "sym_run: decode"
    let succOf (taken : Bool) : Nat := if taken then (bpc + bi13.signExtend 64).toNat else bpc.toNat + 4
    let hnormHc (g : MVarId) : TacticM MVarId := do
      let hcId ← g.withContext do
        pure (mkIdent (← (← getLCtx).lastDecl.get!.fvarId.getUserName))
      let saved ← saveState
      try
        match ← evalTacticAt (← `(tactic| sym_hnorm $hcId)) g with
        | [g'] => pure g'
        | _ => saved.restore; pure g
      catch _ => saved.restore; pure g
    let side (g : MVarId) (child : Tree) (taken : Bool) :
        TacticM (List MVarId × List MVarId) := do
      if let .leaf cs := child then
        -- no step on this side: the premise stays in the step-lemma form
        if cs.pc.toNat == succOf taken && cs.obs.isEmpty &&
            (sc.stops.contains cs.pc.toNat || (isFork && used ≥ sc.fuel)) then
          let (p, st) ← zeroStepChild cx cs nw (tagOf taken) g bop' br1 br2 taken
          return (p, [st])
        if isFork then
          -- continue this side with a new segment from the successor state
          let ρE := (← instantiateMVars (← g.getType)).bindingBody!.getAppArgs[0]!
          let g ← hnormHc (← introHc g)
          let [go, gk] ← g.apply (mkConst ``Tree.WP_leaf) | throwError "sym_run: leaf"
          let [] ← go.apply (mkConst ``ObsOK_nil) | throwError "sym_run: obs"
          return ← runSeg sc cx0 cs ρE used nw (tagOf taken) gk
      -- step-lemma form: the premise is introduced as the step leaves it; later normalisation
      -- (`at *`) rewrites it, the goal-only fact rewriting does not
      let g ← hnormHc (← introHc g)
      symWalk sc cx0 child used nw (tagOf taken) g
    let (p, st) ← match gt', gf' with
      | none, none => pure ([], [])
      | none, some gf' => side gf' ff false
      | some gt', none => side gt' tt true
      | some gt', some gf' =>
        if ← ixTryPrune norm gt' then side gf' ff false
        else if ← ixTryPrune norm gf' then side gt' tt true
        else if sc.explore then
          let (p1, s1) ← side gt' tt true
          let (p2, s2) ← side gf' ff false
          pure (p1 ++ p2, s1 ++ s2)
        else
          -- `sym_run1` stops at this branch: both premises go back in the step-lemma form
          match tt, ff with
          | .leaf ts, .leaf fs =>
            let (p1, st) ← zeroStepChild cx ts nw (tagOf true) gt' bop' br1 br2 true
              (introHc := false)
            let (p2, sf) ← zeroStepChild cx fs nw (tagOf false) gf' bop' br1 br2 false
              (introHc := false)
            pure (p1 ++ p2, [st, sf])
          | _, _ => throwError "sym_run1: branch"
    return (pend0 ++ p, st)

end

/-- The hypothesis part of the normaliser: `sx_norm`, `ix_tab` and `ix_mem` rewrite
`at *`, so after the first step every hypothesis in scope (a branch premise introduced by an
earlier run, say) is in normal form. The goal itself is left alone. -/
def normHyps (g : MVarId) : TacticM MVarId := do
  let gs ← getGoals
  let mut g := g
  for t in [← `(tactic| sx_norm), ← `(tactic| ix_tab), ← `(tactic| sx_norm), ← `(tactic| ix_mem)] do
    let some stx ← liftMacroM (Macro.expandMacro? t) | continue
    -- a guarded `simp_set` stands for `simp only [SET]` with its discharger and location
    let stx ← if stx.getKind != ``VsaIris.SimpGuard.simpSetTac then pure stx else
      let id := mkIdent stx[2].getId.eraseMacroScopes
      match stx[1].isNone, stx[3].isNone with
      | true, true => `(tactic| simp only [$id:ident])
      | true, false => `(tactic| simp only [$id:ident] $(⟨stx[3][0]⟩))
      | false, true => `(tactic| simp $(⟨stx[1][0]⟩):discharger only [$id:ident])
      | false, false => `(tactic| simp $(⟨stx[1][0]⟩):discharger only [$id:ident] $(⟨stx[3][0]⟩))
    let saved ← saveState
    try
      setGoals [g]
      let g' ← g.withContext do
        let r ← mkSimpContext stx (eraseLocal := false)
        let fvars ← g.getNondepPropHyps
        r.dischargeWrapper.with fun discharge? => do
          let (res, _) ← simpGoal g r.ctx r.simprocs discharge? (simplifyTarget := false)
            (fvarIdsToSimp := fvars)
          match res with
          | some (_, g') => pure g'
          | none => throwError "closed"
      g := g'
    catch _ => saved.restore
  setGoals gs
  return g

def symRunCore (explore : Bool) (fuel : Nat) (h : Syntax) (facts : Array Term) (stops : List Nat)
    (raws : List Nat := []) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  let dbg (m : String) : TacticM Unit := do
    if (← getOptions).getBool `sym_run.trace false then
      IO.eprintln s!"sym_run stage: {m} @{(← IO.monoMsNow) - t0}ms"
  let norm ← ixNorm facts
  let g ← getMainGoal
  let g ← do
    let saved ← saveState
    try
      match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) g with
      | [g'] => pure g'
      | _ => saved.restore; pure g
    catch _ => saved.restore; pure g
  let tag0 ← g.getTag
  g.withContext do
  let ty0 := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  let w ← whnfR ty0
  let a := w.getAppArgs
  unless w.getAppFn.isConstOf ``SWP && a.size == 8 do throwError "sym_run: goal is not SWP"
  let some ⟨_, pcv⟩ ← getBitVecValue? a[5]! | throwError "sym_run: pc"
  -- a run that starts at a stop point takes no step and normalises nothing
  if stops.contains pcv.toNat then
    replaceMainGoal [g]
    return
  let g ← normHyps g
  g.withContext do
  let R := a[6]!
  -- data view and its bases
  let text ← whnfR a[1]!
  let DA := if text.getAppNumArgs == 6 then (text.getAppArgs[5]!).getAppArgs.back? else none
  let Rf := Id.run do
    let mut e := R
    while e.isAppOfArity ``upd 4 || e.isAppOfArity ``upd 3 do e := e.getAppArgs[0]!
    return e
  -- registers the goal's register function overrides: a fact `Rf i = x` about the base says
  -- nothing about them
  let written : List Nat := Id.run do
    let mut e := R
    let mut ws : List Nat := []
    while e.isAppOfArity ``upd 4 || e.isAppOfArity ``upd 3 do
      if let some k := e.getAppArgs[1]!.nat? then ws := k :: ws
      e := e.getAppArgs[0]!
    return ws
  let regOf? (lhs : Expr) : Option Nat :=
    if lhs.isApp && lhs.appFn! == R then lhs.appArg!.nat?
    else if lhs.isApp && lhs.appFn! == Rf then
      match lhs.appArg!.nat? with
      | some i => if written.contains i then none else some i
      | none => none
    else none
  let dbase : List SE := []
  let mut known : List (Nat × BitVec 64) := []
  -- literal registers of the goal's own register function (`upd … k lit`, outermost write)
  let mut rch := R
  let mut seenK : List Nat := []
  while rch.isAppOfArity ``upd 4 || rch.isAppOfArity ``upd 3 do
    if let some k := rch.getAppArgs[1]!.nat? then
      unless seenK.contains k do
        seenK := k :: seenK
        if let some ⟨64, v⟩ ← getBitVecValue? rch.getAppArgs[2]! then known := known ++ [(k, v)]
    rch := rch.getAppArgs[0]!
  let mut regEqs : Array (Nat × Expr) := #[]
  let mut ldFacts : Array (Expr × Expr) := #[]
  for f in facts do
    let fe ← Term.elabTerm f none
    let fty ← instantiateMVars (← inferType fe)
    if let some (_, lhs, rhs) := fty.eq? then
      if let some i := regOf? lhs then
        regEqs := regEqs.push (i, rhs)
        if let some ⟨64, v⟩ ← getBitVecValue? rhs then
          known := known ++ [(i, v)]
      else if lhs.isAppOfArity ``ldv 3 then
        ldFacts := ldFacts.push (lhs, rhs)
  let Dt : Expr := if text.getAppNumArgs == 6 then
      ((text.getAppArgs[5]!).getAppArgs[0]?).getD (mkConst ``Std.ExtHashMap.emptyWithCapacity)
    else mkConst ``Unit.unit
  -- known data-view words: `ldv k Dt ADDR = lit`, ADDR = `x.toNat` or `(x + c).toNat`, `R i = x`
  let mut kv : List (MKind × SE × BitVec 64) := []
  let mut kvM : List (MKind × SE × BitVec 64) := []
  for (lhs, rhs) in ldFacts do
    let args := lhs.getAppArgs
    let some ⟨64, v⟩ ← getBitVecValue? rhs | continue
    -- a fact about the data view, or about the entry memory
    let onD ← isDefEq args[1]! Dt
    let onM := !onD && args[1]! == a[7]!
    unless onD || onM do continue
    let kE ← whnfR args[0]!
    let some k := kE.constName?.bind mkindOf? | continue
    let ad := args[2]!
    -- a literal address
    if let some n := ad.nat? then
      if onD then kv := kv ++ [(k, .c (BitVec.ofNat 64 n), v)]
      else kvM := kvM ++ [(k, .c (BitVec.ofNat 64 n), v)]
      continue
    unless ad.isAppOfArity ``BitVec.toNat 2 do continue
    let x := ad.appArg!
    let (xb, off) ← do
      if x.isAppOfArity ``HAdd.hAdd 6 then
        match ← getBitVecValue? x.appArg! with
        | some ⟨64, c⟩ => pure (x.appFn!.appArg!, c)
        | _ => pure (x, (0 : BitVec 64))
      else pure (x, (0 : BitVec 64))
    for (i, e) in regEqs do
      if e == xb then
        if onD then kv := kv ++ [(k, addC (.r i) off, v)]
        else kvM := kvM ++ [(k, addC (.r i) off, v)]
  let DAe : Expr := DA.getD (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat))
  let ρ := mkApp4 (mkConst ``Env.mk) R a[7]! Dt
    (.lam `_ (mkConst ``Nat) (toExpr (0 : BitVec 64)) .default)
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
  let s0 : SS := ⟨BitVec.ofNat 64 pcv.toNat, [], [], []⟩
  let C := mkAppN (mkConst ``cfgI) #[toExpr stopsBV, toExpr dbase, toExpr kv, toExpr kvM,
    toExpr known, mkConst ``interpDataPCs, mkConst ``interpHavocPCs,
    toExpr (raws.map (BitVec.ofNat 64)), toExpr true]
  -- the run-independent premises, once
  let hX ← mkFreshExprMVar (mkAppN (mkConst ``RunCtx) #[a[0]!, mkConst ``interpText, Dt, C, R, a[7]!])
  let gs ← evalTacticAt (← `(tactic| refine RunCtx.mk codeAt_interp (fun _ _ hb => interp_code hb)
    $(⟨h⟩) (by decide) (by decide) (by decide) ?_ ?_ (knownAll_mem ?_))) hX.mvarId!
  let [gK, gKm, gKn] := gs | throwError "sym_run: refine"
  dbg "refined"
  -- facts may be stated on the goal's register function as written (`upd R k v i = x`) or on
  -- its base (`R i = x`): try the facts alone, then with the update reduced
  let closers ← `(tactic| (and_intros <;> first | with_reducible rfl | with_reducible assumption))
  let knownA ← `(tactic| simp only [cfgI, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    false_implies, implies_true, and_true, SE.den, addC, BitVec.add_zero, BitVec.reduceToNat,
    $lems,*])
  let knownB ← `(tactic| simp only [cfgI, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    false_implies, implies_true, and_true, SE.den, addC, upd_apply, Nat.reduceEqDiff, ite_true,
    ite_false, BitVec.add_zero, BitVec.reduceToNat, $lems,*])
  let tryKnown (tac : Syntax) (gg : MVarId) : TacticM Bool := do
    let saved ← saveState
    try
      let gs ← withoutRecover (evalTacticAt tac gg)
      for g1 in gs do
        try
          unless (← withoutRecover (evalTacticAt closers g1)).isEmpty do throwError "open"
        catch e =>
          dbg s!"known values, left: {← ppGoal g1}"
          throw e
      return true
    catch e =>
      dbg s!"known values: {← e.toMessageData.toString}\n{← ppGoal gg}"
      saved.restore
      return false
  for gg in [gK, gKm] do
    unless ← tryKnown knownA gg do
      unless ← tryKnown knownB gg do throwError "sym_run: known values"
  -- known registers: one conjunct each; a literal of the goal's own register function is `rfl`
  do
    let gs ← evalTacticAt (← `(tactic| (simp only [cfgI, KnownAll] <;> and_intros))) gKn
    for g1 in gs do
      let saved ← saveState
      let ok ← try
          pure (← withoutRecover (evalTacticAt (← `(tactic| first
            | exact True.intro | exact rfl | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, $lems,*]; done)
            | assumption)) g1)).isEmpty
        catch _ => pure false
      unless ok do
        dbg s!"known register: {← ppGoal g1}"
        saved.restore; throwError "sym_run: known values"
  dbg "known"
  let cx : ObCtx := { ty0, norm, l0facts := #[], facts, regs := [] }
  let hXe ← instantiateMVars hX
  let Se := a[3]!
  let sc : SegCtx := SegCtx.mk C hXe fuel stops explore ρ Se DAe proveGeom dbg (← IO.mkRef 0) (← IO.mkRef #[])
  let (pend, stuck) ← runSeg sc cx s0 ρ 0 0 tag0 g
  dbg "walk"
  replaceMainGoal (pend ++ stuck)

/-- Source line of the tactic, for the trace. -/
def refLine : TacticM Nat := do
  let some p := (← getRef).getPos? | return 0
  return ((← getFileMap).toPosition p).line

def symRunTac (explore : Bool) (n : Option (TSyntax `num)) (h : Syntax)
    (fs : Option (Syntax.TSepArray `term ",")) (stops : Option (Array (TSyntax `num))) :
    TacticM Unit := do
  let fuel := (n.map (·.getNat)).getD 400
  let facts : Array Term := match fs with | some fs => fs.getElems | none => #[]
  let stopPCs : List Nat := match stops with | some ss => ss.toList.map (·.getNat) | none => []
  -- `set_option sym_run.trace true`, or `SYM_TRACE=1` for a whole build
  let trace := (← getOptions).getBool `sym_run.trace false || (← IO.getEnv "SYM_TRACE").isSome
  let mut raws : List Nat := []
  let mut fin := false
  let mut rounds := 0
  while !fin do
    rounds := rounds + 1
    if rounds > 12 then throwError "sym_run: too many rounds"
    let s1 ← saveState
    let r ← try
        symRunCore explore fuel h facts stopPCs raws
        pure none
      catch e =>
        -- a load whose forwarding is undecided is rerun unreduced
        let msg ← e.toMessageData.toString
        match (msg.splitOn "sym_run: rawpc ")[1]? with
        | some t =>
          match t.trimAscii.toString.toNat? with
          | some pc => if raws.contains pc then throw e else pure (some pc)
          | none => throw e
        | none => throw e
    match r with
    | none => fin := true
    | some pc => s1.restore; raws := raws ++ [pc]
  if trace then logInfo m!"sym_run: symbolic @{← refLine}"

syntax "sym_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| sym_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => symRunTac true n h fs stops
  | `(tactic| sym_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => symRunTac false n h fs stops

end VsaIris.SymExec.Interp
