import VsaIris.Vsa.SnpTac
import VsaIris.Vsa.SymBridge

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Newlib VsaIris.SymExec

theorem piecesText_sub {img : Nat → BitVec 8} {rs rs' : List (Nat × Nat)}
    (h : ∀ a, inRangesB rs a = true → inRangesB rs' a = true) :
    ∀ p ∈ piecesText [⟨img, rs⟩], p ∈ piecesText [⟨img, rs'⟩] := by
  intro p hp
  obtain ⟨q, hq, hr, he⟩ := mem_piecesText_iff.1 hp
  rw [List.mem_singleton] at hq; subst hq
  exact mem_piecesText_iff.2 ⟨_, List.mem_singleton_self _, h _ hr, he⟩

variable {live : Nat → Prop} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}

theorem swp_host_in {T X : List (Nat × BitVec 8)} (h : SWP live X rs S Q pc R Mt) :
    SWP live (T ++ X) rs S Q pc R Mt :=
  swp_text_mono (fun _ hp => List.mem_append_right _ hp) h

theorem swp_host_out {T X : List (Nat × BitVec 8)} (hT : ∀ p ∈ T, p ∈ X)
    (h : SWP live (T ++ X) rs S Q pc R Mt) : SWP live X rs S Q pc R Mt :=
  swp_text_mono (fun p hp => (List.mem_append.1 hp).elim (hT p) id) h

abbrev HostW (live : Nat → Prop) (T D : List (Nat × BitVec 8)) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWP live (T ++ D) nRegs S Q

def arithRanges : List (Nat × Nat) := [(0x800046ac, 0x80004728)]

def arithPieces : List TextPiece := [⟨textByte, arithRanges⟩]

def arithText : List (Nat × BitVec 8) := piecesText arithPieces

theorem arith_code {i : Nat} {code : List (BitVec 8)} (h : bytesHasB arithPieces i code = true) :
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ arithText :=
  codeFoot_mem_pieces h

theorem arith_tblOK : TblOK arithText nRegs arithPieces textByte arithRanges :=
  ⟨codeAt_of_piece (ps := arithPieces) (fun _ hm => hm) (by simp [arithPieces]),
    arith_code, by decide, by decide⟩

namespace StepGen

open Lean Elab Command Term Meta

def hostBinders : String :=
  "{live : Nat → Prop} {D : List (Nat × BitVec 8)} {S : Nat → Prop}\n    " ++
  "{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}"

def hostTbl (txt code : String) (ps ok : Name) : Tbl where
  key := "host/" ++ txt
  flavor := .snp
  pieces := ps
  run := "HostW live " ++ txt ++ " D S Q"
  binders := hostBinders
  text := txt
  code := code
  ok := some ok
  regs := "nRegs"
  gpv := gpV

def hostProof (T : Expr) (ok : Name) (w : Nat) (L : Lem) (ty : Expr) : MetaM (Option Expr) := do
  let some (rule, args) := L.rule | return none
  if rule.contains '.' || rule.startsWith "d_" then return none
  let tbl := (← getConstInfo ok).type.getAppArgs
  let pfs := #[mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``Bool.true []),
    mkApp (.const ``VsaIris.SymExec.decRefl []) (bv 32 w)]
  forallBoundedTelescope ty (some 2) fun xs _ => do
    let X ← mkAppM ``HAppend.hAppend #[T, xs[1]!]
    let body := mkAppN (.const ((`VsaIris.SymExec).str ("x_" ++ rule)) [])
      (tbl.push (.const ok []) ++ args ++ pfs ++ #[xs[0]!, X, xs[1]!, ← mkEqRefl X])
    mkLambdaFVars xs body

elab "#host_steps " fam:ident txt:ident cd:ident ps:ident ok:ident lo:num hi:num : command => do
  let (txtN, psN, okN) ← liftTermElabM do
    pure (← realizeGlobalConstNoOverload txt, ← realizeGlobalConstNoOverload ps,
      ← realizeGlobalConstNoOverload ok)
  let t := hostTbl txt.getId.toString cd.getId.toString psN okN
  liftTermElabM do
    let words ← wordsAt psN (← t.pcsIn lo.getNat hi.getNat)
    for (pc, w) in words do
      for kind in t.kinds.filter (· ∉ ["jalx", "jalro"]) do
        let some L := lemAt t kind pc w | continue
        let (ty, val) ← elabLemCore L (hostProof (.const txtN []) okN w L)
        let nm := (`VsaIris.Sym).str s!"{fam.getId}{kind}_{hxw 8 pc}"
        addDecl (.thmDecl { name := nm, levelParams := [], type := ty, value := val })

end StepGen

#host_steps ht arithText arith_code arithPieces arith_tblOK 0x800046ac 0x80004728

open Lean Elab Tactic in
syntax "host_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| host_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    ixRunCore true n h fs stops ["ht", "htD", "htT", "htO", "htJ", "htC", "htP"] (fun f => do ixNormTab f (some (← nxTab fs)))

end VsaIris.Sym
