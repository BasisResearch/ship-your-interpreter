import VsaIris.Interp.ITac

namespace VsaIris.Sym

open Lean Elab Tactic Meta

def nxPrefixes : List String := ["nt", "ntD", "ntT", "ntO", "ntJ", "ntC", "ntP"]

syntax "snp_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

syntax "snp_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

syntax "snp_runF " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

def nxTab (fs : Option (Syntax.TSepArray `term ",")) : TacticM (TSyntax `tactic) := do
  match fs with
  | none => `(tactic| ((try nx_tab) <;> (try ix_mem)))
  | some fs =>
    let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      fs.getElems.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
    `(tactic| ((try nx_tab) <;> (try ix_mem) <;> (try simp only [$lems,*])))

elab_rules : tactic
  | `(tactic| snp_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    ixRunCore true n h fs stops nxPrefixes (fun f => do ixNormTab f (some (← nxTab fs)))
  | `(tactic| snp_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    ixRunCore false n h fs stops nxPrefixes (fun f => do ixNormTab f (some (← nxTab fs)))
  | `(tactic| snp_runF $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    ixRunCore true n h fs stops nxPrefixes (fun f => do ixNormTab f (some (← nxTab fs))) (condFacts := true)

end VsaIris.Sym
