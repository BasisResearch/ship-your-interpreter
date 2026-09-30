import VsaIris.Interp.ITac
import VsaIris.Vsa.SnpSteps.Part00
import VsaIris.Vsa.SnpSteps.Part01
import VsaIris.Vsa.SnpSteps.Part02
import VsaIris.Vsa.SnpSteps.Part03
import VsaIris.Vsa.SnpSteps.Part04
import VsaIris.Vsa.SnpSteps.Part05
import VsaIris.Vsa.SnpSteps.Part06
import VsaIris.Vsa.SnpSteps.Part07
import VsaIris.Vsa.SnpSteps.Part08
import VsaIris.Vsa.SnpSteps.Part09
import VsaIris.Vsa.SnpSteps.Part10
import VsaIris.Vsa.SnpSteps.Part15
import VsaIris.Vsa.SnpSteps.Part16
import VsaIris.Vsa.SnpSteps.Part21
import VsaIris.Vsa.SnpSteps.Part23
import VsaIris.Vsa.SnpSteps.Part28
import VsaIris.Vsa.SnpSteps.Part29
import VsaIris.Vsa.SnpSteps.Part30

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
