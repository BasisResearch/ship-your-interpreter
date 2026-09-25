import VsaIris.Vsa.SnpSteps
import VsaIris.Interp.ITac

/-!
# Driving the `snprintf` family's step table

`nx_run h` is `ix_run` (`VsaIris/Interp/ITac.lean`, the same driver) over the
`snprintf` table (`SnpSteps/*.lean`, `NW`): at each PC literal it tries
`nt_<pc>` (ALU, store, branch, jump, owned load), `ntD_<pc>` (data load),
`ntT_<pc>` (conversion-table load), `ntO_<pc>` (`snez`/`seqz`), `ntC_<pc>`
(a call, followed inline), `ntJ_<pc>`
(the indirect call) and last `ntP_<pc>` (a load of partly known bytes, whose
continuation holds for every consistent value), and normalizes table words
with `nx_tab`.
-/

namespace VsaIris.Sym

open Lean Elab Tactic Meta

/-- The `snprintf` table's step-lemma prefixes, in the order tried. -/
def nxPrefixes : List String := ["nt", "ntD", "ntT", "ntO", "ntJ", "ntC", "ntP"]

/-- `nx_run h`, `nx_run [n] h`, `nx_run h using [e,…]`, `nx_run h at pc…`. -/
syntax "nx_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

/-- `nx_run1`: `nx_run` that stops at a branch it cannot decide. -/
syntax "nx_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| nx_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    ixRunCore true n h fs stops nxPrefixes (some (← `(tactic| nx_tab)))
  | `(tactic| nx_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    ixRunCore false n h fs stops nxPrefixes (some (← `(tactic| nx_tab)))

end VsaIris.Sym
