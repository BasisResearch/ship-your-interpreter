import VsaIris.Vsa.SnpTac
import VsaIris.Vsa.Stdio

/-!
# The frame of a `snprintf` run

A `snprintf` run owns three byte ranges: newlib's runtime data (`stdioFoot`,
read only: `_impure_ptr` and the locale), the stack scratch below the caller's
`sp`, and the destination window. Every byte it reads but does not own (the
format, the `%s` arguments, the decimal point `"."`) is in the data view,
a concatenation of `accAddrs` ranges; bytes a caller owns are promoted back
at the Iris layer (`LocalRun.promote`). Both memberships are interval
arithmetic, so `sx_side` decides them (`snp_side`).
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Stdio

/-- The stack a `snprintf` call may use (`snprintfNeed`). -/
abbrev snpNeed : Nat := 1024

/-- The bytes a `snprintf` run owns: newlib's data, the scratch
`[s - 1024, s)` and the destination `[dst, dst + n)`. -/
def snpS (s dst n : Nat) (a : Nat) : Prop :=
  stdioFoot a ∨ (s - snpNeed ≤ a ∧ a < s) ∨ (dst ≤ a ∧ a < dst + n)

/-- Owned-byte side conditions of a `snprintf` run. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, snpS, stdioFoot, InRange] at *; sx_addr))

end VsaIris.Sym
