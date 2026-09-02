import experiments.smt.DumpSmtLib

/-!
# `#check_sat` — the whole refute/validate loop as a Lean metaprogram

`#check_sat for <PropName>` encodes the NEGATION of a `Prop`-valued constant
(reusing the elaborated-`Expr` walker in `DumpSmtLib.lean` — NO Python source
parsing anywhere), runs Z3 IN-PROCESS from the elaborator, and reports the
verdict inline:

* Z3 `unsat`  ⇒ **VALID** (the negation has no model in the encoded fragment —
  the statement holds there).
* Z3 `sat`    ⇒ **REFUTED** (a countermodel exists); the model text is logged.
* Z3 `unknown`/timeout ⇒ **UNKNOWN** (should not occur once opacity is driven
  out — every remaining head is either arithmetic/array or a fuel-bounded cut).

When the encoder emitted any `; OPAQUE:` head or `; ENCODE-GAP:`, the verdict is
tagged so we can see it — the goal is ZERO opaque heads (everything unfolds in
the kernel; the only principled non-arithmetic leaf is a fuel-bounded recursion
cut, reported as BOUNDED, not opaque).

Proves nothing (Law 2 untouched): a pure `elab` command, never wired into
`Vsa.lean`, run only via `lake env lean`.  Z3's textual `sat`/`unsat` is the
SOLVER's output, not Lean source — parsing it is fine.
-/

open Lean Elab Meta Command
open Vsa.SmtExport

namespace Vsa.CheckSat

/-- Run Z3 on an SMT-LIB2 string; return its stdout (`sat`/`unsat`/`unknown`
plus any model). -/
def runZ3 (smt : String) : IO String := do
  let (handle, path) ← IO.FS.createTempFile
  handle.putStr smt
  handle.flush
  let out ← IO.Process.output
    { cmd := "z3", args := #["-smt2", "-T:60", path.toString] }
  try IO.FS.removeFile path catch _ => pure ()
  return out.stdout ++ out.stderr

/-- Classify Z3 output into a verdict head. -/
def z3Verdict (out : String) : String :=
  let l := out.trim
  if l.startsWith "unsat" then "VALID"
  else if l.startsWith "sat" then "REFUTED"
  else "UNKNOWN"

/-- `#check_sat for <name>` — encode ¬<name>, run Z3, report inline. -/
elab "#check_sat " " for " nameStx:ident : command => do
  liftTermElabM do
    let name ← resolveGlobalConstNoOverload nameStx
    let (st, hyps, concl) ← runExport name
    let smt := buildSmt st hyps concl
    let out ← runZ3 smt
    let v := z3Verdict out
    let opq := st.opaqueHeads.toList
    let tag :=
      if !st.gaps.isEmpty then s!" [ENCODE-GAP×{st.gaps.size}]"
      else if !opq.isEmpty then s!" [OPAQUE: {opq}]"
      else " [fully-encoded]"
    let model := if v == "REFUTED" then "\n" ++ out.trim else ""
    logInfo m!"#check_sat {name} → {v}{tag}{model}"

end Vsa.CheckSat
