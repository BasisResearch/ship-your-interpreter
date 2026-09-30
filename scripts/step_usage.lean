import VsaBoot

/-!
# Which step-table lemmas are used

Reports, for every theorem declared in a `VsaIris.Vsa.StepTables.*` module, whether a
constant outside those modules reaches it (directly or through another table lemma).
Output: one line `<table module> <name> used|unused`, then per-family counts.

Regenerate the `only` lists of the tables:
`lake env lean scripts/step_usage.lean > usage.txt && python3 scripts/step_only.py usage.txt`
-/

open Lean

def isTableMod (n : Name) : Bool := (`VsaIris.Vsa.StepTables).isPrefixOf n

def constsOf (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => v.getUsedConstantsAsSet.foldl (·.insert ·) s
  | none => s

run_meta do
  let env ← getEnv
  let mods := env.header.moduleNames
  let inTable (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => isTableMod mods[i.toNat]!
    | none => false
  let mut used : NameSet := {}
  let mut tbl : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if inTable n then tbl := tbl.push (n, ci)
    else
      for c in (constsOf ci).toList do
        if inTable c then used := used.insert c
  -- close under references between table lemmas
  let mut changed := true
  while changed do
    changed := false
    for (n, ci) in tbl do
      if used.contains n then
        for c in (constsOf ci).toList do
          if inTable c && !used.contains c then
            used := used.insert c; changed := true
  let mut fam : Std.HashMap String (Nat × Nat) := {}
  for (n, _) in tbl do
    let some i := env.getModuleIdxFor? n | continue
    let u := used.contains n
    IO.println s!"{mods[i.toNat]!} {n} {if u then "used" else "unused"}"
    let s := n.getString!
    let f := (s.splitOn "_")[0]!
    let (a, b) := fam.getD f (0, 0)
    fam := fam.insert f (if u then a + 1 else a, b + 1)
  for (f, (a, b)) in fam.toList do
    IO.println s!"# family {f}: used {a} / generated {b}"
