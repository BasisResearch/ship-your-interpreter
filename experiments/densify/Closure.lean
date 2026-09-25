import Vsa.Elf
open Lean Meta

/-- Constants defined by the Sail model, lean-sail, or Vsa (by defining module). -/
def keep (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := (env.header.moduleNames[idx]!).toString
    m.startsWith "LeanRV64DExecutable" || m.startsWith "Sail" || m.startsWith "Vsa"
  | none => false

def isMonadName (n : Name) : Bool :=
  n == ``EStateM || n == ``ExceptT || n.toString.endsWith "PreSailM" || n.toString.endsWith "PreSailME" ||
  n.toString.endsWith "SailM" || n.toString.endsWith "SailME"

def monadic (env : Environment) (c : Name) : MetaM Bool := do
  let some ci := env.find? c | pure false
  forallTelescope ci.type fun _ body => do
    match body.getAppFn with
    | .const n _ => pure (isMonadName n)
    | _ => pure false

def arity (env : Environment) (c : Name) : MetaM Nat := do
  let some ci := env.find? c | pure 0
  forallTelescope ci.type fun xs _ => pure xs.size

/-- DFS postorder over monadic constants: callees before callers. -/
partial def visit (env : Environment) (c : Name) (st : NameSet × Array String) :
    MetaM (NameSet × Array String) := do
  if st.1.contains c then return st
  let seen := st.1.insert c
  let some ci := env.find? c | return (seen, st.2)
  let used := (ci.value?.map (·.getUsedConstants)).getD #[]
  let mut st := (seen, st.2)
  let mut callees : Array Name := #[]
  for u in used do
    if keep env u && u != c then
      if ← monadic env u then callees := callees.push u
      st ← visit env u st
  if ← monadic env c then
    let ar ← arity env c
    let isRec := used.contains c || used.any (· == ``WellFounded.fix)
    let line := s!"{c}\t{ar}\t{if isRec then "REC" else "-"}\t{String.intercalate "," (callees.toList.map toString)}"
    return (st.1, st.2.push line)
  return st

run_meta do
  let env ← getEnv
  let (_, out) ← visit env ``Vsa.stepOnce ({}, #[])
  IO.FS.writeFile "experiments/densify/closure.tsv" (String.intercalate "\n" out.toList ++ "\n")
  logInfo s!"{out.size} monadic in postorder"
