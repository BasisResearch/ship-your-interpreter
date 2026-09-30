import Vsa.While.Parse
import Vsa.While.TypeInfer
import Vsa.While.Programs

open Vsa.While Vsa.While.Types

def checkFile (path : String) : IO Bool := do
  let src ← IO.FS.readFile path
  match Parse.parse src with
  | .error e => IO.println s!"{path}: {e}"; pure false
  | .ok p =>
    match infer p with
    | .ok Δ =>
      IO.println s!"{path}: well-typed"
      for x in programNames p do
        IO.println s!"  {x} : {Diag.Ty.render (Δ x)}"
      pure true
    | .error e => IO.println s!"{path}: type error: {e}"; pure false

def selftest (dir : String) : IO Bool := do
  let mut ok := true
  for (name, p) in Programs.all do
    let path := s!"{dir}/{name}.wl"
    let src ← IO.FS.readFile path
    match Parse.parse src with
    | .error e => IO.println s!"{path}: {e}"; ok := false
    | .ok q =>
      if reprStr q == reprStr p then IO.println s!"{path}: parse matches Programs.{name}Wl"
      else IO.println s!"{path}: parse DIFFERS from Programs.{name}Wl"; ok := false
  pure ok

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--selftest", dir] => return if ← selftest dir then 0 else 1
  | [] =>
    IO.println "usage: whilecheck FILE.wl ... | whilecheck --selftest DIR"
    return 2
  | files =>
    let mut ok := true
    for f in files do
      unless ← checkFile f do ok := false
    return if ok then 0 else 1
