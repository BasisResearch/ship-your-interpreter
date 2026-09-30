import Lean

/-!
The exception `win_key` throws when the keys of a side condition show it false (two accesses of
one window that overlap, two distinct positions claimed equal). It is an internal exception, so
the macro alternatives behind `win_key` are not tried: a refuted side condition costs no
arithmetic. `simp` dischargers, `first` and `try` catch it like any failure.
-/

namespace VsaIris.Sym

open Lean

initialize winRefutedId : InternalExceptionId ← registerInternalExceptionId `winRefuted

def throwWinRefuted {m : Type → Type} {α : Type} [MonadExceptOf Exception m] : m α :=
  throw (.internal winRefutedId)

def isWinRefuted : Exception → Bool
  | .internal id _ => id == winRefutedId
  | _ => false

end VsaIris.Sym
