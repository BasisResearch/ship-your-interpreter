import VsaIris.Vsa.MallocFastSegs
import VsaIris.Vsa.RunBase
import VsaIris.Vsa.MallocFastHeap
import VsaIris.Vsa.Tools
import VsaIris.LocalRun
import VsaIris.Vsa.JalSite

namespace VsaIris.MallocFast

open Vsa.Sim Vsa.MemRepr Vsa.Sim.DlHeap VsaIris.Inst VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Iris

def stackBase (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) : Mem :=
  (List.range len).foldl (fun m k => m.insert (lo + k) (f (lo + k))) m

theorem stackBase_get (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) (a : Nat) :
    (stackBase m lo len f)[a]? = if lo ≤ a ∧ a < lo + len then some (f a) else m[a]? := by
  unfold stackBase
  induction len generalizing a with
  | zero => simp only [List.range_zero, List.foldl_nil]; rw [ite_eq_right (by omega)]
  | succ len ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.ExtHashMap.getElem?_insert]
    by_cases h : lo + len = a
    · subst h; simp
    · rw [ite_eq_right (by simpa using h), ih]
      by_cases h2 : lo ≤ a ∧ a < lo + len
      · rw [ite_eq_left h2, ite_eq_left ⟨h2.1, by omega⟩]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem or_one_even (x : BitVec 64) (h : x.toNat % 2 = 0) :
    x ||| sign_extend (m := 64) (0x001#12) = x + 1#64 := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 by decide]
  refine (BitVec.add_eq_or_of_and_eq_zero x 1#64 ?_).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

end VsaIris.MallocFast
