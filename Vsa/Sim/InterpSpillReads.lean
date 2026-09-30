import Vsa.Sim.rows.DriveSpillGen
import Vsa.Sim.WriteLogNF
import Vsa.Sim.ReprSurvival

open Vsa.MemRepr LeanRV64DExecutable LeanRV64DExecutable.Functions

namespace Vsa.Sim

/-- Read back one complete word written before a disjoint log suffix. -/
theorem read64_of_writeLog (m : Mem) (before after : List WEntry)
    (a : Nat) (v : BitVec 64) (hd : OutLRange after a 8) :
    read64 (writeLog m (before ++ (a, 8, v) :: after)) a = some v.toNat := by
  rw [writeLog_append]
  let written := writeMap8 (writeLog m before) a (sdData_val v)
  change read64 (writeLog written after) a = some v.toNat
  have he : read64 (writeLog written after) a = read64 written a :=
    read64_agreeP (P := OutL after) (writeLog_out written after)
      (fun k hk => outL_of_range hd (by omega) (by omega))
  rw [he, show read64 written a = some (sdData_val v).toNat from read64_writeMap8 _ _ _,
    sdData_toNat]

/-- Indexed word readback avoids repeating a concrete log's prefix and suffix. -/
theorem read64_of_writeLog_at (m : Mem) (log : List WEntry) (index a : Nat)
    (v : BitVec 64) (hi : log[index]? = some (a, 8, v))
    (hd : OutLRange (log.drop (index + 1)) a 8) :
    read64 (writeLog m log) a = some v.toNat := by
  induction log generalizing index m with
  | nil => simp at hi
  | cons entry rest ih =>
    cases index with
    | zero =>
      have he : entry = (a, 8, v) := Option.some.inj hi
      subst entry
      exact read64_of_writeLog m [] rest a v hd
    | succ i =>
      exact ih (applyW m entry) i (by simpa using hi) (by simpa using hd)

end Vsa.Sim
