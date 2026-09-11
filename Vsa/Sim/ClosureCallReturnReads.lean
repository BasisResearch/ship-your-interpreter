import Vsa.Sim.ClosureCallBodyRun

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Read the incremented depth from dispatch's actual store and disjoint later spills. -/
theorem Post.depth_read
    {sp call object fn interp parent saved5 saved3 : BitVec 64} {count depth : Nat}
    {before called : Config}
    (h : Post sp call object fn interp parent saved5 saved3 count depth before called)
    (G : Geometry sp call object fn interp) (bound : depth < 1000) :
    read32 called.σ.mem (interp.toNat + 8) = some (depth + 1) := by
  let priorWrites := (writes before.σ.mem sp object interp saved5 saved3 count depth).take 4
  let suffix : List WEntry := [(sp.toNat + 1048, 8, saved3), (sp.toNat, 8, BitVec.ofNat 64 count)]
  have split : writes before.σ.mem sp object interp saved5 saved3 count depth =
      priorWrites ++ (interp.toNat + 8, 4, BitVec.ofNat 64 (depth + 1)) :: suffix := rfl
  rw [h.memory, split, writeLog_append]
  generalize writeLog before.σ.mem priorWrites = priorMem
  let written := writeMap4 priorMem (interp.toNat + 8)
    (swData (BitVec.ofNat 64 (depth + 1)))
  have write (m : Mem) (a : Nat) (v : BitVec 64) (rest : List WEntry) :
      writeLog m ((a, 4, v) :: rest) = writeLog (writeMap4 m a (swData v)) rest := rfl
  rw [write]
  have read : read32 (writeLog written suffix) (interp.toNat + 8) =
      read32 written (interp.toNat + 8) := by
    apply read32_agreeP (P := OutL suffix) (writeLog_out written suffix)
    intro k hk
    simp only [suffix, OutL, and_true]
    have := G.interpAbove
    exact ⟨by omega, by omega⟩
  rw [read, show read32 written (interp.toNat + 8) =
    some (swData (BitVec.ofNat 64 (depth + 1))).toNat from read32_writeMap4 _ _ _]
  rw [swData_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show depth + 1 < 2^64 by omega),
    Nat.mod_eq_of_lt (show depth + 1 < 2^32 by omega)]

/-- Loads used by both actual closure return routes. -/
structure BodyReturnReads (m : Mem) (sp interp saved5 saved3 saved7 : BitVec 64) (depth : Nat) : Prop where
  depthRead : read32 m (interp.toNat + 8) = some (depth + 1)
  saved5Read : read64 m (sp.toNat + 1032) = some saved5.toNat
  saved3Read : read64 m (sp.toNat + 1048) = some saved3.toNat
  saved7Read : read64 m (sp.toNat + 1016) = some saved7.toNat

/-- Scope allocation, every binding, and body execution preserve the concrete return loads. -/
theorem BodyRunAt.return_reads
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve : Nat}
    {st final : Vsa.While.St} {env : Nat} {cd : ClosureData} {values : List Value} {status : Status}
    {sp call object fn interp parent saved5 saved3 saved7 p : BitVec 64} {depth : Nat}
    {before called head after : Config}
    (h : BodyRunAt N M phiF phiC shared reserve st final env cd values status
      sp call object fn interp parent saved5 saved3 depth before called head p after)
    (G : Geometry sp call object fn interp) (bound : depth < 1000)
    (stackHi : sp.toNat + 1056 ≤ SL.hi) (interpHi : interp.toNat + 12 ≤ SL.hi)
    (saved7Read : read64 before.σ.mem (sp.toNat + 1016) = some saved7.toNat) :
    BodyReturnReads after.σ.mem sp interp saved5 saved3 saved7 depth := by
  have agreement : AgreeP (fun k => sp.toNat + 1032 ≤ k ∧ k < SL.hi) called.σ.mem after.σ.mem :=
    fun k hk => h.highStack k hk.1 hk.2
  exact
    { depthRead := (read32_agreeP agreement (by
        intro k hk; have := G.interpAbove; constructor <;> omega)).symm.trans (h.dispatch.depth_read G bound)
      saved5Read := (read64_agreeP agreement (by intro k hk; constructor <;> omega)).symm.trans h.dispatch.saved5Read
      saved3Read := (read64_agreeP agreement (by intro k hk; constructor <;> omega)).symm.trans h.dispatch.saved3Read
      saved7Read := (read64_agreeP (P := fun k => sp.toNat + 1016 ≤ k ∧ k < sp.toNat + 1024)
        (fun k hk => h.saved7Frame k hk.1 hk.2) (by intro k hk; constructor <;> omega)).symm.trans saved7Read }

end Vsa.Sim.ClosureCallPrefix
