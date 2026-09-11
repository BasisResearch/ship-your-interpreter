import Vsa.Sim.ClosureReturnOwned

namespace Vsa.Sim.ClosureReturn

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

private theorem read32_agrees {m m' : Mem} {a n : Nat}
    (h : read32 m a = some n) (h' : read32 m' a = some n) :
    ∀ k, a ≤ k → k < a + 4 → m[k]? = m'[k]? := by
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, sum⟩ := read32_bytes m a n h
  obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, sum'⟩ := read32_bytes m' a n h'
  have eq0 : b0 = c0 := by
    apply BitVec.eq_of_toNat_eq
    have := b0.isLt; have := c0.isLt; omega
  have eq1 : b1 = c1 := by
    apply BitVec.eq_of_toNat_eq
    have := b1.isLt; have := c1.isLt; rw [eq0] at sum; omega
  have eq2 : b2 = c2 := by
    apply BitVec.eq_of_toNat_eq
    have := b2.isLt; have := c2.isLt; rw [eq0, eq1] at sum; omega
  have eq3 : b3 = c3 := by
    apply BitVec.eq_of_toNat_eq
    rw [eq0, eq1, eq2] at sum; omega
  intro k lo hi
  have cases : k = a ∨ k = a + 1 ∨ k = a + 2 ∨ k = a + 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · rw [hb0, hc0, eq0]
  · rw [hb1, hc1, eq1]
  · rw [hb2, hc2, eq2]
  · rw [hb3, hc3, eq3]

/-- The bounded decrement restores the caller's four original depth bytes. -/
theorem Post.depth_restored
    {N : NativeAddrs} {phiC : Addr → Nat}
    {sp sret interp saved5 saved3 saved7 : BitVec 64} {depth : Nat} {returns : Bool}
    {before after : Config} {m : Mem}
    (h : Post N phiC sp sret interp saved5 saved3 saved7 depth returns before after)
    (original : read32 m (interp.toNat + 8) = some depth) (bound : depth < 1000) :
    ∀ k, interp.toNat + 8 ≤ k → k < interp.toNat + 12 →
      ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → after.σ.mem[k]? = m[k]? := by
  have written : read32 (writeLog before.σ.mem [(interp.toNat + 8, 4, BitVec.ofNat 64 depth)])
      (interp.toNat + 8) = some depth := by
    have write (mem : Mem) (a : Nat) (v : BitVec 64) :
        writeLog mem [(a, 4, v)] = writeMap4 mem a (swData v) := rfl
    rw [write, read32_writeMap4, swData_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show depth < 2^64 by omega), Nat.mod_eq_of_lt (show depth < 2^32 by omega)]
  intro k lo hi off
  exact (h.restored k off).trans (read32_agrees written original k lo (by omega))

end Vsa.Sim.ClosureReturn

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Actual depth restoration also preserves epilogue slots and the caller's higher frames. -/
theorem BodyRunAt.caller_stack
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve : Nat}
    {st final : Vsa.While.St} {env : Nat} {cd : ClosureData} {values : List Value} {status : Status}
    {sp call object fn interp parent saved5 saved3 saved7 p sret : BitVec 64} {depth : Nat} {returns : Bool}
    {before called head exited after : Config}
    (h : BodyRunAt N M phiF phiC shared reserve st final env cd values status
      sp call object fn interp parent saved5 saved3 depth before called head p exited)
    (post : ClosureReturn.Post N phiC sp sret interp saved5 saved3 saved7 depth returns exited after)
    (original : read32 before.σ.mem (interp.toNat + 8) = some depth) (bound : depth < 1000) :
    ∀ k, sp.toNat + 1056 ≤ k → k < SL.hi →
      ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → after.σ.mem[k]? = before.σ.mem[k]? := by
  intro k lo hi off
  by_cases depthByte : interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12
  · exact post.depth_restored original bound k depthByte.1 depthByte.2 off
  · exact (post.outside k depthByte off).symm.trans ((h.highStack k (by omega) hi).symm.trans
      (h.dispatch.outside k (by unfold footprint; omega)).symm)

end Vsa.Sim.ClosureCallPrefix
