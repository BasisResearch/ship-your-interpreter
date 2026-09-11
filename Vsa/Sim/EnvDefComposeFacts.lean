import Vsa.Sim.EnvDefCompose

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim

/-- The existing strlen return preserves its exact entry memory. -/
theorem strlen_post.mem_eq {r : BitVec 64} {s : String} {m0 : Mem} {c : Config}
    (h : strlen_post r s m0 c) : c.σ.mem = m0 := by
  obtain ⟨_, _, _, _, memory⟩ := h
  exact memory

/-- The existing malloc entry identifies its memory baseline. -/
theorem EnvDefMallocPre.mem_eq
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List (Nat × Nat)}
    {n : Nat} {sp r : BitVec 64} {m0 : Mem} {c : Config}
    (h : EnvDefMallocPre M g exts n sp r m0 c) : c.σ.mem = m0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, memory⟩ := h
  exact memory

/-- The existing memcpy return supplies each byte of its described copy. -/
theorem memcpy_bytepath_post.copied
    {g : (R : Register) → Option (RegisterType R)} {r dst : BitVec 64} {n : Nat}
    {m0 : Mem} {bs : Nat → BitVec 8} {c : Config}
    (h : memcpy_bytepath_post g r dst n m0 bs c) {k : Nat} (hk : k < n) :
    c.σ.mem[dst.toNat + k]? = some (bs k) := by
  obtain ⟨_, _, _, _, copied, _, _, _⟩ := h
  exact copied k hk

#print axioms strlen_post.mem_eq
#print axioms EnvDefMallocPre.mem_eq
#print axioms memcpy_bytepath_post.copied

end Vsa.Sim
