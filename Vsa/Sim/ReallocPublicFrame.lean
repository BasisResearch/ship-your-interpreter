import Vsa.Sim.ReallocSpec

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim

/-- Named facts from the existing realloc ABI postcondition at one endpoint. -/
structure ReallocPostFacts (gpv sp r : BitVec 64)
    (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some r
  stack : c.σ.regs.get? Register.x2 = some sp
  gp : c.σ.regs.get? Register.x3 = some gpv
  abi : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R

/-- Destructure the landed conjunction once; consumers use the named facts. -/
theorem ReallocPost.facts
    {gpv sp r : BitVec 64} {g : (R : Register) → Option (RegisterType R)}
    {c : Config} (h : ReallocPost gpv sp r g c) : ReallocPostFacts gpv sp r g c := by
  obtain ⟨good, tick, pc, stack, gp, abi⟩ := h
  exact ⟨good, tick, pc, stack, gp, abi⟩

/-- The shared realloc entry retains its exact memory baseline. -/
theorem ReallocPre.mem_eq
    {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    {AInv : MState → List Extent → Prop} {exts : List Extent}
    {p n : Nat} {sp r : BitVec 64} {m0 : Mem}
    {g : (R : Register) → Option (RegisterType R)} {c : Config}
    (h : ReallocPre SL gpv headroom AInv exts p n sp r m0 g c) : c.σ.mem = m0 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  exact memory

/-- Either realloc outcome preserves public bytes outside the arena.
The old extent's arena placement is supplied by its ownership geometry. -/
theorem ReallocGrowResult.outside_arena
    {A : Arena} {SL : StackLayout} {privFoot : Nat → Prop}
    {AInv : MState → List Extent → Prop} {exts : List Extent}
    {pOld nOld nNew : Nat} {sp : BitVec 64} {m0 : Mem} {sigma : MState}
    (h : ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 sigma)
    (oldArena : A.contains pOld nOld)
    (a : Nat) (outside : a < A.lo ∨ A.hi ≤ a)
    (hprivate : ¬ privFoot a) (stack : ¬ (SL.lo ≤ a ∧ a < sp.toNat)) :
    sigma.mem[a]? = m0[a]? := by
  rcases h with ⟨_, _, frame⟩ | ⟨pNew, _, _, _, newArena, _, _, _, frame⟩
  · exact frame a hprivate stack (by simp)
  · apply frame a hprivate stack
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rcases oldArena with ⟨lo, hi⟩
      rcases outside with before | after <;> simp only <;> omega
    · rcases newArena with ⟨lo, hi⟩
      rcases outside with before | after <;> simp only <;> omega

#print axioms ReallocPre.mem_eq
#print axioms ReallocPost.facts
#print axioms ReallocGrowResult.outside_arena

end Vsa.Sim
