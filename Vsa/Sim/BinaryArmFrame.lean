import Vsa.Sim.DeriveMetaTowers

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- Saved registers and the actual arm-entry ghost frame. -/
structure BinaryArmFrame
    (g gpre : (R : Register) → Option (RegisterType R))
    (sp aExpr v8 v9 v18 v19 : BitVec 64) : Prop where
  saved8 : g Register.x8 = some v8
  saved9 : g Register.x9 = some v9
  saved18 : g Register.x18 = some v18
  savedSp : g Register.x2 = some sp
  saved19 : g Register.x19 = some v19
  node : gpre Register.x8 = some aExpr
  bridge : ∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R

/-- Project the existing arm-entry facts at the reached configuration. -/
theorem BinaryArmFrame.of_entry
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {armPC : BitVec 64} {callee : Mem → Prop} {e : Expr}
    {sp r sret aExpr aEnv v8 v9 v18 v19 : BitVec 64} {out : Array String}
    {m0 ment : Mem} {c : Config}
    (h : ArmEntryK g N A SL phiF phiC st armPC callee e sp r sret aExpr aEnv
      v8 v9 v18 out m0 ment c)
    (hpre : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R)
    (h19 : gpre Register.x19 = some v19) :
    BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st armPC callee e
    sp r sret aExpr aEnv v8 v9 v18 out m0 ment c h
  have bridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R :=
    fun R hR h8 h9 h18 h2 => (hpre R hR).symm.trans (p.frame R hR h8 h9 h18 h2)
  exact
    { saved8 := p.saved8
      saved9 := p.saved9
      saved18 := p.saved18
      savedSp := p.savedSp
      saved19 := (bridge Register.x19 (by decide) (by decide) (by decide)
        (by decide) (by decide)).symm.trans h19
      node := (hpre Register.x8 (by decide)).symm.trans p.node
      bridge := bridge }

#print axioms BinaryArmFrame.of_entry
end Vsa.Sim
