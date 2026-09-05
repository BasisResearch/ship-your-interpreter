import Vsa.Sim.ErrorSiteJal

/-!
# Unconditional error-site preconditions are refutable

A configuration with `tick = 2` refutes a universal `JalErrPre`, whose tick
bound is `< 2`. Error routes use conditioned `ReachJal` from `ErrorReach`:
the entry configuration reaches a configuration satisfying `JalErrPre`.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Register

namespace Vsa.Sim

/-- For any site parameters, setting `tick := 2` refutes universal `JalErrPre`. -/
theorem jalErrPre_forall_false
    (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (σ : MState) :
    ¬ (∀ c : Config, JalErrPre g inp m0 pcJal b0 b1 b2 b3 c) := by
  intro h
  -- The universal at tick 2 requires 2 < 2.
  obtain ⟨_hG, _hRE, _hLJ, _hmem, _hpc, _hx10, _hwin, _hminstret, htick, _hframe,
    _hb0, _hb1, _hb2, _hb3⟩ := h ⟨σ, 2, 0⟩
  have : (2 : Nat) < 2 := htick
  exact absurd this (by decide)

#print axioms jalErrPre_forall_false

end Vsa.Sim
