import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.Mfr

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

namespace Vsa.Sim

structure W where
  lo : Nat
  hi : Nat

def OutW : List W → Nat → Prop
  | [], _ => True
  | w :: ws, a => (a < w.lo ∨ w.hi ≤ a) ∧ OutW ws a

def OutWRange : List W → Nat → Nat → Prop
  | [], _, _ => True
  | w :: ws, A, n => (A + n ≤ w.lo ∨ w.hi ≤ A) ∧ OutWRange ws A n

def InsideW : List W → Nat → Nat → Prop
  | [], _, _ => False
  | w :: ws, A, n => (w.lo ≤ A ∧ A + n ≤ w.hi) ∨ InsideW ws A n

def FrameOn (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, OutW ws a → m[a]? = m0[a]?

theorem outW_disjoint_inside {ws : List W} {a A n : Nat}
    (ho : OutW ws a) (hi : InsideW ws A n) : a < A ∨ A + n ≤ a := by
  induction ws with
  | nil => exact False.elim hi
  | cons w ws ih =>
    rcases hi with hw | hrest
    · have := ho.1; omega
    · exact ih ho.2 hrest

theorem frameOn_refl (ws : List W) (m : Std.ExtHashMap Nat (BitVec 8)) :
    FrameOn ws m m := fun _ _ => rfl

end Vsa.Sim
