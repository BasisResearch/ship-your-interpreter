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

end Vsa.Sim
