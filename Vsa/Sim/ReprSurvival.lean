import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Sim.Regions

namespace Vsa.Sim

open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

def AgreeP (P : Nat → Prop) (m m' : Mem) : Prop :=
  ∀ a, P a → m[a]? = m'[a]?

theorem AgreeP.trans {P : Nat → Prop} {m m' m'' : Mem}
    (h1 : AgreeP P m m') (h2 : AgreeP P m' m'') : AgreeP P m m'' :=
  fun a ha => (h1 a ha).trans (h2 a ha)

theorem AgreeP.mono {P Q : Nat → Prop} {m m' : Mem}
    (hsub : ∀ a, Q a → P a) (h : AgreeP P m m') : AgreeP Q m m' :=
  fun a ha => h a (hsub a ha)

theorem readLE_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m') :
    ∀ (n a : Nat), (∀ k, k < n → P (a + k)) → readLE m a n = readLE m' a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a hP
    have hhead : m[a]? = m'[a]? := by
      have := h a (by simpa using hP 0 (Nat.succ_pos n)); simpa using this
    have htail : readLE m (a + 1) n = readLE m' (a + 1) n := by
      apply ih
      intro k hk
      have := hP (k + 1) (by omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    simp only [readLE, hhead, htail]

theorem read64_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 8 → P (a + k)) : read64 m a = read64 m' a :=
  readLE_agreeP h 8 a hP

def ValuePayloadCovered (P : Nat → Prop) (m : Mem) (a : Nat) : Value → Prop
  | .str s => ∀ p, read64 m (a + 8) = some p → ∀ k, k ≤ s.length → P (p + k)
  | .native f => ∀ p, read64 m (a + 8) = some p →
      ∀ k, k ≤ (nativeName f).length → P (p + k)
  | _ => True

end Vsa.Sim
