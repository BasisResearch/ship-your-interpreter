import VsaIris.Vsa.Fprintf.Tac
import VsaIris.Interp.ProofArith

/-!
# libgcc's divide inside a stdout run (lane N5)

`__sfvwrite_r`'s direct write rounds its length down with `__moddi3`, and
`_vfprintf_r`'s decimal loop divides by ten with `__hidden___udivdi3` and
`__umoddi3`. E2 proved these routines over the interpreter's step table
(`ProofArith.lean`: `udiv_iw`, `moddi3_iw`); they are not in the stdio table
(the lemma names are per PC, so the two tables cannot both list them). A
stdout run whose data view contains the interpreter's code runs them through
`swpo_bridge` (`SymBridge.lean`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}

/-- The interpreter's code (with the run's data view) inside a stdout run's
read-only list. -/
theorem interpText_sub (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) :
    ∀ p ∈ interpText ++ dataOf Dt DA, p ∈ stdioText ++ dataOf Dt DA := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact List.mem_append_right _ (hsub p h)
  · exact List.mem_append_right _ h

/-- **`__moddi3`** (`0x80004728`) inside a stdout run. -/
theorem moddi3_sw (hlive : ∀ p ∈ interpText, live p.1) (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA)
    (x y r : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (hy : y ≠ 0#64) (h10 : R 10 = x)
    (h11 : R 11 = y) (hr : R 1 = r) (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) → SDivKeep R' R →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t r R' Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x80004728#64 R Mt :=
  swpo_bridge (C := fun pc' R' Mt' => pc' = r ∧ Mt' = Mt ∧
      (R' 10).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) ∧ SDivKeep R' R)
    (interpText_sub hsub)
    (fun _ hk' => moddi3_iw hlive x y r R Mt hy h10 h11 hr hal fun R' h1 h2 => hk' r R' Mt ⟨rfl, rfl, h1, h2⟩)
    (fun pc' R' Mt' ⟨e1, e2, h1, h2⟩ => by subst e1 e2; exact hk R' h1 h2)

/-- **`__hidden___udivdi3`** (`0x800046ac`) inside a stdout run: quotient in
`a0`, remainder in `a1`. -/
theorem udiv_sw (hlive : ∀ p ∈ interpText, live p.1) (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA)
    (n d r : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n)
    (h11 : R 11 = d) (hr : R 1 = r) (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R → SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t r R' Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x800046ac#64 R Mt :=
  swpo_bridge (C := fun pc' R' Mt' => pc' = r ∧ Mt' = Mt ∧ (R' 10).toNat = n.toNat / d.toNat ∧
      (R' 11).toNat = n.toNat % d.toNat ∧ DivKeep R' R)
    (interpText_sub hsub)
    (fun _ hk' => udiv_iw hlive n d r R Mt hd h10 h11 hr hal fun R' h1 h2 h3 => hk' r R' Mt ⟨rfl, rfl, h1, h2, h3⟩)
    (fun pc' R' Mt' ⟨e1, e2, h1, h2, h3⟩ => by subst e1 e2; exact hk R' h1 h2 h3)

end VsaIris.Sym.Fp
