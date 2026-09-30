import VsaIris.Vsa.SymRun

/-!
# Regions: the laws shared by every region-keyed layer

A region is a base and an extent whose bytes all satisfy an ownership predicate (`Rgn`); an
access region (`ARgn`) also lies inside RAM and off the mailbox, so an access inside it is
permitted (`ARgn.ldOK`, `ARgn.stOK`) and owned (`ARgn.acc`). Each law takes the key-in-region
check as one conjunction. The allocator layer (`Region.lean`) mints regions from the heap
walk and closes the check with linear arithmetic; the stack-window layer (`Stdout/Win.lean`)
mints one region per stack frame and closes the check by `decide` on literal offsets.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim VsaIris.Sym

/-- `ext` consecutive bytes from `base`, each satisfying `P`. -/
structure Rgn (P : Nat → Prop) (base ext : Nat) : Prop where
  byte : ∀ k, k < ext → P (base + k)

namespace Rgn

variable {P P' : Nat → Prop} {b e : Nat}

theorem mem (r : Rgn P b e) {a : Nat} (h1 : b ≤ a) (h2 : a < b + e) : P a := by
  have := r.byte (a - b) (by omega)
  rwa [show b + (a - b) = a by omega] at this

theorem sub (r : Rgn P b e) {b' e' : Nat} (h1 : b ≤ b') (h2 : b' + e' ≤ b + e) : Rgn P b' e' :=
  ⟨fun k hk => r.mem (by omega) (by omega)⟩

theorem mono (r : Rgn P b e) (h : ∀ a, P a → P' a) : Rgn P' b e :=
  ⟨fun k hk => h _ (r.byte k hk)⟩

theorem word (r : Rgn P b e) {a w : Nat} (h1 : b ≤ a) (h2 : a + w ≤ b + e) :
    ∀ k, k < w → P (a + k) :=
  (r.sub h1 h2).byte

end Rgn

section Laws

variable {b e a w : Nat}

/-- An access region: bytes owned under `S`, inside RAM and off the mailbox. It
carries its own access-range facts, so it needs no heap context (copy sources and
destinations, caller buffers). -/
structure ARgn (S : Nat → Prop) (base ext : Nat) : Prop where
  own : Rgn S base ext
  lo : 0x8001ad10 ≤ base
  hi : base + ext ≤ 0x100000000

theorem ARgn.ldOK {S : Nat → Prop} (r : ARgn S b e) (h : b ≤ a ∧ a + w ≤ b + e) : LdOK a w := by
  have := r.lo; have := r.hi; unfold LdOK Vsa.Sim.tohostAddr; omega

theorem ARgn.stOK {S : Nat → Prop} (r : ARgn S b e) (h : b ≤ a ∧ a + w ≤ b + e ∧ a % w = 0) :
    StOK a w := by
  have := r.lo; have := r.hi; unfold StOK Vsa.Sim.tohostAddr; omega

theorem ARgn.acc {S : Nat → Prop} (r : ARgn S b e) (h : b ≤ a ∧ a + w ≤ b + e) :
    ∀ x ∈ accAddrs a w, S x := fun x hx => by
  have := of_mem_accAddrs hx
  exact r.own.mem (by omega) (by omega)

end Laws

end VsaIris.VsaHeap
