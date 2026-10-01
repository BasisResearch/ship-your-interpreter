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

/-! ## Keys: an address as an atom plus a literal offset

A keyed address and a region base that normalise to the same atom `t` plus literal offsets
`c` and `c0` decide membership by literals alone: `c0 ≤ c ∧ c + w ≤ c0 + L ∧ 0 < w`, where `L`
is the literal extent (or a literal floor of a symbolic one). The check is one closed boolean,
so the kernel evaluates it on literals. -/

section Keys

theorem lin_lit (n : Nat) : n = 0 + n := (Nat.zero_add n).symm
theorem lin_atom (x : Nat) : x = x + 0 := rfl
theorem lin_addL {x y t a b c : Nat} (px : x = t + a) (py : y = 0 + b) (hc : a + b = c) :
    x + y = t + c := by subst px py hc; omega
theorem lin_addR {x y u a b c : Nat} (px : x = 0 + a) (py : y = u + b) (hc : a + b = c) :
    x + y = u + c := by subst px py hc; omega
theorem lin_trans {x y t c : Nat} (h : x = y) (py : y = t + c) : x = t + c := h.trans py
/-- An inner wrap-around is removed by the bound on the whole key. -/
theorem lin_mod {y t c' c M : Nat} (py : y = t + c') (hlt : t + c < M) (h : Nat.ble c' c = true) :
    y % M = t + c' := by
  rw [Nat.ble_eq] at h; rw [py, Nat.mod_eq_of_lt (by omega)]
theorem lin_mod0 {y c' M : Nat} (py : y = 0 + c') (h : Nat.blt c' M = true) : y % M = 0 + c' := by
  rw [Nat.blt_eq] at h; rw [py, Nat.mod_eq_of_lt (by omega)]
theorem lin_key {x t c A : Nat} (px : x = t + c) (hA : x = A) : t + c = A := px ▸ hA
theorem ext_lit (e : Nat) : e ≤ e := Nat.le_refl e
theorem ext_le {e s k L0 L : Nat} (pe : e = s + k) (hs : L0 ≤ s) (hc : L0 + k = L) : L ≤ e := by
  subst pe hc; omega

theorem key_chk {c0 c w L : Nat}
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    c0 ≤ c ∧ c + w ≤ c0 + L ∧ 0 < w := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h; omega

theorem key_al {t c m w : Nat} (hal : t % m = 0) (h : (m % w == 0 && c % w == 0) = true) :
    (t + c) % w = 0 := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h.1)
    (Nat.dvd_of_mod_eq_zero hal)) (Nat.dvd_of_mod_eq_zero h.2))

variable {S : Nat → Prop} {b e t c0 c L A m : Nat}

theorem ARgn.lt_k (r : ARgn S b e) (hb : b = t + c0) (he : L ≤ e) (c w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    t + c < 18446744073709551616 := by
  have h := key_chk h; have := r.hi; omega

theorem ARgn.ldOK_k (r : ARgn S b e) (hb : b = t + c0) (he : L ≤ e) (hA : t + c = A) (w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) : LdOK A w := by
  have h := key_chk h; subst hb hA; exact r.ldOK (by omega)

theorem ARgn.stOK_k (r : ARgn S b e) (hb : b = t + c0) (he : L ≤ e) (hA : t + c = A) (w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true)
    (hal : t % m = 0) (ha : (m % w == 0 && c % w == 0) = true) : StOK A w := by
  have h2 := key_al hal ha
  have h := key_chk h; subst hb hA; exact r.stOK ⟨by omega, by omega, h2⟩

theorem ARgn.acc_k (r : ARgn S b e) (hb : b = t + c0) (he : L ≤ e) (hA : t + c = A) (w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    ∀ x ∈ accAddrs A w, S x := by
  have h := key_chk h; subst hb hA; exact r.acc ⟨by omega, by omega⟩

end Keys

end VsaIris.VsaHeap
