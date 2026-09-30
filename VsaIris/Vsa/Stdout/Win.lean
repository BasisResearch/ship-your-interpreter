import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.SymCompact
import VsaIris.Vsa.SymExec
import VsaIris.Vsa.RegionCore

/-!
# Stack windows: address keys for the newlib runs

Every address of a newlib run is a static literal or `sp + c` with a literal `c`. A
`StackWin S sp n` is the access region (`ARgn`, `RegionCore.lean`) of the `n` bytes below
`sp`, aligned, and placed off the static data window `[0x8001b520, 0x8001c168)`. Over it,
each address side condition is one `decide` on the literals:

* access permitted and owned: `StackWin.ldOK`, `.stOK`, `.stOKb`, `.own` (instances of the region
  laws `ARgn.ldOK`/`.stOK`/`.acc` through the key check `StackWin.key`);
* two stack accesses: `SymExec.sepC_sound`; stack against static: `.static_stack`,
  `.stack_static`; two literals: `decide`;
* membership of the forgotten stack `[sp - n, sp + c)`: `.static_out`, `.stack_out`,
  `.stack_in`; of the whole window: `.static_outN`, `.key`.

`open scoped VsaIris.Sym.Win` makes `nx_addr`, `nx_fdisch` and `sx_side` try these first
(`win_key`, `win_side`) and keeps the register file of an `nx_run` compact (`nx_tidy`); the
arithmetic dischargers remain the fallback. A run puts its window in the
context once: `StackWin.of_out` / `.of_top` from the usual `hs1 … hal` hypotheses.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.VsaHeap

/-- The `n` bytes below `sp`: owned under `S`, inside RAM and off the mailbox, 16-aligned at the
top, and off the static data window. -/
structure StackWin (S : Nat → Prop) (sp : BitVec 64) (n : Nat) : Prop where
  rgn : ARgn S (sp.toNat - n) n
  align : sp.toNat % 16 = 0
  place : sp.toNat ≤ 0x8001b520 ∨ 0x8001c168 + n ≤ sp.toNat

namespace StackWin

variable {S : Nat → Prop} {sp c c2 : BitVec 64} {n a w w1 w2 : Nat}

/-- The key check: a literal offset `c` (that is, `sp - (2^64 - c)`) of width `w` is in the window. -/
theorem key (hw : StackWin S sp n) (h : w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    sp.toNat - n ≤ (sp + c).toNat ∧ (sp + c).toNat + w ≤ sp.toNat - n + n := by
  have h1 := hw.rgn.lo; have := sp.isLt; have := c.isLt
  rw [BitVec.toNat_add]; omega

theorem ldOK (hw : StackWin S sp n) (h : w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    LdOK (sp + c).toNat w :=
  hw.rgn.ldOK (hw.key h)

theorem stOK (hw : StackWin S sp n)
    (h : (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n ∧
      c.toNat % w = 0) : StOK (sp + c).toNat w := by
  obtain ⟨hw', h1, h2, h3⟩ := h
  have k := hw.key ⟨h1, h2⟩
  refine hw.rgn.stOK ⟨k.1, k.2, ?_⟩
  have := hw.align; have := hw.rgn.lo; have := sp.isLt; have := c.isLt
  rw [BitVec.toNat_add]
  rcases hw' with rfl | rfl | rfl | rfl <;> omega

theorem stOKb (hw : StackWin S sp n) (h : 1 ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    StOKb (sp + c).toNat := by
  have k := hw.key h
  have := hw.rgn.lo; have := hw.rgn.hi
  unfold StOKb tohostAddr; omega

theorem own (hw : StackWin S sp n) (h : w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    ∀ b, b ∈ accAddrs (sp + c).toNat w → S b :=
  hw.rgn.acc (hw.key h)

/-- Static access against a stack access. -/
theorem static_stack (hw : StackWin S sp n)
    (h : 0x8001b520 ≤ a ∧ a + w1 ≤ 0x8001c168 ∧ w2 ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    a + w1 ≤ (sp + c).toNat ∨ (sp + c).toNat + w2 ≤ a := by
  obtain ⟨h1, h2, h3⟩ := h
  have k := hw.key h3; have := hw.place; have := hw.rgn.lo
  omega

/-- Stack access against a static access. -/
theorem stack_static (hw : StackWin S sp n)
    (h : 0x8001b520 ≤ a ∧ a + w2 ≤ 0x8001c168 ∧ w1 ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    (sp + c).toNat + w1 ≤ a ∨ a + w2 ≤ (sp + c).toNat :=
  (hw.static_stack h).symm

/-- A static access is outside the forgotten stack `[sp - n, sp + c)`. -/
theorem static_out (hw : StackWin S sp n)
    (h : 0x8001b520 ≤ a ∧ a + w ≤ 0x8001c168 ∧ 2 ^ 64 - c.toNat ≤ n) :
    a + w ≤ sp.toNat - n ∨ sp.toNat - n + ((sp + c).toNat - (sp.toNat - n)) ≤ a := by
  obtain ⟨h1, h2, h3⟩ := h
  have k := hw.key (w := 0) ⟨Nat.zero_le _, h3⟩; have := hw.place; have := hw.rgn.lo
  omega

/-- A stack access at or above `sp + c` is outside the forgotten stack `[sp - n, sp + c)`. -/
theorem stack_out (hw : StackWin S sp n) (h : c.toNat ≤ c2.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    (sp + c2).toNat + w ≤ sp.toNat - n ∨
      sp.toNat - n + ((sp + c).toNat - (sp.toNat - n)) ≤ (sp + c2).toNat := by
  have h1 := hw.rgn.lo; have := sp.isLt; have := c.isLt; have := c2.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add]; omega

/-- A stack access below `sp + c` is inside the forgotten stack `[sp - n, sp + c)`. -/
theorem stack_in (hw : StackWin S sp n) (h : 2 ^ 64 - c2.toNat ≤ n ∧ c2.toNat + w ≤ c.toNat) :
    sp.toNat - n ≤ (sp + c2).toNat ∧
      (sp + c2).toNat + w ≤ sp.toNat - n + ((sp + c).toNat - (sp.toNat - n)) := by
  have h1 := hw.rgn.lo; have := sp.isLt; have := c.isLt; have := c2.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add]; omega

/-- A static access is outside the whole window. -/
theorem static_outN (hw : StackWin S sp n) (h : 0x8001b520 ≤ a ∧ a + w ≤ 0x8001c168) :
    a + w ≤ sp.toNat - n ∨ sp.toNat - n + n ≤ a := by
  have := hw.place; have := hw.rgn.lo
  omega

end StackWin

/-! ### The footprint `outS` -/

/-- The window of a callee frame: `frame` bytes below `sp`, inside the caller's `outS s need`. -/
theorem StackWin.of_out {s sp : BitVec 64} {need frame : Nat}
    (hs1 : s.toNat - need + frame ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) :
    StackWin (outS s need) sp frame :=
  ⟨⟨⟨fun k hk => .inr (.inr (by omega))⟩, by omega, by omega⟩, hal, .inr (by omega)⟩

/-- The whole window of `outS s need`. -/
theorem StackWin.of_top {s : BitVec 64} {need : Nat} (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) :
    StackWin (outS s need) s need :=
  ⟨⟨⟨fun k hk => .inr (.inr (by omega))⟩, by omega, by omega⟩, hal, .inr (by omega)⟩

theorem stdioFoot_rng (a n : Nat)
    (h : (decide (0x8001b520 ≤ a ∧ a + n ≤ 0x8001b538) || decide (0x8001b53c ≤ a ∧ a + n ≤ 0x8001b960) ||
      decide (0x8001b978 ≤ a ∧ a + n ≤ 0x8001b990) || decide (0x8001b9b0 ≤ a ∧ a + n ≤ 0x8001ba08) ||
      decide (0x8001ba0c ≤ a ∧ a + n ≤ 0x8001ba18) || decide (0x8001ba68 ≤ a ∧ a + n ≤ 0x8001c168)) = true) :
    ∀ i, i < n → stdioFoot (a + i) ∧ ¬ impureW (a + i) := by
  intro i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold stdioFoot InRange impureW
  omega

/-- A static access inside the stdio footprint (off the impure word) is inside `outS`. -/
theorem outS_static {s : BitVec 64} {need a w : Nat}
    (h : (decide (0x8001b520 ≤ a ∧ a + w ≤ 0x8001b538) || decide (0x8001b53c ≤ a ∧ a + w ≤ 0x8001b960) ||
      decide (0x8001b978 ≤ a ∧ a + w ≤ 0x8001b990) || decide (0x8001b9b0 ≤ a ∧ a + w ≤ 0x8001ba08) ||
      decide (0x8001ba0c ≤ a ∧ a + w ≤ 0x8001ba18) || decide (0x8001ba68 ≤ a ∧ a + w ≤ 0x8001c168)) = true) :
    ∀ b, b ∈ accAddrs a w → outS s need b := by
  intro b hb
  have hb := mem_accAddrs_iff.mp hb
  have := stdioFoot_rng a w h (b - a) (by omega)
  rw [show a + (b - a) = b by omega] at this
  exact .inl this

/-- An access to the errno word is inside `outS`. -/
theorem outS_errno {s : BitVec 64} {need a w : Nat} (h : 0x8001ba08 ≤ a ∧ a + w ≤ 0x8001ba0c) :
    ∀ b, b ∈ accAddrs a w → outS s need b := by
  intro b hb
  have hb := mem_accAddrs_iff.mp hb
  exact .inr (.inl (by omega))

/-! ### Dischargers -/

/-- The key lemmas, on a goal whose offsets are literals. -/
macro "win_key0" : tactic => `(tactic| first
  | exact VsaIris.SymExec.sepC_sound (by decide)
  | decide
  | exact StackWin.static_stack (by assumption) (by decide)
  | exact StackWin.stack_static (by assumption) (by decide)
  | exact StackWin.static_out (by assumption) (by decide)
  | exact StackWin.stack_out (by assumption) (by decide)
  | exact StackWin.stack_in (by assumption) (by decide)
  | exact StackWin.static_outN (by assumption) (by decide)
  | exact StackWin.key (by assumption) (by decide)
  | fail "win_key: no key applies")

/-- Address disjointness and forgotten-region membership by key; an offset left as `sp + c + c'`
(a callee's frame under the caller's `sp + c`) is folded first. No arithmetic fallback. -/
macro "win_key" : tactic => `(tactic| first
  | win_key0
  | (simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢; win_key0))

/-- The side lemmas, on a goal whose offsets are literals. -/
macro "win_side0" : tactic => `(tactic| first
  | decide
  | exact StackWin.stOK (by assumption) (by decide)
  | exact StackWin.ldOK (by assumption) (by decide)
  | exact StackWin.stOKb (by assumption) (by decide)
  | exact StackWin.own (by assumption) (by decide)
  | exact outS_static (by decide)
  | exact outS_errno (by decide)
  | fail "win_side: no key applies")

/-- Step side goals (access permitted, access owned) by key. No arithmetic fallback. -/
macro "win_side" : tactic => `(tactic| first
  | win_side0
  | (simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢; win_side0))

namespace Win

scoped macro_rules | `(tactic| nx_addr) => `(tactic| win_key)

scoped macro_rules | `(tactic| sx_side) => `(tactic| win_side)

/-- Keep the register file compact during a run. -/
scoped macro_rules | `(tactic| nx_tidy) => `(tactic| nx_compactIf 40)

end Win

end VsaIris.Sym
