import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.SymCompact
import VsaIris.Vsa.SymExec
import VsaIris.Vsa.RegionCore

/-!
# Stack windows: address keys for the newlib runs

Every address of a newlib run is a static literal, `sp + c` with a literal `c`, or `sp`. A
`StackWin S sp n m` is the access region (`ARgn`, `RegionCore.lean`) of the `n` bytes below and
the `m` bytes above `sp`, aligned, and placed off the static data window
`[0x8001b520, 0x8001c168)`. Over it, each address side condition is one `decide` on the literals:

* the key check `StackWin.key` / `.key0` puts an access inside the region; access permitted and
  owned are then the region laws `ARgn.ldOK`/`.stOK`/`.acc` (`StackWin.ldOK`, `.stOK`, `.stOKb`,
  `.own` and their offset-0 forms);
* two stack accesses: `SymExec.sepC_sound`, `sep0L`, `sep0R`; stack against static:
  `.static_stack`, `.stack_static`, `.static_base`, `.base_static`; two literals: `decide`;
* membership of the forgotten stack `[sp - n, sp + c)`: `.static_out`, `.stack_out`,
  `.stack_in`; of the whole lower window: `.static_outN`, `.stack_inN`.

`win_key` and `win_side` read the shape of the goal and apply the matching lemma.
`open scoped VsaIris.Sym.Win` makes `nx_addr`, `nx_fdisch` and `sx_side` try them first and keeps
the register file of an `nx_run` compact (`nx_tidy`); the arithmetic dischargers remain the
fallback. A run puts its window in the context once: `nx_win sp n m` (from the usual
`hs1 … hal` hypotheses by `omega`), or `StackWin.of_out` / `.of_top`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.VsaHeap

/-- The `n` bytes below and `m` bytes above `sp`: owned under `S`, inside RAM and off the
mailbox, `sp` 8-aligned, and off the static data window. -/
structure StackWin (S : Nat → Prop) (sp : BitVec 64) (n m : Nat) : Prop where
  rgn : ARgn S (sp.toNat - n) (n + m)
  align : sp.toNat % 8 = 0
  place : sp.toNat + m ≤ 0x8001b520 ∨ 0x8001c168 + n ≤ sp.toNat

/-- The key check on a literal offset: `c` is `-k` with the access inside the `n` bytes below, or
non-negative with the access inside the `m` bytes above. -/
def inWin (n m : Nat) (c : BitVec 64) (w : Nat) : Bool :=
  decide (w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) || decide (c.toNat + w ≤ m)

namespace StackWin

variable {S : Nat → Prop} {sp c c2 : BitVec 64} {n m a w w1 w2 : Nat}

theorem key (hw : StackWin S sp n m) (h : inWin n m c w = true) :
    sp.toNat - n ≤ (sp + c).toNat ∧ (sp + c).toNat + w ≤ sp.toNat - n + (n + m) := by
  have h1 := hw.rgn.lo; have h2 := hw.rgn.hi; have := sp.isLt; have := c.isLt
  simp only [inWin, Bool.or_eq_true, decide_eq_true_eq] at h
  rw [BitVec.toNat_add]
  rcases h with h | h <;> omega

theorem key0 (hw : StackWin S sp n m) (h : w ≤ m) :
    sp.toNat - n ≤ sp.toNat ∧ sp.toNat + w ≤ sp.toNat - n + (n + m) := by
  have h1 := hw.rgn.lo; omega

theorem al (hw : StackWin S sp n m) (h : (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ c.toNat % w = 0) :
    (sp + c).toNat % w = 0 := by
  have := hw.align
  rw [BitVec.toNat_add]
  obtain ⟨h1, h2⟩ := h
  rcases h1 with rfl | rfl | rfl | rfl <;> omega

theorem al0 (hw : StackWin S sp n m) (h : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) : sp.toNat % w = 0 := by
  have := hw.align
  rcases h with rfl | rfl | rfl | rfl <;> omega

theorem ldOK (hw : StackWin S sp n m) (h : inWin n m c w = true) : LdOK (sp + c).toNat w :=
  hw.rgn.ldOK (hw.key h)

theorem ldOK0 (hw : StackWin S sp n m) (h : w ≤ m) : LdOK sp.toNat w :=
  hw.rgn.ldOK (hw.key0 h)

theorem stOK (hw : StackWin S sp n m)
    (h : inWin n m c w = true ∧ (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ c.toNat % w = 0) :
    StOK (sp + c).toNat w :=
  have k := hw.key h.1
  hw.rgn.stOK ⟨k.1, k.2, hw.al h.2⟩

theorem stOK0 (hw : StackWin S sp n m) (h : w ≤ m ∧ (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)) :
    StOK sp.toNat w :=
  have k := hw.key0 h.1
  hw.rgn.stOK ⟨k.1, k.2, hw.al0 h.2⟩

theorem stOKb (hw : StackWin S sp n m) (h : inWin n m c 1 = true) : StOKb (sp + c).toNat := by
  have k := hw.key h
  have := hw.rgn.lo; have := hw.rgn.hi
  unfold StOKb tohostAddr; omega

theorem stOKb0 (hw : StackWin S sp n m) (h : 1 ≤ m) : StOKb sp.toNat := by
  have k := hw.key0 h
  have := hw.rgn.lo; have := hw.rgn.hi
  unfold StOKb tohostAddr; omega

theorem own (hw : StackWin S sp n m) (h : inWin n m c w = true) :
    ∀ b, b ∈ accAddrs (sp + c).toNat w → S b :=
  hw.rgn.acc (hw.key h)

theorem own0 (hw : StackWin S sp n m) (h : w ≤ m) : ∀ b, b ∈ accAddrs sp.toNat w → S b :=
  hw.rgn.acc (hw.key0 h)

/-- An access inside the window is off a static access. -/
theorem off_static (hw : StackWin S sp n m) {A : Nat}
    (k : sp.toNat - n ≤ A ∧ A + w2 ≤ sp.toNat - n + (n + m))
    (h : 0x8001b520 ≤ a ∧ a + w1 ≤ 0x8001c168) : a + w1 ≤ A ∨ A + w2 ≤ a := by
  have := hw.place; have := hw.rgn.lo
  omega

/-- Static access against a stack access. -/
theorem static_stack (hw : StackWin S sp n m)
    (h : (0x8001b520 ≤ a ∧ a + w1 ≤ 0x8001c168) ∧ inWin n m c w2 = true) :
    a + w1 ≤ (sp + c).toNat ∨ (sp + c).toNat + w2 ≤ a :=
  hw.off_static (hw.key h.2) h.1

/-- Stack access against a static access. -/
theorem stack_static (hw : StackWin S sp n m)
    (h : (0x8001b520 ≤ a ∧ a + w2 ≤ 0x8001c168) ∧ inWin n m c w1 = true) :
    (sp + c).toNat + w1 ≤ a ∨ a + w2 ≤ (sp + c).toNat :=
  (hw.off_static (hw.key h.2) h.1).symm

theorem static_base (hw : StackWin S sp n m)
    (h : (0x8001b520 ≤ a ∧ a + w1 ≤ 0x8001c168) ∧ w2 ≤ m) :
    a + w1 ≤ sp.toNat ∨ sp.toNat + w2 ≤ a :=
  hw.off_static (hw.key0 h.2) h.1

theorem base_static (hw : StackWin S sp n m)
    (h : (0x8001b520 ≤ a ∧ a + w2 ≤ 0x8001c168) ∧ w1 ≤ m) :
    sp.toNat + w1 ≤ a ∨ a + w2 ≤ sp.toNat :=
  (hw.off_static (hw.key0 h.2) h.1).symm

/-- A static access is outside the forgotten stack `[sp - n, sp + c)`. -/
theorem static_out (hw : StackWin S sp n m)
    (h : 0x8001b520 ≤ a ∧ a + w ≤ 0x8001c168 ∧ 2 ^ 64 - c.toNat ≤ n) :
    a + w ≤ sp.toNat - n ∨ sp.toNat - n + ((sp + c).toNat - (sp.toNat - n)) ≤ a := by
  have h1 := hw.rgn.lo; have := hw.place; have := sp.isLt; have := c.isLt
  rw [BitVec.toNat_add]; omega

/-- A stack access at or above `sp + c` is outside the forgotten stack `[sp - n, sp + c)`. -/
theorem stack_out (hw : StackWin S sp n m) (h : c.toNat ≤ c2.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    (sp + c2).toNat + w ≤ sp.toNat - n ∨
      sp.toNat - n + ((sp + c).toNat - (sp.toNat - n)) ≤ (sp + c2).toNat := by
  have h1 := hw.rgn.lo; have := sp.isLt; have := c.isLt; have := c2.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add]; omega

/-- A stack access below `sp + c` is inside the forgotten stack `[sp - n, sp + c)`. -/
theorem stack_in (hw : StackWin S sp n m) (h : 2 ^ 64 - c2.toNat ≤ n ∧ c2.toNat + w ≤ c.toNat) :
    sp.toNat - n ≤ (sp + c2).toNat ∧
      (sp + c2).toNat + w ≤ sp.toNat - n + ((sp + c).toNat - (sp.toNat - n)) := by
  have h1 := hw.rgn.lo; have := sp.isLt; have := c.isLt; have := c2.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add]; omega

/-- A static access is outside the whole lower window. -/
theorem static_outN (hw : StackWin S sp n m) (h : 0x8001b520 ≤ a ∧ a + w ≤ 0x8001c168) :
    a + w ≤ sp.toNat - n ∨ sp.toNat - n + n ≤ a := by
  have := hw.place; have := hw.rgn.lo
  omega

/-- A stack access below `sp` is inside the whole lower window. -/
theorem stack_inN (hw : StackWin S sp n m) (h : w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    sp.toNat - n ≤ (sp + c).toNat ∧ (sp + c).toNat + w ≤ sp.toNat - n + n := by
  have h1 := hw.rgn.lo; have := sp.isLt; have := c.isLt
  rw [BitVec.toNat_add]; omega

end StackWin

/-- `sp` against `sp + c`. -/
theorem sep0L {sp c : BitVec 64} {w1 w2 : Nat} (h : VsaIris.SymExec.sepC 0#64 w1 c w2 = true) :
    sp.toNat + w1 ≤ (sp + c).toNat ∨ (sp + c).toNat + w2 ≤ sp.toNat := by
  have := VsaIris.SymExec.sepC_sound (b := sp) h
  rwa [BitVec.add_zero] at this

/-- `sp + c` against `sp`. -/
theorem sep0R {sp c : BitVec 64} {w1 w2 : Nat} (h : VsaIris.SymExec.sepC c w1 0#64 w2 = true) :
    (sp + c).toNat + w1 ≤ sp.toNat ∨ sp.toNat + w2 ≤ (sp + c).toNat := by
  have := VsaIris.SymExec.sepC_sound (b := sp) h
  rwa [BitVec.add_zero] at this

/-! ### The footprint `outS` -/

/-- The window of a callee frame: `frame` bytes below and `above` bytes above `sp`, inside the
caller's `outS s need`. -/
theorem StackWin.of_out {s sp : BitVec 64} {need frame above : Nat}
    (hs1 : s.toNat - need + frame ≤ sp.toNat) (hs2 : sp.toNat + above ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) :
    StackWin (outS s need) sp frame above :=
  ⟨⟨⟨fun k hk => .inr (.inr (by omega))⟩, by omega, by omega⟩, by omega, .inr (by omega)⟩

/-- The whole window of `outS s need`. -/
theorem StackWin.of_top {s : BitVec 64} {need : Nat} (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : s.toNat % 16 = 0) :
    StackWin (outS s need) s need 0 :=
  ⟨⟨⟨fun k hk => .inr (.inr (by omega))⟩, by omega, by omega⟩, by omega, .inr (by omega)⟩

/-- A window inside `outS s need`, all premises in one conjunction for `omega`. -/
theorem StackWin.of_outS {s sp : BitVec 64} {need n m : Nat}
    (h : s.toNat - need + n ≤ sp.toNat ∧ sp.toNat + m ≤ s.toNat ∧ s.toNat ≤ 0x88000000 ∧
      0x8001c168 ≤ s.toNat - need ∧ sp.toNat % 8 = 0) : StackWin (outS s need) sp n m :=
  ⟨⟨⟨fun k hk => .inr (.inr (by omega))⟩, by omega, by omega⟩, h.2.2.2.2, .inr (by omega)⟩

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

section Dispatch

open Lean Elab Tactic Meta

/-- The key of an address term. -/
inductive AKey where
  | lit
  | off (x : Expr)
  | base (x : Expr)

def akey? (e : Expr) : MetaM (Option AKey) := do
  let e := e.consumeMData
  if e.nat?.isSome || e.rawNatLit?.isSome then return some .lit
  if e.isAppOfArity ``BitVec.toNat 2 then
    let x := e.appArg!.consumeMData
    if x.isAppOfArity ``HAdd.hAdd 6 then
      -- `b + c` with a literal `c`; an unfolded `b + c + c'` has no key (fold it first)
      let b := x.appFn!.appArg!.consumeMData
      if b.isAppOfArity ``HAdd.hAdd 6 then return none
      if (← getBitVecValue? x.appArg!).isSome then return some (.off b)
      return none
    return some (.base x)
  return none

/-- `A + w ≤ B`: the pair `(A, B)`. -/
def leAdd? (e : Expr) : Option (Expr × Expr) := do
  guard (e.isAppOfArity ``LE.le 4)
  let l := e.appFn!.appArg!
  guard (l.isAppOfArity ``HAdd.hAdd 6)
  some (l.appFn!.appArg!, e.appArg!)

/-- `x.toNat - n` with a literal `n`: the start of a forgotten stack region. -/
def isWinLo (e : Expr) : Bool :=
  e.isAppOfArity ``HSub.hSub 6 && e.appFn!.appArg!.isAppOfArity ``BitVec.toNat 2 &&
    (e.appArg!.nat?.isSome || e.appArg!.rawNatLit?.isSome)

/-- `LO + N ≤ A` or `A + w ≤ LO + N`: is the extent `N` a literal? -/
def extLit (loN : Expr) : Option Bool := do
  guard (loN.isAppOfArity ``HAdd.hAdd 6)
  let N := loN.appArg!
  some (N.nat?.isSome || N.rawNatLit?.isSome)

/-- Address side conditions by the keys of the addresses: disjointness of two accesses
(`A + w₁ ≤ B ∨ B + w₂ ≤ A`), outside a forgotten stack region (`A + w ≤ LO ∨ LO + N ≤ A`),
inside one (`LO ≤ A ∧ A + w ≤ LO + N`). The goal's shape selects the lemma; nothing is tried
blind. -/
elab "win_key0" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let tac ← if let some (p, q) := t.app2? ``Or then do
      let some (A, B) := leAdd? p | throwError "win_key: shape"
      let some ka ← akey? A | throwError "win_key: key"
      if isWinLo B then
        unless q.isAppOfArity ``LE.le 4 do throwError "win_key: shape"
        match extLit q.appFn!.appArg!, ka with
        | some true, .lit => `(tactic| exact StackWin.static_outN (by assumption) (by decide))
        | some false, .lit => `(tactic| exact StackWin.static_out (by assumption) (by decide))
        | some false, .off _ => `(tactic| exact StackWin.stack_out (by assumption) (by decide))
        | _, _ => throwError "win_key: key"
      else
        let some kb ← akey? B | throwError "win_key: key"
        match ka, kb with
        | .lit, .lit => `(tactic| decide)
        | .off x, .off y =>
          unless x == y do throwError "win_key: two bases"
          `(tactic| exact VsaIris.SymExec.sepC_sound (by decide))
        | .base x, .off y =>
          unless x == y do throwError "win_key: two bases"
          `(tactic| exact sep0L (by decide))
        | .off x, .base y =>
          unless x == y do throwError "win_key: two bases"
          `(tactic| exact sep0R (by decide))
        | .lit, .off _ => `(tactic| exact StackWin.static_stack (by assumption) (by decide))
        | .off _, .lit => `(tactic| exact StackWin.stack_static (by assumption) (by decide))
        | .lit, .base _ => `(tactic| exact StackWin.static_base (by assumption) (by decide))
        | .base _, .lit => `(tactic| exact StackWin.base_static (by assumption) (by decide))
        | _, _ => throwError "win_key: key"
    else if let some (p, q) := t.app2? ``And then do
      -- `LO ≤ A ∧ A + w ≤ LO + N`
      unless p.isAppOfArity ``LE.le 4 && isWinLo p.appFn!.appArg! do throwError "win_key: shape"
      let some (.off _) ← akey? p.appArg! | throwError "win_key: key"
      unless q.isAppOfArity ``LE.le 4 do throwError "win_key: shape"
      match extLit q.appArg! with
      | some true => `(tactic| exact StackWin.stack_inN (by assumption) (by decide))
      | some false => `(tactic| exact StackWin.stack_in (by assumption) (by decide))
      | none => throwError "win_key: shape"
    else throwError "win_key: shape"
  evalTactic tac

/-- Access permitted / access owned, by the key of the address. -/
elab "win_acc" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let tac ← if t.isAppOfArity ``LdOK 2 then do
      match ← akey? t.appFn!.appArg! with
      | some .lit => `(tactic| decide)
      | some (.off _) => `(tactic| exact StackWin.ldOK (by assumption) (by decide))
      | some (.base _) => `(tactic| exact StackWin.ldOK0 (by assumption) (by decide))
      | none => throwError "win_acc: key"
    else if t.isAppOfArity ``StOK 2 then do
      match ← akey? t.appFn!.appArg! with
      | some .lit => `(tactic| decide)
      | some (.off _) => `(tactic| exact StackWin.stOK (by assumption) (by decide))
      | some (.base _) => `(tactic| exact StackWin.stOK0 (by assumption) (by decide))
      | none => throwError "win_acc: key"
    else if t.isAppOfArity ``StOKb 1 then do
      match ← akey? t.appArg! with
      | some .lit => `(tactic| decide)
      | some (.off _) => `(tactic| exact StackWin.stOKb (by assumption) (by decide))
      | some (.base _) => `(tactic| exact StackWin.stOKb0 (by assumption) (by decide))
      | none => throwError "win_acc: key"
    else if t.isForall then do
      -- `∀ b, b ∈ accAddrs A w → S b`
      let d := t.bindingBody!
      unless d.isForall && !d.bindingBody!.hasLooseBVar 0 do throwError "win_acc: shape"
      let mem := d.bindingDomain!
      let some acc := mem.getAppArgs.find? (·.isAppOfArity ``accAddrs 2) | throwError "win_acc: shape"
      match ← akey? acc.appFn!.appArg! with
      | some .lit => `(tactic| first | exact outS_static (by decide) | exact outS_errno (by decide))
      | some (.off _) => `(tactic| exact StackWin.own (by assumption) (by decide))
      | some (.base _) => `(tactic| exact StackWin.own0 (by assumption) (by decide))
      | none => throwError "win_acc: key"
    else throwError "win_acc: shape"
  evalTactic tac

/-- `nx_win sp n m`: put the window of the `n` bytes below and `m` bytes above `sp` in the
context as `hw_<sp>`, from the run's stack hypotheses (`omega`). The footprint is read off the goal. -/
elab "nx_win " sp:term:max n:term:max m:term:max : tactic => withMainContext do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  unless ty.getAppFn.isConstOf ``SWP do throwError "nx_win: not an SWP goal"
  let S ← Term.exprToSyntax ty.getAppArgs[3]!
  let hw := mkIdent (if sp.raw.isIdent then Name.mkSimple s!"hw_{sp.raw.getId}" else `hw)
  evalTactic (← `(tactic| have $hw : StackWin $S $sp $n $m := StackWin.of_outS (by omega)))

end Dispatch

/-- Address disjointness and forgotten-region membership by key; an offset left as `sp + c + c'`
(a callee's frame under the caller's `sp + c`) is folded first. No arithmetic fallback. -/
macro "win_key" : tactic => `(tactic| first
  | win_key0
  | (simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢; win_key0))

/-- Step side goals (access permitted, access owned) by key. No arithmetic fallback. -/
macro "win_side" : tactic => `(tactic| first
  | win_acc
  | (simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢; win_acc))

namespace Win

scoped macro_rules | `(tactic| nx_addr) => `(tactic| win_key)

scoped macro_rules | `(tactic| sx_side) => `(tactic| win_side)

/-- Keep the register file compact during a run. -/
scoped macro_rules | `(tactic| nx_tidy) => `(tactic| nx_compactIf 36)

end Win

/-! ### Shape checks -/

section Checks

variable (s : BitVec 64) (hw : StackWin (outS s 768) s 768 0)
include hw

example : ∀ b ∈ accAddrs (s + 18446744073709551472#64).toNat 8, outS s 768 b := by win_side
example : ∀ b ∈ accAddrs 2147596920 2, outS s 768 b := by win_side
example : StOK (s + 18446744073709551472#64).toNat 8 := by win_side
example : LdOK 2147596920 2 := by win_side
example : 2147596920 + 8 ≤ (s + 18446744073709551472#64).toNat ∨
    (s + 18446744073709551472#64).toNat + 8 ≤ 2147596920 := by win_key
example : (s + 18446744073709551472#64).toNat + 8 ≤ (s + 18446744073709551480#64).toNat ∨
    (s + 18446744073709551480#64).toNat + 8 ≤ (s + 18446744073709551472#64).toNat := by win_key
example : s.toNat - 768 ≤ (s + 18446744073709551408#64 + 18446744073709551608#64).toNat ∧
    (s + 18446744073709551408#64 + 18446744073709551608#64).toNat + 8 ≤ s.toNat - 768 + 768 := by
  win_key
example : 2147596920 + 2 ≤ s.toNat - 768 ∨ s.toNat - 768 + 768 ≤ 2147596920 := by win_key
example : 2147596920 + 2 ≤ s.toNat - 768 ∨
    s.toNat - 768 + ((s + 18446744073709551472#64).toNat - (s.toNat - 768)) ≤ 2147596920 := by
  win_key
example : (s + 18446744073709551480#64).toNat + 8 ≤ s.toNat - 768 ∨
    s.toNat - 768 + ((s + 18446744073709551472#64).toNat - (s.toNat - 768)) ≤
      (s + 18446744073709551480#64).toNat := by win_key
example : s.toNat - 768 ≤ (s + 18446744073709551464#64).toNat ∧
    (s + 18446744073709551464#64).toNat + 8 ≤
      s.toNat - 768 + ((s + 18446744073709551472#64).toNat - (s.toNat - 768)) := by win_key

end Checks

end VsaIris.Sym
