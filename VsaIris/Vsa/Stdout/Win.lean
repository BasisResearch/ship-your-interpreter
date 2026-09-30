import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.SymCompact
import VsaIris.Vsa.SymExec
import VsaIris.Vsa.RegionCore
import VsaIris.Vsa.Stdout.WinRefute

/-!
# Windows: address keys for the newlib runs

Every address of a newlib run is a static literal or a literal offset from the top `T` of a
stack frame. A `Win S T n m` is the access region (`ARgn`, `RegionCore.lean`) of the `n` bytes
below and the `m` bytes above `T`, aligned, and placed off the static data window
`[0x8001b520, 0x8001c168)`. The key of an address `A` in a window is its position
`A + d = T + u` with literal `d`, `u`; over keys each address side condition is one `decide`:

* access permitted and owned: `Win.ldOK`, `.stOK`, `.stOKb`, `.own` (the region laws
  `ARgn.ldOK`/`.stOK`/`.acc` through `Win.mem`), `.lt64`;
* two accesses in one window: `Win.sep`; in two windows whose separation is in the context:
  `.sepW`, `.sepW'`; window against static: `.static_win`, `.win_static`; two literals: `decide`;
* membership of the forgotten stack `[sp - n, sp + c)`: `StackWin.static_out`, `.stack_out`,
  `.stack_in`; of the whole lower window: `.static_outN`, `.stack_inN`.

Positions are produced per address form: `StackWin.posN`/`.posP` for `(sp + c).toNat` with a
`BitVec` stack pointer (`StackWin S sp n m = Win S sp.toNat n m`), `pos0` for the top itself,
`Win.posK`/`.posK0`/`.posKT`/`.posKT0` for `s - K + k` with a `Nat` stack pointer.

`win_key` and `win_side` read the shape of the goal and apply the matching lemma.
`open scoped VsaIris.Sym.Win` makes `nx_addr`, `nx_fdisch`, `sx_addr` and `sx_side` try them
first and keeps the register file of an `nx_run` compact (`nx_tidy`); the arithmetic dischargers
remain the fallback. A run puts its window in the context once: `nx_win sp n m` (from the usual
`hs1 … hal` hypotheses by `omega`), or `StackWin.of_out` / `.of_top`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.VsaHeap

/-- The `n` bytes below and `m` bytes above `T`: owned under `S`, inside RAM and off the
mailbox, `T` 8-aligned, and off the static data window. -/
structure Win (S : Nat → Prop) (T n m : Nat) : Prop where
  rgn : ARgn S (T - n) (n + m)
  align : T % 8 = 0
  place : T + m ≤ 0x8001b520 ∨ 0x8001c168 + n ≤ T

/-- A window below (and above) a `BitVec` stack pointer. -/
abbrev StackWin (S : Nat → Prop) (sp : BitVec 64) (n m : Nat) : Prop := Win S sp.toNat n m

namespace Win

variable {S S' : Nat → Prop} {T T' n m n' m' A B d u d' u' a w w1 w2 : Nat}

/-- The key check: an address at position `A + d = T + u` with width `w` is in the window. -/
theorem mem (hw : Win S T n m) (p : A + d = T + u) (h : d ≤ n + u ∧ u + w ≤ m + d) :
    T - n ≤ A ∧ A + w ≤ T - n + (n + m) := by
  have := hw.rgn.lo; omega

theorem ldOK (hw : Win S T n m) (p : A + d = T + u) (h : d ≤ n + u ∧ u + w ≤ m + d) : LdOK A w :=
  hw.rgn.ldOK (hw.mem p h)

theorem stOK (hw : Win S T n m) (p : A + d = T + u)
    (h : (d ≤ n + u ∧ u + w ≤ m + d) ∧ (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ d % w = 0 ∧ u % w = 0) :
    StOK A w := by
  obtain ⟨h1, hw', h2, h3⟩ := h
  have k := hw.mem p h1
  refine hw.rgn.stOK ⟨k.1, k.2, ?_⟩
  have := hw.align
  rcases hw' with rfl | rfl | rfl | rfl <;> omega

theorem stOKb (hw : Win S T n m) (p : A + d = T + u) (h : d ≤ n + u ∧ u + 1 ≤ m + d) :
    StOKb A := by
  have k := hw.mem p h
  have := hw.rgn.lo; have := hw.rgn.hi
  unfold StOKb tohostAddr; omega

theorem own (hw : Win S T n m) (p : A + d = T + u) (h : d ≤ n + u ∧ u + w ≤ m + d) :
    ∀ b, b ∈ accAddrs A w → S b :=
  hw.rgn.acc (hw.mem p h)

theorem lt64 (hw : Win S T n m) (p : A + d = T + u) (h : d ≤ n + u ∧ u + 0 ≤ m + d) :
    A < 2 ^ 64 := by
  have k := hw.mem p h
  have := hw.rgn.hi; omega

/-- Two accesses in one window. -/
theorem sep (p : A + d = T + u) (q : B + d' = T + u')
    (h : u + w1 + d' ≤ u' + d ∨ u' + w2 + d ≤ u + d') : A + w1 ≤ B ∨ B + w2 ≤ A := by
  omega

/-- Two keys at one position. -/
theorem pos_eq (p : A + d = T + u) (q : B + d' = T + u') (h : u + d' = u' + d) : A = B := by
  omega

/-- A static access against an access in the window. -/
theorem static_win (hw : Win S T n m) (p : A + d = T + u)
    (h : (0x8001b520 ≤ a ∧ a + w1 ≤ 0x8001c168) ∧ d ≤ n + u ∧ u + w2 ≤ m + d) :
    a + w1 ≤ A ∨ A + w2 ≤ a := by
  have k := hw.mem p h.2
  have := hw.place; have := hw.rgn.lo
  omega

/-- An access in the window against a static access. -/
theorem win_static (hw : Win S T n m) (p : A + d = T + u)
    (h : (0x8001b520 ≤ a ∧ a + w2 ≤ 0x8001c168) ∧ d ≤ n + u ∧ u + w1 ≤ m + d) :
    A + w1 ≤ a ∨ a + w2 ≤ A :=
  (hw.static_win p h).symm

/-- Accesses in two windows, the first window below the second. -/
theorem sepW (h1 : Win S T n m) (h2 : Win S' T' n' m') (hd : T + m ≤ T' - n')
    (p : A + d = T + u) (q : B + d' = T' + u')
    (h : (d ≤ n + u ∧ u + w1 ≤ m + d) ∧ d' ≤ n' + u' ∧ u' + w2 ≤ m' + d') :
    A + w1 ≤ B ∨ B + w2 ≤ A := by
  have ka := h1.mem p h.1; have kb := h2.mem q h.2
  have := h1.rgn.lo
  exact .inl (by omega)

/-- Accesses in two windows, the second window below the first. -/
theorem sepW' (h1 : Win S T n m) (h2 : Win S' T' n' m') (hd : T' + m' ≤ T - n)
    (p : A + d = T + u) (q : B + d' = T' + u')
    (h : (d ≤ n + u ∧ u + w1 ≤ m + d) ∧ d' ≤ n' + u' ∧ u' + w2 ≤ m' + d') :
    A + w1 ≤ B ∨ B + w2 ≤ A := by
  have ka := h1.mem p h.1; have kb := h2.mem q h.2
  have := h2.rgn.lo
  exact .inr (by omega)

/-! Positions with a `Nat` top: `s - K + k`. -/

variable {s K k : Nat}

theorem posK (hw : Win S s n m) (h : K ≤ n) : s - K + k + K = s + k := by
  have := hw.rgn.lo; omega

theorem posK0 (hw : Win S s n m) (h : K ≤ n) : s - K + K = s + 0 := by
  have := hw.rgn.lo; omega

theorem posKT (hw : Win S s n m) (h : K ≤ n ∧ k ≤ K + m) :
    (BitVec.ofNat 64 (s - K + k)).toNat + K = s + k := by
  have := hw.rgn.lo; have := hw.rgn.hi
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem posKT0 (hw : Win S s n m) (h : K ≤ n) : (BitVec.ofNat 64 (s - K)).toNat + K = s + 0 := by
  have := hw.rgn.lo; have := hw.rgn.hi
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

end Win

/-- The position of the top itself. -/
theorem pos0 (T : Nat) : T + 0 = T + 0 := rfl

namespace StackWin

variable {S : Nat → Prop} {sp c c2 : BitVec 64} {n m a w : Nat}

/-- The position of `sp + c` for a negative literal `c`. -/
theorem posN (hw : StackWin S sp n m) (h : 2 ^ 64 - c.toNat ≤ n) :
    (sp + c).toNat + (2 ^ 64 - c.toNat) = sp.toNat + 0 := by
  have := hw.rgn.lo; have := sp.isLt; have := c.isLt
  rw [BitVec.toNat_add]; omega

/-- The position of `sp + c` for a non-negative literal `c`. -/
theorem posP (hw : StackWin S sp n m) (h : c.toNat ≤ m) :
    (sp + c).toNat + 0 = sp.toNat + c.toNat := by
  have := hw.rgn.lo; have := hw.rgn.hi; have := sp.isLt
  rw [BitVec.toNat_add]; omega

/-! The dominant form, `sp + c` with a negative literal `c`, in one step each (two accesses of
one window: `SymExec.sepC_sound`). -/

theorem ldOKN (hw : StackWin S sp n m) (h : w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    LdOK (sp + c).toNat w :=
  Win.ldOK hw (hw.posN h.2) ⟨by omega, by omega⟩

theorem stOKN (hw : StackWin S sp n m)
    (h : (w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) ∧ (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧
      (2 ^ 64 - c.toNat) % w = 0) : StOK (sp + c).toNat w :=
  Win.stOK hw (hw.posN h.1.2) ⟨⟨by omega, by omega⟩, h.2.1, h.2.2, by
    rcases h.2.1 with rfl | rfl | rfl | rfl <;> rfl⟩

theorem stOKbN (hw : StackWin S sp n m) (h : 1 ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    StOKb (sp + c).toNat :=
  Win.stOKb hw (hw.posN h.2) ⟨by omega, by omega⟩

theorem ownN (hw : StackWin S sp n m) (h : w ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    ∀ b, b ∈ accAddrs (sp + c).toNat w → S b :=
  Win.own hw (hw.posN h.2) ⟨by omega, by omega⟩

theorem static_stackN (hw : StackWin S sp n m) {w1 w2 : Nat}
    (h : (0x8001b520 ≤ a ∧ a + w1 ≤ 0x8001c168) ∧ w2 ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    a + w1 ≤ (sp + c).toNat ∨ (sp + c).toNat + w2 ≤ a :=
  Win.static_win hw (hw.posN h.2.2) ⟨h.1, by omega, by omega⟩

theorem stack_staticN (hw : StackWin S sp n m) {w1 w2 : Nat}
    (h : (0x8001b520 ≤ a ∧ a + w2 ≤ 0x8001c168) ∧ w1 ≤ 2 ^ 64 - c.toNat ∧ 2 ^ 64 - c.toNat ≤ n) :
    (sp + c).toNat + w1 ≤ a ∨ a + w2 ≤ (sp + c).toNat :=
  (hw.static_stackN h).symm

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
  ⟨⟨⟨fun k hk => .inr (.inr (by omega))⟩, by omega, by omega⟩, by omega, .inr (by omega)⟩

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

def isNatLit (e : Expr) : Bool := e.consumeMData.nat?.isSome || e.consumeMData.rawNatLit?.isSome

/-- The key of an address term: a literal, or the top of its window with the syntax of its
position proof and its signed offset from the top. -/
inductive AKey where
  | lit (v : Nat)
  | pos (top : Expr) (prf : Term) (off : Int) (neg : Bool := false)

def natLit? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  match e.nat? with
  | some n => some n
  | none => e.rawNatLit?

/-- `s - K + k` / `s - K` with literal `K`, `k`: the top `s` and the offset. -/
def natOff? (e : Expr) : Option (Expr × Int × Bool) := do
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let k ← natLit? e.appArg!
    let l := e.appFn!.appArg!.consumeMData
    guard (l.isAppOfArity ``HSub.hSub 6 && l.appFn!.appArg!.isFVar)
    let K ← natLit? l.appArg!
    some (l.appFn!.appArg!, (k : Int) - K, true)
  else
    guard (e.isAppOfArity ``HSub.hSub 6 && e.appFn!.appArg!.isFVar)
    let K ← natLit? e.appArg!
    some (e.appFn!.appArg!, - (K : Int), false)

def akey? (e : Expr) : TacticM (Option AKey) := do
  let e := e.consumeMData
  if let some v := natLit? e then return some (.lit v)
  if e.isAppOfArity ``BitVec.toNat 2 then
    let x := e.appArg!.consumeMData
    if x.isAppOfArity ``BitVec.ofNat 2 then
      match natOff? x.appArg! with
      | some (s, o, true) => return some (.pos s (← `(Win.posKT (by with_reducible assumption) (by decide))) o)
      | some (s, o, false) => return some (.pos s (← `(Win.posKT0 (by with_reducible assumption) (by decide))) o)
      | none => return none
    if x.isAppOfArity ``HAdd.hAdd 6 then
      -- `b + c` with a literal `c`; an unfolded `b + c + c'` has no key (fold it first)
      let b := x.appFn!.appArg!.consumeMData
      if b.isAppOfArity ``HAdd.hAdd 6 then return none
      let some ⟨_, v⟩ ← getBitVecValue? x.appArg! | return none
      if v.toNat ≥ 2 ^ 63 then
        return some (.pos b (← `(StackWin.posN (by with_reducible assumption) (by decide)))
          ((v.toNat : Int) - 2 ^ 64) true)
      else return some (.pos b (← `(StackWin.posP (by with_reducible assumption) (by decide))) v.toNat)
    return some (.pos x (← `(pos0 _)) 0)
  match natOff? e with
  | some (s, o, true) => return some (.pos s (← `(Win.posK (by with_reducible assumption) (by decide))) o)
  | some (s, o, false) => return some (.pos s (← `(Win.posK0 (by with_reducible assumption) (by decide))) o)
  | none => return none

/-- The windows of the context: `(T, n, m)`. -/
def ctxWins : TacticM (Array (Expr × Expr × Expr)) := withMainContext do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``Win 4 then
      return acc.push (t.getAppArgs[1]!, t.getAppArgs[2]!, t.getAppArgs[3]!)
    else return acc

/-- The accesses `[o, o + w)` (offsets from `top`) lie in a window of the context with that top:
their positions are then exact, and a literal comparison of them is a fact about the addresses. -/
def inCtxWin (top : Expr) (accs : List (Int × Nat)) : TacticM Bool := do
  for (T, n, m) in ← ctxWins do
    let T := T.consumeMData
    let same := T == top || (T.isAppOfArity ``BitVec.toNat 2 && T.appArg!.consumeMData == top)
    if same then
      if let (some n, some m) := (natLit? n, natLit? m) then
        if accs.all fun (o, w) => - (n : Int) ≤ o && o + w ≤ m then return true
  return false

/-- `A + w ≤ B`: the pair `(A, B)`. -/
def leAdd? (e : Expr) : Option (Expr × Expr) := do
  guard (e.isAppOfArity ``LE.le 4)
  let l := e.appFn!.appArg!
  guard (l.isAppOfArity ``HAdd.hAdd 6)
  some (l.appFn!.appArg!, e.appArg!)

/-- `x.toNat - n` with a literal `n`: the start of a forgotten stack region. -/
def isWinLo (e : Expr) : Bool :=
  e.isAppOfArity ``HSub.hSub 6 && e.appFn!.appArg!.isAppOfArity ``BitVec.toNat 2 &&
    isNatLit e.appArg!

/-- `LO + N ≤ A` or `A + w ≤ LO + N`: is the extent `N` a literal? -/
def extLit (loN : Expr) : Option Bool := do
  guard (loN.isAppOfArity ``HAdd.hAdd 6)
  some (isNatLit loN.appArg!)

/-- Address side conditions by the keys of the addresses: disjointness of two accesses
(`A + w₁ ≤ B ∨ B + w₂ ≤ A`), outside a forgotten stack region (`A + w ≤ LO ∨ LO + N ≤ A`),
inside one (`LO ≤ A ∧ A + w ≤ LO + N`), below `2 ^ 64`, equal (`A = B`). The goal's shape
selects the lemma; nothing is tried blind. When the keys show the condition false, the
exception `winRefuted` is thrown. -/
def winKeyCore : TacticM Unit := withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let tac ← if let some (p, q) := t.app2? ``Or then do
      let some (A, B) := leAdd? p | throwError "win_key: shape"
      if isWinLo B then
        unless q.isAppOfArity ``LE.le 4 do throwError "win_key: shape"
        let some ka ← akey? A | throwError "win_key: key"
        let aLit := match ka with | .lit _ => true | _ => false
        match extLit q.appFn!.appArg!, aLit with
        | some true, true => `(tactic| exact StackWin.static_outN (by with_reducible assumption) (by decide))
        | some false, true => `(tactic| exact StackWin.static_out (by with_reducible assumption) (by decide))
        | some false, false => `(tactic| exact StackWin.stack_out (by with_reducible assumption) (by decide))
        | _, _ => throwError "win_key: key"
      else
        let some ka ← akey? A | throwError "win_key: key"
        let some kb ← akey? B | throwError "win_key: key"
        -- the widths, when literal
        let w1 := natLit? p.appFn!.appArg!.appArg!
        let w2 := if q.isAppOfArity ``LE.le 4 && q.appFn!.appArg!.isAppOfArity ``HAdd.hAdd 6 then
          natLit? q.appFn!.appArg!.appArg! else none
        match ka, kb with
        | .lit a, .lit b =>
          if let (some w1, some w2) := (w1, w2) then
            unless a + w1 ≤ b || b + w2 ≤ a do throwWinRefuted
          `(tactic| decide)
        | .pos x pa oa na, .pos y pb ob nb =>
          if x == y then
            if let (some w1, some w2) := (w1, w2) then
              unless oa + w1 ≤ ob || ob + w2 ≤ oa do
                if ← inCtxWin x [(oa, w1), (ob, w2)] then throwWinRefuted
            if na && nb then `(tactic| exact VsaIris.SymExec.sepC_sound (by decide))
            else `(tactic| exact Win.sep $pa $pb (by decide))
          else `(tactic| first
            | exact Win.sepW (by with_reducible assumption) (by with_reducible assumption)
                (by with_reducible assumption) $pa $pb (by decide)
            | exact Win.sepW' (by with_reducible assumption) (by with_reducible assumption)
                (by with_reducible assumption) $pa $pb (by decide))
        | .lit _, .pos _ pb _ nb =>
          if nb then `(tactic| exact StackWin.static_stackN (by with_reducible assumption) (by decide))
          else `(tactic| exact Win.static_win (by with_reducible assumption) $pb (by decide))
        | .pos _ pa _ na, .lit _ =>
          if na then `(tactic| exact StackWin.stack_staticN (by with_reducible assumption) (by decide))
          else `(tactic| exact Win.win_static (by with_reducible assumption) $pa (by decide))
    else if let some (p, q) := t.app2? ``And then do
      -- `LO ≤ A ∧ A + w ≤ LO + N`
      unless p.isAppOfArity ``LE.le 4 && isWinLo p.appFn!.appArg! do throwError "win_key: shape"
      unless q.isAppOfArity ``LE.le 4 do throwError "win_key: shape"
      let some (.pos _ _ _ _) ← akey? p.appArg! | throwError "win_key: key"
      match extLit q.appArg! with
      | some true => `(tactic| exact StackWin.stack_inN (by with_reducible assumption) (by decide))
      | some false => `(tactic| exact StackWin.stack_in (by with_reducible assumption) (by decide))
      | none => throwError "win_key: shape"
    else if t.isAppOfArity ``LT.lt 4 then do
      -- `A < 2 ^ 64`
      let some (.pos _ pa _ _) ← akey? t.appFn!.appArg! | throwError "win_key: key"
      `(tactic| exact Win.lt64 (by with_reducible assumption) $pa (by decide))
    else if t.isAppOfArity ``Eq 3 then do
      -- `A = B`
      let A := t.appFn!.appArg!.consumeMData
      let B := t.appArg!.consumeMData
      if A == B then `(tactic| rfl)
      else
        let some ka ← akey? A | throwError "win_key: key"
        let some kb ← akey? B | throwError "win_key: key"
        match ka, kb with
        | .lit a, .lit b => if a == b then `(tactic| rfl) else throwWinRefuted
        | .pos x pa oa _, .pos y pb ob _ =>
          unless x == y do throwError "win_key: two bases"
          if oa == ob then `(tactic| exact Win.pos_eq $pa $pb (by decide))
          else if ← inCtxWin x [(oa, 0), (ob, 0)] then throwWinRefuted
          else throwError "win_key: key"
        | _, _ => throwError "win_key: key"
    else throwError "win_key: shape"
  withoutRecover (evalTactic tac)

elab "win_key0" : tactic => winKeyCore

/-- Address disjointness, equality and forgotten-region membership by key; an offset left as
`sp + c + c'` (a callee's frame under the caller's `sp + c`) is folded first. No arithmetic
fallback; a condition the keys show false stops the alternatives behind it (`winRefuted`). -/
elab "win_key" : tactic => do
  let s ← saveState
  try winKeyCore
  catch e =>
    if isWinRefuted e then throw e
    s.restore
    withoutRecover
      (evalTactic (← `(tactic| (simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢; win_key0))))

/-- Access permitted / access owned, by the key of the address. `stat` closes the ownership of a
static access in the footprint at hand. -/
def winAcc (stat : TSyntax `tactic) : TacticM Unit := withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let tac ← if t.isAppOfArity ``LdOK 2 then do
      match ← akey? t.appFn!.appArg! with
      | some (.lit _) => `(tactic| decide)
      | some (.pos _ _ _ true) => `(tactic| exact StackWin.ldOKN (by with_reducible assumption) (by decide))
      | some (.pos _ pa _ false) => `(tactic| exact Win.ldOK (by with_reducible assumption) $pa (by decide))
      | none => throwError "win_acc: key"
    else if t.isAppOfArity ``StOK 2 then do
      match ← akey? t.appFn!.appArg! with
      | some (.lit _) => `(tactic| decide)
      | some (.pos _ _ _ true) => `(tactic| exact StackWin.stOKN (by with_reducible assumption) (by decide))
      | some (.pos _ pa _ false) => `(tactic| exact Win.stOK (by with_reducible assumption) $pa (by decide))
      | none => throwError "win_acc: key"
    else if t.isAppOfArity ``StOKb 1 then do
      match ← akey? t.appArg! with
      | some (.lit _) => `(tactic| decide)
      | some (.pos _ _ _ true) => `(tactic| exact StackWin.stOKbN (by with_reducible assumption) (by decide))
      | some (.pos _ pa _ false) => `(tactic| exact Win.stOKb (by with_reducible assumption) $pa (by decide))
      | none => throwError "win_acc: key"
    else if t.isForall then do
      -- `∀ b, b ∈ accAddrs A w → S b`
      let d := t.bindingBody!
      unless d.isForall && !d.bindingBody!.hasLooseBVar 0 do throwError "win_acc: shape"
      let mem := d.bindingDomain!
      let some acc := mem.getAppArgs.find? (·.isAppOfArity ``accAddrs 2) | throwError "win_acc: shape"
      match ← akey? acc.appFn!.appArg! with
      | some (.lit _) => pure stat
      | some (.pos _ _ _ true) => `(tactic| exact StackWin.ownN (by with_reducible assumption) (by decide))
      | some (.pos _ pa _ false) => `(tactic| exact Win.own (by with_reducible assumption) $pa (by decide))
      | none => throwError "win_acc: key"
    else throwError "win_acc: shape"
  withoutRecover (evalTactic tac)

/-- `win_foot f`: the goal is `∀ b, b ∈ accAddrs a w → f … b`. Guards a footprint's static
ownership lemma, so no lemma is unified against another footprint. -/
elab "win_foot " f:ident : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isForall && t.bindingBody!.isForall do throwError "win_foot: shape"
  let c ← realizeGlobalConstNoOverload f
  unless t.bindingBody!.bindingBody!.getAppFn.isConstOf c do throwError "win_foot: another footprint"

/-- Ownership of a static access, per footprint. -/
syntax "win_static_own" : tactic
macro_rules
  | `(tactic| win_static_own) =>
    `(tactic| (win_foot outS; first | exact outS_static (by decide) | exact outS_errno (by decide)))

elab "win_acc" : tactic => do winAcc (← `(tactic| win_static_own))

/-- Put the separation of the window `(T, n, m)` from each window of `others` in the context, in
the order that holds. -/
def winSeps (tag : String) (T n m : Term) (others : Array (Expr × Expr × Expr)) :
    TacticM Unit := do
  let mut i := 0
  for (b', n', m') in others do
    i := i + 1
    let hs := mkIdent (Name.mkSimple s!"hsep_{tag}_{i}")
    let b' ← withMainContext (Term.exprToSyntax b')
    let n' ← withMainContext (Term.exprToSyntax n')
    let m' ← withMainContext (Term.exprToSyntax m')
    evalTactic (← `(tactic| first
      | have $hs : $b' + $m' ≤ $T - $n := by omega
      | have $hs : $T + $m ≤ $b' - $n' := by omega
      | skip))

/-- The footprint of the `SWP` under the binders of the goal. -/
def goalFoot : TacticM Term := withMainContext do
  let Se ← forallTelescope (← instantiateMVars (← getMainTarget)) fun xs b => do
    let ty ← whnfR b
    unless ty.getAppFn.isConstOf ``SWP do throwError "nx_win: not an SWP goal"
    let S := ty.getAppArgs[3]!
    if xs.any fun x => S.containsFVar x.fvarId! then throwError "nx_win: the footprint is bound"
    pure S
  Term.exprToSyntax Se

/-- `nx_win sp n m`: put the window of the `n` bytes below and `m` bytes above `sp` in the
context as `hw_<sp>`, from the run's stack hypotheses (`omega`), with its separation from the
windows already there. The footprint is read off the goal. -/
elab "nx_win " sp:term:max n:term:max m:term:max : tactic => do
  let S ← goalFoot
  let tag := if sp.raw.isIdent then s!"{sp.raw.getId}" else "0"
  let others ← ctxWins
  let hw := mkIdent (Name.mkSimple s!"hw_{tag}")
  evalTactic (← `(tactic| have $hw : StackWin $S $sp $n $m := StackWin.of_outS (by omega)))
  winSeps tag (← `(($sp).toNat)) n m others

end Dispatch

/-- Step side goals (access permitted, access owned) by key. No arithmetic fallback. -/
macro "win_side" : tactic => `(tactic| first
  | win_acc
  | (simp only [BitVec.add_assoc, BitVec.reduceAdd] at ⊢; win_acc))

namespace Win

scoped macro_rules | `(tactic| nx_addr) => `(tactic| win_key)

scoped macro_rules | `(tactic| sx_addr) => `(tactic| win_key)

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

example (f : BitVec 64) (hf : StackWin (outS s 768) f 0 184) (hd : s.toNat + 0 ≤ f.toNat - 0) :
    (f + 24#64).toNat + 8 ≤ (s + 18446744073709551584#64).toNat ∨
      (s + 18446744073709551584#64).toNat + 8 ≤ (f + 24#64).toNat := by win_key
example (f : BitVec 64) (hf : StackWin (outS s 768) f 0 184) (hd : s.toNat + 0 ≤ f.toNat - 0) :
    (s + 18446744073709551584#64).toNat + 8 ≤ f.toNat ∨
      f.toNat + 8 ≤ (s + 18446744073709551584#64).toNat := by win_key

end Checks

end VsaIris.Sym
