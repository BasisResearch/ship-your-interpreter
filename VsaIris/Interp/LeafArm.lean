import VsaIris.Interp.Arm

/-!
# The node facts of `eval_expr`'s leaf, `var`, `assign` and `fn` arms (lane E1)

INTERP_DESIGN.md §6, §9 E1. The generated cases of family `leaf`
(`scripts/iris_arms/templates/leaf_*.lean`) read a node's kind tag and at most
two fields after it (`+8`, `+16`), never the line field at `+4`. `LeafNode`
is what those runs need, the leaf analogue of lane G's `BinNode`: the tag's
loads, the node's placement, and the view `leafView` (tag word, then `w`
field bytes from `+8`). The per-constructor facts (`int`'s value word, a
string field's pointer and `strAt`, `assign`'s child) come from
`ExprReprWithin` by one lemma each.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.While Vsa.Sim

/-- Every byte of a geometric view has the string routines' window
(`SharedWin`), which `ReadOK.win` records. -/
theorem sharedWin_of_readOK {P : Nat → Prop} (hg : ∀ k, P k → ReadOK k) : SharedWin P :=
  fun k hk => by
    have h := hg k hk
    exact ⟨h.lo, h.win.1, h.win.2⟩

/-- The bytes a leaf run reads: the tag word and `w` field bytes from `+8`. -/
abbrev leafView (a w : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) w

/-- What a leaf node gives its runs: the tag's loads, the placement, the view. -/
structure LeafNode (m : Mem) (P : Nat → Prop) (aX : BitVec 64) (tag w : Nat) : Prop where
  kind : ldv .lw m aX.toNat = BitVec.ofNat 64 tag
  kindu : ldv .lwu m aX.toNat = BitVec.ofNat 64 tag
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 8 + w ≤ 0x100000000
  off : aX.toNat + 8 + w ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aX.toNat
  view : ∀ a ∈ leafView aX.toNat w, P a ∧ (m[a]?).isSome

/-- A leaf node from its tag and its field bytes (at most two words). -/
theorem leafNode_mk {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {tag w : Nat}
    (hg : ∀ k, P k → ReadOK k) (htag : tag < 2 ^ 31) (hw : w = 0 ∨ w = 4 ∨ w = 8 ∨ w = 16)
    (h6 : read32 m aX.toNat = some tag) (c6 : Covers P aX.toNat 4)
    (cf : Covers P (aX.toNat + 8) w) (sf : ∀ i, i < w → (m[aX.toNat + 8 + i]?).isSome) :
    LeafNode m P aX tag w := by
  have g0 := hg _ (by simpa using c6 0 (by omega))
  have w0 := g0.win
  refine ⟨ldv_lw_read32 h6 htag, ldv_lwu_read32 h6, g0.lo, ?_, ?_, ?_⟩
  · rcases hw with rfl | rfl | rfl | rfl
    · omega
    · have := (hg _ (cf 0 (by omega))).win; omega
    · have := (hg _ (cf 0 (by omega))).win; omega
    · have := (hg _ (cf 8 (by omega))).win; simp only [Nat.add_assoc] at this ⊢; omega
  · rcases hw with rfl | rfl | rfl | rfl
    · omega
    · have := (hg _ (cf 0 (by omega))).win; omega
    · have := (hg _ (cf 0 (by omega))).win; omega
    · have h8 := (hg _ (cf 0 (by omega))).win; have h16 := (hg _ (cf 8 (by omega))).win
      simp only [Nat.add_assoc] at h8 h16 ⊢; omega
  · intro a ha
    simp only [List.mem_append, mem_accAddrs_iff] at ha
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + j := ⟨a - aX.toNat, by omega⟩
      exact ⟨c6 j (by omega), isSome_of_readLE h6 (by omega)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 8 + j := ⟨a - (aX.toNat + 8), by omega⟩
      exact ⟨cf j (by omega), sf j (by omega)⟩

/-- The field bytes of a doubleword read are present. -/
theorem some_of_read64 {m : Mem} {a v : Nat} (h : read64 m a = some v) :
    ∀ i, i < 8 → (m[a + i]?).isSome := fun _ hi => isSome_of_readLE h hi

theorem some_of_read32 {m : Mem} {a v : Nat} (h : read32 m a = some v) :
    ∀ i, i < 4 → (m[a + i]?).isSome := fun _ hi => isSome_of_readLE h hi

/-- A node field address without wrap-around. -/
theorem toNat_add_field {aX : BitVec 64} {c : Nat} (h : aX.toNat + c < 2 ^ 64) (hc : c < 2 ^ 64) :
    (aX + BitVec.ofNat 64 c).toNat = aX.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt h]

theorem signExtend64_zero_iff (x : BitVec 32) : x.signExtend 64 = 0#64 ↔ x.toNat = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_signExtend] at this
    simp at this
    omega
  · intro h
    have : x = 0#32 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; decide

/-- A signed word load is zero exactly when its word is. -/
theorem ldv_lw_zero_iff {m : Mem} {a k : Nat} (h : read32 m a = some k) :
    ldv .lw m a = 0#64 ↔ k = 0 := by
  have hw := toNat_append4 (memImg m) a
  rw [readLE_memImg h] at hw
  show ldvf .lw (memImg m) a = 0#64 ↔ k = 0
  simp only [ldvf, bytesAt4, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  rw [signExtend64_zero_iff, hw]

/-! ## Per-constructor facts -/

/-- `null`: the tag only. -/
theorem leafNode_null {m : Mem} {P : Nat → Prop} {aX : BitVec 64}
    (h : ExprReprWithin m P aX.toNat .null) (hg : ∀ k, P k → ReadOK k) :
    LeafNode m P aX 3 0 := by
  cases h with
  | null h6 c6 =>
    exact leafNode_mk hg (by decide) (by omega) h6 c6 (fun _ h => by omega) (fun _ h => by omega)

/-- `int n`: the value word. -/
theorem leafNode_int {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {n : Int}
    (h : ExprReprWithin m P aX.toNat (.int n)) (hg : ∀ k, P k → ReadOK k) :
    LeafNode m P aX 0 8 ∧ (ldv .ld m (aX + 8#64).toNat).toInt = n := by
  cases h with
  | int h6 c6 hv cv =>
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hv
    have hn := leafNode_mk (w := 8) hg (by decide) (by omega) h6 c6 cv (some_of_read64 hk)
    refine ⟨hn, ?_⟩
    rw [toNat_add_field (by have := hn.hi; omega) (by decide), ldv_ld_read64 hk]

/-- `bool b`: the word's truth. -/
theorem leafNode_bool {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {b : Bool}
    (h : ExprReprWithin m P aX.toNat (.bool b)) (hg : ∀ k, P k → ReadOK k) :
    LeafNode m P aX 2 4 ∧ (ldv .lw m (aX + 8#64).toNat != 0#64) = b := by
  cases h with
  | boolTrue h6 c6 hv cv hb =>
    have hn := leafNode_mk (w := 4) hg (by decide) (by omega) h6 c6 cv (some_of_read32 hv)
    refine ⟨hn, ?_⟩
    rw [toNat_add_field (by have := hn.hi; omega) (by decide)]
    have := (not_congr (ldv_lw_zero_iff hv)).2 hb
    simpa using this
  | boolFalse h6 c6 hv cv =>
    have hn := leafNode_mk (w := 4) hg (by decide) (by omega) h6 c6 cv (some_of_read32 hv)
    refine ⟨hn, ?_⟩
    rw [toNat_add_field (by have := hn.hi; omega) (by decide)]
    have := (ldv_lw_zero_iff hv).2 rfl
    simp [this]

/-- A string field (`str`, `var`): its pointer and its string. -/
structure StrField (m : Mem) (P : Nat → Prop) (aX : BitVec 64) (s : String) (p : Nat) : Prop where
  ptr : ldv .ld m (aX + 8#64).toNat = BitVec.ofNat 64 p
  lt : p < 2 ^ 64
  ne : p ≠ 0
  str : CStringWithin m P p s

/-- `str s`: the string pointer. -/
theorem leafNode_str {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {s : String}
    (h : ExprReprWithin m P aX.toNat (.str s)) (hg : ∀ k, P k → ReadOK k) :
    ∃ p, LeafNode m P aX 1 8 ∧ StrField m P aX s p := by
  cases h with
  | str h6 c6 hv cv hs =>
    rename_i p
    have hn := leafNode_mk (w := 8) hg (by decide) (by omega) h6 c6 cv (some_of_read64 hv)
    refine ⟨p, hn, ?_, readLE_lt hv, ?_, hs⟩
    · rw [toNat_add_field (by have := hn.hi; omega) (by decide), ldv_ld_read64 hv]
    · have := (hg _ (hs.2 0 (by omega))).lo; omega

/-- `var x`: the name pointer. -/
theorem leafNode_var {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {x : String}
    (h : ExprReprWithin m P aX.toNat (.var x)) (hg : ∀ k, P k → ReadOK k) :
    ∃ p, LeafNode m P aX 4 8 ∧ StrField m P aX x p := by
  cases h with
  | var h6 c6 hv cv hs =>
    rename_i p
    have hn := leafNode_mk (w := 8) hg (by decide) (by omega) h6 c6 cv (some_of_read64 hv)
    refine ⟨p, hn, ?_, readLE_lt hv, ?_, hs⟩
    · rw [toNat_add_field (by have := hn.hi; omega) (by decide), ldv_ld_read64 hv]
    · have := (hg _ (hs.2 0 (by omega))).lo; omega

/-- `assign x e`: the name pointer and the child. -/
theorem leafNode_assign {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {x : String} {e : Expr}
    (h : ExprReprWithin m P aX.toNat (.assign x e)) (hg : ∀ k, P k → ReadOK k) :
    ∃ p q, LeafNode m P aX 5 16 ∧ StrField m P aX x p ∧
      ldv .ld m (aX + 16#64).toNat = BitVec.ofNat 64 q ∧ q < 2 ^ 64 ∧ ExprReprWithin m P q e := by
  cases h with
  | assign h6 c6 hv cv hs hq cq he =>
    rename_i p q
    have hn := leafNode_mk (w := 16) hg (by decide) (by omega) h6 c6
      (fun i hi => if h8 : i < 8 then cv i h8 else by
        have := cq (i - 8) (by omega); rwa [show aX.toNat + 16 + (i - 8) = aX.toNat + 8 + i by omega]
          at this)
      (fun i hi => if h8 : i < 8 then some_of_read64 hv i h8 else by
        have := some_of_read64 hq (i - 8) (by omega)
        rwa [show aX.toNat + 16 + (i - 8) = aX.toNat + 8 + i by omega] at this)
    refine ⟨p, q, hn, ⟨?_, readLE_lt hv, ?_, hs⟩, ?_, readLE_lt hq, he⟩
    · rw [toNat_add_field (by have := hn.hi; omega) (by decide), ldv_ld_read64 hv]
    · have := (hg _ (hs.2 0 (by omega))).lo; omega
    · rw [toNat_add_field (by have := hn.hi; omega) (by decide), ldv_ld_read64 hq]

/-- `fn`: the tag only (the node pointer itself is stored into the closure). -/
theorem leafNode_fn {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {nm : Option String}
    {ps : List String} {ss : List Stmt}
    (h : ExprReprWithin m P aX.toNat (.fn nm ps ss)) (hg : ∀ k, P k → ReadOK k) :
    LeafNode m P aX 10 0 := by
  cases h with
  | fnNamed h6 c6 =>
    exact leafNode_mk hg (by decide) (by omega) h6 c6 (fun _ h => by omega) (fun _ h => by omega)
  | fnAnon h6 c6 =>
    exact leafNode_mk hg (by decide) (by omega) h6 c6 (fun _ h => by omega) (fun _ h => by omega)

end VsaIris.Interp
