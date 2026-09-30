import Vsa.Sim.Boot.Store

/-!
# Kernel-cheap checks for boot witnesses

Bool-valued checks written for kernel evaluation (`Nat.blt`/`Nat.ble` and `cond` instead of
`Decidable` instances), each with a soundness lemma to the specification check it replaces.

- `pagesOk`: the log's stores, page by page. It consumes each packed page by shifting instead
  of indexing every entry, and looks up the run of an entry's first byte once for all its
  bytes. Sound for search trees whose runs respect their pivots (`RunTree.wfB`).
- `RangeTree.mem`: membership in a set of byte ranges by binary search.
-/

namespace Vsa.Sim.Boot

open Vsa.Sim

/-! ### Run trees -/

def RunTree.findB : RunTree → Nat → Run
  | .leaf r, _ => r
  | .node p l r, x => bif Nat.blt x p then l.findB x else r.findB x

theorem RunTree.findB_eq (t : RunTree) (x : Nat) : t.findB x = t.find x := by
  induction t with
  | leaf r => rfl
  | node p l r ihl ihr =>
    simp only [findB, find, ihl, ihr]
    by_cases h : x < p
    · simp [h, Nat.blt_eq]
    · simp [h, Nat.blt_eq]

/-- Every run lies within the bounds its pivots give it. -/
def RunTree.wfB : RunTree → Nat → Nat → Bool
  | .leaf r, lo, hi => Nat.ble lo r.base && Nat.ble (r.base + r.len) hi
  | .node p l r, lo, hi => l.wfB lo p && r.wfB p hi

theorem RunTree.wfB_le {t : RunTree} {lo hi : Nat} (h : t.wfB lo hi = true) : lo ≤ hi := by
  induction t generalizing lo hi with
  | leaf r => simp only [wfB, Bool.and_eq_true, Nat.ble_eq] at h; omega
  | node p l r ihl ihr =>
    simp only [wfB, Bool.and_eq_true] at h
    have := ihl h.1; have := ihr h.2; omega

theorem RunTree.wfB_runs {t : RunTree} {lo hi : Nat} (h : t.wfB lo hi = true) :
    ∀ r ∈ t.runs, lo ≤ r.base ∧ r.base + r.len ≤ hi := by
  induction t generalizing lo hi with
  | leaf r0 =>
    intro r hr
    simp only [runs, List.mem_singleton] at hr
    subst hr
    simp only [wfB, Bool.and_eq_true, Nat.ble_eq] at h
    exact h
  | node p l r ihl ihr =>
    intro r' hr
    simp only [wfB, Bool.and_eq_true] at h
    simp only [runs, List.mem_append] at hr
    have h1 := RunTree.wfB_le h.1
    have h2 := RunTree.wfB_le h.2
    rcases hr with hr | hr
    · have := ihl h.1 r' hr; omega
    · have := ihr h.2 r' hr; omega

theorem RunTree.fin_of_wf {t : RunTree} {lo hi : Nat} (h : t.wfB lo hi = true) {x : Nat}
    {r : Run} {c : Nat × Nat} (hr : r ∈ t.runs) (hc : r.cell x = some c) : t.fin x = some c := by
  induction t generalizing lo hi with
  | leaf r0 =>
    simp only [runs, List.mem_singleton] at hr
    subst hr
    exact hc
  | node p l r ihl ihr =>
    simp only [wfB, Bool.and_eq_true] at h
    have hx := Run.cell_range hc
    simp only [runs, List.mem_append] at hr
    unfold fin find
    by_cases hp : x < p
    · simp only [hp, ↓reduceIte]
      rcases hr with hr | hr
      · exact ihl h.1 hr
      · have := RunTree.wfB_runs h.2 _ hr; omega
    · simp only [hp, ↓reduceIte]
      rcases hr with hr | hr
      · have := RunTree.wfB_runs h.1 _ hr; omega
      · exact ihr h.2 hr

def Run.inB (r : Run) (x : Nat) : Bool := Nat.ble r.base x && Nat.blt x (r.base + r.len)

def Run.kOf (r : Run) (x : Nat) : Nat := (r.cells >>> (32 * (x - r.base))) % 2 ^ 32 % 2 ^ 24

theorem Run.cell_of_inB {r : Run} {x : Nat} (h : r.inB x = true) :
    ∃ b, r.cell x = some (r.kOf x, b) := by
  simp only [inB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  exact ⟨((r.cells >>> (32 * (x - r.base))) % 2 ^ 32) >>> 24, by
    unfold Run.cell Run.kOf; simp only [h, and_self, ↓reduceIte]⟩

def finOk (t : RunTree) (i x : Nat) : Bool :=
  match (t.findB x).cell x with
  | some (k, _) => Nat.ble i k
  | none => false

/-- The bytes `[a, a + n)` of store `i`, looked up in run `r` while they fall inside it. -/
def bytesOkR (t : RunTree) (r : Run) (i a : Nat) : Nat → Bool
  | 0 => true
  | j + 1 => (bif r.inB (a + j) then Nat.ble i (r.kOf (a + j)) else finOk t i (a + j)) &&
      bytesOkR t r i a j

theorem storeBytesOk_of_bytesOkR {t : RunTree} {lo hi : Nat} (hwf : t.wfB lo hi = true)
    {r : Run} (hr : r ∈ t.runs) {i a : Nat} :
    ∀ {n}, bytesOkR t r i a n = true → storeBytesOk t i a n = true := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [bytesOkR, Bool.and_eq_true] at h
    simp only [storeBytesOk, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    have h1 := h.1
    cases hin : r.inB (a + n) with
    | true =>
      rw [hin, Bool.cond_true, Nat.ble_eq] at h1
      obtain ⟨b, hc⟩ := Run.cell_of_inB hin
      rw [RunTree.fin_of_wf hwf hr hc]
      exact decide_eq_true h1
    | false =>
      rw [hin, Bool.cond_false] at h1
      unfold finOk at h1
      rw [RunTree.findB_eq] at h1
      unfold RunTree.fin
      split at h1
      · rename_i k b hc
        rw [hc]
        exact decide_eq_true (Nat.ble_eq.mp h1)
      · cases h1

/-- The stores of one packed page, consumed by shifting: `p` is the page shifted past the
entries already checked and `i` the next entry's index. -/
def pageOk (t : RunTree) (len : Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | p, i, n + 1 =>
    (Nat.ble len i ||
      (let e := p % 2 ^ 128
       let a := e % 2 ^ 32
       bytesOkR t (t.findB a) i a ((e >>> 32) % 16))) &&
    pageOk t len (p >>> 128) (i + 1) n

def pagesOk (L : PackedLog) (t : RunTree) (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => pageOk t L.len (L.page (lo + n)) (64 * (lo + n)) 64 && pagesOk L t lo n

theorem pageOk_spec {L : PackedLog} {t : RunTree} {lo hi : Nat} (hwf : t.wfB lo hi = true)
    (pg : Nat) : ∀ n j, j + n ≤ 64 →
      pageOk t L.len (L.page pg >>> (128 * j)) (64 * pg + j) n = true →
      ∀ j', j ≤ j' → j' < j + n → storeOk L t (64 * pg + j') = true := by
  intro n
  induction n with
  | zero => intro j _ _ j' h1 h2; omega
  | succ n ih =>
    intro j hj h j' h1 h2
    simp only [pageOk, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
    by_cases hjj : j' = j
    · subst hjj
      have hraw : L.raw (64 * pg + j') = L.page pg >>> (128 * j') % 2 ^ 128 := by
        unfold PackedLog.raw
        congr 3 <;> omega
      unfold storeOk
      rcases h.1 with hl | hb
      · simp [hl]
      · rw [hraw]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        right
        exact storeBytesOk_of_bytesOkR hwf (by rw [RunTree.findB_eq]; exact t.find_mem _) hb
    · have h2' := h.2
      rw [← Nat.shiftRight_add, show 128 * j + 128 = 128 * (j + 1) by omega,
        show 64 * pg + j + 1 = 64 * pg + (j + 1) by omega] at h2'
      exact ih (j + 1) (by omega) h2' j' (by omega) (by omega)

theorem pagesOk_spec {L : PackedLog} {t : RunTree} {lo hi : Nat} (hwf : t.wfB lo hi = true)
    {p0 : Nat} : ∀ {n}, pagesOk L t p0 n = true →
      ∀ i, 64 * p0 ≤ i → i < 64 * (p0 + n) → storeOk L t i = true := by
  intro n
  induction n with
  | zero => intro _ i h1 h2; omega
  | succ n ih =>
    intro h i h1 h2
    simp only [pagesOk, Bool.and_eq_true] at h
    by_cases hi : i < 64 * (p0 + n)
    · exact ih h.2 i h1 hi
    · have hp := pageOk_spec hwf (L := L) (p0 + n) 64 0 (by omega)
        (by simpa using h.1) (i - 64 * (p0 + n)) (by omega) (by omega)
      rwa [show 64 * (p0 + n) + (i - 64 * (p0 + n)) = i by omega] at hp

/-- Pages `[0, 16 n)` of the log, checked in blocks of 16 pages (one theorem per block). -/
def PagesUpTo (L : PackedLog) (t : RunTree) : Nat → Prop
  | 0 => True
  | n + 1 => PagesUpTo L t n ∧ pagesOk L t (16 * n) 16 = true

theorem PagesUpTo.spec {L : PackedLog} {t : RunTree} {lo hi : Nat} (hwf : t.wfB lo hi = true) :
    ∀ {n}, PagesUpTo L t n → ∀ i, i < 1024 * n → storeOk L t i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    by_cases hn : i < 1024 * n
    · exact ih h.1 i hn
    · exact pagesOk_spec hwf h.2 i (by omega) (by rw [Nat.mul_succ] at hi; omega)


/-! ### Run cells against their writers -/

/-- The byte a packed store writes at `x`, in `Nat` arithmetic. -/
def entryByteN (e x : Nat) : Option Nat :=
  let a := e % 2 ^ 32
  let w := (e >>> 32) % 16
  bif (Nat.beq w 1 || Nat.beq w 2 || Nat.beq w 4 || Nat.beq w 8) && Nat.ble a x &&
    Nat.blt x (a + w)
  then some ((e >>> 36 >>> (8 * (x - a))) % 256) else none

theorem shr_mod_byte (x n s : Nat) (h : s + 8 ≤ n) : (x % 2 ^ n) >>> s % 256 = x >>> s % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show (256:Nat) = 2^8 from rfl]
  by_cases hi : i < 8
  · have : s + i < n := by omega
    simp [hi, this]
  · simp [hi]

private theorem ex8 (d : BitVec 64) (s : Nat) :
    (sdData_val d).extractLsb' s 8 = BitVec.ofNat 8 ((d.toNat >>> s) % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.mod_eq_of_lt d.isLt]

private theorem ex4 (d : BitVec 64) (s : Nat) (hs : s + 8 ≤ 32) :
    (swData d).extractLsb' s 8 = BitVec.ofNat 8 ((d.toNat >>> s) % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp [swData, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
  exact shr_mod_byte _ 32 _ hs

private theorem ex2 (d : BitVec 64) (s : Nat) (hs : s + 8 ≤ 16) :
    (shData d).extractLsb' s 8 = BitVec.ofNat 8 ((d.toNat >>> s) % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp [shData, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
  exact shr_mod_byte _ 16 _ hs

private theorem ex1 (d : BitVec 64) : sbData d = BitVec.ofNat 8 ((d.toNat >>> 0) % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]

private theorem mod64 (x s : Nat) (h : s + 8 ≤ 64) :
    (x % 18446744073709551616) >>> s % 256 = x >>> s % 256 := shr_mod_byte x 64 s h

set_option linter.unusedSimpArgs false in
theorem writeEntryByte_unpack (e x : Nat) :
    writeEntryByte (unpackEntry e) x = (entryByteN e x).map (BitVec.ofNat 8) := by
  unfold unpackEntry entryByteN
  generalize ha : e % 2 ^ 32 = a
  generalize hw : (e >>> 32) % 16 = w
  unfold writeEntryByte
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    by_cases h : x = a
    · subst h; simp [ex1, mod64]
    · simp [h, Ne.symm h]; omega
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rcases (show x = a ∨ x = a + 1 ∨ (x ≠ a ∧ x ≠ a + 1) by omega) with rfl | rfl | ⟨h0, h1⟩
    · simp [ex2, mod64]
    · simp [ex2, mod64]
    · simp [Ne.symm h0, Ne.symm h1]; omega
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rcases (show x = a ∨ x = a + 1 ∨ x = a + 2 ∨ x = a + 3 ∨
      (x ≠ a ∧ x ≠ a + 1 ∧ x ≠ a + 2 ∧ x ≠ a + 3) by omega) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h2, h3⟩
    · simp [ex4, mod64]
    · simp [ex4, mod64]
    · simp [ex4, mod64]
    · simp [ex4, mod64]
    · simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]; omega
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rcases (show x = a ∨ x = a + 1 ∨ x = a + 2 ∨ x = a + 3 ∨ x = a + 4 ∨ x = a + 5 ∨
      x = a + 6 ∨ x = a + 7 ∨ (x ≠ a ∧ x ≠ a + 1 ∧ x ≠ a + 2 ∧ x ≠ a + 3 ∧ x ≠ a + 4 ∧
      x ≠ a + 5 ∧ x ≠ a + 6 ∧ x ≠ a + 7) by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    all_goals first
      | simp [ex8, mod64]; done
      | simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
          Ne.symm h6, Ne.symm h7]; omega
  · rename_i h1 h2 h4 h8
    have n1 : w ≠ 1 := fun h => h1 _ _ (by rw [h])
    have n2 : w ≠ 2 := fun h => h2 _ _ (by rw [h])
    have n4 : w ≠ 4 := fun h => h4 _ _ (by rw [h])
    have n8 : w ≠ 8 := fun h => h8 _ _ (by rw [h])
    simp [n1, n2, n4, n8]


/-- The cells `j, j + 1, …` of a run at `base` (`p` = the cells shifted past `j`), each checked
against the store it names; `pr` caches the packed store `pk` of the previous cell. -/
def cellsOk (L : PackedLog) (base : Nat) : Nat → Nat → Nat → Nat → Nat → Bool
  | _, _, 0, _, _ => true
  | p, j, n + 1, pk, pr =>
    let c := p % 2 ^ 32
    let k := c % 2 ^ 24
    let raw := bif Nat.beq k pk then pr else L.raw k
    (Nat.blt k L.len &&
      (match entryByteN raw (base + j) with
       | some v => Nat.beq v (c >>> 24)
       | none => false)) &&
    cellsOk L base (p >>> 32) (j + 1) n k raw

def runOkF (L : PackedLog) (r : Run) : Bool := cellsOk L r.base r.cells 0 r.len (2 ^ 24) 0

theorem cellsOk_spec {L : PackedLog} {base cells : Nat} : ∀ n j pk pr,
    (pk = 2 ^ 24 ∨ pr = L.raw pk) →
    cellsOk L base (cells >>> (32 * j)) j n pk pr = true →
    ∀ j', j ≤ j' → j' < j + n →
      (cells >>> (32 * j')) % 2 ^ 32 % 2 ^ 24 < L.len ∧
      writeEntryByte (L.entry ((cells >>> (32 * j')) % 2 ^ 32 % 2 ^ 24)) (base + j') =
        some (BitVec.ofNat 8 (((cells >>> (32 * j')) % 2 ^ 32) >>> 24)) := by
  intro n
  induction n with
  | zero => intro j _ _ _ _ j' h1 h2; omega
  | succ n ih =>
    intro j pk pr hinv h j' h1 h2
    simp only [cellsOk, Bool.and_eq_true, Nat.blt_eq] at h
    have hraw : (bif Nat.beq ((cells >>> (32 * j)) % 2 ^ 32 % 2 ^ 24) pk then pr
        else L.raw ((cells >>> (32 * j)) % 2 ^ 32 % 2 ^ 24)) =
        L.raw ((cells >>> (32 * j)) % 2 ^ 32 % 2 ^ 24) := by
      cases hb : Nat.beq ((cells >>> (32 * j)) % 2 ^ 32 % 2 ^ 24) pk with
      | false => rfl
      | true =>
        have hk := Nat.eq_of_beq_eq_true hb
        rcases hinv with hp | hp
        · have : (cells >>> (32 * j)) % 2 ^ 32 % 2 ^ 24 < 2 ^ 24 := Nat.mod_lt _ (by decide)
          omega
        · rw [Bool.cond_true, hp, hk]
    by_cases hjj : j' = j
    · subst hjj
      rw [hraw] at h
      refine ⟨h.1.1, ?_⟩
      have h12 := h.1.2
      unfold PackedLog.entry
      rw [writeEntryByte_unpack]
      split at h12
      · rename_i v hv
        rw [hv, Nat.eq_of_beq_eq_true h12]
        rfl
      · cases h12
    · have h2' := h.2
      rw [← Nat.shiftRight_add, show 32 * j + 32 = 32 * (j + 1) by omega] at h2'
      exact ih (j + 1) _ _ (Or.inr hraw) h2' j' (by omega) (by omega)

theorem runOk_of_runOkF {L : PackedLog} {r : Run} (h : runOkF L r = true) :
    runOk L r r.len = true := by
  have hs := cellsOk_spec (L := L) (base := r.base) (cells := r.cells) r.len 0 (2 ^ 24) 0
    (Or.inl rfl) (by simpa [runOkF] using h)
  suffices ∀ n, n ≤ r.len → runOk L r n = true from this r.len (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runOk, Bool.and_eq_true]
    refine ⟨?_, ih (by omega)⟩
    have hc : r.cell (r.base + n) = some ((r.cells >>> (32 * n)) % 2 ^ 32 % 2 ^ 24,
        ((r.cells >>> (32 * n)) % 2 ^ 32) >>> 24) := by
      unfold Run.cell
      have hin : r.base ≤ r.base + n ∧ r.base + n < r.base + r.len := ⟨by omega, by omega⟩
      simp only [hin, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [hc]
    obtain ⟨h1, h2⟩ := hs n (by omega) (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨h1, h2⟩

theorem logOk_of_pages {L : PackedLog} {t : RunTree} {n lo hi : Nat} (hs : PagesUpTo L t n)
    (hwf : t.wfB lo hi = true) (hlen : L.len ≤ 1024 * n)
    (hr : t.runs.all (runOkF L) = true) : LogOk L t :=
  ⟨fun i hi => hs.spec hwf i (by omega),
    fun r hr' => runOk_of_runOkF (List.all_eq_true.mp hr r hr')⟩

/-! ### Range trees -/

inductive RangeTree where
  | leaf (lo len : Nat)
  | node (pivot : Nat) (l r : RangeTree)

def RangeTree.mem : RangeTree → Nat → Bool
  | .leaf lo n, k => Nat.ble lo k && Nat.blt k (lo + n)
  | .node p l r, k => bif Nat.blt k p then l.mem k else r.mem k

def RangeTree.ranges : RangeTree → List (Nat × Nat)
  | .leaf lo n => [(lo, n)]
  | .node _ l r => l.ranges ++ r.ranges

theorem RangeTree.mem_sound {t : RangeTree} {k : Nat} (h : t.mem k = true) :
    ∃ r ∈ t.ranges, r.1 ≤ k ∧ k < r.1 + r.2 := by
  induction t with
  | leaf lo n =>
    simp only [mem, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    exact ⟨(lo, n), by simp [ranges], h⟩
  | node p l r ihl ihr =>
    simp only [mem] at h
    cases hb : Nat.blt k p with
    | true =>
      rw [hb, Bool.cond_true] at h
      obtain ⟨x, hx, hk⟩ := ihl h
      exact ⟨x, by simp [ranges, hx], hk⟩
    | false =>
      rw [hb, Bool.cond_false] at h
      obtain ⟨x, hx, hk⟩ := ihr h
      exact ⟨x, by simp [ranges, hx], hk⟩

end Vsa.Sim.Boot
