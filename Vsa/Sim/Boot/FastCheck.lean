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

theorem logOk_of_pages {L : PackedLog} {t : RunTree} {n lo hi : Nat} (hs : PagesUpTo L t n)
    (hwf : t.wfB lo hi = true) (hlen : L.len ≤ 1024 * n)
    (hr : ∀ r ∈ t.runs, runOk L r r.len = true) : LogOk L t :=
  ⟨fun i hi => hs.spec hwf i (by omega), hr⟩

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
