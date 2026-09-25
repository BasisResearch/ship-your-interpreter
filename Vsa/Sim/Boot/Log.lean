import Vsa.Sim.WriteLogRead

/-!
# The boot write log and its final byte map

The emulator's store sequence from `_start` to `interp_run`'s entry is a
first-order write log (`List WEntry`, program order). A program's log has
1,300–16,400 stores, so a kernel check that folds it sequentially nests one
lazy accumulator per store. This module avoids the fold.

* `PackedLog`: the log as packed pages (64 entries of 128 bits per page:
  address 32 bits, width 4 bits, data 64 bits). `PackedLog.log` is the
  `List WEntry` in program order.
* `RunTree`: the final byte map, a search tree over runs of consecutive
  written addresses. Each cell holds the index of the address's last writer
  and the byte it wrote.
* `LogOk`: each store's bytes have a cell whose writer index is at least
  the store's own, and each cell's writer covers the address with the cell's
  byte (checked by `writeEntryByte`, the model's own byte semantics). Each
  store and each cell is checked independently.
* `logRead_of_check`: the check determines every byte of
  `writeLog m L.log`: the cell's byte where there is a cell, `m`'s byte
  elsewhere.
-/

namespace Vsa.Sim.Boot

/-! ## The packed log -/

/-- A packed entry: address in bits 0–31, width in bits 32–35, data from bit 36. -/
def unpackEntry (e : Nat) : WEntry :=
  (e % 2 ^ 32, (e >>> 32) % 16, BitVec.ofNat 64 (e >>> 36))

/-- A write log as pages of 64 packed 128-bit entries. -/
structure PackedLog where
  page : Nat → Nat
  len : Nat

/-- The `i`-th packed entry. -/
def PackedLog.raw (L : PackedLog) (i : Nat) : Nat :=
  (L.page (i / 64) >>> (128 * (i % 64))) % 2 ^ 128

def PackedLog.entry (L : PackedLog) (i : Nat) : WEntry := unpackEntry (L.raw i)

/-- The log in program order. -/
def PackedLog.log (L : PackedLog) : List WEntry := (List.range L.len).map L.entry

/-! ## The final byte map -/

/-- Consecutive final bytes from `base`: cell `j` is bits `32 j … 32 j + 31` of
`cells`, the last writer's index in its low 24 bits and the byte above them. -/
structure Run where
  base : Nat
  len : Nat
  cells : Nat

/-- The cell at address `x`: `(last writer, byte)`. -/
def Run.cell (r : Run) (x : Nat) : Option (Nat × Nat) :=
  if r.base ≤ x ∧ x < r.base + r.len then
    let c := (r.cells >>> (32 * (x - r.base))) % 2 ^ 32
    some (c % 2 ^ 24, c >>> 24)
  else none

/-- A search tree over runs: `node p l r` sends addresses below `p` left. -/
inductive RunTree where
  | leaf (r : Run)
  | node (pivot : Nat) (l r : RunTree)

def RunTree.find : RunTree → Nat → Run
  | .leaf r, _ => r
  | .node p l r, x => if x < p then l.find x else r.find x

def RunTree.runs : RunTree → List Run
  | .leaf r => [r]
  | .node _ l r => l.runs ++ r.runs

theorem RunTree.find_mem (t : RunTree) (x : Nat) : t.find x ∈ t.runs := by
  induction t with
  | leaf r => exact List.mem_singleton.mpr rfl
  | node p l r ihl ihr =>
    simp only [find, runs, List.mem_append]
    split
    · exact Or.inl ihl
    · exact Or.inr ihr

/-- The final cell at `x`, if any store wrote `x`. -/
def RunTree.fin (t : RunTree) (x : Nat) : Option (Nat × Nat) := (t.find x).cell x

/-! ## The check -/

/-- Every byte `a + j` (`j < n`) of store `i` has a cell whose writer is `i` or later. -/
def storeBytesOk (t : RunTree) (i a : Nat) : Nat → Bool
  | 0 => true
  | j + 1 =>
    (match t.fin (a + j) with
     | some (k, _) => decide (i ≤ k)
     | none => false) && storeBytesOk t i a j

/-- Store `i`'s bytes pass `storeBytesOk` (vacuous past the log's end, so the
last chunk may overshoot). -/
def storeOk (L : PackedLog) (t : RunTree) (i : Nat) : Bool :=
  decide (L.len ≤ i) || storeBytesOk t i (L.raw i % 2 ^ 32) ((L.raw i >>> 32) % 16)

/-- Stores `lo … lo + n - 1` pass `storeOk` (one kernel check per chunk). -/
def storesIn (L : PackedLog) (t : RunTree) (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => storeOk L t (lo + n) && storesIn L t lo n

/-- Cells `base … base + n - 1` of `r` name a store of the log that writes their byte. -/
def runOk (L : PackedLog) (r : Run) : Nat → Bool
  | 0 => true
  | j + 1 =>
    (match r.cell (r.base + j) with
     | some (k, b) =>
       decide (k < L.len) && writeEntryByte (L.entry k) (r.base + j) == some (BitVec.ofNat 8 b)
     | none => false) && runOk L r j

/-- The boot-log check: stores against cells, cells against stores. The
generated witnesses prove `stores` in chunks (`storesIn_spec`, `chunks_cover`). -/
structure LogOk (L : PackedLog) (t : RunTree) : Prop where
  stores : ∀ i, i < L.len → storeOk L t i = true
  runs : ∀ r ∈ t.runs, runOk L r r.len = true

/-! ## Soundness -/

/-- A store supplies bytes only inside `[base, base + width)`. -/
theorem writeEntryByte_range {e : WEntry} {x : Nat} {b : BitVec 8}
    (h : writeEntryByte e x = some b) : e.1 ≤ x ∧ x < e.1 + e.2.1 := by
  obtain ⟨a, w, d⟩ := e
  unfold writeEntryByte at h
  split at h <;> (repeat' split at h) <;> simp_all <;> omega

theorem storeBytesOk_spec {t : RunTree} {i a n : Nat} (h : storeBytesOk t i a n = true)
    {j : Nat} (hj : j < n) : ∃ k b, t.fin (a + j) = some (k, b) ∧ i ≤ k := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [storeBytesOk, Bool.and_eq_true] at h
    by_cases hjn : j = n
    · subst hjn
      have h1 := h.1
      split at h1
      · rename_i k b hf
        exact ⟨k, b, hf, of_decide_eq_true h1⟩
      · cases h1
    · exact ih h.2 (by omega)

theorem storeOk_spec {L : PackedLog} {t : RunTree} {i : Nat} (hi : i < L.len)
    (h : storeOk L t i = true)
    {x : Nat} {b : BitVec 8} (hx : writeEntryByte (L.entry i) x = some b) :
    ∃ k c, t.fin x = some (k, c) ∧ i ≤ k := by
  simp only [storeOk, Bool.or_eq_true, decide_eq_true_eq] at h
  replace h := h.resolve_left (by omega)
  have hr := writeEntryByte_range hx
  simp only [PackedLog.entry, unpackEntry] at hr
  have := storeBytesOk_spec h (j := x - L.raw i % 2 ^ 32) (by omega)
  rwa [show L.raw i % 2 ^ 32 + (x - L.raw i % 2 ^ 32) = x by omega] at this

theorem storesIn_spec {L : PackedLog} {t : RunTree} {lo n : Nat} (h : storesIn L t lo n = true)
    {i : Nat} (hlo : lo ≤ i) (hi : i < lo + n) : storeOk L t i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [storesIn, Bool.and_eq_true] at h
    by_cases hin : i = lo + n
    · subst hin; exact h.1
    · exact ih h.2 (by omega)

/-- `k` chunks of `size` stores from `lo`. -/
def chunks (lo size : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => (lo, size) :: chunks (lo + size) size k

/-- Chunks that each pass `storesIn` cover their whole range. -/
theorem chunks_cover {L : PackedLog} {t : RunTree} {lo size k : Nat}
    (h : ∀ c ∈ chunks lo size k, storesIn L t c.1 c.2 = true) {i : Nat}
    (hlo : lo ≤ i) (hi : i < lo + size * k) : storeOk L t i = true := by
  induction k generalizing lo with
  | zero => omega
  | succ k ih =>
    simp only [chunks, List.mem_cons, forall_eq_or_imp] at h
    by_cases hc : i < lo + size
    · exact storesIn_spec h.1 hlo hc
    · exact ih h.2 (by omega) (by rw [Nat.mul_succ] at hi; omega)

theorem runOk_spec {L : PackedLog} {r : Run} {n : Nat} (h : runOk L r n = true)
    {j : Nat} (hj : j < n) {k b : Nat} (hc : r.cell (r.base + j) = some (k, b)) :
    k < L.len ∧ writeEntryByte (L.entry k) (r.base + j) = some (BitVec.ofNat 8 b) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [runOk, Bool.and_eq_true] at h
    by_cases hjn : j = n
    · subst hjn
      have h1 := h.1
      rw [hc] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      exact h1
    · exact ih h.2 (by omega)

theorem Run.cell_range {r : Run} {x : Nat} {c : Nat × Nat} (h : r.cell x = some c) :
    r.base ≤ x ∧ x < r.base + r.len := by
  unfold Run.cell at h
  split at h
  · assumption
  · cases h

/-- A cell names a store of the log that writes the cell's byte. -/
theorem LogOk.cell {L : PackedLog} {t : RunTree} (h : LogOk L t) {x k b : Nat}
    (hf : t.fin x = some (k, b)) :
    k < L.len ∧ writeEntryByte (L.entry k) x = some (BitVec.ofNat 8 b) := by
  have hr := h.runs _ (t.find_mem x)
  have hrange := Run.cell_range hf
  have := runOk_spec hr (j := x - (t.find x).base) (by omega)
    (by rw [show (t.find x).base + (x - (t.find x).base) = x by omega]; exact hf)
  rwa [show (t.find x).base + (x - (t.find x).base) = x by omega] at this

/-- A store's byte has a cell whose writer is that store or a later one. -/
theorem LogOk.store {L : PackedLog} {t : RunTree} (h : LogOk L t) {i x : Nat}
    (hi : i < L.len) {b : BitVec 8} (hx : writeEntryByte (L.entry i) x = some b) :
    ∃ k c, t.fin x = some (k, c) ∧ i ≤ k :=
  storeOk_spec hi (h.stores i hi) hx

private theorem logReadNewest_foldr (init : Nat → Option (BitVec 8)) (r : List WEntry) (x : Nat) :
    logReadNewest init r x = r.foldr (fun e p => entryRead p e x) (init x) := by
  induction r with
  | nil => rfl
  | cons e rest ih =>
    simp only [logReadNewest, List.foldr_cons, entryRead, ih]

theorem logRead_foldl (init : Nat → Option (BitVec 8)) (l : List WEntry) (x : Nat) :
    logRead init l x = l.foldl (fun p e => entryRead p e x) (init x) := by
  rw [logRead, logReadNewest_foldr, List.foldr_reverse]

/-- The fold of the first `n` stores. -/
private theorem fold_range_succ (L : PackedLog) (x n : Nat) (z : Option (BitVec 8)) :
    ((List.range (n + 1)).map L.entry).foldl (fun p e => entryRead p e x) z =
      entryRead (((List.range n).map L.entry).foldl (fun p e => entryRead p e x) z)
        (L.entry n) x := by
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

private theorem entryRead_none {p : Option (BitVec 8)} {e : WEntry} {x : Nat}
    (h : writeEntryByte e x = none) : entryRead p e x = p := by
  simp [entryRead, h]

/-- **The boot log's bytes.** A passing check determines every byte of the log's
fold: the cell's byte where a store wrote, the initial byte elsewhere. -/
theorem logRead_of_check {L : PackedLog} {t : RunTree} (h : LogOk L t)
    (init : Nat → Option (BitVec 8)) (x : Nat) :
    logRead init L.log x =
      match t.fin x with
      | some (_, b) => some (BitVec.ofNat 8 b)
      | none => init x := by
  rw [logRead_foldl, PackedLog.log]
  -- no store past `n` covers `x` beyond its cell's writer
  have hstep : ∀ n, n < L.len → ∀ z,
      (∀ k c, t.fin x = some (k, c) → k < n) →
      entryRead z (L.entry n) x = z := by
    intro n hn z hk
    cases hw : writeEntryByte (L.entry n) x with
    | none => exact entryRead_none hw
    | some b =>
      obtain ⟨k, c, hf, hle⟩ := LogOk.store h hn hw
      exact absurd (hk k c hf) (by omega)
  cases hf : t.fin x with
  | none =>
    suffices ∀ n, n ≤ L.len →
        ((List.range n).map L.entry).foldl (fun p e => entryRead p e x) (init x) = init x from
      this L.len (Nat.le_refl _)
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [fold_range_succ, ih (by omega)]
      exact hstep n (by omega) _ (fun k c hc => by rw [hf] at hc; cases hc)
  | some kc =>
    obtain ⟨k, b⟩ := kc
    obtain ⟨hk, hw⟩ := LogOk.cell h hf
    suffices ∀ n, k < n → n ≤ L.len →
        ((List.range n).map L.entry).foldl (fun p e => entryRead p e x) (init x) =
          some (BitVec.ofNat 8 b) from this L.len hk (Nat.le_refl _)
    intro n hkn hn
    induction n with
    | zero => omega
    | succ n ih =>
      rw [fold_range_succ]
      by_cases hkn' : k = n
      · subst hkn'
        simp [entryRead, hw]
      · rw [ih (by omega) (by omega)]
        exact hstep n (by omega) _ (fun k' c' hc => by
          rw [hf] at hc
          cases hc
          omega)

/-- The byte view of `writeLog m L.log` under a passing check. -/
def logView (t : RunTree) (init : Nat → Option (BitVec 8)) (x : Nat) : Option (BitVec 8) :=
  match t.fin x with
  | some (_, b) => some (BitVec.ofNat 8 b)
  | none => init x

theorem writeLog_view {L : PackedLog} {t : RunTree} (h : LogOk L t)
    (m : Std.ExtHashMap Nat (BitVec 8)) (x : Nat) :
    (writeLog m L.log)[x]? = logView t (fun a => m[a]?) x := by
  rw [writeLog_getElem?_logRead, logRead_of_check h]
  rfl

end Vsa.Sim.Boot
