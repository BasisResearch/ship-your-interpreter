import VsaIris.Vsa.HeapRoom
import VsaIris.Vsa.SymRun

/-!
# The heap algebra: bin lists as rings of links

dlmalloc's bins are circular doubly-linked lists threaded through each
node's `fd` (`+16`) and `bk` (`+24`) words, the bin header included.
`DlHeap.BinList` states one bin inductively from its first node. The
allocator changes bins by unlinking a node and by linking one in (at the
head, or before a larger node in a sorted large bin). Those edits are local
in a different view:

* `Links m l`: consecutive nodes of `l` are linked both ways
  (`fd x = y`, `bk y = x`);
* `Ring m b qs := Links m (b :: qs ++ [b])`: the bin `b` with members `qs`.

`binList_iff_ring` identifies the two views. `Links.transport` moves a ring
to a memory that agrees on its link words. `ring_unlink` and `ring_link` are
the two edits. The link words of distinct 16-aligned nodes never overlap
(`linkWords_disjoint`), so an edit leaves every other link alone.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- The forward link of a node. -/
abbrev fdOf (m : Mem) (x : Nat) : Option Nat := read64 m (x + 16)

/-- The backward link of a node. -/
abbrev bkOf (m : Mem) (x : Nat) : Option Nat := read64 m (x + 24)

/-- Consecutive nodes are linked both ways. -/
def Links (m : Mem) : List Nat → Prop
  | x :: y :: rest => fdOf m x = some y ∧ bkOf m y = some x ∧ Links m (y :: rest)
  | _ => True

/-- The circular list of bin `b` with members `qs`, in `fd` order. -/
def Ring (m : Mem) (b : Nat) (qs : List Nat) : Prop := Links m (b :: qs ++ [b])

@[simp] theorem links_nil (m : Mem) : Links m [] := trivial
@[simp] theorem links_single (m : Mem) (x : Nat) : Links m [x] := trivial

theorem links_cons_cons {m : Mem} {x y : Nat} {rest : List Nat} :
    Links m (x :: y :: rest) ↔ fdOf m x = some y ∧ bkOf m y = some x ∧ Links m (y :: rest) :=
  Iff.rfl

/-- Links of a concatenation: both halves and the seam. -/
theorem links_append {m : Mem} :
    ∀ (l₁ : List Nat) (x : Nat) (l₂ : List Nat),
      Links m (l₁ ++ x :: l₂) ↔ Links m (l₁ ++ [x]) ∧ Links m (x :: l₂)
  | [], x, l₂ => by simp
  | [a], x, l₂ => by
    show (fdOf m a = some x ∧ bkOf m x = some a ∧ Links m (x :: l₂)) ↔
      (fdOf m a = some x ∧ bkOf m x = some a ∧ True) ∧ Links m (x :: l₂)
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, trivial⟩, h3⟩
    · rintro ⟨⟨h1, h2, _⟩, h3⟩; exact ⟨h1, h2, h3⟩
  | a :: b :: l₁, x, l₂ => by
    have ih := links_append (m := m) (b :: l₁) x l₂
    show (fdOf m a = some b ∧ bkOf m b = some a ∧ Links m (b :: l₁ ++ x :: l₂)) ↔
      (fdOf m a = some b ∧ bkOf m b = some a ∧ Links m (b :: l₁ ++ [x])) ∧ Links m (x :: l₂)
    rw [ih]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- Links read only the link words of their nodes: `fd` of every node but the
last, `bk` of every node but the first. -/
theorem Links.transport {m m' : Mem} :
    ∀ {l : List Nat}, Links m l →
      (∀ x y, [x, y] <:+: l → fdOf m' x = fdOf m x ∧ bkOf m' y = bkOf m y) → Links m' l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | x :: y :: rest, ⟨h1, h2, h3⟩, hag => by
    have hxy := hag x y ⟨[], rest, rfl⟩
    refine ⟨hxy.1.trans h1, hxy.2.trans h2, Links.transport h3 fun a b hab => hag a b ?_⟩
    obtain ⟨s, t, e⟩ := hab
    exact ⟨x :: s, t, by rw [← e]; rfl⟩

/-- The empty bin: its header points at itself both ways. -/
theorem ring_nil_iff {m : Mem} {b : Nat} : Ring m b [] ↔ fdOf m b = some b ∧ bkOf m b = some b := by
  show (fdOf m b = some b ∧ bkOf m b = some b ∧ True) ↔ _
  simp

/-! ## `BinList` is a ring -/

theorem binChain_links {m : Mem} {b : Nat} :
    ∀ {q prev : Nat} {qs : List Nat}, BinChain m b q prev qs →
      (∀ x ∈ qs, x ≠ b) ∧ Links m (qs ++ [b]) ∧ q = (qs ++ [b]).headD b ∧ bkOf m q = some prev
  | _, _, [], BinChain.close hc => by
    exact ⟨(fun _ h => nomatch h), trivial, rfl, hc⟩
  | _, _, q :: qs, BinChain.link hne hp hn rest => by
    obtain ⟨hne', hl, hq, hbk⟩ := binChain_links rest
    refine ⟨fun x hx => ?_, ?_, rfl, hp⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hne
      · exact hne' x hx
    · rcases qs with _ | ⟨q', qs⟩
      · simp only [List.nil_append, List.headD_cons] at hq
        subst hq
        exact ⟨hn, hbk, trivial⟩
      · simp only [List.cons_append, List.headD_cons] at hq hl
        subst hq
        exact ⟨hn, hbk, hl⟩

theorem links_binChain {m : Mem} {b : Nat} :
    ∀ {prev : Nat} {qs : List Nat}, (∀ x ∈ qs, x ≠ b) → Links m (qs ++ [b]) →
      bkOf m ((qs ++ [b]).headD b) = some prev →
      BinChain m b ((qs ++ [b]).headD b) prev qs
  | _, [], _, _, hbk => BinChain.close hbk
  | _, q :: qs, hne, hl, hbk => by
    simp only [List.cons_append, List.headD_cons] at hbk ⊢
    have hq := hne q List.mem_cons_self
    rcases qs with _ | ⟨q', qs⟩
    · exact BinChain.link hq hbk hl.1 (BinChain.close hl.2.1)
    · have := links_binChain (prev := q) (qs := q' :: qs)
        (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hl.2.2
        (by simp only [List.cons_append, List.headD_cons]; exact hl.2.1)
      simp only [List.cons_append, List.headD_cons] at this
      exact BinChain.link hq hbk hl.1 this

/-- **A bin list is a ring.** -/
theorem binList_iff_ring {m : Mem} {i : Nat} {qs : List Nat} :
    BinList m i qs ↔ Ring m (binAt i) qs ∧ ∀ x ∈ qs, x ≠ binAt i := by
  constructor
  · rintro ⟨first, hf, hc⟩
    obtain ⟨hne, hl, hq, hbk⟩ := binChain_links hc
    refine ⟨?_, hne⟩
    show Links m (binAt i :: (qs ++ [binAt i]))
    rcases h : qs ++ [binAt i] with _ | ⟨y, rest⟩
    · simp at h
    · rw [h] at hl hq
      simp only [List.headD_cons] at hq
      subst hq
      exact ⟨hf, hbk, hl⟩
  · rintro ⟨hr, hne⟩
    change Links m (binAt i :: (qs ++ [binAt i])) at hr
    rcases h : qs ++ [binAt i] with _ | ⟨y, rest⟩
    · simp at h
    · rw [h] at hr
      obtain ⟨hf, hbk, hl⟩ := hr
      refine ⟨y, hf, ?_⟩
      have := links_binChain (m := m) (prev := binAt i) hne (by rw [h]; exact hl)
        (by rw [h]; exact hbk)
      simpa only [h, List.headD_cons] using this

/-! ## Link words -/

/-- The link words of 16-aligned nodes: `fd` of one never overlaps `bk` of
another, and distinct nodes' same-kind words are disjoint. -/
theorem linkWords_disjoint {x y : Nat} (hx : x % 16 = 0) (hy : y % 16 = 0) :
    (x + 16 + 8 ≤ y + 24 ∨ y + 24 + 8 ≤ x + 16) ∧
    (x ≠ y → (x + 16 + 8 ≤ y + 16 ∨ y + 16 + 8 ≤ x + 16) ∧
      (x + 24 + 8 ≤ y + 24 ∨ y + 24 + 8 ≤ x + 24)) := by
  refine ⟨by omega, fun hne => ⟨by omega, by omega⟩⟩

/-! ## Unlinking -/

/-- **Unlink a node.** Removing `y` from between `x` and `z` needs exactly
`fd x := z` and `bk z := x`; every other link word is kept. -/
theorem links_unlink {m m' : Mem} {pre post : List Nat} {x y z : Nat}
    (h : Links m (pre ++ x :: y :: z :: post))
    (hfd : fdOf m' x = some z) (hbk : bkOf m' z = some x)
    (hag : ∀ a b, [a, b] <:+: (pre ++ [x]) ∨ [a, b] <:+: (z :: post) →
      fdOf m' a = fdOf m a ∧ bkOf m' b = bkOf m b) :
    Links m' (pre ++ x :: z :: post) := by
  rw [links_append] at h ⊢
  obtain ⟨hpre, _, _, hpost⟩ := h
  refine ⟨hpre.transport fun a b hab => hag a b (.inl hab), hfd, hbk, ?_⟩
  exact hpost.2.2.transport fun a b hab => hag a b (.inr hab)

/-! ## Linking in -/

/-- **Link a node in.** Inserting `y` between `x` and `z` needs `fd x := y`,
`bk y := x`, `fd y := z` and `bk z := y`; every other link word is kept. -/
theorem links_link {m m' : Mem} {pre post : List Nat} {x y z : Nat}
    (h : Links m (pre ++ x :: z :: post))
    (h1 : fdOf m' x = some y) (h2 : bkOf m' y = some x) (h3 : fdOf m' y = some z)
    (h4 : bkOf m' z = some y)
    (hag : ∀ a b, [a, b] <:+: (pre ++ [x]) ∨ [a, b] <:+: (z :: post) →
      fdOf m' a = fdOf m a ∧ bkOf m' b = bkOf m b) :
    Links m' (pre ++ x :: y :: z :: post) := by
  rw [links_append] at h ⊢
  obtain ⟨hpre, _, _, hpost⟩ := h
  exact ⟨hpre.transport fun a b hab => hag a b (.inl hab), h1, h2, h3, h4,
    hpost.transport fun a b hab => hag a b (.inr hab)⟩


/-! ## The chunk walk -/

/-- A chunk with its in-use flag replaced when it ends at `q`. -/
def reflag (q : Nat) (b : Bool) (c : Chunk) : Chunk :=
  if c.addr + c.size = q then { c with inuse := b } else c

/-- **Rewrite one header.** Changing the header word at `q` keeps the walk:
the chunk ending at `q` takes its in-use flag from the new header, and a
header that is not the top's keeps its size and flag bits. -/
theorem walk_reheader {m m' : Mem} {q h' : Nat} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs →
      (∀ r, r ≠ q → (r = top ∨ ∃ c ∈ cs, c.addr = r) → read64 m' (r + 8) = read64 m (r + 8)) →
      read64 m' (q + 8) = some h' →
      (q ≠ top → (q = top ∨ ∃ c ∈ cs, c.addr = q) →
        ∃ h, read64 m (q + 8) = some h ∧ chunkSize h' = chunkSize h ∧ h' % 4 < 2) →
      ChunkWalk m' p top (cs.map (reflag q (prevInuse h')))
  | _, _, [], ChunkWalk.top, _, _, _ => .top
  | p, top, _ :: cs, @ChunkWalk.chunk _ _ _ hh h2 _ hh0 hlow hmin hal hn rest, hag, hq, hsame => by
    have hmem : ∀ r, (r = top ∨ ∃ c ∈ cs, c.addr = r) →
        (r = top ∨ ∃ c ∈ (⟨p, chunkSize hh, prevInuse h2⟩ :: cs), c.addr = r) := by
      rintro r (hr | ⟨c, hc, hca⟩)
      · exact .inl hr
      · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hca⟩
    have ih := walk_reheader rest (fun r hr hr' => hag r hr (hmem r hr'))
      hq (fun hne hr => hsame hne (hmem q hr))
    have hself : (p = top ∨ ∃ c ∈ (⟨p, chunkSize hh, prevInuse h2⟩ :: cs), c.addr = p) :=
      .inr ⟨_, List.mem_cons_self, rfl⟩
    -- this chunk's header in `m'`
    obtain ⟨hh', hp', hsz, hlow'⟩ : ∃ hh', read64 m' (p + 8) = some hh' ∧ chunkSize hh' = chunkSize hh ∧
        hh' % 4 < 2 := by
      by_cases hpq : p = q
      · subst hpq
        have hpt : p ≠ top := by have := rest.le; omega
        obtain ⟨h0, hr0, hs, hl⟩ := hsame hpt hself
        rw [hh0] at hr0; cases hr0
        exact ⟨h', hq, hs, hl⟩
      · exact ⟨hh, (hag p hpq hself).trans hh0, rfl, hlow⟩
    -- the next header in `m'`
    have hnext_mem : (p + chunkSize hh = top ∨ ∃ c ∈ (⟨p, chunkSize hh, prevInuse h2⟩ :: cs),
        c.addr = p + chunkSize hh) := by
      rcases rest.head_or_top with he | ⟨c, hc, hca⟩
      · exact .inl he
      · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hca⟩
    have hsz' : chunkSize hh' = chunkSize hh := hsz
    simp only [List.map_cons]
    by_cases hnq : p + chunkSize hh = q
    · -- this chunk ends at `q`: its flag is the new header's
      have hr : reflag q (prevInuse h') ⟨p, chunkSize hh, prevInuse h2⟩ =
          ⟨p, chunkSize hh', prevInuse h'⟩ := by
        simp [reflag, hnq, hsz']
      rw [hr]
      have := ChunkWalk.chunk (m := m') (h := hh') (h' := h') hp' hlow' (by rw [hsz']; exact hmin)
        (by rw [hsz']; exact hal) (by rw [hsz', hnq]; exact hq) (by rw [hsz']; exact ih)
      exact this
    · have hr : reflag q (prevInuse h') ⟨p, chunkSize hh, prevInuse h2⟩ =
          ⟨p, chunkSize hh', prevInuse h2⟩ := by
        simp [reflag, hnq, hsz']
      rw [hr]
      have hn' : read64 m' (p + chunkSize hh' + 8) = some h2 := by
        rw [hsz', hag _ hnq hnext_mem]; exact hn
      exact ChunkWalk.chunk (m := m') hp' hlow' (by rw [hsz']; exact hmin)
        (by rw [hsz']; exact hal) hn' (by rw [hsz']; exact ih)

/-- Every chunk of a walk from an aligned start is 16-aligned. -/
theorem walk_aligned {m : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs → p % 16 = 0 →
      (∀ c ∈ cs, c.addr % 16 = 0) ∧ top % 16 = 0
  | _, _, [], ChunkWalk.top, hp => ⟨(fun _ h => nomatch h), hp⟩
  | _, _, _ :: _, ChunkWalk.chunk _ _ _ hal _ rest, hp => by
    obtain ⟨h1, h2⟩ := walk_aligned rest (by omega)
    refine ⟨fun c hc => ?_, h2⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hp
    · exact h1 c hc

/-- The chunk after `c` in a walk: the next chunk, or the top. Its header
carries `c`'s in-use flag. -/
theorem walk_next_of {m : Mem} {p top : Nat} {c : Chunk} :
    ∀ {cs₁ cs₂ : List Chunk}, ChunkWalk m p top (cs₁ ++ c :: cs₂) →
      (∃ h, read64 m (c.addr + c.size + 8) = some h ∧ prevInuse h = c.inuse) ∧
      (c.addr + c.size = top ∧ cs₂ = [] ∨ ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = c.addr + c.size)
  | [], cs₂, w => by
    cases w with
    | chunk hh hlow hmin hal hn rest =>
      refine ⟨⟨_, hn, rfl⟩, ?_⟩
      cases rest with
      | top => exact .inl ⟨rfl, rfl⟩
      | chunk => exact .inr ⟨_, _, rfl, rfl⟩
  | _ :: cs₁, cs₂, w => by
    cases w with
    | chunk _ _ _ _ _ rest => exact walk_next_of rest


/-! ## Bins and the reflagged walk -/

/-- Bin `i` replaced by `l`. -/
def updBins (bins : Nat → List Nat) (i : Nat) (l : List Nat) (j : Nat) : List Nat :=
  if j = i then l else bins j

theorem updBins_same (bins : Nat → List Nat) (i : Nat) (l : List Nat) : updBins bins i l i = l := by
  simp [updBins]

theorem updBins_other (bins : Nat → List Nat) {i j : Nat} (l : List Nat) (h : j ≠ i) :
    updBins bins i l j = bins j := by
  simp [updBins, h]

theorem mem_reflag {q : Nat} {b : Bool} {cs : List Chunk} {c' : Chunk} (h : c' ∈ cs.map (reflag q b)) :
    ∃ c ∈ cs, c'.addr = c.addr ∧ c'.size = c.size ∧
      (c.addr + c.size = q ∧ c'.inuse = b ∨ c.addr + c.size ≠ q ∧ c' = c) := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
  unfold reflag
  by_cases hq : c.addr + c.size = q
  · simp only [hq, ite_true]; exact ⟨c, hc, rfl, rfl, .inl ⟨hq, by simp⟩⟩
  · simp only [hq, ite_false]; exact ⟨c, hc, rfl, rfl, .inr ⟨hq, rfl⟩⟩

theorem reflag_mem {q : Nat} {b : Bool} {cs : List Chunk} {c : Chunk} (hc : c ∈ cs) :
    reflag q b c ∈ cs.map (reflag q b) := List.mem_map_of_mem hc

theorem reflag_addr (q : Nat) (b : Bool) (c : Chunk) : (reflag q b c).addr = c.addr := by
  unfold reflag; split <;> rfl

theorem reflag_size (q : Nat) (b : Bool) (c : Chunk) : (reflag q b c).size = c.size := by
  unfold reflag; split <;> rfl

theorem reflag_inuse_true {q : Nat} {c : Chunk} (h : c.inuse = true) : (reflag q true c).inuse = true := by
  unfold reflag; split <;> simp [h]

/-- Setting a chunk in use keeps the walk coalesced. -/
theorem coalesced_reflag_true {cs : List Chunk} {q : Nat}
    (h : ∀ i (hi : i + 1 < cs.length), cs[i].inuse = true ∨ cs[i + 1].inuse = true) :
    ∀ i (hi : i + 1 < (cs.map (reflag q true)).length),
      (cs.map (reflag q true))[i].inuse = true ∨ (cs.map (reflag q true))[i + 1].inuse = true := by
  intro i hi
  simp only [List.length_map] at hi
  simp only [List.getElem_map]
  rcases h i hi with h1 | h1
  · exact .inl (reflag_inuse_true h1)
  · exact .inr (reflag_inuse_true h1)


/-! ## Adjacent pairs -/

theorem pair_mem {a b : Nat} {l : List Nat} (h : [a, b] <:+: l) : a ∈ l ∧ b ∈ l := by
  obtain ⟨s, t, rfl⟩ := h
  exact ⟨by simp, by simp⟩

/-- In a duplicate-free list, the first of an adjacent pair is not the last element. -/
theorem pair_ne_last {a b x : Nat} {l : List Nat} (h : [a, b] <:+: l ++ [x])
    (hnd : (l ++ [x]).Nodup) : a ≠ x := by
  rintro rfl
  obtain ⟨s, t, e⟩ := h
  have hl : (l ++ [a]).getLast? = some a := by simp
  rw [← e] at hl hnd
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hl hnd
  have hbt : a ∈ b :: t := by
    have e2 : (s ++ a :: b :: t).getLast? = (b :: t).getLast? := by
      rw [show s ++ a :: b :: t = (s ++ [a]) ++ (b :: t) by simp, List.getLast?_append]
      cases h : (b :: t).getLast? with
      | none => simp at h
      | some y => simp
    rw [e2] at hl
    exact List.mem_of_getLast? hl
  rw [List.nodup_append] at hnd
  exact (List.nodup_cons.mp hnd.2.1).1 hbt

/-- In a duplicate-free list, the second of an adjacent pair is not the head. -/
theorem pair_ne_head {a b x : Nat} {l : List Nat} (h : [a, b] <:+: x :: l)
    (hnd : (x :: l).Nodup) : b ≠ x := by
  rintro rfl
  obtain ⟨s, t, e⟩ := h
  rw [← e] at hnd
  rcases s with _ | ⟨s0, s'⟩
  · simp only [List.nil_append, List.cons_append] at e hnd
    obtain ⟨rfl, _⟩ := List.cons.inj e
    simp at hnd
  · simp only [List.cons_append] at e
    obtain ⟨rfl, _⟩ := List.cons.inj e
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.nodup_cons] at hnd
    exact hnd.1 (by simp)

end VsaIris.VsaHeap
