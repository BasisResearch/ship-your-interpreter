import VsaIris.Vsa.HeapFree
import VsaIris.Vsa.MallocCtx

/-!
# Heap surgery permits

Two layers over the dlmalloc invariant `PHeapAt`.

* **Sections.** `ChunkSec`, `FreeSec` and `NodeSec` are the local facts of one
  chunk, one free chunk, or one bin node (bounds, alignment, header reads,
  header/link-word footprint), read off the global invariant by one lemma each.
* **Permits.** A `Permit` is a heap edit as data: the 8-byte reads the edited
  memory must show, the words it must keep, and its byte window. `Realises H m m' p`
  says the memory `m'` carries out `p` over `m`. `Realises.of_log` confirms this
  from the path's actual `writeLog` (the window check is one `EntryIn` goal per store via
  `wl_win`, the reads are one `rd_log` call). One soundness theorem per edit (`PHeapAt.split_permit`,
  `.unlink_permit`, `.absorb_permit`) wraps the existing per-operation lemma.
  `Realises.seq_agree` composes two edits' windows.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Inst

/-! ## Sections -/

/-- Local facts of the chunk `⟨a, s, u⟩` of the walk. -/
structure ChunkSec (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat) (chunks : List Chunk)
    (a s : Nat) (u : Bool) : Prop where
  lo : 0x8001c170 ≤ a
  hi : a + s ≤ top
  room : top + 16 ≤ brkv
  brk : brkv ≤ 0x87800000
  al : a % 16 = 0
  sz16 : s % 16 = 0
  sz32 : 32 ≤ s
  hdr : ∃ h, read64 m (a + 8) = some h ∧ chunkSize h = s ∧ h % 4 < 2
  nhdr : ∃ hn, read64 m (a + s + 8) = some hn ∧ prevInuse hn = u
  hfoot : ∀ k, k < 8 → vsaFoot H (a + 8 + k)
  nfoot : ∀ k, k < 8 → vsaFoot H (a + s + 8 + k)
  next : a + s = top ∨ ∃ d ∈ chunks, d.addr = a + s

theorem BlockHeapAt.sec {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) : ChunkSec m H top brkv chunks c.addr c.size c.inuse := by
  have HH := B.heap
  have hb := HH.walk.chunk_bounds c hc
  have hbrk := HH.brk_le; have hroom := B.top_room
  unfold heapStart heapEnd at *
  exact ⟨hb.1, hb.2.1, hroom, hbrk, HH.aligned.1 c hc, (walk_sizes HH.walk c hc).1,
    (walk_sizes HH.walk c hc).2, (HH.headers hc).1, (HH.headers hc).2,
    foot_header B (.inr ⟨c, hc, rfl⟩), foot_header B (HH.end_bnd hc |>.elim .inl .inr),
    HH.end_bnd hc⟩

/-- Bring the arithmetic fields of a section into context for `omega`. -/
syntax "sec_arith " term : tactic
macro_rules
  | `(tactic| sec_arith $S) =>
    `(tactic| (have := ChunkSec.lo $S; have := ChunkSec.hi $S; have := ChunkSec.room $S
               have := ChunkSec.brk $S; have := ChunkSec.al $S; have := ChunkSec.sz16 $S
               have := ChunkSec.sz32 $S))

/-- The walk successor of a chunk that does not end at `top`. -/
theorem BlockHeapAt.next_chunk {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) (hnt : c.addr + c.size ≠ top) :
    ∃ cs₁ d cs₃, chunks = cs₁ ++ c :: d :: cs₃ ∧ d.addr = c.addr + c.size := by
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := B.heap.walk
  rw [hsplit] at hw
  rcases (walk_next_of hw).2 with ⟨he, _⟩ | ⟨d, cs₃, rfl, hd⟩
  · exact absurd he hnt
  · exact ⟨cs₁, d, cs₃, hsplit, hd⟩

/-- The walk successor of `c` is the given chunk `d` at `c`'s end. -/
theorem BlockHeapAt.next_eq {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins)
    {c d : Chunk} (hc : c ∈ chunks) (hd : d ∈ chunks) (hda : d.addr = c.addr + c.size) :
    ∃ cs₁ cs₃, chunks = cs₁ ++ c :: d :: cs₃ := by
  have hb := B.heap.walk.chunk_bounds d hd
  obtain ⟨cs₁, d', cs₃, hsplit, hd'⟩ := B.next_chunk hc (by omega)
  have hdm : d' ∈ chunks := by rw [hsplit]; simp
  obtain rfl := B.heap.chunk_eq hdm hd (by omega)
  exact ⟨cs₁, cs₃, hsplit⟩

theorem foot_free_span {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) (hf : c.inuse = false) :
    ∀ a, c.addr + 8 ≤ a → a < c.addr + c.size + 16 → vsaFoot H a := by
  have hb := B.heap.walk.chunk_bounds
  have hs := B.heap.walk.chunk_sep
  have hroom := B.top_room
  have hbrk := B.heap.brk_le
  have hle := B.heap.walk.le
  have hbc := hb c hc
  intro a h1 h2
  by_cases hh : a < c.addr + 16
  · have := foot_header B (.inr ⟨c, hc, rfl⟩) (a - (c.addr + 8)) (by omega)
    rwa [show c.addr + 8 + (a - (c.addr + 8)) = a by omega] at this
  by_cases ht : c.addr + c.size + 8 ≤ a
  · have := foot_header B (B.heap.end_bnd hc |>.elim .inl .inr) (a - (c.addr + c.size + 8))
      (by omega)
    rwa [show c.addr + c.size + 8 + (a - (c.addr + c.size + 8)) = a by omega] at this
  refine foot_of_arena B.heap (by unfold heapStart at *; omega) (by omega) ?_
  intro c' hc' hu hin
  have := hb c' hc'
  rcases hs c' hc' c hc with rfl | h3 | h3
  · rw [hu] at hf; cases hf
  · omega
  · omega

/-- Local facts of one free chunk: its section plus the whole span it owns. -/
structure FreeSec (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat) (chunks : List Chunk)
    (a s : Nat) : Prop extends ChunkSec m H top brkv chunks a s false where
  body : ∀ b, a + 8 ≤ b → b < a + s + 16 → vsaFoot H b

theorem BlockHeapAt.freeSec {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins)
    {a s : Nat} (hc : ⟨a, s, false⟩ ∈ chunks) : FreeSec m H top brkv chunks a s :=
  { B.sec hc with body := foot_free_span B hc rfl }

/-- Local facts of one node of bin `i` (the bin header or a member chunk). -/
structure NodeSec (H : List (Nat × Nat)) (top : Nat) (chunks : List Chunk) (x : Nat) : Prop where
  al : x % 16 = 0
  lo : 0x8001ad20 ≤ x
  hi : x + 32 ≤ top
  fd : ∀ k, k < 8 → vsaFoot H (x + 16 + k)
  bk : ∀ k, k < 8 → vsaFoot H (x + 24 + k)
  bnd : ∀ b, (b = top ∨ ∃ c ∈ chunks, c.addr = b) → ∀ k, 0 < k → k < 32 → b ≠ x + k

theorem BlockHeapAt.nodeSec {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins)
    {i x : Nat} (hi0 : 0 < i) (hi : i < numBins) (hx : x = binAt i ∨ x ∈ bins i) :
    NodeSec H top chunks x := by
  have HH := B.heap
  obtain ⟨hx16, hnode⟩ := HH.node hi0 hi hx
  have hf := B.node_foot hi0 hi hx
  have hloc : 0x8001ad20 ≤ x ∧ x + 32 ≤ top := by
    rcases hnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo i hi; have := HH.walk.le
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  refine ⟨hx16, hloc.1, hloc.2, fun k hk => ?_, fun k hk => ?_,
    fun b hb k hk0 hk => HH.bnd_ne_node hi hnode hb k hk0 hk⟩
  · have := hf (16 + k) (by omega) (by omega); rwa [show x + (16 + k) = x + 16 + k by omega] at this
  · have := hf (24 + k) (by omega) (by omega); rwa [show x + (24 + k) = x + 24 + k by omega] at this

/-- An 8-byte heap word is off the allocator's stack frame. -/
theorem off_stack_of {C : MCtx} {a : Nat}
    (hd : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hf : ∀ k, k < 8 → vsaFoot C.H (a + k)) : a + 8 ≤ C.s.toNat - 256 ∨ C.s.toNat ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have hk : (if a ≥ C.s.toNat - mHead then 0 else C.s.toNat - mHead - a) < 8 := by
    unfold mHead; split <;> omega
  exact hd _ (by unfold mHead at *; split <;> omega) (by unfold mHead at *; split <;> omega) (hf _ hk)

/-! ## Write-log windows (one check per store) -/

/-- Outside the window `P`, memory `m` agrees with `m0`. -/
def WinAgree (P : Nat → Prop) (m m0 : Mem) : Prop := ∀ a, ¬ P a → m[a]? = m0[a]?

/-- Every byte of the store `e` lies in the window `P`. -/
def EntryIn (P : Nat → Prop) (e : WEntry) : Prop := ∀ b, e.1 ≤ b → b < e.1 + e.2.1 → P b

theorem WinAgree.store {P : Nat → Prop} {m m0 : Mem} {e : WEntry} (h : WinAgree P m m0)
    (he : EntryIn P e) : WinAgree P (writeLog m [e]) m0 := fun a ha => by
  rw [writeLog_out _ [e] _ ⟨Classical.byContradiction fun hc => ha (he a (by omega) (by omega)),
    trivial⟩, h a ha]

/-- Every byte satisfying `P` is present in `m`. -/
def Present (P : Nat → Prop) (m : Mem) : Prop := ∀ b, P b → (m[b]?).isSome

theorem Present.store {P : Nat → Prop} {m : Mem} {e : WEntry} (h : Present P m) :
    Present P (writeLog m [e]) := fun b hb => writeLog_present _ _ _ (h b hb)

/-- One peeling step: close `WinAgree P m m` by reflexivity when both memories are the same
term, otherwise peel the outermost store of `m`. -/
elab "wl_step" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  match ty.getAppFnArgs with
  | (``WinAgree, #[_, m, m0]) =>
    if m == m0 then Lean.Elab.Tactic.evalTactic (← `(tactic| exact fun _ _ => rfl))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| refine WinAgree.store ?_ ?_))
  | _ => throwError "wl_step: goal is not `WinAgree`"

/-- Peel every store of a nested `writeLog` into one `EntryIn` goal each, introducing the
byte `b` and its bounds `hb1 hb2`; `base` closes the unwritten memory when it is not the
permit's source memory. -/
syntax "wl_win" (ppSpace term)? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wl_win) =>
    `(tactic| (repeat' wl_step
               all_goals (unfold EntryIn; intro b hb1 hb2; simp only at hb1 hb2 ⊢)))
  | `(tactic| wl_win $base) =>
    `(tactic| (try change WinAgree _ _ _
               repeat' (first | wl_step | exact $base)
               all_goals (unfold EntryIn; intro b hb1 hb2; simp only at hb1 hb2 ⊢)))

/-- Presence of the footprint through every store of a nested `writeLog`. -/
syntax "wl_pres " term : tactic
macro_rules
  | `(tactic| wl_pres $base) => `(tactic| ((repeat' refine Present.store ?_); exact $base))

/-! ## Permits -/

/-- A heap edit as data: required 8-byte reads, kept words, byte window. -/
structure Permit where
  reads : List (Nat × Nat)
  keeps : List Nat
  win : Nat → Prop

def ReadsOK (m : Mem) : List (Nat × Nat) → Prop
  | [] => True
  | r :: l => read64 m r.1 = some r.2 ∧ ReadsOK m l

def KeepsOK (m m' : Mem) : List Nat → Prop
  | [] => True
  | a :: l => read64 m' a = read64 m a ∧ KeepsOK m m' l

/-- `m'` carries out the edit `p` over `m` on the footprint `H`. -/
structure Realises (H : List (Nat × Nat)) (m m' : Mem) (p : Permit) : Prop where
  reads : ReadsOK m' p.reads
  keeps : KeepsOK m m' p.keeps
  agree : ∀ a, vsaFoot H a → ¬ p.win a → m'[a]? = m[a]?

/-- Confirm a permit against the path's actual stores: every store lies in the permit's
window or off the heap footprint (`wl_win`), and the reads hold (`rd_log`). -/
theorem Realises.of_log {H : List (Nat × Nat)} {m m' : Mem} {p : Permit}
    (hlog : WinAgree (fun a => p.win a ∨ ¬ vsaFoot H a) m' m)
    (hr : ReadsOK m' p.reads) (hk : KeepsOK m m' p.keeps) : Realises H m m' p :=
  ⟨hr, hk, fun a ha hw => hlog a (by rintro (h | h) <;> contradiction)⟩

/-- Sequential composition of two edits' windows. -/
theorem Realises.seq_agree {H : List (Nat × Nat)} {m m1 m2 : Mem} {p q : Permit}
    (h1 : Realises H m m1 p) (h2 : Realises H m1 m2 q) :
    ∀ a, vsaFoot H a → ¬ (p.win a ∨ q.win a) → m2[a]? = m[a]? :=
  fun a ha hw => (h2.agree a ha fun h => hw (.inr h)).trans (h1.agree a ha fun h => hw (.inl h))

/-- Discharge the reads and kept words of a permit over a concrete store log. -/
syntax "rd_log" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rd_log) => `(tactic| rd_log [])
  | `(tactic| rd_log [$hs,*]) =>
    `(tactic| (simp only [ReadsOK, KeepsOK, and_true]
               repeat' refine And.intro ?_ ?_
               all_goals (simp (disch := omega) only [read64_hit_eq, read64_miss]
                          try simp only [$hs,*])))

/-! ### Split a free chunk (bin-1 remainder) -/

abbrev splitPermit (v nb sz pred succ : Nat) : Permit where
  reads := [(v + 8, nb + 1), (v + nb + 8, sz - nb + 1), (v + nb + 16, binAt 1),
    (v + nb + 24, binAt 1), (binAt 1 + 16, v + nb), (binAt 1 + 24, v + nb), (v + sz, sz - nb)]
  keeps := [v + sz + 8]
  win a := TakeW pred succ (v + sz) a ∨ CarveW v nb sz a

theorem PHeapAt.split_permit {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {v sz : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨v, sz, false⟩ :: cs₂) bins)
    {i : Nat} (hi0 : 0 < i) (hi : i < numBins) {pre post : List Nat}
    (hbin : bins i = pre ++ v :: post)
    {nb n : Nat} (hnb16 : nb % 16 = 0) (hnb32 : 32 ≤ nb) (hsz : nb + 32 ≤ sz) (hn : n + 8 ≤ nb)
    (hb1 : updBins bins i (pre ++ post) 1 = [])
    {pred succ : Nat} (hpred : (binAt i :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt i]).head? = some succ)
    (hfd : i ≠ 1 → fdOf m' pred = some succ) (hbk : i ≠ 1 → bkOf m' succ = some pred)
    (hR : Realises H m m' (splitPermit v nb sz pred succ)) :
    PHeapAt m' ((v + 16, n) :: H) top brkv
      (cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: cs₂)
      (updBins (updBins bins i (pre ++ post)) 1 [v + nb]) :=
  have ⟨r1, r2, r3, r4, r5, r6, r7, _⟩ := hR.reads
  h.splitFree hi0 hi hbin hnb16 hnb32 hsz hn hb1 hpred hsucc hfd hbk r1 r2 r3 r4 r5 r6 r7
    hR.keeps.1 fun a ha h1 h2 => hR.agree a ha (by rintro (h | h) <;> contradiction)

/-! ### Unlink a free chunk from its bin and set the next chunk's prev-inuse bit -/

abbrev unlinkPermit (pred succ nx hd' : Nat) : Permit where
  reads := [(pred + 16, succ), (succ + 24, pred), (nx + 8, hd')]
  keeps := []
  win := TakeW pred succ nx

theorem PHeapAt.unlink_permit {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {i : Nat} (hi0 : 0 < i) (hi : i < numBins) {pre post : List Nat} {v : Nat}
    (hbin : bins i = pre ++ v :: post) {c : Chunk} (hc : c ∈ chunks) (hcv : c.addr = v)
    {pred succ : Nat} (hpred : (binAt i :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt i]).head? = some succ) {hd' : Nat}
    (hsz : ∀ hd, read64 m (v + c.size + 8) = some hd → chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2)
    (hpi : prevInuse hd' = true)
    (hR : Realises H m m' (unlinkPermit pred succ (v + c.size) hd')) :
    PHeapAt m' H top brkv (chunks.map (reflag (v + c.size) true)) (updBins bins i (pre ++ post)) :=
  have ⟨r1, r2, r3, _⟩ := hR.reads
  h.unlink hi0 hi hbin hc hcv hpred hsucc r1 r2 r3 hsz hpi hR.agree

/-! ### Absorb an in-use neighbour into an in-use chunk (reheader) -/

abbrev absorbPermit (x a h' : Nat) : Permit where
  reads := [(x + 8, h')]
  keeps := []
  win w := (x + 8 ≤ w ∧ w < x + 16) ∨ (x + a + 8 ≤ w ∧ w < x + a + 16)

theorem PHeapAt.absorb_permit {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {x a b : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂) bins)
    (hno : ∀ e ∈ H, e.1 ≠ x + a + 16) {h' : Nat} (hsz : chunkSize h' = a + b)
    (hlow : h' % 4 < 2) (hpi : ∀ h0, read64 m (x + 8) = some h0 → prevInuse h' = prevInuse h0)
    (hR : Realises H m m' (absorbPermit x a h')) :
    PHeapAt m' H top brkv (cs₁ ++ ⟨x, a + b, true⟩ :: cs₂) bins :=
  h.absorb hno hR.reads.1 hsz hlow hpi fun w hw h1 h2 =>
    hR.agree w hw (by rintro (h | h) <;> contradiction)

end VsaIris.VsaHeap
