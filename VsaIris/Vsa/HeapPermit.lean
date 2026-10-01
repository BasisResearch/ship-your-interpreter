import VsaIris.Vsa.HeapFree
import VsaIris.Vsa.Region

/-!
# Heap surgery permits

A `Permit` is a heap edit as data: the 8-byte reads the edited memory must show,
the words it must keep, and its byte window. `Realises H m m' p` says the memory
`m'` carries out `p` over `m`. `Realises.of_log` confirms this from the path's
actual `writeLog`: the window check is one key goal per store (`wl_win`, over the
key-list view `LogIn` of `Region.lean`), the reads are one `rd_log` call. One
soundness theorem per edit (`PHeapAt.split_permit`, `.unlink_permit`,
`.absorb_permit`) wraps the existing per-operation lemma. `Realises.seq_agree`
composes two edits' windows.

The local facts of a chunk, a free chunk or a bin node are the regions of
`Region.lean` (`BlockHeapAt.chunkK`, `.freeSpan`, `.nodeK`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Inst

/-! ## Write-log windows (one check per store) -/

/-- Outside the window `P`, memory `m` agrees with `m0`. -/
def WinAgree (P : Nat → Prop) (m m0 : Mem) : Prop := ∀ a, ¬ P a → m[a]? = m0[a]?

theorem WinAgree.refl (P : Nat → Prop) (m : Mem) : WinAgree P m m := fun _ _ => rfl

theorem WinAgree.step {P : Nat → Prop} {m m0 : Mem} {L : List WEntry} (h : WinAgree P m m0)
    (hL : LogIn P L) : WinAgree P (writeLog m L) m0 :=
  fun a ha => (writeLog_out _ _ _ (outL_of_logIn hL a ha)).trans (h a ha)

/-- Turn `WinAgree P (stores over m0) m0` into one key goal per store, introducing the
byte `b` and its bounds `hb1 hb2`. -/
syntax "wl_win" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wl_win) =>
    `(tactic| (repeat' (first
                 | with_reducible exact WinAgree.refl _ _
                 | refine WinAgree.step ?_ ⟨?_, trivial⟩)
               all_goals (intro b hb1 hb2; try simp only at hb1 hb2 ⊢)))

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

/-- Discharge the reads and kept words of a permit over a concrete store log; also closes a
single `read64 (writeLog …) a = some v` goal of an edit that has no permit. -/
syntax "rd_log" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rd_log) => `(tactic| rd_log [])
  | `(tactic| rd_log [$hs,*]) =>
    `(tactic| (try simp only [ReadsOK, KeepsOK, and_true]
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

/-- Take a binned free chunk whole: the unlink edit, with the chunk's block entering the
footprint. -/
theorem PHeapAt.take_permit {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {i : Nat} (hi0 : 0 < i) (hi : i < numBins) {pre post : List Nat} {v : Nat}
    (hbin : bins i = pre ++ v :: post) {c : Chunk} (hc : c ∈ chunks) (hcv : c.addr = v)
    {n : Nat} (hn : n + 8 ≤ c.size) {pred succ : Nat}
    (hpred : (binAt i :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt i]).head? = some succ) {hd' : Nat}
    (hsz : ∀ hd, read64 m (v + c.size + 8) = some hd → chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2)
    (hpi : prevInuse hd' = true)
    (hR : Realises H m m' (unlinkPermit pred succ (v + c.size) hd')) :
    PHeapAt m' ((v + 16, n) :: H) top brkv (chunks.map (reflag (v + c.size) true))
      (updBins bins i (pre ++ post)) :=
  have ⟨r1, r2, r3, _⟩ := hR.reads
  h.take hi0 hi hbin hc hcv hn hpred hsucc r1 r2 r3 hsz hpi hR.agree

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
