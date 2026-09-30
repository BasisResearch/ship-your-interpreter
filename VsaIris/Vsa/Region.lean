import VsaIris.Vsa.MallocCtx

/-!
# Region-keyed memory for allocator path proofs (candidate KT)

Every address an allocator path touches is `region ⊕ offset`. A region is a
base and an extent whose bytes all satisfy an ownership predicate; regions are
minted once:

* a heap chunk from the chunk walk of `PHeapAt` (`BlockHeapAt.chunkK`,
  `.freeSpan`, `.next`, `.nodeK`),
* the program-lifetime static table (`globRgn`, `binRgn`),
* the stack frame (`MWin`'s stack half, `win_stack`).

The laws are proved once over regions:

* in-window / off-mailbox (L3): `Rgn.ldOK`, `Rgn.stOK`, `WOK.rgn`;
* off-stack (L3): `Rgn.offStack`;
* frame (L5): a store log is summarised by its key list; `LogIn` says every
  key lies in a region, and `frame_log` carries the frame post through the
  whole log at once;
* read-over-write (L2) stays `read64_hit_eq`/`read64_miss` keyed by the log.

`rgn_side` extends `sx_side`, so the `sx_run` driver discharges ownership and
access-range obligations from any region in the local context: the access is
keyed once (`rgn_key`: address normalised to Nat arithmetic), regions are ranked
by the atoms they share with the key, and each candidate is one linear check.
`rgn_win` closes one `LogIn` key the same way; `log_in` closes a whole key list.
`open_fields` exposes a minted structure's geometry to the arithmetic deciders.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- `ext` consecutive bytes from `base`, each satisfying `P`. -/
structure Rgn (P : Nat → Prop) (base ext : Nat) : Prop where
  byte : ∀ k, k < ext → P (base + k)

namespace Rgn

variable {P P' : Nat → Prop} {b e : Nat}

theorem mem (r : Rgn P b e) {a : Nat} (h1 : b ≤ a) (h2 : a < b + e) : P a := by
  have := r.byte (a - b) (by omega)
  rwa [show b + (a - b) = a by omega] at this

theorem sub (r : Rgn P b e) {b' e' : Nat} (h1 : b ≤ b') (h2 : b' + e' ≤ b + e) : Rgn P b' e' :=
  ⟨fun k hk => r.mem (by omega) (by omega)⟩

theorem mono (r : Rgn P b e) (h : ∀ a, P a → P' a) : Rgn P' b e :=
  ⟨fun k hk => h _ (r.byte k hk)⟩

theorem word (r : Rgn P b e) {a w : Nat} (h1 : b ≤ a) (h2 : a + w ≤ b + e) :
    ∀ k, k < w → P (a + k) :=
  (r.sub h1 h2).byte

theorem lower {H : List (Nat × Nat)} {x : Nat × Nat} (r : Rgn (vsaFoot (x :: H)) b e) :
    Rgn (vsaFoot H) b e :=
  r.mono fun _ => vsaFoot_of_cons'
where
  vsaFoot_of_cons' {a : Nat} : vsaFoot (x :: H) a → vsaFoot H a
    | .inl h => .inl h
    | .inr ⟨h1, h2, h3⟩ => .inr ⟨h1, h2, fun e' he' => h3 e' (List.mem_cons_of_mem _ he')⟩

end Rgn

theorem vsaFoot_range {H : List (Nat × Nat)} {a : Nat} (h : vsaFoot H a) :
    0x8001ad10 ≤ a ∧ a < 0x87800000 := by
  rcases h with h | ⟨h1, h2, _⟩
  · unfold allocGlobal InRange at h; omega
  · unfold heapStart at h1; unfold heapEnd at h2; omega

section Laws

variable {H : List (Nat × Nat)} {b e a w : Nat}

/-! Each law takes the key-in-region check as ONE conjunction, so a candidate
region costs one arithmetic query. -/

theorem Rgn.ldOK (r : Rgn (vsaFoot H) b e) (h : b ≤ a ∧ a + w ≤ b + e ∧ 0 < w) : LdOK a w := by
  have l := vsaFoot_range (r.mem h.1 (by omega))
  have u := vsaFoot_range (r.mem (a := a + w - 1) (by omega) (by omega))
  unfold LdOK Vsa.Sim.tohostAddr; omega

theorem Rgn.stOK (r : Rgn (vsaFoot H) b e) (h : b ≤ a ∧ a + w ≤ b + e ∧ 0 < w ∧ a % w = 0) :
    StOK a w := by
  have l := vsaFoot_range (r.mem h.1 (by omega))
  have u := vsaFoot_range (r.mem (a := a + w - 1) (by omega) (by omega))
  unfold StOK Vsa.Sim.tohostAddr; omega

theorem WOK.rgn {C : MCtx} (O : WOK C) (r : Rgn (vsaFoot C.H) b e) (h : b ≤ a ∧ a + w ≤ b + e) :
    ∀ x ∈ accAddrs a w, C.S x :=
  O.foot (r.word h.1 h.2)

theorem Rgn.win {s : BitVec 64} (r : Rgn (vsaFoot H) b e) (h : b ≤ a ∧ a + w ≤ b + e) :
    ∀ x, a ≤ x → x < a + w → MWin H s x :=
  fun _ hx1 hx2 => .inl (r.mem (by omega) (by omega))

theorem win_stack' {s : BitVec 64} (h : s.toNat - 256 ≤ a ∧ a + w ≤ s.toNat) :
    ∀ x, a ≤ x → x < a + w → MWin H s x :=
  win_stack (by unfold mHead; exact h.1) h.2

/-- A heap region never meets the stack window. -/
theorem Rgn.offStack {s : BitVec 64} (r : Rgn (vsaFoot H) b e)
    (hd : ∀ a, s.toNat - mHead ≤ a → a < s.toNat → ¬ vsaFoot H a) (he : 0 < e) :
    b + e ≤ s.toNat - mHead ∨ s.toNat ≤ b := by
  refine Classical.byContradiction fun hc => ?_
  by_cases h : s.toNat - mHead ≤ b
  · exact hd b h (by omega) (r.mem (by omega) (by omega))
  · exact hd _ (Nat.le_refl _) (by unfold mHead at *; omega) (r.mem (by omega) (by omega))

/-- A single owned byte is off the stack window. -/
theorem offStack_pt {s : BitVec 64} (hd : ∀ a, s.toNat - mHead ≤ a → a < s.toNat → ¬ vsaFoot H a)
    (ha : vsaFoot H a) : a < s.toNat - 256 ∨ s.toNat ≤ a := by
  have := (⟨fun k hk => by rwa [show k = 0 by omega]⟩ : Rgn (vsaFoot H) a 1).offStack hd (by decide)
  unfold mHead at this; omega

end Laws

/-! ## The static table (V1): minted once against the fixed layout. -/

theorem globRgn (H : List (Nat × Nat)) : Rgn (vsaFoot H) 0x8001ad10 0x810 :=
  ⟨fun k hk => .inl (.inl ⟨by omega, by omega⟩)⟩

/-- The `fd`/`bk` link words of bin `j`'s header. -/
theorem binRgn (H : List (Nat × Nat)) {j : Nat} (hj : j < numBins) :
    Rgn (vsaFoot H) (binAt j + 16) 16 := by
  have := binAt_geo j hj
  exact (globRgn H).sub (by omega) (by omega)

/-! ## Chunk regions, minted from the chunk walk. -/

/-- The local section of one chunk of the walk: bounds, alignment, its two header
regions (own header, next boundary header), the two header reads and its walk
successor. -/
structure ChunkK (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat) (chunks : List Chunk)
    (c : Chunk) : Prop where
  lo : 0x8001c170 ≤ c.addr
  hi : c.addr + c.size ≤ top
  room : top + 16 ≤ brkv
  brk : brkv ≤ 0x87800000
  al : c.addr % 16 = 0
  topal : top % 16 = 0
  sz16 : c.size % 16 = 0
  sz32 : 32 ≤ c.size
  hdr : Rgn (vsaFoot H) (c.addr + 8) 8
  nhdr : Rgn (vsaFoot H) (c.addr + c.size + 8) 8
  hdrv : ∃ h, read64 m (c.addr + 8) = some h ∧ chunkSize h = c.size ∧ h % 4 < 2
  nhdrv : ∃ hn, read64 m (c.addr + c.size + 8) = some hn ∧ prevInuse hn = c.inuse
  next : c.addr + c.size = top ∨ ∃ d ∈ chunks, d.addr = c.addr + c.size

variable {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

theorem BlockHeapAt.chunkK (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) : ChunkK m H top brkv chunks c := by
  have HH := B.heap
  have hb := HH.walk.chunk_bounds c hc
  have hs := walk_sizes HH.walk c hc
  have hbrk := HH.brk_le
  unfold heapStart heapEnd at *
  exact ⟨hb.1, hb.2.1, B.top_room, hbrk, HH.aligned.1 c hc, HH.aligned.2, hs.1, hs.2,
    ⟨foot_header B (.inr ⟨c, hc, rfl⟩)⟩, ⟨foot_header B (HH.end_bnd hc)⟩, (HH.headers hc).1,
    (HH.headers hc).2, HH.end_bnd hc⟩

theorem ChunkK.lower {x : Nat × Nat} {c : Chunk} (K : ChunkK m (x :: H) top brkv chunks c) :
    ChunkK m H top brkv chunks c :=
  { K with hdr := K.hdr.lower, nhdr := K.nhdr.lower }

/-- A free chunk owns its whole span, header to next header. -/
theorem BlockHeapAt.freeSpan (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) (hf : c.inuse = false) : Rgn (vsaFoot H) (c.addr + 8) (c.size + 8) := by
  have hb := B.heap.walk.chunk_bounds
  have hs := B.heap.walk.chunk_sep
  have hroom := B.top_room
  have hbrk := B.heap.brk_le
  have hle := B.heap.walk.le
  have hbc := hb c hc
  refine ⟨fun k hk => ?_⟩
  by_cases hh : k < 8
  · exact (⟨foot_header B (.inr ⟨c, hc, rfl⟩)⟩ : Rgn _ _ 8).byte k hh
  by_cases ht : c.size ≤ k
  · have := foot_header B (B.heap.end_bnd hc) (k - c.size) (by omega)
    rwa [show c.addr + c.size + 8 + (k - c.size) = c.addr + 8 + k by omega] at this
  refine foot_of_arena B.heap (by unfold heapStart at *; omega) (by omega) ?_
  intro c' hc' hu hin
  have := hb c' hc'
  rcases hs c' hc' c hc with rfl | h3 | h3
  · rw [hu] at hf; cases hf
  · omega
  · omega

theorem foot_free_span (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) (hf : c.inuse = false) :
    ∀ a, c.addr + 8 ≤ a → a < c.addr + c.size + 16 → vsaFoot H a :=
  fun _ h1 h2 => (B.freeSpan hc hf).mem h1 (by omega)

/-- The neighbour region: a chunk that does not end at `top` is followed by a
chunk starting at its end. -/
theorem BlockHeapAt.next (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk} (hc : c ∈ chunks)
    (hne : c.addr + c.size ≠ top) :
    ∃ cs₁ d cs₃, chunks = cs₁ ++ c :: d :: cs₃ ∧ d.addr = c.addr + c.size := by
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := B.heap.walk
  rw [hsplit] at hw
  rcases (walk_next_of hw).2 with ⟨he, _⟩ | ⟨d, cs₃, rfl, hd⟩
  · exact absurd he hne
  · exact ⟨cs₁, d, cs₃, hsplit, hd⟩

/-- The walk successor of `c` is the given chunk `d` at `c`'s end. -/
theorem BlockHeapAt.next_eq (B : BlockHeapAt m H top brkv chunks bins) {c d : Chunk}
    (hc : c ∈ chunks) (hd : d ∈ chunks) (hda : d.addr = c.addr + c.size) :
    ∃ cs₁ cs₃, chunks = cs₁ ++ c :: d :: cs₃ := by
  have hb := B.heap.walk.chunk_bounds d hd
  obtain ⟨cs₁, d', cs₃, hsplit, hd'⟩ := B.next hc (by omega)
  have hdm : d' ∈ chunks := by rw [hsplit]; simp
  obtain rfl := B.heap.chunk_eq hdm hd (by omega)
  exact ⟨cs₁, cs₃, hsplit⟩

/-- A bin-ring node (a bin header or a binned free chunk): alignment, bounds, its
`fd`/`bk` link region, and separation of its link words from chunk boundaries. -/
structure NodeK (H : List (Nat × Nat)) (top : Nat) (chunks : List Chunk) (x : Nat) : Prop where
  al : x % 16 = 0
  lo : 0x8001ad20 ≤ x
  hi : x + 32 ≤ top
  links : Rgn (vsaFoot H) (x + 16) 16
  bnd : ∀ b, (b = top ∨ ∃ c ∈ chunks, c.addr = b) → ∀ k, 0 < k → k < 32 → b ≠ x + k

theorem BlockHeapAt.nodeK (B : BlockHeapAt m H top brkv chunks bins) {j x : Nat} (hj0 : 0 < j)
    (hj : j < numBins) (hx : x = binAt j ∨ x ∈ bins j) : NodeK H top chunks x := by
  have HH := B.heap
  obtain ⟨hx16, hnode⟩ := HH.node hj0 hj hx
  have hloc : 0x8001ad20 ≤ x ∧ x + 32 ≤ top := by
    rcases hnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo j hj; have := HH.walk.le
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  exact ⟨hx16, hloc.1, hloc.2, ⟨fun k hk => by
    have := B.node_foot hj0 hj hx (16 + k) (by omega) (by omega)
    rwa [← Nat.add_assoc] at this⟩, fun b hb k hk0 hk => HH.bnd_ne_node hj hnode hb k hk0 hk⟩

theorem NodeK.lower {x : Nat × Nat} {z : Nat} (K : NodeK (x :: H) top chunks z) :
    NodeK H top chunks z :=
  { K with links := K.links.lower }

/-- An 8-byte heap word is off the allocator's stack frame. -/
theorem off_stack_of {C : MCtx} {a : Nat}
    (hd : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hf : ∀ k, k < 8 → vsaFoot C.H (a + k)) : a + 8 ≤ C.s.toNat - 256 ∨ C.s.toNat ≤ a :=
  (⟨hf⟩ : Rgn (vsaFoot C.H) a 8).offStack hd (by decide)

/-! ## Store logs as key lists (T). -/

theorem writeLog_nest (m : Mem) (l1 l2 : List WEntry) :
    writeLog (writeLog m l1) l2 = writeLog m (l1 ++ l2) :=
  (writeLog_append m l1 l2).symm

/-- Every key written by the log lies in `P`. -/
def LogIn (P : Nat → Prop) : List WEntry → Prop
  | [] => True
  | e :: L => (∀ b, e.1 ≤ b → b < e.1 + e.2.1 → P b) ∧ LogIn P L

theorem outL_of_logIn {P : Nat → Prop} : ∀ {L : List WEntry}, LogIn P L → ∀ b, ¬ P b → OutL L b
  | [], _, _, _ => trivial
  | _ :: _, ⟨h1, h2⟩, b, hb => ⟨Classical.byContradiction fun hc => hb (h1 b (by omega) (by omega)),
      outL_of_logIn h2 b hb⟩

/-- Frame (L5) through a whole log whose keys lie in the window. -/
theorem frame_log {C : MCtx} {Mt : Mem} {L : List WEntry} (hL : LogIn (MWin C.H C.s) L)
    (hf : ∀ b, ¬ MWin C.H C.s b → Mt[b]? = C.Mt0[b]?) :
    ∀ b, ¬ MWin C.H C.s b → (writeLog Mt L)[b]? = C.Mt0[b]? :=
  fun b hb => by rw [writeLog_out _ _ _ (outL_of_logIn hL b hb), hf b hb]

theorem pres_log {C : MCtx} {Mt : Mem} (L : List WEntry)
    (hp : ∀ b, vsaFoot C.H b → (Mt[b]?).isSome) :
    ∀ b, vsaFoot C.H b → ((writeLog Mt L)[b]?).isSome :=
  fun b hb => writeLog_present _ _ _ (hp b hb)

/-! ## Tactics -/

/-- Address arithmetic on the goal only: normalise register updates and `BitVec`
additions, then `omega` over the facts in context (no hypothesis rewriting). -/
macro "rgn_arith" : tactic =>
  `(tactic| first
    | omega
    | (simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow] ; omega))

/-- Key an access (V5): replace the address term `a` by a fresh `A` with the
defining equation normalised to Nat arithmetic (register updates, register
additions, literal offsets, wrap-around removed when the bound is in context).
Region candidates then compare `A` against region bases by linear arithmetic only. -/
macro "rgn_key " a:term : tactic =>
  `(tactic| (generalize hA : $a = A
             (try simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
               LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
               BitVec.reduceSignExtend, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat,
               Nat.reducePow] at hA)
             (repeat rw [Nat.mod_eq_of_lt (by omega)] at hA)))

/-- Normalise the goal only (register updates, immediates, loads through stores). -/
macro "rgn_norm" : tactic =>
  `(tactic| simp (disch := rgn_arith) only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true,
      ite_false, reduceIte, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.reduceSignExtend, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat,
      VsaIris.Sym.ldv_store_hit, VsaIris.Sym.ldv_ld_hit_eq, VsaIris.Sym.ldv_ld_miss])

/-- Replace loads whose value the context knows (`read64 M a' = some x`) in the goal. -/
macro "rgn_ld " "[" hs:term,* "]" : tactic => do
  let ls ← hs.getElems.mapM fun h => `(Lean.Parser.Tactic.simpLemma| VsaIris.Sym.ldv_at $h)
  `(tactic| simp (disch := rgn_arith) only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true,
      ite_false, VsaIris.Sym.ldv_ld_miss, $ls,*])

open Lean Elab Tactic Meta

/-- A region hypothesis: its name, base and extent. -/
structure RgnHyp where
  name : Name
  base : Expr
  ext : Expr

/-- The regions and ownership contexts in the local context. -/
def rgnScan (g : MVarId) : TacticM (Array Syntax.Term × Array RgnHyp) :=
  g.withContext do
    let mut oks : Array Syntax.Term := #[]
    let mut rgns : Array RgnHyp := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      let fn := ty.getAppFn
      if fn.isConstOf ``Rgn then rgns := rgns.push ⟨d.userName, ty.appFn!.appArg!, ty.appArg!⟩
      else if let .const n _ := fn then
        if n == ``WOK then oks := oks.push (mkIdent d.userName)
        else if (← getEnv).contains (n ++ `toWOK) then
          oks := oks.push (← `(($(mkIdent d.userName)).toWOK))
    return (oks, rgns)

/-- The first-order atoms (local constants other than register files) of `e`,
after replacing each `x.toNat` by the right side of a context equation
`x.toNat = rhs`. -/
def rgnAtoms (g : MVarId) (e : Expr) : MetaM (Array FVarId) := g.withContext do
  let mut eqs : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, r) := ty.eq? then
      if l.isAppOfArity ``BitVec.toNat 2 then eqs := eqs.push (l, r)
  let e' := e.replace fun t => eqs.findSome? fun (l, r) => if l == t then some r else none
  let mut out : Array FVarId := #[]
  for f in (collectFVars {} e').fvarIds do
    let fty ← whnfR (← f.getType)
    unless fty.isForall do out := out.push f
  return out

/-- Key the access `a` of goal `g`, rank the regions (the hinted one first, then
by atoms shared with the key, symbolic extents before literal ones), and try each
region's candidate tactics. Returns the region that closed the goal. -/
def rgnTry (g : MVarId) (a : Expr) (rgns : Array RgnHyp) (hint : Option Name)
    (mk : Syntax.Term → TacticM (Array (TSyntax `tactic))) (extra : Array (TSyntax `tactic)) :
    TacticM (Option Name) := do
  let ka ← rgnAtoms g a
  let mut scored : Array (Int × Name) := #[]
  for r in rgns do
    let kb ← rgnAtoms g r.base
    let shared := (kb.filter ka.contains).size
    let sc : Int := (4 * shared : Int) - (2 * (kb.size - shared) : Nat) +
      (if r.ext.nat?.isNone then 1 else 0) + (if hint == some r.name then 1000 else 0)
    scored := scored.push (sc, r.name)
  let ranked := scored.qsort (fun x y => x.1 > y.1)
  let mut cands : Array (Name × TSyntax `tactic) := extra.map (Name.anonymous, ·)
  for (_, r) in ranked do
    for t in ← mk (mkIdent r) do cands := cands.push (r, t)
  let s0 ← saveState
  let aStx ← g.withContext (Term.exprToSyntax a)
  let [g'] ← evalTacticAt (← `(tactic| rgn_key $aStx)) g | s0.restore; return none
  for (r, t) in cands do
    let s ← saveState
    try
      let gs ← evalTacticAt t g'
      if gs.isEmpty then return some r
      s.restore
    catch _ => s.restore
  s0.restore
  return none

/-- Close an access goal of `g` (`∀ x ∈ accAddrs a w, C.S x`, `LdOK` or `StOK`) from
a region in context. -/
def rgnSide (g : MVarId) (hint : Option Name) : TacticM (Option Name) := do
  let (oks, rgns) ← rgnScan g
  if rgns.isEmpty then return none
  let tgt ← instantiateMVars (← g.getType)
  let some app := tgt.find? fun e =>
      e.isAppOfArity ``accAddrs 2 || e.isAppOfArity ``LdOK 2 || e.isAppOfArity ``StOK 2
    | return none
  let mk : Syntax.Term → TacticM (Array (TSyntax `tactic)) := fun r => do
    if app.isAppOf ``LdOK then
      return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.ldOK $r ?_; omega))]
    else if app.isAppOf ``StOK then
      return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.stOK $r ?_; omega))]
    else
      oks.mapM fun o => `(tactic| (refine VsaIris.VsaHeap.WOK.rgn $o $r ?_; omega))
  rgnTry g app.appFn!.appArg! rgns hint mk #[]

/-- Close an ownership (`∀ x ∈ accAddrs a w, C.S x`), `LdOK` or `StOK` goal
from any region in context. -/
elab "rgn_side" : tactic => do
  let g ← getMainGoal
  match ← rgnSide g none with
  | some _ => setGoals []
  | none => throwError "rgn_side: no region closes the goal"

macro_rules | `(tactic| sx_side) => `(tactic| rgn_side)

/-- Step the `st_<pc>` table from the goal, closing each access obligation with
`rgn_side` and leaving the context untouched. Stops at a listed pc, at a branch,
or at an obligation no region closes (left as a goal); the final goal is
normalised by `rgn_norm`. -/
elab "rgn_run " h:term " at " stops:num+ : tactic => do
  let stopPCs := stops.toList.map (·.getNat)
  let mut cur ← getMainGoal
  let mut pending : List MVarId := []
  repeat
    let some pc ← cur.withContext (do VsaIris.Sym.swpPC? (← cur.getType)) | break
    if stopPCs.contains pc then break
    let some gs ← VsaIris.Sym.sxStep h cur | break
    let mut conts : List MVarId := []
    let mut hint : Option Name := none
    for g in gs do
      let ty ← g.withContext (do instantiateMVars (← g.getType))
      if ← g.withContext (forallTelescopeReducing ty fun _ b => VsaIris.Sym.isSWP b) then
        conts := conts ++ [g]
      else
        match ← rgnSide g hint with
        | some r => hint := some r
        | none => pending := pending ++ [g]
    match conts with
    | [c] => cur := c
    | cs => setGoals (pending ++ cs); return
  let cur' ← evalTacticAt (← `(tactic| try rgn_norm)) cur
  setGoals (pending ++ cur')

/-- Close one `LogIn (MWin H s)` key `∀ b, a ≤ b → b < a + w → MWin H s b`: from a
region in context, or the stack window. -/
elab "rgn_win" : tactic => do
  let g ← getMainGoal
  let (_, rgns) ← rgnScan g
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ _ body _ := tgt | throwError "rgn_win: not a key goal"
  let .forallE _ le _ _ := body | throwError "rgn_win: not a key goal"
  let a := le.appFn!.appArg!
  if a.hasLooseBVars then throwError "rgn_win: not a key goal"
  let stack ← `(tactic| (refine VsaIris.VsaHeap.win_stack' ?_; omega))
  let mk : Syntax.Term → TacticM (Array (TSyntax `tactic)) := fun r => do
    return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.win $r ?_; omega))]
  match ← rgnTry g a rgns none mk #[stack] with
  | some _ => setGoals []
  | none => throwError "rgn_win: no region contains the key"

/-- `open_fields h` adds every field of the named-field structure `h` as a
hypothesis `h_<field>` (projections of constructor terms reduced), so the
arithmetic deciders see a minted region's geometry. -/
elab "open_fields " h:ident : tactic => do
  let g ← getMainGoal
  let n ← g.withContext do
    let d ← getLocalDeclFromUserName h.getId
    let ty ← whnfR (← instantiateMVars d.type)
    let .const n _ := ty.getAppFn | throwError "open_fields: not a structure"
    pure n
  let some info := getStructureInfo? (← getEnv) n | throwError "open_fields: not a structure"
  for f in info.fieldNames do
    let nm := mkIdent (Name.mkSimple s!"{h.getId}_{f}")
    let pj := mkIdent (h.getId ++ f)
    evalTactic (← `(tactic| have $nm := $pj:ident))
    evalTactic (← `(tactic| try simp only at $nm:ident))

/-- Discharge `LogIn (MWin H s) L` for an explicit key list. -/
macro "log_in" : tactic =>
  `(tactic| (simp only [VsaIris.VsaHeap.LogIn, and_true]; repeat' apply And.intro) <;> rgn_win)

end VsaIris.VsaHeap
