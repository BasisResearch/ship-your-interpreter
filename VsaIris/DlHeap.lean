import VsaIris.Call

/-!
# The dlmalloc heap as a separation-logic resource

Port of xv6iris `iris/KallocInv.v` (the logical allocator layer) and
`iris/SpecKalloc.v` / `iris/SpecKfree.v` (the caller-facing specs), from
xv6's page free list to newlib's dlmalloc (VSA `Vsa/Sim/DlHeap.lean`).

MachCSL's design, kept:
* the allocator's protected resource owns its global state *and every byte
  that is not handed out*: `kmem_res` (KallocInv.v:394) is the free-list head
  word plus `freelist_chain` over every free page (KallocInv.v:281). Here
  `isHeap L H` owns the allocator globals plus every arena byte outside the
  live extents `H`, with a pure shape predicate over the owned bytes (VSA's
  `HeapAt`, the analogue of `freelist_chain`'s pointer structure);
* allocation hands out ownership of the block, "a standard CSL encoding of
  memory allocation" (paper §6.5): `kalloc_post` (KallocInv.v:436) is null
  or `page_filled r …`; `mallocPost` is null or `blockOwn p n`;
* freeing takes the block's bytes back at ANY value: `kfree_pre p :=
  page_valid p ∗ page_own p` (KallocInv.v:444), `page_own` being 4096
  `byte_any` cells (KallocInv.v:149-159, the A6.87 ruling in the comment
  there). `freePre p n := blockOwn p n` is the same with `n` bytes;
* the specs are continuation-style WPs over the loop (SpecKalloc.v:30-56),
  here `fnSpec`, and unproved callees are parameters of a module type
  (`Module Type KALLOC`, SpecKalloc.v:52): `DlMallocImpl` below.

What changes, and why (DESIGN.md §"Deviations"):
* no lock: VSA is sequential, so `isHeap` is an exclusive resource threaded
  through the interpreter, like MachCSL's boot-mode `kalloc_avail (Some n)`,
  not `is_lock γ lk "kmem" …`;
* no page count ghost (`kmem_avail_auth`, KallocInv.v:321): VSA's
  per-program capacity bound (`InitialAllocatorAt.capacity`) plays that
  role and stays a pure fact;
* ownership of a byte SET rather than a fixed-length big-sep: dlmalloc's
  free bytes are a state-dependent set, not a list of 4096-byte pages.

**How this removes the malloc frame obstruction** (commit eb73d8c,
`PROOF_CLOSURE_PLAN.md` §2): VSA's `MallocContract` framed malloc by a
state-independent `privFoot` that had to contain every byte malloc may write
and avoid every live payload. `isHeap L H` owns `heapFoot L H`, which is
*relative to the current live extents*: malloc may write any byte it owns,
and the bytes it owns change as blocks are carved out and returned. The
caller's bytes survive because the caller owns them and malloc does not:
that is the frame rule, not a per-contract footprint clause. See
`eb73d8c_witness` at the bottom for the concrete case.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

open Classical

/-! ## Owning a set of bytes -/

section OwnSet

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `byte_any` (KallocInv.v:149): the byte is owned, its value is not
promised. -/
abbrev byteAny (a : Nat) : IProp GF := iprop(∃ b, a ↦ₘ b)

/-- Ownership of every byte of a (finite) set, each carrying `Φ`. -/
def ownSet (S : Nat → Prop) (Φ : Nat → IProp GF) : IProp GF :=
  iprop(∃ l : List Nat, ⌜l.Nodup ∧ ∀ a, a ∈ l ↔ S a⌝ ∗ sepL l Φ)

theorem sepL_append {α} (l₁ l₂ : List α) (Φ : α → IProp GF) :
    sepL (l₁ ++ l₂) Φ ⊣⊢ sepL l₁ Φ ∗ sepL l₂ Φ := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, sepL_nil]
    exact emp_sep.symm
  | cons x xs ih =>
    simp only [List.cons_append, sepL_cons]
    exact (sep_congr_right ih).trans sep_assoc.symm

theorem sepL_filter {α} (l : List α) (q : α → Bool) (Φ : α → IProp GF) :
    sepL l Φ ⊣⊢ sepL (l.filter q) Φ ∗ sepL (l.filter (fun a => !q a)) Φ := by
  induction l with
  | nil => simp only [List.filter_nil, sepL_nil]; exact emp_sep.symm
  | cons x xs ih =>
    rw [List.filter_cons, List.filter_cons]
    cases hq : q x
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, sepL_cons]
      refine (sep_congr_right ih).trans ?_
      exact sep_assoc.symm.trans ((sep_congr_left sep_comm).trans sep_assoc)
    · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, sepL_cons]
      exact (sep_congr_right ih).trans sep_assoc.symm

theorem sepL_mono {α} (l : List α) (Φ Ψ : α → IProp GF) (h : ∀ a, Φ a ⊢ Ψ a) :
    sepL l Φ ⊢ sepL l Ψ := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih => exact sep_mono (h x) ih

/-- Relabel the set. -/
theorem ownSet_iff {S T : Nat → Prop} (Φ : Nat → IProp GF) (h : ∀ a, S a ↔ T a) :
    ownSet S Φ ⊢ ownSet T Φ := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  iexists l
  iframe Hl
  ipureintro
  exact ⟨hnd, fun a => (hmem a).trans (h a)⟩

theorem ownSet_mono {S : Nat → Prop} (Φ Ψ : Nat → IProp GF) (h : ∀ a, Φ a ⊢ Ψ a) :
    ownSet S Φ ⊢ ownSet S Ψ := by
  unfold ownSet
  iintro ⟨%l, %hl, Hl⟩
  iexists l
  isplitr
  · ipureintro; exact hl
  iapply sepL_mono l Φ Ψ h $$ Hl

/-- **Carving.** Owning `S` is owning its `B` part and the rest. This is the
set-level content of `kmem_res`'s pop and push (KallocInv.v:403-434). -/
theorem ownSet_split (S B : Nat → Prop) (Φ : Nat → IProp GF) :
    ownSet S Φ ⊢ ownSet (fun a => S a ∧ B a) Φ ∗ ownSet (fun a => S a ∧ ¬ B a) Φ := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  ihave ⟨H1, H2⟩ := (sepL_filter l (fun a => decide (B a)) Φ).1 $$ Hl
  isplitl [H1]
  · iexists (l.filter (fun a => decide (B a)))
    iframe H1
    ipureintro
    refine ⟨hnd.filter _, fun a => ?_⟩
    simp [List.mem_filter, hmem]
  · iexists (l.filter (fun a => !decide (B a)))
    iframe H2
    ipureintro
    refine ⟨hnd.filter _, fun a => ?_⟩
    simp [List.mem_filter, hmem]

/-- Joining two disjoint owned sets. -/
theorem ownSet_join (S T : Nat → Prop) (Φ : Nat → IProp GF) (hdisj : ∀ a, S a → ¬ T a) :
    ownSet S Φ ∗ ownSet T Φ ⊢ ownSet (fun a => S a ∨ T a) Φ := by
  unfold ownSet
  iintro ⟨⟨%l₁, %⟨hnd₁, hmem₁⟩, H1⟩, ⟨%l₂, %⟨hnd₂, hmem₂⟩, H2⟩⟩
  iexists (l₁ ++ l₂)
  isplitr
  · ipureintro
    refine ⟨List.nodup_append.2 ⟨hnd₁, hnd₂, fun a ha b hb hab => ?_⟩, fun a => ?_⟩
    · subst hab; exact hdisj a ((hmem₁ a).1 ha) ((hmem₂ a).1 hb)
    · simp [List.mem_append, hmem₁, hmem₂]
  iapply (sepL_append l₁ l₂ Φ).2
  iframe H1 H2

/-- Two exclusively owned bytes are distinct (`ghost_map_elem_ne`). -/
theorem byteAny_ne (a a' : Nat) : byteAny (GF := GF) a ∗ byteAny a' ⊢ ⌜a ≠ a'⌝ := by
  iintro ⟨⟨%b, Ha⟩, ⟨%b', Ha'⟩⟩
  iapply mem_ne a a' _ b b' $$ Ha Ha'

/-- A byte the caller owns is not in any set of bytes someone else owns.
This single lemma is what VSA derives by hand, per call site, as
`HeapOwned.ownedOff`/`entryOff` (`Vsa/Sim/AllocOff.lean`) from the ledger
and `privFoot_disjoint`. -/
theorem owned_off (a : Nat) (v : BitVec 8) (S : Nat → Prop) :
    (a ↦ₘ v) ⊢@{IProp GF} ownSet S byteAny -∗ ⌜¬ S a⌝ := by
  unfold ownSet
  iintro Ha ⟨%l, %⟨_, hmem⟩, Hl⟩
  suffices h : ∀ l : List Nat, (a ↦ₘ v) ⊢@{IProp GF} sepL l byteAny -∗ ⌜a ∉ l⌝ by
    ihave %hn := h l $$ Ha Hl
    ipureintro
    exact fun hs => hn ((hmem a).2 hs)
  intro l
  induction l with
  | nil => iintro _ _; ipureintro; exact List.not_mem_nil
  | cons x xs ih =>
    rw [sepL_cons]
    iintro Ha ⟨⟨%b, Hx⟩, Hxs⟩
    ihave %hx := mem_ne a x _ v b $$ Ha Hx
    ihave %hxs := ih $$ Ha Hxs
    ipureintro
    simp [List.mem_cons, hx, hxs]

end OwnSet

/-! ## The heap resource -/

/-- What VSA's `Vsa/Sim/DlHeap.lean` and `Vsa/Alloc.lean` fix about the
binary's dlmalloc, abstracted so this file builds without VSA. -/
structure DlLayout where
  /-- `AllocGlobalByte` (`Vsa/Alloc.lean:66`): `__malloc_av_`, `brk.0`, … -/
  global : Nat → Prop
  /-- `_end` (`DlHeap.heapStart`). -/
  lo : Nat
  /-- `__heap_end` (`DlHeap.heapEnd`). -/
  hi : Nat
  /-- The globals lie in `.data`/`.bss`, outside the arena
  (`AllocGlobalByte.bounds`). -/
  global_off_arena : ∀ a, global a → a < lo ∨ hi ≤ a
  /-- `HeapAt` (`DlHeap.lean:95`): the chunk walk, bins and top, read off
  the bytes the allocator owns, with `H` the live extents. The analogue of
  `freelist_chain`'s pointer structure (KallocInv.v:281). -/
  Shape : (Nat → BitVec 8) → List (Nat × Nat) → Prop

/-- Byte `a` lies in extent `e = (start, len)`. -/
def InExt (e : Nat × Nat) (a : Nat) : Prop := e.1 ≤ a ∧ a < e.1 + e.2

/-- **The allocator's footprint**, relative to the live extents: its globals
and every arena byte that is not inside a live block. Chunk headers, footers,
bin links and the top chunk all live here, wherever the current state puts
them. -/
def heapFoot (L : DlLayout) (H : List (Nat × Nat)) (a : Nat) : Prop :=
  L.global a ∨ (L.lo ≤ a ∧ a < L.hi ∧ ∀ e ∈ H, ¬ InExt e a)

/-- A block malloc may return while `H` is live: non-null, in the arena, and
disjoint from every live extent (VSA `MallocContract.spec`'s success arm:
`p ≠ 0 ∧ A.contains p n ∧ ∀ e ∈ exts, ExtDisjoint (p, n) e`). -/
def FreshBlock (L : DlLayout) (H : List (Nat × Nat)) (p n : Nat) : Prop :=
  p ≠ 0 ∧ L.lo ≤ p ∧ p + n ≤ L.hi ∧ ∀ e ∈ H, ∀ a, InExt (p, n) a → ¬ InExt e a

section Heap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `kmem_res` (KallocInv.v:394) for dlmalloc: some byte image satisfying
the heap shape, and ownership of every byte of the footprint at that image. -/
def isHeap (L : DlLayout) (H : List (Nat × Nat)) : IProp GF :=
  iprop(∃ img : Nat → BitVec 8, ⌜L.Shape img H⌝ ∗
    ownSet (heapFoot L H) (fun a => a ↦ₘ img a))

/-- `page_own` (KallocInv.v:159) for an `n`-byte block. -/
def blockOwn (p n : Nat) : IProp GF := ownSet (InExt (p, n)) byteAny

theorem ownSet_forget (S : Nat → Prop) (img : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ img a) ⊢ ownSet S byteAny :=
  ownSet_mono _ _ (fun a => by iintro H; iexists img a; iexact H)

/-- **Carve** a fresh block out of the allocator's footprint, for any per-byte
resource `Φ` (byte ownership at any value, or at the image's values). -/
theorem heapFoot_carve_gen (L : DlLayout) (H : List (Nat × Nat)) (p n : Nat)
    (hf : FreshBlock L H p n) (Φ : Nat → IProp GF) :
    ownSet (GF := GF) (heapFoot L H) Φ ⊢
      ownSet (heapFoot L ((p, n) :: H)) Φ ∗ ownSet (InExt (p, n)) Φ := by
  obtain ⟨_, hlo, hhi, hdisj⟩ := hf
  iintro Hh
  ihave ⟨Hb, Hr⟩ := ownSet_split (heapFoot L H) (InExt (p, n)) Φ $$ Hh
  isplitl [Hr]
  · iapply ownSet_iff Φ _ $$ Hr
    intro a
    unfold heapFoot InExt
    constructor
    · rintro ⟨hg | ⟨h1, h2, h3⟩, hn⟩
      · exact .inl hg
      · refine .inr ⟨h1, h2, fun e he => ?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact hn
        · exact h3 e he
    · rintro (hg | ⟨h1, h2, h3⟩)
      · refine ⟨.inl hg, fun ⟨hp1, hp2⟩ => ?_⟩
        rcases L.global_off_arena a hg with h | h <;> simp at hp1 hp2 <;> omega
      · exact ⟨.inr ⟨h1, h2, fun e he => h3 e (List.mem_cons_of_mem _ he)⟩,
          h3 (p, n) List.mem_cons_self⟩
  · iapply ownSet_iff Φ _ $$ Hb
    intro a
    constructor
    · exact fun h => h.2
    · intro ha
      refine ⟨.inr ⟨?_, ?_, fun e he => hdisj e he a ha⟩, ha⟩
      · unfold InExt at ha; simp at ha; omega
      · unfold InExt at ha; simp at ha; omega

/-- **Carve** a fresh block out of the allocator's footprint: what the malloc
proof does at its return (KallocInv.v "kalloc's logical core", the pop). -/
theorem heapFoot_carve (L : DlLayout) (H : List (Nat × Nat)) (p n : Nat)
    (hf : FreshBlock L H p n) :
    ownSet (GF := GF) (heapFoot L H) byteAny ⊢
      ownSet (heapFoot L ((p, n) :: H)) byteAny ∗ blockOwn p n :=
  heapFoot_carve_gen L H p n hf byteAny

/-- **Return** a block to the footprint: what the free proof does (the
push, `kmem_res_push`, KallocInv.v:417). -/
theorem heapFoot_return (L : DlLayout) (H : List (Nat × Nat)) (p n : Nat)
    (hf : FreshBlock L H p n) :
    ownSet (GF := GF) (heapFoot L ((p, n) :: H)) byteAny ∗ blockOwn p n ⊢
      ownSet (heapFoot L H) byteAny := by
  obtain ⟨_, hlo, hhi, hdisj⟩ := hf
  have hsep : ∀ a, heapFoot L ((p, n) :: H) a → ¬ InExt (p, n) a := by
    intro a ha hb
    rcases ha with hg | ⟨_, _, h3⟩
    · rcases L.global_off_arena a hg with h | h <;> unfold InExt at hb <;> simp at hb <;> omega
    · exact h3 (p, n) List.mem_cons_self hb
  unfold blockOwn
  iintro Hh
  ihave Hj := ownSet_join (heapFoot L ((p, n) :: H)) (InExt (p, n)) byteAny hsep $$ Hh
  iapply ownSet_iff byteAny _ $$ Hj
  intro a
  unfold heapFoot
  constructor
  · rintro ((hg | ⟨h1, h2, h3⟩) | hb)
    · exact .inl hg
    · exact .inr ⟨h1, h2, fun e he => h3 e (List.mem_cons_of_mem _ he)⟩
    · refine .inr ⟨?_, ?_, fun e he => hdisj e he a hb⟩
      · unfold InExt at hb; simp at hb; omega
      · unfold InExt at hb; simp at hb; omega
  · rintro (hg | ⟨h1, h2, h3⟩)
    · exact .inl (.inl hg)
    · by_cases hb : InExt (p, n) a
      · exact .inr hb
      · refine .inl (.inr ⟨h1, h2, fun e he => ?_⟩)
        rcases List.mem_cons.mp he with rfl | he
        · exact hb
        · exact h3 e he

/-- A byte the caller owns is outside the allocator's footprint. -/
theorem owned_off_heap (L : DlLayout) (H : List (Nat × Nat)) (a : Nat) (v : BitVec 8) :
    (a ↦ₘ v) ⊢@{IProp GF} isHeap L H -∗ ⌜¬ heapFoot L H a⌝ := by
  unfold isHeap
  iintro Ha ⟨%img, -, Hh⟩
  ihave Hh := ownSet_forget _ img $$ Hh
  iapply owned_off a v _ $$ Ha Hh

/-- A byte the caller owns is outside any block handed to someone else. -/
theorem owned_off_block (p n a : Nat) (v : BitVec 8) :
    (a ↦ₘ v) ⊢@{IProp GF} blockOwn p n -∗ ⌜¬ InExt (p, n) a⌝ :=
  owned_off a v _

/-! ## The specs (SpecKalloc.v / SpecKfree.v) -/

def gp : Nat := 3

/-- Registers a callee may clobber, owned at any value. MachCSL threads the
whole register file (`gpr_file`, execution-model.md "Registers & the
register file") and states callee-saved preservation as
`⌜callee_saved m mr⌝`; with per-register points-to the callee-saved ones are
simply not handed over. -/
def clobbered (rs : List Nat) : IProp GF := sepL rs (fun r => iprop(∃ v, r ↦ᵣ v))

/-- Callee-saved registers the callee uses and restores: handed over at their
values and handed back at the same values. A callee that spills a register
(`_malloc_r` runs `sd s0,80(sp); mv s0,a0`) must own it during the call,
because the state interpretation agrees with the machine at every step. -/
def savedOwn (saved : List (Nat × BitVec 64)) : IProp GF := sepL saved (fun p => p.1 ↦ᵣ p.2)

/-- The callee's code bytes, persistent (MachCSL's `text_pointsto … □`). A
closed spec `⊢ fnSpec …` cannot be proved for real code without them: from
emp, the bytes at the entry are unconstrained. -/
def textOwn (text : List (Nat × BitVec 8)) : IProp GF := sepL text (fun p => p.1 ↦ₘ□ p.2)

instance (text : List (Nat × BitVec 8)) : Persistent (textOwn (GF := GF) text) := by
  unfold textOwn; infer_instance

/-- The stack bytes below `sp` a callee may use (VSA `StackOK SL sp
headroom`). An owned resource, handed to the callee and back, instead of the
"stack window below the entry sp" exception in `MallocContract`'s frame. -/
def stackScratch (s : BitVec 64) (headroom : Nat) : IProp GF :=
  blockOwn (s.toNat - headroom) headroom

/-- `kalloc_post` (KallocInv.v:436): null with the heap unchanged, or a fresh
aligned block with its ownership and the extended live list. -/
def mallocPost (L : DlLayout) (H : List (Nat × Nat)) (n : Nat) (p : BitVec 64) : IProp GF :=
  iprop((⌜p = 0⌝ ∗ isHeap L H) ∨
    (⌜FreshBlock L H p.toNat n ∧ p.toNat % 16 = 0⌝ ∗
      isHeap L ((p.toNat, n) :: H) ∗ blockOwn p.toNat n))

variable (M : MachineModel)

/-- `wp_kalloc_sconf_body` (SpecKalloc.v:30), sequential: -/
def mallocSpec (L : DlLayout) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat)
    (H : List (Nat × Nat)) (n s : BitVec 64) : IProp GF :=
  fnSpec (M := M) entry
    (fun _ => iprop(a0 ↦ᵣ n ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeap L H))
    (fun _ => iprop(∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ mallocPost L H n.toNat p))

/-- `wp_kfree_sconf_body` (SpecKfree.v:30): `kfree_pre p := page_own p`
(KallocInv.v:444), the block at any contents. -/
def freeSpec (L : DlLayout) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat)
    (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) : IProp GF :=
  fnSpec (M := M) entry
    (fun _ => iprop(a0 ↦ᵣ q ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeap L ((q.toNat, n) :: H) ∗ blockOwn q.toNat n))
    (fun _ => iprop(sp ↦ᵣ s ∗ (∃ v, a0 ↦ᵣ v) ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeap L H))

end Heap

/-- **The allocator as a module parameter**, as MachCSL leaves an unproved
callee (`Module Type KALLOC`, SpecKalloc.v:52; `LinkKalloc.v` instantiates
it with `ProofKalloc`). This is VSA's `MallocContract` restated: the one
assumption about the binary's dlmalloc. It is NOT proved here; discharging
it is the instruction-level proof of `_malloc_r`/`_free_r` against the Sail
model (MachCSL's ProofKalloc.v is 834 lines for xv6's much simpler kalloc).
The difference from `MallocContract` is that this statement can be true of
dlmalloc; see `eb73d8c_witness`. `text` is the allocator's code (owned
persistently by the caller's context) and `savedRegs` the callee-saved
registers it spills and restores. `VsaIris.dlMallocImpl_of_localRuns`
(`LocalRun.lean`, `MallocRun.lean`) builds this structure from first-order
facts about the machine's steps. -/
structure DlMallocImpl (M : MachineModel) (L : DlLayout) (mallocEntry freeEntry gpv : BitVec 64)
    (clob savedRegs : List Nat) (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop where
  malloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] H n s
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs →
    textOwn (GF := GF) text ⊢ mallocSpec M L mallocEntry gpv clob saved headroom H n s
  free : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] H q n s
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs →
    textOwn (GF := GF) text ⊢ freeSpec M L freeEntry gpv clob saved headroom H q n s

section Client

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- **Calling malloc with an arbitrary frame.** Whatever `R` the caller owns
(its store, its AST bytes, other live blocks, saved registers) comes back
unchanged in the continuation. Nothing about `R` appears in malloc's spec:
this is VSA's `HeapOwned.transport_off`/`.repr_off` and the whole
`privFoot` clause, as one application of the frame rule. -/
theorem wp_call_malloc {Φ : Nat × String → IProp GF} {L : DlLayout}
    {mallocEntry freeEntry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (impl : DlMallocImpl M L mallocEntry freeEntry gpv clob savedRegs headroom text)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec M i code mallocEntry)
    (H : List (Nat × Nat)) (v n s : BitVec 64) (saved : List (Nat × BitVec 64))
    (hsaved : saved.map Prod.fst = savedRegs) (R : IProp GF) :
    instrAt (GF := GF) i code ∗ textOwn text ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ a0 ↦ᵣ n ∗
      sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗ stackScratch s headroom ∗
      isHeap L H ∗ R ∗
      (∀ p, PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ a0 ↦ᵣ p -∗
        sp ↦ᵣ s -∗ clobbered clob -∗ savedOwn saved -∗ stackScratch s headroom -∗
        mallocPost L H n.toNat p -∗ R -∗ mTWP M Φ)
    ⊢ mTWP M Φ := by
  have hs := impl.malloc (GF := GF) H n s saved hsaved
  unfold mallocSpec at hs
  iintro ⟨#Hi, #Htext, Hpc, Hra, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, Hheap, HR, Hk⟩
  ihave #Hspec := hs $$ Htext
  iapply wp_call (M := M) hexec
  iframe Hi Hspec Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk Hheap
  iintro Hpc Hra ⟨%p, Ha0, Hsp, Hclob, Hsv, Hstk, Hpost⟩
  iapply Hk $$ %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk Hpost HR

/-- The caller's byte `a` survives a malloc call *with its value*, and it is
disjoint from both the returned block and the allocator's new footprint. -/
theorem wp_call_malloc_keeps {Φ : Nat × String → IProp GF} {L : DlLayout}
    {mallocEntry freeEntry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (impl : DlMallocImpl M L mallocEntry freeEntry gpv clob savedRegs headroom text)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec M i code mallocEntry)
    (H : List (Nat × Nat)) (v n s : BitVec 64) (saved : List (Nat × BitVec 64))
    (hsaved : saved.map Prod.fst = savedRegs) (a : Nat) (b : BitVec 8) :
    instrAt (GF := GF) i code ∗ textOwn text ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ a0 ↦ᵣ n ∗
      sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗ stackScratch s headroom ∗
      isHeap L H ∗ a ↦ₘ b ∗
      (∀ p, PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ a0 ↦ᵣ p -∗
        sp ↦ᵣ s -∗ clobbered clob -∗ savedOwn saved -∗ stackScratch s headroom -∗
        mallocPost L H n.toNat p -∗ a ↦ₘ b -∗
        ⌜p ≠ 0 → ¬ InExt (p.toNat, n.toNat) a ∧ ¬ heapFoot L ((p.toNat, n.toNat) :: H) a⌝ -∗
        mTWP M Φ)
    ⊢ mTWP M Φ := by
  iintro ⟨Hi, Htext, Hpc, Hra, Ha0, Hsp, Hgp, Hclob, Hsv, Hstk, Hheap, Hab, Hk⟩
  iapply wp_call_malloc impl hexec H v n s saved hsaved (a ↦ₘ b)
  iframe Hi Htext Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk Hheap Hab
  unfold mallocPost
  iintro %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk Hpost Hab
  icases Hpost with (⟨%hp, Hheap⟩ | ⟨%hf, Hheap, Hblk⟩)
  · iapply Hk $$ %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk [Hheap] Hab
    · ileft; iframe Hheap; ipureintro; exact hp
    ipureintro
    intro hne; exact absurd hp hne
  · ihave %hb := owned_off_block p.toNat n.toNat a b $$ Hab Hblk
    ihave %hh := owned_off_heap L ((p.toNat, n.toNat) :: H) a b $$ Hab Hheap
    iapply Hk $$ %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk [Hheap Hblk] Hab
    · iright; iframe Hheap Hblk; ipureintro; exact hf
    ipureintro
    intro _; exact ⟨hb, hh⟩

end Client

/-! ## The eb73d8c witness

`PROOF_CLOSURE_PLAN.md` §2 (commit eb73d8c): on the admitted control heap
(top chunk at `0x82000200`), `malloc(32)` writes the new top header at
`0x82000238`, while `malloc(64)` from the same state returns
`[0x82000210, 0x82000250)`, which contains it. -/

/-- No state-independent footprint can frame both calls. This is the
obstruction to `MallocContract.privFoot`, stated and proved. -/
theorem no_fixed_privFoot (H0 : List (Nat × Nat)) :
    ¬ ∃ F : Nat → Prop, F 0x82000238 ∧
      ∀ H ∈ [H0, (0x82000210, 64) :: H0], ∀ e ∈ H, ∀ a, InExt e a → ¬ F a := by
  rintro ⟨F, hw, hlive⟩
  exact hlive ((0x82000210, 64) :: H0) (by simp) (0x82000210, 64) List.mem_cons_self
    0x82000238 (by unfold InExt; decide) hw

/-- The live-relative footprint handles both: before the call the allocator
owns `0x82000238` (so `malloc(32)` may write it); `malloc(64)`'s block is
fresh and contains it; after that call the byte has moved to the caller with
the block and the allocator no longer owns it. -/
theorem eb73d8c_witness (L : DlLayout) (hlo : L.lo = 0x8001c170) (hhi : L.hi = 0x87800000)
    (H0 : List (Nat × Nat)) (hH0 : ∀ e ∈ H0, e.1 + e.2 ≤ 0x82000200) :
    heapFoot L H0 0x82000238 ∧
    FreshBlock L H0 0x82000210 64 ∧
    InExt (0x82000210, 64) 0x82000238 ∧
    ¬ heapFoot L ((0x82000210, 64) :: H0) 0x82000238 := by
  refine ⟨.inr ⟨by omega, by omega, fun e he h => ?_⟩, ⟨by decide, by omega, by omega, ?_⟩,
    by unfold InExt; decide, ?_⟩
  · have := hH0 e he; unfold InExt at h; omega
  · intro e he a ha h
    have := hH0 e he; unfold InExt at ha h; simp at ha; omega
  · rintro (hg | ⟨_, _, h⟩)
    · rcases L.global_off_arena _ hg with h | h <;> omega
    · exact h (0x82000210, 64) List.mem_cons_self (by unfold InExt; decide)

end VsaIris
