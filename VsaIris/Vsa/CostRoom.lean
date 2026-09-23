import VsaIris.Vsa.Malloc
import Vsa.While.CostExists
import Vsa.AllocResource
import Vsa.Sim.NativeNameAudit.ControlHeapAllocator

/-!
# The Room ↔ Cost bridge (INTERP_DESIGN.md §5, package S1)

The total specs index the counted heap regime by COST BYTES:
`evalSpecT_body … D` runs from `heapRes (.counted (k + n))` to
`heapRes (.counted k)`, where `n` is `D`'s cost (`Vsa.While.Cost`). This file
fixes the capacity predicate that makes that index meaningful. It is designed
against the Iris `isHeapRoom`, not against VSA's `AllocationReserve`, which is
unsatisfiable after `malloc(24)` (`vsa_reserve_fails_after_split`,
`split24_vsa_reserve_false`).

## The predicate

`costRoom img H k`: the allocator's `av->top` pointer `top` satisfies
`top + 2k + extendSlack ≤ heapEnd`. It reads only the top word, which is an
allocator global, so it is footprint-local (`roomLocal_cost`). It says nothing
about live blocks: freshness and disjointness are `vsaLayout.Shape`'s job,
which `isHeapRoom` carries beside it. So the live-extent clause that broke
VSA's reserve is absent by construction.

Why `2k`, and why `extendSlack`: every modeled charge `c` covers its request
`n ≤ c` with `16 ≤ c`, and then `physSize n ≤ 2c` (`physSize_le_two_charge`).
A top split advances `top` by `physSize n`; a bin hit leaves it; a free that
merges into top lowers it. `extendSlack` pays for `malloc_extend_top`'s page
rounding when `sbrk` grows the top chunk up to `__heap_end`.

## The three bridges

1. **Boundary.** `DlHeap.InitialAllocatorAt.capacity` is exactly
   `costReserve` at the derivation's cost (`costReserve_of_initial`,
   `costRoom_of_bigStep`).
2. **Per allocation.** `CostTop.spend`: a malloc whose top advance is at most
   `2c` turns `costReserve (c + k)` into `costReserve k`. The per-site charge
   lemmas (`env_new`, closure, name copy, the two array reallocs, stringify,
   the concat buffer) give `n ≤ c` and `16 ≤ c`.
3. **The Iris spec.** `mallocRoomSpec` spends one unit credit. Instantiated at
   `costRoomAt c k` (credit `j` means `j * c + k` bytes), one unit is `c`
   bytes: `isHeapRoom_costAt_one`/`_zero` rewrite its pre and post to
   `isHeapRoom costRoom H (c + k)` and `isHeapRoom costRoom _ k`. The first-order
   obligation is `MallocCostRun`: `MallocRoomRun` at every `costRoomAt c k`
   with `16 ≤ c`, for requests `n ≤ c` (H4; `IrisHoles.alloc`).

Satisfiability: `Control.costReserve` exhibits the reserve with 2^20 credit
bytes at the control heap image, which also inhabits `Loaded interpRunLayout`.
-/

namespace VsaIris.VsaHeap

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst Vsa.While

/-! ## Charges cover requests (pure arithmetic over the cost model) -/

/-- **One modeled charge pays for one chunk, twice over.** A request within a
charge of at least one granule occupies at most twice the charge. -/
theorem physSize_le_two_charge {n c : Nat} (hn : n ≤ c) (hc : 16 ≤ c) :
    physSize n ≤ 2 * c := by
  have := physSize_mono hn
  have : physSize c ≤ 2 * c := by unfold physSize; omega
  omega

theorem roundUp16_ge (n : Nat) : n ≤ roundUp16 n := by unfold roundUp16; omega

theorem roundUp16_granule {n : Nat} (h : 0 < n) : 16 ≤ roundUp16 n := by
  unfold roundUp16; omega

/-- A charge covers its request and is at least one granule. -/
structure Covers (n c : Nat) : Prop where
  request : n ≤ c
  granule : 16 ≤ c

theorem Covers.physSize {n c : Nat} (h : Covers n c) : physSize n ≤ 2 * c :=
  physSize_le_two_charge h.request h.granule

/-- `roundUp16` charges (name copy, stringify, concat buffer) cover any
nonempty request. -/
theorem Covers.roundUp {n : Nat} (h : 0 < n) : Covers n (roundUp16 n) :=
  ⟨roundUp16_ge n, roundUp16_granule h⟩

/-- `env_new`: `malloc(sizeof(Env))` (`env.c:12`). -/
theorem covers_envNew : Covers 32 envBytes := ⟨by decide, by decide⟩

/-- `EX_FN`: `malloc(sizeof(Closure))` (`interp.c:258`). -/
theorem covers_closure : Covers 16 closureBytes := ⟨by decide, by decide⟩

/-- `env_define`: `xmalloc(strlen(name) + 1)` (`env.c:35`). -/
theorem covers_nameCopy (x : String) : Covers (x.length + 1) (nameCopyCost x) :=
  Covers.roundUp (Nat.succ_pos _)

/-- `stringify`: `malloc(len + 1)` (`interp.c:84-106`). -/
theorem covers_stringify (store : Store) (v : Value) :
    Covers ((v.catDisplay store).length + 1) (stringifyCost store v) :=
  Covers.roundUp (Nat.succ_pos _)

/-- The concat buffer `malloc(la + lb + 1)` (`interp.c:118`). -/
theorem covers_concatBuffer (la lb : Nat) : Covers (la + lb + 1) (roundUp16 (la + lb + 1)) :=
  Covers.roundUp (Nat.succ_pos _)

/-- Array growth to `cap ≥ 2` (`env.c:31-32`) charges one `arrayReallocCost`
for two requests; it splits exactly into a names charge `8 * cap` and a vals
charge `24 * cap`, each covering its own `realloc`. -/
theorem arrayRealloc_split {cap : Nat} (h : 2 ≤ cap) :
    arrayReallocCost cap = 8 * cap + 24 * cap ∧ Covers (8 * cap) (8 * cap) ∧
      Covers (24 * cap) (24 * cap) := by
  refine ⟨?_, ⟨Nat.le_refl _, by omega⟩, ⟨Nat.le_refl _, by omega⟩⟩
  unfold arrayReallocCost roundUp16; omega

/-! ## The byte-credit reserve -/

/-- The reserve at a memory, with its top pointer named. -/
structure CostTop (m : Mem) (k top : Nat) : Prop where
  top_pointer : read64 m topAddr = some top
  fits : top + 2 * k + extendSlack ≤ heapEnd

/-- Room for `k` more cost bytes. -/
def CostReserve (m : Mem) (k : Nat) : Prop := ∃ top, CostTop m k top

theorem CostTop.mono {m : Mem} {k k' top : Nat} (h : CostTop m k top) (hle : k' ≤ k) :
    CostTop m k' top := ⟨h.top_pointer, by have := h.fits; omega⟩

/-- **One allocation spends its charge.** Whatever path the allocator took
(top split, bin hit, `sbrk` extension, a free merging into top), if the new
top is at most `2c` above the old, `c` credits are spent. -/
theorem CostTop.spend {m m' : Mem} {c k top top' : Nat} (h : CostTop m (c + k) top)
    (htop : read64 m' topAddr = some top') (hadv : top' ≤ top + 2 * c) :
    CostTop m' k top' := ⟨htop, by have := h.fits; omega⟩

/-- A top split for a request covered by charge `c` advances top by
`physSize n ≤ 2c`. -/
theorem CostTop.split {m m' : Mem} {n c k top : Nat} (h : CostTop m (c + k) top)
    (hcov : Covers n c) (htop : read64 m' topAddr = some (top + physSize n)) :
    CostTop m' k (top + physSize n) :=
  h.spend htop (by have := hcov.physSize; omega)

private theorem top_foot (H : List (Nat × Nat)) : ∀ j, j < 8 → vsaFoot H (topAddr + j) :=
  fun j hj => .inl (.inl ⟨by unfold topAddr avAddr; omega, by unfold topAddr avAddr; omega⟩)

theorem CostReserve.transport_foot {m m' : Mem} {H : List (Nat × Nat)} {k : Nat}
    (h : CostReserve m k) (hag : AgreeP (vsaFoot H) m m') : CostReserve m' k := by
  obtain ⟨top, t⟩ := h
  exact ⟨top, (read64_agreeP hag (top_foot H)).symm.trans t.top_pointer, t.fits⟩

/-! ## The capacity predicate for `isHeapRoom` -/

/-- **The counted regime's capacity**, credits in cost bytes. -/
def costRoom : RoomPred := fun img H k => ∃ m, ImgOn (vsaFoot H) img m ∧ CostReserve m k

theorem roomLocal_cost : RoomLocal vsaLayout costRoom := by
  rintro H img img' k h ⟨m, hm, hr⟩
  exact ⟨m, fun a ha => (hm a ha).trans (by rw [h a ha]), hr⟩

theorem costRoom_mono {img : Nat → BitVec 8} {H : List (Nat × Nat)} {k k' : Nat}
    (h : costRoom img H k) (hle : k' ≤ k) : costRoom img H k' := by
  obtain ⟨m, hm, top, t⟩ := h
  exact ⟨m, hm, top, t.mono hle⟩

/-- The reserve of the owned image holds at any memory carrying it. -/
theorem costReserve_of_room {img : Nat → BitVec 8} {H : List (Nat × Nat)} {k : Nat}
    {m1 : Mem} (hroom : costRoom img H k) (him : ImgOn (vsaFoot H) img m1) :
    CostReserve m1 k := by
  obtain ⟨m, hm, hr⟩ := hroom
  exact hr.transport_foot fun a ha => (hm a ha).trans (him a ha).symm

/-- `isHeapRoom` with byte credits is monotone: dropping credits is free. -/
theorem isHeapRoom_cost_mono {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (H : List (Nat × Nat)) {k k' : Nat} (hle : k' ≤ k) :
    isHeapRoom (GF := GF) vsaLayout costRoom H k ⊢ isHeapRoom vsaLayout costRoom H k' := by
  unfold isHeapRoom
  iintro ⟨%img, %⟨hs, hr⟩, HF⟩
  iexists img
  iframe HF
  ipureintro; exact ⟨hs, costRoom_mono hr hle⟩

/-! ## One unit credit = one charge: `mallocRoomSpec` at byte credits -/

/-- Unit credits scaled to one site's charge `c`, over a base of `k₀` bytes. -/
def costRoomAt (c k₀ : Nat) : RoomPred := fun img H j => costRoom img H (j * c + k₀)

theorem roomLocal_costAt (c k₀ : Nat) : RoomLocal vsaLayout (costRoomAt c k₀) :=
  fun H img img' _ h hr => roomLocal_cost H img img' _ h hr

theorem isHeapRoom_costAt_one {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (c k : Nat) (H : List (Nat × Nat)) :
    isHeapRoom (GF := GF) vsaLayout (costRoomAt c k) H 1 =
      isHeapRoom vsaLayout costRoom H (c + k) := by
  simp only [isHeapRoom, costRoomAt, Nat.one_mul]

theorem isHeapRoom_costAt_zero {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (c k : Nat) (H : List (Nat × Nat)) :
    isHeapRoom (GF := GF) vsaLayout (costRoomAt c k) H 0 =
      isHeapRoom vsaLayout costRoom H k := by
  simp only [isHeapRoom, costRoomAt, Nat.zero_mul, Nat.zero_add]

/-- **`_malloc_r` under byte credits, first-order** (H4's obligation,
`IrisHoles.alloc`): at every charge `c ≥ 16`, a request `n ≤ c` from a heap
with `c + k` credit bytes returns a fresh block and leaves `k`. It is
`MallocRoomRun` at `costRoomAt c k`, so it includes the `sbrk` extension path
whenever the top chunk is below `physSize n`. -/
def MallocCostRun (M : MachineModel) (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64)
    (clob savedRegs : List Nat) (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop :=
  ∀ c k, 16 ≤ c → MallocRoomRun M vsaLayout (costRoomAt c k) c SpOK entry gpv clob savedRegs
    headroom text

/-- **The malloc spec a total case lemma consumes at an allocation site with
charge `c`**: from `isHeapRoom costRoom H (c + k)`, a fresh block and
`isHeapRoom costRoom ((p, n) :: H) k` (after `isHeapRoom_costAt_one`/`_zero`). -/
theorem mallocCostSpec {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    {M : MachineModel} (Wp : MachWP (GF := GF) M)
    {SpOK : BitVec 64 → Prop} {entry gpv : BitVec 64}
    {clob savedRegs : List Nat} {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hrun : MallocCostRun M SpOK entry gpv clob savedRegs headroom text)
    (hnd : (allocRegs clob savedRegs).Nodup)
    (H : List (Nat × Nat)) (n s : BitVec 64) (c k : Nat) (saved : List (Nat × BitVec 64))
    (hsv : saved.map Prod.fst = savedRegs) (hc : 16 ≤ c) (hn : n.toNat ≤ c) :
    textOwn (GF := GF) text ⊢
      mallocRoomSpec Wp vsaLayout (costRoomAt c k) SpOK entry gpv clob saved headroom H n s 0 :=
  mallocRoomSpec_of_run Wp (hrun c k hc) shapeLocal_vsaLayout (roomLocal_costAt c k) hnd
    H n s 0 saved hsv hn

/-! ## The boundary: capacity is the reserve at the derivation's cost -/

/-- `InitialAllocatorAt.capacity` at a costed whole-program derivation. -/
theorem costReserve_of_initial {m : Mem} {exts : List (Nat × Nat)}
    {reallocs : Nat × Nat → Prop} {stmts count top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat}
    (hA : InitialAllocatorAt m exts reallocs stmts count top brkv chunks bins)
    {p : Program} (hp : ProgramRepr m stmts count p) {st' : St} {n : Nat}
    (hn : ExecSeqCost initSt 0 0 p st' .normal n) : CostTop m n top := by
  refine ⟨hA.heap.top_ptr, ?_⟩
  have := hA.capacity p hp st' n hn
  have : 0 < extendSlack := by decide
  omega

/-- **The counted regime's start** (A0): a big-step behaviour of the loaded
program has a costed derivation whose cost is covered by the boundary heap. -/
theorem costRoom_of_bigStep {m : Mem} {exts : List (Nat × Nat)}
    {reallocs : Nat × Nat → Prop} {stmts count : Nat}
    (hA : InitialAllocator m exts reallocs stmts count)
    {p : Program} (hp : ProgramRepr m stmts count p) {out : String} (hb : BigStep p out)
    {img : Nat → BitVec 8} {H : List (Nat × Nat)} (him : ImgOn (vsaFoot H) img m) :
    ∃ st' n, ExecSeqCost initSt 0 0 p st' .normal n ∧ st'.out = out ∧ costRoom img H n := by
  obtain ⟨st', n, hn, hout⟩ := BigStep.cost hb
  obtain ⟨top, brkv, chunks, bins, hA⟩ := hA
  exact ⟨st', n, hn, hout, m, him, top, costReserve_of_initial hA hp hn⟩

/-! ## Satisfiability at the control heap -/

namespace Control

open Vsa.Sim.NativeNameAudit.Control

/-- The control heap image (`NativeNameAudit.Control.heapMem`, whose
configuration inhabits `Loaded interpRunLayout`) carries 2^20 credit bytes. -/
theorem costReserve : CostReserve heapMem (2 ^ 20) :=
  ⟨heapTop, heapAt.top_ptr, by unfold heapTop extendSlack heapEnd; decide⟩

end Control

#print axioms physSize_le_two_charge
#print axioms arrayRealloc_split
#print axioms CostTop.split
#print axioms roomLocal_cost
#print axioms isHeapRoom_cost_mono
#print axioms isHeapRoom_costAt_one
#print axioms mallocCostSpec
#print axioms costRoom_of_bigStep
#print axioms Control.costReserve

end VsaIris.VsaHeap
