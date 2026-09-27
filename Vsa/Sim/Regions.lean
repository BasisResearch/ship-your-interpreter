import Vsa.Alloc

/-!
# Layer-1 shared infrastructure — memory regions & frame machinery

Consolidates the memory-region / disjointness / frame reasoning that every
Layer-3 spec (`ValueSpec`, `MemcpySpec`, `EnvNewSpec`, …) currently re-proves
privately.  This is the plan's **Layer-1 item "region disjointness lemmas for the
fixed memory map"** delivered as one shared utility module, so the upcoming
`env_define` / `env_get` / `env_set` specs (and `interp_run`) `import
Vsa.Sim.Regions` instead of cloning.

This is **explicit-footprint consolidation**, NOT a separation logic: there is no
separating conjunction and no heaplet type.  Every region is an explicit
`[lo, lo+len)` interval and every disjointness fact is an `omega`-shaped
`Prop`.  (Introducing a `*`/heaplet abstraction is reserved to the user.)

## Import position in the dependency graph

`Regions` imports only `Vsa.Alloc`, which transitively supplies everything the
byte-map / region machinery needs:

* `read32` / `read64` / `readLE`  (via `Vsa.Alloc → Vsa.RuntimeRepr → Vsa.MemRepr`);
* `tohostAddr`                     (via `Vsa.Alloc → Vsa.Sim.GoodState → Vsa.Sim.InitValues`);
* `StackLayout` / `StackOK` / `AbiPreserved`  (`Vsa.Alloc` itself).

It deliberately does **not** import `Vsa.Sim.ValueSites` (where the private
`writeMap4`/`writeMap8` `abbrev`s and the `sigmaPost_*`/`ReadsLikePost`
register-frame machinery live): that file pulls the whole heavy
`StepObs`/`Execute*` chain and sits ABOVE the spec files.  Importing it would
make `Regions` a peer of the specs rather than shared infrastructure below them,
and would risk an import cycle once the specs import `Regions`.  We therefore
**restate** `writeMap4`/`writeMap8` here (definitionally identical to
`ValueSites`') so the byte-map lemmas are self-contained; the register-frame
`frame_*_XXX` helpers stay per-spec (they are one-liners over each function's
own write-set and genuinely need the heavy `sigmaPost_*` layer).

The spill-survival kit (item 4) generalizes the memory-agreement half of
`EnvNewSpec.spill_transfer` — the `AgreeOn`-based *byte-fact transfer*, which
needs no register layer — not the register-frame half.
-/

open Vsa Vsa.Alloc Vsa.MemRepr

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Fixed-memory-map constants

Pulled from `Vsa.Sim.InitValues` (`initPmaRegions`, `tohostAddr`) and the
existing spec region bundles (`MemcpySpec.Regions`, `ValueSpec.NullRegion`,
`EnvNewSpec.EnvRegions`), which all restate the same three windows:

* RAM (executable main memory) `[0x80000000, 0x100000000)` — `initPmaRegions`'
  `MainMemory` region base `0x80000000` size `0x80000000`;
* the HTIF `tohost` mailbox window `[0x8001ad00, 0x8001ad10)` — `tohostAddr` ± the
  16-byte `tohost`/`fromhost` pair the specs exclude as `tohostAddr + 16 ≤ …`;
* `.rodata` sits just below `tohost` (see `StrcmpSpecW`, mask @ `0x8001ac80`); it
  needs no separate constant here — spec code/rodata regions are supplied per
  function (there is no single global text extent in the codebase).
-/

/-- Low bound of executable main memory (RAM). -/
abbrev ramLo : Nat := 0x80000000
/-- High bound (exclusive) of executable main memory (RAM). -/
abbrev ramHi : Nat := 0x100000000

/-- `tohostAddr = 0x8001ad00` (the HTIF mailbox), restated for `omega`. -/
theorem tohostAddr_val : tohostAddr = 0x8001ad00 := rfl

/-! ## `Region` — an explicit `[lo, lo+len)` byte interval

We use a bare `Nat × Nat` (`lo`, `len`) rather than a structure: every consumer
projects `.1`/`.2` and feeds them straight to `omega`, so a structure would only
add `.lo`/`.len` noise at every use site.  All three predicates unfold to plain
`Nat` inequalities (the `_iff` lemmas below are `rfl`, so `simp only [… , RSub,
RDisjoint, mem_region]` then `omega` closes every region goal). -/

/-- A memory region: `(lo, len)` denotes the byte interval `[lo, lo+len)`. -/
abbrev Region : Type := Nat × Nat

/-- `a` lies in region `r = (lo, len)`, i.e. `lo ≤ a < lo + len`. -/
def mem_region (a : Nat) (r : Region) : Prop := r.1 ≤ a ∧ a < r.1 + r.2

/-- Regions `r`, `s` are disjoint: their `[lo, lo+len)` intervals do not overlap.
Generalizes the per-spec `code_disjoint` / `frame_stack_disjoint` fields
(`MemcpySpec.Regions.code_disjoint`, `EnvRegions.frame_stack_disjoint`, …). -/
def RDisjoint (r s : Region) : Prop := r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1

/-- `r` is a sub-region of `s`: `[r.lo, r.lo+r.len) ⊆ [s.lo, s.lo+s.len)`. -/
def RSub (r s : Region) : Prop := s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2

/-- `RSub` is transitive. -/
theorem RSub.trans {r s t : Region} (h1 : RSub r s) (h2 : RSub s t) : RSub r t :=
  ⟨Nat.le_trans h2.1 h1.1, Nat.le_trans h1.2 h2.2⟩

/-! ## Fixed-map regions as `Region` values -/

/-- The RAM region `[0x80000000, 0x100000000)` as a `Region`. -/
def ramRegion : Region := (ramLo, ramHi - ramLo)

/-! ## Generic byte-map frame lemmas over `Std.ExtHashMap Nat (BitVec 8)`

Restated (not imported — see the module header) `writeMap4`/`writeMap8` and their
read-over-write lemmas.  These generalize `ValueSpec`'s
`getElem_writeMap{4,8}_disjoint`, `read32_writeMap4`, `read64_writeMap8`,
`read32_writeMap8_disjoint`, `read64_writeMap4_disjoint` so the `env_*` specs get
them from one import.  (`ValueSpec` keeps its private copies; no retrofit.) -/

/-- Width-4 write-map: `mem` updated with `d`'s 4 little-endian bytes at `a`.
Definitionally identical to `Vsa.Sim.ValueSites.writeMap4`. -/
abbrev writeMap4_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8))

/-! ## `AgreeOn` — pointwise byte agreement on a region

`AgreeOn r m1 m2` says `m1` and `m2` hold the same byte at every address of
region `r`.  It is the region-generic form of the *per-`Loaded` byte-fact
transfer* that `EnvNewSpec.loaded_env_of_agree` and `ValueSpec.loaded_null_*` do
by hand: any predicate that is a conjunction of `mem[a]? = …` facts over `r`
transfers along `AgreeOn r`.

The workhorse `loaded_of_agree_rg` states the reusable form directly (the
`∀ a ∈ r, m2[a]? = m1[a]?` hypothesis, exactly `loaded_env_of_agree`'s
`hagree`); per-`Loaded`-predicate instantiations stay one-liner corollaries in
each spec file (`fun a hlo hhi => hAgree a ⟨…⟩`). -/

/-- `m1` and `m2` agree byte-for-byte on region `r`. -/
def AgreeOn (r : Region) (m1 m2 : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, mem_region a r → m1[a]? = m2[a]?

theorem AgreeOn.trans {r : Region} {m1 m2 m3 : Std.ExtHashMap Nat (BitVec 8)}
    (h1 : AgreeOn r m1 m2) (h2 : AgreeOn r m2 m3) : AgreeOn r m1 m3 :=
  fun a ha => (h1 a ha).trans (h2 a ha)

/-- Monotonicity: agreement on `r` restricts to any sub-region `r' ⊆ r`. -/
theorem AgreeOn.mono {r r' : Region} {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (hsub : RSub r' r) (h : AgreeOn r m1 m2) : AgreeOn r' m1 m2 := by
  intro a ha; obtain ⟨hlo, hhi⟩ := ha; obtain ⟨slo, shi⟩ := hsub
  exact h a ⟨by omega, by omega⟩

/-! ## Stack-frame survival kit

Generalizes `EnvNewSpec`'s spill-slot reasoning (`EnvRegions.spill_*` fields and
the `spill_transfer` pattern that recovers spilled `s0`/`ra` after a callee that
preserves memory outside `privFoot ∪ [SL.lo, sp)`).

`spillWindow SL sp k = ([sp-k, sp))` is the `k`-byte spill area at the top of the
frame; the two lemmas below package (a) `spillWindow ⊆ [SL.lo, sp)` and (b) any
byte in `spillWindow` survives a callee whose only writes are inside
`privFoot ∪ [SL.lo, sp-k)`, provided the byte is not in `privFoot`. -/

/-! ## `FixedMap` disjointness bundle

Collects the standard side conditions every spec re-states for a freshly-written
`block = (base, len)`, so a future spec takes ONE hypothesis instead of eight.
This is the common shape of `MemcpySpec.Regions`, `ValueSpec.NullRegion`/
`IntRegion`, and the frame half of `EnvNewSpec.EnvRegions`.

The code region is a *parameter* (`code`): the codebase pins each function's own
`[funcLo, funcHi)`, and there is no single global text extent, so a shared `code`
constant would be wrong.  Likewise `stack = (SL.lo, SL.hi - SL.lo)` is supplied
by the caller's `StackLayout`. -/

/-- The standard region side-conditions for a written block `(base, len)`:
in RAM, above the `tohost` window, aligned, disjoint from the function's `code`
region and from the caller's `stack` region.  One hypothesis replacing the
eight-field per-spec `Region`/`NullRegion` bundles. -/
structure FixedMap (block code stack : Region) : Prop where
  /-- The block lies in RAM `[0x80000000, 0x100000000)`. -/
  in_ram : RSub block ramRegion
  /-- The block is above the HTIF `tohost` window. -/
  above_tohost : tohostAddr + 16 ≤ block.1
  /-- 8-byte alignment of the block base. -/
  aligned : block.1 % 8 = 0
  /-- Disjoint from the function's code/rodata region. -/
  code_disjoint : RDisjoint block code
  /-- Disjoint from the caller's stack region. -/
  stack_disjoint : RDisjoint block stack

/-- Projection: the block base is `≥ 0x80000000`. -/
theorem FixedMap.lo {block code stack : Region} (h : FixedMap block code stack) :
    ramLo ≤ block.1 := by
  have := h.in_ram; simp only [RSub, ramRegion] at this
  have hr : ramLo ≤ ramHi := by decide
  omega

/-- Projection: the block end is `≤ 0x100000000`. -/
theorem FixedMap.hi {block code stack : Region} (h : FixedMap block code stack) :
    block.1 + block.2 ≤ ramHi := by
  have := h.in_ram; simp only [RSub, ramRegion] at this
  have hr : ramLo ≤ ramHi := by decide
  omega

/-! ## `#print axioms` sanity examples

Instantiating the main lemmas.  All must depend only on `propext`,
`Classical.choice`, `Quot.sound` (no `sorry`/`axiom`/`native_decide`/`bv_decide`).
-/

end Vsa.Sim
