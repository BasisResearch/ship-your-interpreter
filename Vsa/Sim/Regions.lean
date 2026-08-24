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

theorem ramLo_val : ramLo = 0x80000000 := rfl
theorem ramHi_val : ramHi = 0x100000000 := rfl
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

theorem mem_region_iff (a : Nat) (r : Region) :
    mem_region a r ↔ r.1 ≤ a ∧ a < r.1 + r.2 := Iff.rfl
theorem RDisjoint_iff (r s : Region) :
    RDisjoint r s ↔ r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 := Iff.rfl
theorem RSub_iff (r s : Region) :
    RSub r s ↔ s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2 := Iff.rfl

/-- Disjointness is symmetric. -/
theorem RDisjoint.symm {r s : Region} (h : RDisjoint r s) : RDisjoint s r := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- `RSub` is reflexive. -/
theorem RSub.refl (r : Region) : RSub r r := ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- `RSub` is transitive. -/
theorem RSub.trans {r s t : Region} (h1 : RSub r s) (h2 : RSub s t) : RSub r t :=
  ⟨Nat.le_trans h2.1 h1.1, Nat.le_trans h1.2 h2.2⟩

/-- Disjointness is monotone under `RSub`: a subregion of a disjoint region is
still disjoint. -/
theorem RDisjoint.of_sub_left {r r' s : Region} (hsub : RSub r' r) (h : RDisjoint r s) :
    RDisjoint r' s := by
  obtain ⟨hlo, hhi⟩ := hsub; rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If `a ∈ r` and `RDisjoint r s`, then `a ∉ s`. -/
theorem not_mem_of_disjoint {a : Nat} {r s : Region} (ha : mem_region a r)
    (hd : RDisjoint r s) : ¬ mem_region a s := by
  obtain ⟨hlo, hhi⟩ := ha; rintro ⟨hlo', hhi'⟩; rcases hd with h | h <;> omega

/-! ## Fixed-map regions as `Region` values -/

/-- The RAM region `[0x80000000, 0x100000000)` as a `Region`. -/
def ramRegion : Region := (ramLo, ramHi - ramLo)
/-- The HTIF `tohost` window `[0x8001ad00, 0x8001ad10)` as a `Region`. -/
def tohostWin : Region := (tohostAddr, 16)

theorem mem_ramRegion (a : Nat) : mem_region a ramRegion ↔ ramLo ≤ a ∧ a < ramHi := by
  simp only [mem_region, ramRegion]; omega
theorem mem_tohostWin (a : Nat) : mem_region a tohostWin ↔ tohostAddr ≤ a ∧ a < tohostAddr + 16 := by
  simp only [mem_region, tohostWin]

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

/-- Width-8 write-map: `mem` updated with `d`'s 8 little-endian bytes at `a`.
Definitionally identical to `Vsa.Sim.ValueSites.writeMap8`. -/
abbrev writeMap8_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8)).insert
    (a + 4) (d.extractLsb' 32 8)).insert (a + 5) (d.extractLsb' 40 8)).insert
    (a + 6) (d.extractLsb' 48 8)).insert (a + 7) (d.extractLsb' 56 8))

/-- Read-over-write: `(mem.insert j v)[i]? = mem[i]?` when `j ≠ i`.
Generalizes `ValueSpec.getElem_insert_ne` (Bool-disequality form). -/
theorem getElem_insert_ne_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (i j : Nat) (v : BitVec 8)
    (hne : (j == i) = false) : (mem.insert j v)[i]? = mem[i]? := by
  rw [Std.ExtHashMap.getElem?_insert,
    if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]

/-- Read-over-write: `(mem.insert i v)[i]? = some v`.
Generalizes `ValueSpec.getElem_insert_self`. -/
theorem getElem_insert_self_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (v : BitVec 8) :
    (mem.insert i v)[i]? = some v := by
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by simp)]

/-- A byte read at `k` disjoint from the `writeMap4`-window `[a4, a4+4)` passes
through to `mem`.  Generalizes `ValueSpec.getElem_writeMap4_disjoint`. -/
theorem getElem_writeMap4_disjoint_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 k : Nat)
    (d : BitVec (8 * 4)) (hk : k < a4 ∨ a4 + 4 ≤ k) :
    (writeMap4_rg mem a4 d)[k]? = mem[k]? := by
  simp only [writeMap4_rg]
  rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

/-- A byte read at `k` disjoint from the `writeMap8`-window `[a8, a8+8)` passes
through to `mem`.  Generalizes `ValueSpec.getElem_writeMap8_disjoint` (used by
`EnvNewSpec.loaded_env_writeMap8` / `read64_writeMap8_disjoint`). -/
theorem getElem_writeMap8_disjoint_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 k : Nat)
    (d : BitVec (8 * 8)) (hk : k < a8 ∨ a8 + 8 ≤ k) :
    (writeMap8_rg mem a8 d)[k]? = mem[k]? := by
  simp only [writeMap8_rg]
  rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

/-- The four bytes of `writeMap4_rg mem a d`, read back individually. -/
theorem getElem_writeMap4_k_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4_rg mem a d)[a]? = some (d.extractLsb' 0 8)
    ∧ (writeMap4_rg mem a d)[a + 1]? = some (d.extractLsb' 8 8)
    ∧ (writeMap4_rg mem a d)[a + 2]? = some (d.extractLsb' 16 8)
    ∧ (writeMap4_rg mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap4_rg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_self_rg]

/-- `read32` of a freshly `writeMap4`-written window recovers `d.toNat`.
Generalizes `ValueSpec.read32_writeMap4`. -/
theorem read32_writeMap4_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    read32 (writeMap4_rg mem a d) a = some d.toNat := by
  obtain ⟨e0, e1, e2, e3⟩ := getElem_writeMap4_k_rg mem a d
  simp only [read32, readLE, e0, e1, e2, e3, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 32 := by have := d.isLt; simpa using this
  omega

/-- The eight bytes of `writeMap8_rg mem a d`, read back individually. -/
theorem getElem_writeMap8_k_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8_rg mem a d)[a]? = some (d.extractLsb' 0 8)
    ∧ (writeMap8_rg mem a d)[a + 1]? = some (d.extractLsb' 8 8)
    ∧ (writeMap8_rg mem a d)[a + 2]? = some (d.extractLsb' 16 8)
    ∧ (writeMap8_rg mem a d)[a + 3]? = some (d.extractLsb' 24 8)
    ∧ (writeMap8_rg mem a d)[a + 4]? = some (d.extractLsb' 32 8)
    ∧ (writeMap8_rg mem a d)[a + 5]? = some (d.extractLsb' 40 8)
    ∧ (writeMap8_rg mem a d)[a + 6]? = some (d.extractLsb' 48 8)
    ∧ (writeMap8_rg mem a d)[a + 7]? = some (d.extractLsb' 56 8) := by
  simp only [writeMap8_rg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_ne_rg _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self_rg]
  · rw [getElem_insert_self_rg]

/-- `read64` of a freshly `writeMap8`-written window recovers `d.toNat`.
Generalizes `ValueSpec.read64_writeMap8`. -/
theorem read64_writeMap8_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read64 (writeMap8_rg mem a d) a = some d.toNat := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := getElem_writeMap8_k_rg mem a d
  simp only [read64, readLE, e0, e1, e2, e3, e4, e5, e6, e7, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 64 := by have := d.isLt; simpa using this
  omega

/-- `read32` at `a` is unaffected by a `writeMap8` window disjoint from `[a, a+4)`.
Generalizes `ValueSpec.read32_writeMap8_disjoint`. -/
theorem read32_writeMap8_disjoint_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 4 ≤ a8 ∨ a8 + 8 ≤ a) :
    read32 (writeMap8_rg mem a8 d) a = read32 mem a := by
  have g0 := getElem_writeMap8_disjoint_rg mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint_rg mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint_rg mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint_rg mem a8 (a + 3) d (by omega)
  simp only [read32, readLE, g0, g1, g2, g3]

/-- `read64` at `a` is unaffected by a `writeMap8` window disjoint from `[a, a+8)`.
Generalizes `EnvNewSpec.read64_writeMap8_disjoint`. -/
theorem read64_writeMap8_disjoint_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8_rg mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint_rg mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint_rg mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint_rg mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint_rg mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint_rg mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint_rg mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint_rg mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint_rg mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

/-- `read32` at `a` is unaffected by a `writeMap4` window disjoint from `[a, a+4)`.
Generalizes `ValueSpec.read32_writeMap4_disjoint`. -/
theorem read32_writeMap4_disjoint_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a a4 : Nat)
    (d : BitVec (8 * 4)) (hdis : a + 4 ≤ a4 ∨ a4 + 4 ≤ a) :
    read32 (writeMap4_rg mem a4 d) a = read32 mem a := by
  have g0 := getElem_writeMap4_disjoint_rg mem a4 a d (by omega)
  have g1 := getElem_writeMap4_disjoint_rg mem a4 (a + 1) d (by omega)
  have g2 := getElem_writeMap4_disjoint_rg mem a4 (a + 2) d (by omega)
  have g3 := getElem_writeMap4_disjoint_rg mem a4 (a + 3) d (by omega)
  simp only [read32, readLE, g0, g1, g2, g3]

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

theorem AgreeOn.refl (r : Region) (m : Std.ExtHashMap Nat (BitVec 8)) : AgreeOn r m m :=
  fun _ _ => rfl

theorem AgreeOn.symm {r : Region} {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h : AgreeOn r m1 m2) : AgreeOn r m2 m1 := fun a ha => (h a ha).symm

theorem AgreeOn.trans {r : Region} {m1 m2 m3 : Std.ExtHashMap Nat (BitVec 8)}
    (h1 : AgreeOn r m1 m2) (h2 : AgreeOn r m2 m3) : AgreeOn r m1 m3 :=
  fun a ha => (h1 a ha).trans (h2 a ha)

/-- Monotonicity: agreement on `r` restricts to any sub-region `r' ⊆ r`. -/
theorem AgreeOn.mono {r r' : Region} {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (hsub : RSub r' r) (h : AgreeOn r m1 m2) : AgreeOn r' m1 m2 := by
  intro a ha; obtain ⟨hlo, hhi⟩ := ha; obtain ⟨slo, shi⟩ := hsub
  exact h a ⟨by omega, by omega⟩

/-- A `writeMap8` whose window `w = (a8, 8)` is disjoint from `r` leaves `mem` and
`writeMap8_rg mem a8 d` agreeing on `r`.  Generalizes the survival step in
`EnvNewSpec.loaded_env_writeMap8` / `read64_writeMap8_disjoint`. -/
theorem agree_of_write8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat)
    (d : BitVec (8 * 8)) (r : Region) (hd : RDisjoint r (a8, 8)) :
    AgreeOn r mem (writeMap8_rg mem a8 d) := by
  intro a ha; obtain ⟨hlo, hhi⟩ := ha
  refine (getElem_writeMap8_disjoint_rg mem a8 a d ?_).symm
  simp only [RDisjoint] at hd; omega

/-- A `writeMap4` whose window `w = (a4, 4)` is disjoint from `r` leaves `mem` and
`writeMap4_rg mem a4 d` agreeing on `r`. -/
theorem agree_of_write4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 : Nat)
    (d : BitVec (8 * 4)) (r : Region) (hd : RDisjoint r (a4, 4)) :
    AgreeOn r mem (writeMap4_rg mem a4 d) := by
  intro a ha; obtain ⟨hlo, hhi⟩ := ha
  refine (getElem_writeMap4_disjoint_rg mem a4 a d ?_).symm
  simp only [RDisjoint] at hd; omega

/-- **The byte-fact-transfer workhorse.**  Any code/data predicate `P` that is a
conjunction of `mem[a]? = …` facts over the region `r = (lo, len)` transfers from
`m1` to any `m2` agreeing with `m1` on `[lo, lo+len)`.  This is the region-generic
restatement of `EnvNewSpec.loaded_env_of_agree` / `ValueSpec.loaded_null_*`: the
caller supplies `P`'s transfer body as `hP` (typically `fun a hlo hhi =>
hAgree a ⟨hlo, hhi⟩ ▸ …`, or via `simp only [Loaded, chunk]` + `rw [hAgree …]`).

The reusable *proof engine* is `AgreeOn.get?_eq`: it exposes, for any concrete
address in `r`, the single `m2[a]? = m1[a]?` rewrite the private `loaded_*_of_agree`
proofs apply per byte. -/
theorem AgreeOn.get?_eq {r : Region} {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h : AgreeOn r m1 m2) {a : Nat} (ha : mem_region a r) : m1[a]? = m2[a]? := h a ha

/-- Region-form of `loaded_env_of_agree`'s hypothesis: `∀ a ∈ [lo, lo+len),
m2[a]? = m1[a]?` packaged as `AgreeOn`.  Lets a spec state its `hagree` as a
bounded `∀` and hand it to `AgreeOn` consumers.  (Note the direction: the private
`loaded_env_of_agree` uses `m2[a]? = m1[a]?`, i.e. `AgreeOn r m2 m1`.) -/
theorem agreeOn_of_bounds {lo len : Nat} {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ a, lo ≤ a → a < lo + len → m1[a]? = m2[a]?) : AgreeOn (lo, len) m1 m2 :=
  fun a ha => h a ha.1 ha.2

/-! ## Stack-frame survival kit

Generalizes `EnvNewSpec`'s spill-slot reasoning (`EnvRegions.spill_*` fields and
the `spill_transfer` pattern that recovers spilled `s0`/`ra` after a callee that
preserves memory outside `privFoot ∪ [SL.lo, sp)`).

`spillWindow SL sp k = ([sp-k, sp))` is the `k`-byte spill area at the top of the
frame; the two lemmas below package (a) `spillWindow ⊆ [SL.lo, sp)` and (b) any
byte in `spillWindow` survives a callee whose only writes are inside
`privFoot ∪ [SL.lo, sp-k)`, provided the byte is not in `privFoot`. -/

/-- The `k`-byte spill window `[sp - k, sp)` at the top of the frame. -/
def spillWindow (sp k : Nat) : Region := (sp - k, k)

theorem mem_spillWindow (a sp k : Nat) (hk : k ≤ sp) :
    mem_region a (spillWindow sp k) ↔ sp - k ≤ a ∧ a < sp := by
  simp only [mem_region, spillWindow]; omega

/-- **Spill window is inside the stack region `[SL.lo, sp)`** (the exact
`EnvRegions.spill_lo`/`spill_hi` fact, region-form).  `SL.lo ≤ sp - k` (frame has
room) and `sp ≤ sp` give the two `RSub` bounds. -/
theorem spillWindow_sub_stack (SL : StackLayout) (sp k : Nat)
    (hlo : SL.lo ≤ sp - k) (hk : k ≤ sp) :
    RSub (spillWindow sp k) (SL.lo, sp - SL.lo) := by
  simp only [RSub, spillWindow]; omega

/-- **Spill slots survive a memory-preserving callee.**  If a callee preserves
every byte outside `privFoot ∪ [SL.lo, sp-k)` (the `EnvNewSpec` malloc-post
shape: `∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp-k) → post[a]? = pre[a]?`), and
a spill byte `a ∈ [sp-k, sp)` is not allocator-private, then it survives:
`post[a]? = pre[a]?`.  This is `EnvNewSpec.spill_transfer`, generalized: the
`¬ privFoot` side condition is `EnvRegions.spill_not_priv`. -/
theorem spill_transfer_rg (privFoot : Nat → Prop) (SL : StackLayout) (sp k : Nat)
    (pre post : Std.ExtHashMap Nat (BitVec 8))
    (hpres : ∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp - k) → post[a]? = pre[a]?)
    (a : Nat) (ha : mem_region a (spillWindow sp k)) (hk : k ≤ sp)
    (hnp : ¬ privFoot a) : post[a]? = pre[a]? := by
  rw [mem_spillWindow a sp k hk] at ha
  exact hpres a hnp (by omega)

/-- Agreement form of `spill_transfer_rg`: the callee-preserving post agrees with
the pre on the whole spill window, given every spill byte avoids `privFoot`.
Hands the survival fact straight to the `read64_*`/`loaded_*` read-backs the caller
uses to recover the spilled `s0`/`ra`. -/
theorem spill_agree_rg (privFoot : Nat → Prop) (SL : StackLayout) (sp k : Nat)
    (pre post : Std.ExtHashMap Nat (BitVec 8))
    (hpres : ∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp - k) → post[a]? = pre[a]?)
    (hk : k ≤ sp)
    (hnp : ∀ a, mem_region a (spillWindow sp k) → ¬ privFoot a) :
    AgreeOn (spillWindow sp k) post pre :=
  fun a ha => spill_transfer_rg privFoot SL sp k pre post hpres a ha hk (hnp a ha)

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

/-- Projection: the block base is above the `tohost` window (`omega` form). -/
theorem FixedMap.win {block code stack : Region} (h : FixedMap block code stack) :
    tohostAddr + 16 ≤ block.1 := h.above_tohost

/-- Projection: the block is disjoint from the `tohost` window itself. -/
theorem FixedMap.tohost_disjoint {block code stack : Region} (h : FixedMap block code stack) :
    RDisjoint block tohostWin := by
  simp only [RDisjoint, tohostWin]; right; have := h.above_tohost; omega

/-- A sub-block of a `FixedMap` block (e.g. the tag `[base, base+4)` within a
24-byte `Value` at `base`) inherits code- and stack-disjointness. -/
theorem FixedMap.sub_code_disjoint {block code stack sub : Region}
    (h : FixedMap block code stack) (hsub : RSub sub block) : RDisjoint sub code :=
  RDisjoint.of_sub_left hsub h.code_disjoint

theorem FixedMap.sub_stack_disjoint {block code stack sub : Region}
    (h : FixedMap block code stack) (hsub : RSub sub block) : RDisjoint sub stack :=
  RDisjoint.of_sub_left hsub h.stack_disjoint

/-! ## `#print axioms` sanity examples

Instantiating the main lemmas.  All must depend only on `propext`,
`Classical.choice`, `Quot.sound` (no `sorry`/`axiom`/`native_decide`/`bv_decide`).
-/

section Sanity
example (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read64 (writeMap8_rg mem a d) a = some d.toNat := read64_writeMap8_rg mem a d

example (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat) (d : BitVec (8 * 8))
    (h : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8_rg mem a8 d) a = read64 mem a :=
  read64_writeMap8_disjoint_rg mem a a8 d h

example (r : Region) (m1 m2 m3 : Std.ExtHashMap Nat (BitVec 8))
    (h1 : AgreeOn r m1 m2) (h2 : AgreeOn r m2 m3) : AgreeOn r m1 m3 := h1.trans h2

example (block code stack : Region) (h : FixedMap block code stack) :
    RDisjoint block code := h.code_disjoint
end Sanity

#print axioms read64_writeMap8_rg
#print axioms read64_writeMap8_disjoint_rg
#print axioms AgreeOn.trans
#print axioms spill_transfer_rg
#print axioms FixedMap.tohost_disjoint

end Vsa.Sim
