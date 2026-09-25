import Vsa.Sim.Boot.Image

/-!
# `initializeMemory` is the loader memory `loadedMem`

`initializeMemory .B64 elf` (`riscv-lean/lean_emulator/LeanRiscv.lean`)
inserts each ELFSage piece (interpreted segments, then bits and bobs) byte by
byte, panicking on an address already written. `ElfLoads elf script` says the
parsed pieces are `bootPieces` carrying `imageByte script`; then the loader's
memory is `loadedMem script` (`initializeMemory_eq`), since `bootPieces` are
pairwise disjoint and the panic branch is never taken.

`ElfLoads` is a statement about the ELFSage parse of a concrete file. The
kernel does not parse the 138 KB file (see `Vsa.ElfMono`); the native dump
`scripts/boot_elf_pieces.lean` and `scripts/gen_boot_witness.py corpus`
compare every script build's pieces with the proof ELF's.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr LeanRV64DExecutable

/-- The pieces `initializeMemory` inserts, in order, with their bytes. -/
def elfPieces (elf : ELF64File) : List (Nat × List UInt8) :=
  elf.interpreted_segments.map (fun p => (p.2.segment_base, p.2.segment_body.data.toList)) ++
    elf.bits_and_bobs.map (fun p => (p.1, p.2.data.toList))

/-- The image's pieces with their bytes. -/
def imagePieces (script : Nat) : List (Nat × List UInt8) :=
  bootPieces.map fun p => (p.1, (List.range p.2).map fun i => UInt8.ofBitVec (imageByte script (p.1 + i)))

/-- The parsed ELF loads the image of `script`. -/
def ElfLoads (elf : ELF64File) (script : Nat) : Prop := elfPieces elf = imagePieces script

/-! ## One piece -/

/-- A byte-inserting step that inserts at fresh addresses. -/
def InsertsFresh (f : Mem → Nat × UInt8 → Mem) : Prop :=
  ∀ mem a b, mem.contains a = false → f mem (a, b) = mem.insert a b.toBitVec

theorem piece_fold {f : Mem → Nat × UInt8 → Mem} (hf : InsertsFresh f) :
    ∀ (body : List UInt8) (mem : Mem) (base : Nat),
      (∀ i, i < body.length → mem.contains (base + i) = false) →
      ∀ x, (((List.range' base body.length).zip body).foldl f mem)[x]? =
        if h : base ≤ x ∧ x < base + body.length then
          some (body[x - base]'(by omega)).toBitVec
        else mem[x]? := by
  intro body
  induction body with
  | nil =>
    intro mem base _ x
    simp only [List.length_nil, List.range'_zero, List.zip_nil_left, List.foldl_nil]
    rw [dif_neg (by omega)]
  | cons b rest ih =>
    intro mem base hfresh x
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons]
    rw [hf mem base b (by simpa using hfresh 0 (by simp)), ih]
    · by_cases hx : base = x
      · subst hx
        rw [dif_neg (by omega), dif_pos (by omega)]
        simp
      · rw [Std.ExtHashMap.getElem?_insert]
        simp only [beq_iff_eq, hx, ↓reduceIte]
        by_cases h1 : base + 1 ≤ x ∧ x < base + 1 + rest.length
        · rw [dif_pos h1, dif_pos (by omega)]
          simp only [Option.some.injEq]
          rw [List.getElem_cons, dif_neg (by omega)]
          congr 2
        · rw [dif_neg h1, dif_neg (by omega)]
    · intro i hi
      rw [Std.ExtHashMap.contains_insert]
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨by omega, ?_⟩
      have := hfresh (i + 1) (by simp; omega)
      rwa [show base + (i + 1) = base + 1 + i by omega] at this

/-! ## All pieces -/

/-- Insert each piece's bytes at its base, in order. -/
def insertPieces (f : Mem → Nat × UInt8 → Mem) (mem : Mem) (ps : List (Nat × List UInt8)) :
    Mem :=
  ps.foldl (fun mem p => ((List.range' p.1 p.2.length).zip p.2).foldl f mem) mem

/-- Two pieces do not overlap. -/
def PieceDisjoint (a b : Nat × List UInt8) : Prop :=
  a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1

/-- The byte a piece list places at `x` (the first piece holding it). -/
def pieceByte : List (Nat × List UInt8) → Nat → Option (BitVec 8)
  | [], _ => none
  | p :: ps, x =>
    if h : p.1 ≤ x ∧ x < p.1 + p.2.length then some (p.2[x - p.1]'(by omega)).toBitVec
    else pieceByte ps x

theorem pieceByte_none_of {ps : List (Nat × List UInt8)} {x : Nat}
    (h : ∀ p ∈ ps, ¬ (p.1 ≤ x ∧ x < p.1 + p.2.length)) : pieceByte ps x = none := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pieceByte]
    rw [dif_neg (h p (List.mem_cons_self))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem insertPieces_get {f : Mem → Nat × UInt8 → Mem} (hf : InsertsFresh f) :
    ∀ (ps : List (Nat × List UInt8)), ps.Pairwise PieceDisjoint → ∀ (mem : Mem),
      (∀ p ∈ ps, ∀ i, i < p.2.length → mem.contains (p.1 + i) = false) →
      ∀ x, (insertPieces f mem ps)[x]? =
        match pieceByte ps x with
        | some b => some b
        | none => mem[x]? := by
  intro ps
  induction ps with
  | nil => intro _ mem _ x; simp [insertPieces, pieceByte]
  | cons p ps ih =>
    intro hd mem hfresh x
    rw [List.pairwise_cons] at hd
    have hp := piece_fold hf p.2 mem p.1 (hfresh p List.mem_cons_self)
    unfold insertPieces
    rw [List.foldl_cons]
    change (insertPieces f _ ps)[x]? = _
    rw [ih hd.2]
    · simp only [pieceByte]
      by_cases hx : p.1 ≤ x ∧ x < p.1 + p.2.length
      · rw [dif_pos hx]
        rw [pieceByte_none_of (fun q hq hqx => by
          have := hd.1 q hq; unfold PieceDisjoint at this; omega)]
        rw [hp, dif_pos hx]
      · rw [dif_neg hx]
        cases pieceByte ps x with
        | some b => rfl
        | none => rw [hp, dif_neg hx]
    · intro q hq i hi
      have hq' := hfresh q (List.mem_cons_of_mem _ hq) i hi
      have hdis := hd.1 q hq
      unfold PieceDisjoint at hdis
      rw [Std.ExtHashMap.contains_eq_isSome_getElem?, hp, dif_neg (by omega),
        ← Std.ExtHashMap.contains_eq_isSome_getElem?]
      exact hq'

/-! ## The loader -/

/-- `initializeMemory`'s per-byte step. -/
def loadStep (mem : Mem) (ab : Nat × UInt8) : Mem :=
  if mem.contains ab.1 then panic s!"Address {ab.1} is already written to!"
  else mem.insert ab.1 ab.2.toBitVec

theorem loadStep_fresh : InsertsFresh loadStep := by
  intro mem a b h
  simp [loadStep, h]

/-- `initializeMemory` is the piece insertion over `elfPieces`. -/
theorem initializeMemory_pieces (elf : ELF64File) :
    initializeMemory .B64 elf = insertPieces loadStep ∅ (elfPieces elf) := by
  unfold initializeMemory insertPieces elfPieces loadStep
  simp only [List.foldl_append, List.foldl_map, ← Array.foldl_toList, Array.toList_zip,
    Array.toList_range', Array.length_toList]
  rfl

private theorem imagePieces_shape (script : Nat) :
    (imagePieces script).map (fun p => (p.1, p.2.length)) = bootPieces := by
  simp [imagePieces, Function.comp_def]

private theorem imagePieces_disjoint (script : Nat) : (imagePieces script).Pairwise PieceDisjoint := by
  have h : bootPieces.Pairwise (fun a b => a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1) := by decide
  rw [← imagePieces_shape script, List.pairwise_map] at h
  exact h

private theorem pieceByte_image (byte : Nat → BitVec 8) :
    ∀ (ps : List (Nat × Nat)) (x : Nat),
      pieceByte (ps.map fun p => (p.1, (List.range p.2).map fun i => UInt8.ofBitVec (byte (p.1 + i))))
        x = if inPieces ps x then some (byte x) else none := by
  intro ps x
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, pieceByte, List.length_map, List.length_range, inPieces,
      List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hx : p.1 ≤ x ∧ x < p.1 + p.2
    · rw [dif_pos hx, if_pos (Or.inl hx)]
      simp only [List.getElem_map, List.getElem_range, Option.some.injEq]
      rw [show p.1 + (x - p.1) = x by omega]
    · rw [dif_neg hx, ih]
      unfold inPieces
      simp only [hx, false_or]

/-- **The loader's memory.** An ELF whose parse loads the image of `script`
initialises exactly `loadedMem script`. -/
theorem initializeMemory_eq {elf : ELF64File} {script : Nat} (h : ElfLoads elf script) :
    initializeMemory .B64 elf = loadedMem script := by
  rw [initializeMemory_pieces, h]
  apply Std.ExtHashMap.ext_getElem?
  intro x
  rw [insertPieces_get loadStep_fresh _ (imagePieces_disjoint script) ∅ (by simp),
    loadedMem_get, imageView, imagePieces, pieceByte_image]
  split <;> simp_all

end Vsa.Sim.Boot
