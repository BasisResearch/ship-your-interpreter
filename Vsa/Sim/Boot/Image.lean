import Vsa.Sim.Boot.Log
import Vsa.Sim.Boot.ImageData
import Vsa.Sim.Code.FixedImageData

/-!
# The loader's memory for a script build of the interpreter ELF

`initializeMemory .B64` (`riscv-lean/lean_emulator/LeanRiscv.lean`) inserts
the bytes of every piece ELFSage reports (interpreted segments, then "bits and
bobs") at the piece's base. For every script build of the interpreter those
pieces are `bootPieces` (`ImageData.lean`, dumped natively by
`scripts/boot_elf_pieces.lean`), and the bytes differ from the proof ELF's
only inside the script blob `[0x80018be0, 0x80018be0 + 453)`
(`scripts/gen_boot_witness.py corpus` checks both).

* `loaderMem pieces byte`: those insertions, for a byte function.
* `imageByte script`: the ELF's bytes with `script` (453 bytes, packed) in
  the blob; `.text` and the rest of `.rodata` are the fixed image
  (`Code.fixedTextByte`, `Code.fixedRodataByte`).
* `bootMem script L`: the store log `L` applied to the loader's memory, and
  `bootMem_get`: its bytes under a `LogOk`.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr

/-- `n` insertions of `byte` from `base`, in address order. -/
def insertRange (m : Mem) (base : Nat) (byte : Nat → BitVec 8) : Nat → Mem
  | 0 => m
  | n + 1 => (insertRange m base byte n).insert (base + n) (byte (base + n))

theorem insertRange_get (m : Mem) (base : Nat) (byte : Nat → BitVec 8) (n x : Nat) :
    (insertRange m base byte n)[x]? =
      if base ≤ x ∧ x < base + n then some (byte x) else m[x]? := by
  induction n with
  | zero => simp [insertRange]; omega
  | succ n ih =>
    rw [insertRange, Std.ExtHashMap.getElem?_insert, ih]
    by_cases h : base + n = x
    · subst h; simp
    · simp only [beq_iff_eq, h, ↓reduceIte]
      split <;> split <;> first | rfl | omega

/-- Whether `x` lies in one of the pieces. -/
def inPieces (pieces : List (Nat × Nat)) (x : Nat) : Bool :=
  pieces.any fun p => decide (p.1 ≤ x ∧ x < p.1 + p.2)

/-- The loader's insertions of `byte` over `pieces`. -/
def loaderMem (pieces : List (Nat × Nat)) (byte : Nat → BitVec 8) : Mem :=
  pieces.foldl (fun m p => insertRange m p.1 byte p.2) ∅

private theorem foldl_insertRange_get (pieces : List (Nat × Nat)) (byte : Nat → BitVec 8)
    (m : Mem) (x : Nat) :
    (pieces.foldl (fun m p => insertRange m p.1 byte p.2) m)[x]? =
      if inPieces pieces x then some (byte x) else m[x]? := by
  induction pieces generalizing m with
  | nil => simp [inPieces]
  | cons p ps ih =>
    rw [List.foldl_cons, ih, insertRange_get]
    simp only [inPieces, List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hp : p.1 ≤ x ∧ x < p.1 + p.2
    · simp [hp]
    · simp only [hp, false_or, ↓reduceIte]

theorem loaderMem_get (pieces : List (Nat × Nat)) (byte : Nat → BitVec 8) (x : Nat) :
    (loaderMem pieces byte)[x]? = if inPieces pieces x then some (byte x) else none := by
  rw [loaderMem, foldl_insertRange_get]
  simp

/-- `_script_start`: the embedded script blob, 453 bytes padded with newlines,
then a NUL (which belongs to the fixed image). -/
def scriptBase : Nat := 0x80018be0
def scriptLen : Nat := 453

/-- The loaded ELF's bytes with `script` (packed little-endian) in the blob. -/
def imageByte (script : Nat) (x : Nat) : BitVec 8 :=
  if x < 0x80000000 then bootLowByte x
  else if x < 0x80018be0 then Code.fixedTextByte (x - 0x80000000)
  else if x < 0x80018be0 + 453 then BitVec.ofNat 8 (script >>> (8 * (x - 0x80018be0)))
  else if x < 0x8001acf0 then Code.fixedRodataByte (x - 0x80018be0)
  else bootDataByte (x - 0x8001acf0)

/-- The loader's byte view: present exactly on the pieces. -/
def imageView (script : Nat) (x : Nat) : Option (BitVec 8) :=
  if inPieces bootPieces x then some (imageByte script x) else none

/-- The loader's memory for a script build. -/
def loadedMem (script : Nat) : Mem := loaderMem bootPieces (imageByte script)

theorem loadedMem_get (script x : Nat) : (loadedMem script)[x]? = imageView script x :=
  loaderMem_get _ _ x

/-- The memory at `interp_run`'s entry: the boot store log over the loader's memory. -/
def bootMem (script : Nat) (L : PackedLog) : Mem := writeLog (loadedMem script) L.log

/-- The entry memory's byte view: the final byte map over the loader's view. -/
def bootView (script : Nat) (t : RunTree) (x : Nat) : Option (BitVec 8) :=
  logView t (imageView script) x

theorem bootMem_get {script : Nat} {L : PackedLog} {t : RunTree} (h : LogOk L t)
    (x : Nat) : (bootMem script L)[x]? = bootView script t x := by
  rw [bootMem, writeLog_view h, bootView,
    show (fun a => (loadedMem script)[a]?) = imageView script from funext (loadedMem_get script)]

end Vsa.Sim.Boot
