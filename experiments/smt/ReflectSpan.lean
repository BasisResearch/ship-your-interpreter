import Vsa.Sim.BlockDecode
import Vsa.Sim.BlockMem

/-!
# `ReflectSpan` — decode a code span from the proof ELF and reflect its write-log

The faithful encoding of `Steps c c'` for a straight-line span is the block-
reflection write-log: `c' = applyWriteLog c (wlogM instrs)`.  This tool produces
`instrs` AUTOMATICALLY (no hand-transcription): it reads the proof ELF
(`c/while-riscv-htif.elf`), extracts the 4-byte words over `[lo, hi)`, and
decodes each with the PROOF's own `mkLine` (`Vsa/Sim/BlockDecode.lean`), then
folds `wlogM` (`Vsa/Sim/BlockMem.lean`).  Using the proof decoder + fold means a
wrong transcription cannot slip in — the emitted log is exactly what
block-reflection computes.

`#reflect_span <lo> <hi>` #evals the decoded `MInstr` list + its `wlogM`.  Proves
nothing; run via `lake env lean`.
-/

open Vsa.Sim LeanRV64DExecutable

namespace Vsa.ReflectSpan

/-- ELF64 PT_LOAD map: read the proof ELF and return `vaddr → byte?`. -/
def loadElf (path : String) : IO (Nat → Option (BitVec 8)) := do
  let bytes ← IO.FS.readBinFile path
  let b : Nat → Nat := fun o => (bytes.get! o).toNat
  let rd16 : Nat → Nat := fun o => b o + b (o+1) * 256
  let rd32 : Nat → Nat := fun o => b o + b (o+1) * 256 + b (o+2) * 65536 + b (o+3) * 16777216
  let rd64 : Nat → Nat := fun o => rd32 o + rd32 (o+4) * 4294967296
  let phoff := rd64 0x20
  let phentsize := rd16 0x36
  let phnum := rd16 0x38
  let mut segs : Array (Nat × Nat × Nat) := #[]
  for i in List.range phnum do
    let o := phoff + i * phentsize
    if rd32 o == 1 then  -- PT_LOAD
      let p_offset := rd64 (o + 0x08)
      let p_vaddr := rd64 (o + 0x10)
      let p_filesz := rd64 (o + 0x20)
      segs := segs.push (p_vaddr, p_offset, p_filesz)
  return fun va => Id.run do
    for (v, off, sz) in segs do
      if v ≤ va && va < v + sz then return some (BitVec.ofNat 8 (bytes.get! (off + (va - v))).toNat)
    return none

/-- Read a 32-bit little-endian word at `va` (0 if unmapped). -/
def wordAt (img : Nat → Option (BitVec 8)) (va : Nat) : BitVec 32 :=
  let b (i : Nat) : BitVec 32 := ((img (va + i)).getD 0).setWidth 32
  (b 0) ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24)

/-- Decode the span `[lo, hi)` into the proof's `MInstr` list via `mkLine`. -/
def decodeSpan (img : Nat → Option (BitVec 8)) (lo hi : Nat) : List MInstr := Id.run do
  let mut out : List MInstr := []
  let mut pc := lo
  while pc < hi do
    out := out ++ [mkLine (BitVec.ofNat 64 pc) (wordAt img pc)]
    pc := pc + 4
  return out

/-- The proof ELF path (the object under verification — read only). -/
def elfPath : String := "c/while-riscv-htif.elf"

/-- Probe base for entry register `n` (matches `WlogExtract.baseOf`). -/
def baseOf (n : Nat) : Nat := 0x40000000 * (n + 1)

/-- Resolve a concrete store address back to `(reg, signed offset)` against the
probe bases, so the SMT store re-symbolises to `bvadd <reg> <off>`. -/
def resolveAddr (regs : List Nat) (a : Nat) : Option (Nat × Int) :=
  regs.findSome? (fun r =>
    let d : Int := (a : Int) - (baseOf r : Int)
    if d.natAbs ≤ 8192 then some (r, d) else none)

/-- SMT name for register `n`. -/
def regName (n : Nat) : String := s!"x{n}"

/-- Emit the write-log of span `[lo,hi)` as an SMT store-chain relating the entry
memory `mem` to the exit memory `mem'` (`Steps c c'` for a straight-line span).
Each 8-byte store becomes eight `(store … (+ base off j) …)` byte writes; the
address base is re-symbolised to its entry register.  A store whose address does
not resolve to a probe base is emitted at its absolute literal. -/
def reflectStepsSmt (lo hi : Nat) (regs : List Nat) : IO String := do
  let img ← loadElf elfPath
  let instrs := decodeSpan img lo hi
  let entry : GRegs := regs.map (fun n => (n, BitVec.ofNat 64 (baseOf n)))
  let log := wlogM instrs entry []
  -- fold the byte writes over a symbolic `mem` array (Int → BV8)
  let mut cur := "mem"
  for (a, w, d) in log do
    let addr : String := match resolveAddr regs a with
      | some (r, off) => s!"(+ {regName r} {off})"
      | none => toString a
    for j in List.range w do
      let byte := s!"((_ extract {8*j+7} {8*j}) (_ bv{d.toNat} 64))"
      cur := s!"(store {cur} (+ {addr} {j}) {byte})"
  -- the entry regs as SMT ints (symbolic)
  let decls := String.intercalate "\n" (regs.map (fun r => s!"(declare-fun {regName r} () Int)"))
  return s!"; Steps reflection of span [{lo},{hi})\n{decls}\n(declare-fun mem () (Array Int (_ BitVec 8)))\n(define-fun mem_exit () (Array Int (_ BitVec 8)) {cur})\n"

end Vsa.ReflectSpan

open Vsa.ReflectSpan in
elab "#reflect_span " loStx:num hiStx:num : command => do
  let lo := loStx.getNat
  let hi := hiStx.getNat
  Lean.Elab.Command.liftTermElabM do
    let img ← loadElf elfPath
    let instrs := decodeSpan img lo hi
    Lean.logInfo m!"span [{lo},{hi}) → {instrs.length} instrs; rd/rs1/imm = {reprStr (instrs.map (fun i => (i.rd, i.rs1, i.imm.toNat)))}"
    -- probe entry regs (distinct, far-apart bases; the SMT emitter re-symbolises)
    let entry : GRegs := [2, 1, 8, 9, 18, 19].map (fun n => (n, BitVec.ofNat 64 (0x40000000 * (n + 1))))
    let log := wlogM instrs entry []
    Lean.logInfo m!"wlogM = {reprStr log}"
