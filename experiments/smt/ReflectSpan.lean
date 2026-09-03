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

-- ==========================================================================
-- Multi-block reflection: split a span at control-flow terminators and compose
-- straight-line write-logs across the seams (the SMT analogue of FnSummary.seq /
-- callSplice / tailJump).  Terminators are read from the RAW opcode (RISC-V):
--   BRANCH = 0x63, JAL = 0x6f, JALR = 0x67, SYSTEM/ECALL = 0x73.
-- ==========================================================================

/-- Low 7-bit opcode of a word. -/
def opcode (w : BitVec 32) : Nat := (w &&& 0x7f).toNat

/-- Is this word a control-flow terminator (branch / jump / call / return)? -/
def isTerm (w : BitVec 32) : Bool :=
  let op := opcode w
  op == 0x63 || op == 0x6f || op == 0x67 || op == 0x73

/-- A terminator's class + target (for JAL/BRANCH the target is PC-relative). -/
inductive Term where
  | branch (target : Nat)      -- conditional; fallthrough OR target
  | jal    (rd target : Nat)   -- call (rd=1) or plain jump
  | jalr   (rd : Nat)          -- indirect (call rd=1 / ret rd=0 via ra)
  | sys                        -- ecall/ebreak
  deriving Repr

/-- Decode the terminator at `pc` (word `w`), computing PC-relative targets. -/
def decodeTerm (pc : Nat) (w : BitVec 32) : Term :=
  let op := opcode w
  let bit (i : Nat) : Nat := ((w >>> i) &&& 1).toNat
  let rd := ((w >>> 7) &&& 0x1f).toNat
  if op == 0x6f then
    -- JAL imm[20|10:1|11|19:12]
    let imm := (bit 31)*(Nat.pow 2 20) + (((w>>>12) &&& 0xff).toNat)*(Nat.pow 2 12)
             + (bit 20)*(Nat.pow 2 11) + (((w>>>21) &&& 0x3ff).toNat)*2
    let imm := if bit 31 == 1 then Int.ofNat imm - (Nat.pow 2 21) else Int.ofNat imm
    Term.jal rd ((Int.ofNat pc + imm).toNat)
  else if op == 0x63 then
    -- BRANCH imm[12|10:5|4:1|11]
    let imm := (bit 31)*(Nat.pow 2 12) + (bit 7)*(Nat.pow 2 11) + (((w>>>25) &&& 0x3f).toNat)*(Nat.pow 2 5)
             + (((w>>>8) &&& 0xf).toNat)*2
    let imm := if bit 31 == 1 then Int.ofNat imm - (Nat.pow 2 13) else Int.ofNat imm
    Term.branch ((Int.ofNat pc + imm).toNat)
  else if op == 0x67 then Term.jalr rd
  else Term.sys

/-- Split `[lo,hi)` into maximal straight-line blocks, each ending at a
terminator (or at `hi`).  Returns `(blockInstrs, terminator?, blockEndPC)`. -/
def splitBlocks (img : Nat → Option (BitVec 8)) (lo hi : Nat) :
    List (List MInstr × Option Term × Nat) := Id.run do
  let mut out := []
  let mut cur : List MInstr := []
  let mut blkStart := lo
  let mut pc := lo
  while pc < hi do
    let w := wordAt img pc
    if isTerm w then
      out := out ++ [(cur, some (decodeTerm pc w), pc)]
      cur := []
      blkStart := pc + 4
    else
      cur := cur ++ [mkLine (BitVec.ofNat 64 pc) w]
    pc := pc + 4
  if !cur.isEmpty then out := out ++ [(cur, none, hi)]
  return out

/-- Append a straight-line block's write-log stores onto the SMT memory term. -/
def appendBlockLog (regs : List Nat) (mem0 : String) (instrs : List MInstr) : String := Id.run do
  let entry : GRegs := regs.map (fun n => (n, BitVec.ofNat 64 (baseOf n)))
  let log := wlogM instrs entry []
  let mut cur := mem0
  for (a, w, d) in log do
    let addr : String := match resolveAddr regs a with
      | some (r, off) => s!"(+ {regName r} {off})"
      | none => toString a
    for j in List.range w do
      cur := s!"(store {cur} (+ {addr} {j}) ((_ extract {8*j+7} {8*j}) (_ bv{d.toNat} 64)))"
  return cur

/-- Multi-block `Steps` encoding of `[lo,hi)`: compose each straight-line block's
write-log, splicing a callee/loop SUMMARY function at each seam (the SMT analogue
of `FnSummary.callSplice`/`tailJump`).  Returns `(memExitTerm, summarySymbols)`;
each summary symbol `S : Array→Array` is declared and gets its fold/unfold axiom
from the callee's own reflection (calls) or the mined loop invariant (loops). -/
def reflectStepsMulti (img : Nat → Option (BitVec 8)) (regs : List Nat) (lo hi : Nat) :
    String × List String := Id.run do
  let blocks := splitBlocks img lo hi
  let mut cur := "mem"
  let mut summaries : List String := []
  for (instrs, term?, endPC) in blocks do
    cur := appendBlockLog regs cur instrs
    match term? with
    | some (Term.jal rd target) =>
      if target < endPC then
        let s := s!"loop_{target}"; summaries := s :: summaries; cur := s!"({s} {cur})"
      else if rd == 1 then
        let s := s!"callee_{target}"; summaries := s :: summaries; cur := s!"({s} {cur})"
      -- plain forward jump (rd=0): straight fallthrough of the log, no seam effect
    | some (Term.jalr _) => pure ()           -- indirect call/ret: caller resumes
    | some (Term.branch target) =>
      let s := s!"branch_{target}"; summaries := s :: summaries; cur := s!"({s} {cur})"
    | _ => pure ()
  return (cur, summaries.eraseDups)

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
