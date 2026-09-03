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

/-- A 64-bit literal from a (possibly negative) `Int`, two's complement. -/
def bv64 (i : Int) : String :=
  let n : Nat := (i % 18446744073709551616 + 18446744073709551616).toNat % 18446744073709551616
  let hex := String.ofList (Nat.toDigits 16 n)
  s!"#x{String.ofList (List.replicate (16 - hex.length) '0')}{hex}"

/-- A 64-bit literal from a `Nat`. -/
def bvN (n : Nat) : String := bv64 (Int.ofNat n)

/-- reg `n` of state term `S`. -/
def stR (S : String) (n : Nat) : String := s!"(select (rr {S}) {bvN n})"

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
  | jalr   (rd rs1 : Nat)      -- indirect: CALL rd=1 / RET rd=0∧rs1=ra / computed goto
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
  else if op == 0x67 then Term.jalr rd (((w >>> 15) &&& 0x1f).toNat)
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

/-- Signed value of a 12-bit immediate. -/
def imm12 (i : BitVec 12) : Int :=
  if i.toNat ≥ 2048 then (i.toNat : Int) - 4096 else (i.toNat : Int)

/-- Symbolic register execution: fold each instruction's REGISTER effect into a
map `reg → SMT Int term`, over a symbolic entry map and memory term.  Covers the
arithmetic/logical MKinds exactly; loads become a `loadw`/`loadb` term over the
memory array (faithful to the read address); an unmodelled kind leaves `rd` as a
fresh uninterpreted term (flagged).  This is the register twin of `wlogM`. -/
def symStep (regs : Nat → String) (mem : String) (i : MInstr) : Nat → String :=
  let nv : Option String := match i.kind with
    | .addi  => some s!"(+ {regs i.rs1} {imm12 i.imm})"
    | .add   => some s!"(+ {regs i.rs1} {regs i.rs2})"
    | .sub   => some s!"(- {regs i.rs1} {regs i.rs2})"
    | .addiw => some s!"(+ {regs i.rs1} {imm12 i.imm})"
    | .addw  => some s!"(+ {regs i.rs1} {regs i.rs2})"
    | .subw  => some s!"(- {regs i.rs1} {regs i.rs2})"
    | .or    => some s!"(bvor_i {regs i.rs1} {regs i.rs2})"
    | .and   => some s!"(bvand_i {regs i.rs1} {regs i.rs2})"
    | .xor   => some s!"(bvxor_i {regs i.rs1} {regs i.rs2})"
    | .lui   => some s!"{imm12 i.imm * 4096}"
    | .slti  => some s!"(ite (< {regs i.rs1} {imm12 i.imm}) 1 0)"
    | .slt   => some s!"(ite (< {regs i.rs1} {regs i.rs2}) 1 0)"
    | .ld    => some s!"(loadw {mem} (+ {regs i.rs1} {imm12 i.imm}))"
    | .lw    => some s!"(loadw {mem} (+ {regs i.rs1} {imm12 i.imm}))"
    | .lwu   => some s!"(loadw {mem} (+ {regs i.rs1} {imm12 i.imm}))"
    | .lbu   => some s!"(loadb {mem} (+ {regs i.rs1} {imm12 i.imm}))"
    | _      => none
  fun n => if n == i.rd && i.rd != 0 then (nv.getD (regs n)) else regs n

/-- Fold `symStep` over a block; the store instructions do not change registers. -/
def symRun (mem : String) (entry : Nat → String) (is : List MInstr) : Nat → String :=
  is.foldl (fun regs i => symStep regs mem i) entry

/-- Resolve register `n`'s outcome value (from `runGM`) to a symbolic SMT term:
`(+ x<r> off)` against a probe base, else the literal.  `none` if `n` is not in
the outcome (unchanged from entry ⇒ its own symbol). -/
def symRegVal (regs : List Nat) (out : GRegs) (n : Nat) : String :=
  match out.find? (fun p => p.1 == n) with
  | none => regName n
  | some (_, v) =>
    match resolveAddr regs v.toNat with
    | some (r, off) => s!"(+ {regName r} {off})"
    | none => toString v.toNat

/-- Decode a branch's exit condition at the block end into an SMT Bool over the
block's register outcome.  funct3: beq=0 bne=1 blt=4 bge=5 bltu=6 bgeu=7. -/
def branchCond (regs : List Nat) (out : GRegs) (w : BitVec 32) : String :=
  let f3 := ((w >>> 12) &&& 7).toNat
  let rs1 := ((w >>> 15) &&& 0x1f).toNat
  let rs2 := ((w >>> 20) &&& 0x1f).toNat
  let a := symRegVal regs out rs1
  let b := symRegVal regs out rs2
  match f3 with
  | 0 => s!"(= {a} {b})"
  | 1 => s!"(not (= {a} {b}))"
  | 4 => s!"(< {a} {b})"
  | 5 => s!"(>= {a} {b})"
  | 6 => s!"(< {a} {b})"
  | _ => s!"(>= {a} {b})"

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
    | some (Term.jalr _ _) => pure ()         -- indirect call/ret: caller resumes
    | some (Term.branch target) =>
      let s := s!"branch_{target}"; summaries := s :: summaries; cur := s!"({s} {cur})"
    | _ => pure ()
  return (cur, summaries.eraseDups)

/-- Find a callee's exit: scan from `entry` for the first `ret` — `jalr x0, 0(ra)`,
i.e. JALR with rd = x0 AND rs1 = x1.  A `jalr x0, 0(rN)` for any other `rN` is a
COMPUTED GOTO (the interpreter's AST-kind jump tables dispatch that way at
`0x800031ac` / `0x80004030`); stopping there truncates the callee at its
dispatch header.  Bounded by `maxLen` words. -/
def findRet (img : Nat → Option (BitVec 8)) (entry : Nat) (maxLen : Nat := 4096) : Nat := Id.run do
  let mut pc := entry
  let mut n := 0
  while n < maxLen do
    let w := wordAt img pc
    if opcode w == 0x67 && ((w >>> 7) &&& 0x1f).toNat == 0
        && ((w >>> 15) &&& 0x1f).toNat == 1 then return pc + 4
    pc := pc + 4; n := n + 1
  return pc

/-- Find a loop's back-edge: from head `t`, the first terminator whose target is
`≤ t` (the branch/jump that closes the loop).  Returns that terminator's PC. -/
def findBackEdge (img : Nat → Option (BitVec 8)) (t : Nat) (maxLen : Nat := 4096) : Nat := Id.run do
  let mut pc := t + 4
  let mut n := 0
  while n < maxLen do
    let w := wordAt img pc
    if isTerm w then
      match decodeTerm pc w with
      | Term.jal rd tgt => if rd != 1 && tgt ≤ t then return pc
      | Term.branch tgt => if tgt ≤ t then return pc
      | _ => pure ()
    pc := pc + 4; n := n + 1
  return pc

/-- **Ground indirect-dispatch sites** — `(jalr PC, jump-table base, arm count)`.

The interpreter dispatches on an AST kind through a rodata table of 32-bit
self-relative offsets: `arm k = base + (int32) table[k]`.  Both tables are the
PINNED ones the proof fixes (`Vsa.Sim.KindTablePins` at `0x80019f58`,
`StmtTablePins` at `0x80019fb8`, supplied by
`Vsa.Sim.Rows.{kind,stmt}TablePins_of_bytes` from the loaded image), and the arm
addresses this resolves to are exactly the proof's `evalArm*`/`execArm*`
constants.  A `jalr x0` at a PC NOT listed here is reflected as a named opaque
per-site summary rather than silently ending the path. -/
def dispatchSites : List (Nat × Nat × Nat) :=
  [ (0x800031ac, 0x80019f58, 10)     -- eval_expr: 10 `Expr` kind arms
  , (0x80003558, 0x80019f84, 13)     -- the binary/logical operator sub-dispatch
                                     --   (`binOpTok` 11…23 → 13 table entries,
                                     --   the table running up to the `Stmt` one)
  , (0x80004030, 0x80019fb8, 9) ]    -- exec_stmt: 9 `Stmt` kind arms

/-- **Entry-ground pins**, as SMT over the entry memory `mm s0`.

The three AST-kind jump tables' rodata words (the `KindTablePins`/`StmtTablePins`
half of `EvalEntry.ground`) plus the stack/arena layout facts `EvalEntry` carries
(`stackOK`/`stackBudget` and arena-stack disjointness).  Without the table words a
resolved dispatch guard cannot decide, and without the layout facts a heap
pointer read out of unconstrained memory can alias the caller's frame — so the
frame conjunct is refutable for reasons that have nothing to do with the arm.
This is the residual's PRE, encoded, not an assumption added for convenience. -/
def entryPinsSmt (img : Nat → Option (BitVec 8)) : String := Id.run do
  let mut out : List String := []
  for (_, base, n) in dispatchSites do
    for k in List.range n do
      let a := base + 4 * k
      let w := (wordAt img a).toNat
      out := out ++ [s!"(assert (= (ld4 (mm s0) {bvN a}) {bvN w}))"]
  let layout := [
    "; EvalEntry.stackBudget / stackOK: sp sits inside the stack with headroom",
    s!"(assert (bvule (bvadd SL_lo {bvN 4352}) {stR "s0" 2}))",
    s!"(assert (bvule {stR "s0" 2} SL_hi))",
    "; the arm's own frame lies ABOVE sp and inside the stack too: the span starts",
    "; after the prologue has lowered sp, so its spills are at sp+k for k < frame,",
    "; and those belong to the frame the caller's own `StackOK` already placed",
    s!"(assert (bvule (bvadd {stR "s0" 2} #x0000000000001100) SL_hi))",
    "(assert (bvult SL_lo SL_hi))",
    "; the heap arena is disjoint from the stack window",
    "(assert (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)))",
    "(assert (bvult A_lo A_hi))",
    "; `InterpCodeLoaded`: the code image is disjoint from BOTH — without this the",
    "; code-preservation post cannot even be stated (an address in the code region",
    "; would be allowed to sit inside the stack)",
    "(assert (or (bvult SL_hi #x0000000080000000) (bvuge SL_lo #x0000000080018be0)))",
    "(assert (or (bvult A_hi #x0000000080000000) (bvuge A_lo #x0000000080018be0)))",
    "; the stack sits above the first megabyte, so `sp - frame` cannot underflow,",
    "; and both regions are inside the 4 GB the HTIF image addresses, so `sp + frame`",
    "; cannot wrap either (without this the solver puts the stack at the top of the",
    "; address space and wraps a spill into the code image)",
    "(assert (bvule #x0000000000100000 SL_lo))",
    "(assert (bvult SL_hi #x0000000100000000))",
    "(assert (bvult A_hi #x0000000100000000))" ]
  return String.intercalate "\n" (out ++ layout)

/-- Read a 32-bit little-endian SIGNED word (the jump-table entries are
self-relative offsets). -/
def sword32 (img : Nat → Option (BitVec 8)) (va : Nat) : Int :=
  let w := (wordAt img va).toNat
  if w ≥ 2147483648 then (w : Int) - 4294967296 else (w : Int)

/-- The arm targets of the dispatch at `p`, read out of the ELF's jump table. -/
def dispatchArms (img : Nat → Option (BitVec 8)) (p : Nat) : Option (List Nat) :=
  match dispatchSites.find? (fun (q, _, _) => q == p) with
  | none => none
  | some (_, base, n) =>
    some ((List.range n).map (fun k => ((base : Int) + sword32 img (base + 4 * k)).toNat))

/-- Emit the fold/unfold axiom for every summary symbol, recursively.  A
`callee_<t>` axiom is the callee's OWN `reflectStepsMulti` (recursion bottoms out
at leaves); a symbol seen again is genuinely RECURSIVE ⇒ left as an uninterpreted
`Array→Array` function (its own unfold axiom, define-fun-rec style — Z3's
datatype recursion).  `loop_/branch_` summaries are declared and flagged as
needing the mined invariant.  Returns the axiom block + the still-open
(loop/recursive) summaries. -/
partial def emitAxioms (img : Nat → Option (BitVec 8)) (regs : List Nat)
    (worklist : List String) (visited : List String) (acc : List String) :
    List String × List String := Id.run do
  match worklist with
  | [] => (acc, visited)
  | s :: rest =>
    if visited.contains s then emitAxioms img regs rest visited acc
    else
      let visited := s :: visited
      if s.startsWith "callee_" then
        let t := (s.drop 7).toNat!
        let exit := findRet img t
        let (body, subs) := reflectStepsMulti img regs t exit
        -- axiom: ∀ mem, s(mem) = body[mem]   (declarations emitted separately)
        let ax := s!"(assert (forall ((mem (Array Int (_ BitVec 8)))) (= ({s} mem) {body})))"
        emitAxioms img regs (subs ++ rest) visited (acc ++ [ax])
      else if s.startsWith "loop_" then
        -- loop: recursive memory effect.  body = [t, back-edge); one iteration's
        -- write-log, then recurse until the exit test `loopcond_t` holds.  This is
        -- the faithful define-fun-rec (Z3 datatype recursion); the mined invariant
        -- is a DECIDABILITY aid, not part of the (gap-free) encoding.
        let t := (s.drop 5).toNat!
        let back := findBackEdge img t
        let (body, subs) := reflectStepsMulti img regs t back
        let ax := s!"(assert (forall ((mem (Array Int (_ BitVec 8)))) (= ({s} mem) (ite (loopcond_{t} mem) mem ({s} {body})))))"
        emitAxioms img regs (subs ++ rest) visited (acc ++ [ax])
      else
        -- branch: two-way join; the mem-effect is one arm's write-log or the other
        emitAxioms img regs rest visited acc

/-- Branch condition over a SYMBOLIC register map (threaded state), not the
concrete `runGM`.  Exact for register-carried operands. -/
def branchCondSym (rf : Nat → String) (w : BitVec 32) : String :=
  let f3 := ((w >>> 12) &&& 7).toNat
  let a := rf (((w >>> 15) &&& 0x1f).toNat)
  let b := rf (((w >>> 20) &&& 0x1f).toNat)
  match f3 with
  | 0 => s!"(= {a} {b})"       | 1 => s!"(not (= {a} {b}))"
  | 4 => s!"(bvslt {a} {b})"   | 5 => s!"(bvsge {a} {b})"     -- blt / bge (signed)
  | 6 => s!"(bvult {a} {b})"   | _ => s!"(bvuge {a} {b})"     -- bltu / bgeu

/-- Clobber caller-saved registers across a call (ABI: a0 = return value symbol,
ra/t*/a* fresh).  Callee-saved (sp, s0-s11, gp, tp) preserved. -/
def clobber (target : Nat) (rf : Nat → String) : Nat → String :=
  let saved : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  fun n => if n == 10 then s!"(callret_{target} {n})" else if saved.contains n then rf n
           else s!"clob_{target}_{n}"

/-- Path-aware reflection: follow the CFG from `pc`, threading BOTH the memory
term and the symbolic register map.  Branches become exact `ite`s over
`branchCondSym`; calls apply a callee summary + ABI clobber; loops/backedges emit
a `loop_` summary; `ret`/`hi` end the path.  `fuel` bounds path length (cycles go
through `loop_` summaries, so forward recursion terminates). -/
partial def reflectPath (img : Nat → Option (BitVec 8)) (regs : List Nat) (hi fuel : Nat)
    (pc : Nat) (mem : String) (rf : Nat → String) :
    String × (Nat → String) × List String := Id.run do
  if fuel == 0 then return (mem, rf, [])
  -- accumulate a straight-line block until a terminator or hi
  let mut cur : List MInstr := []
  let mut p := pc
  while p < hi && !(isTerm (wordAt img p)) do
    cur := cur ++ [mkLine (BitVec.ofNat 64 p) (wordAt img p)]
    p := p + 4
  let mem1 := appendBlockLog regs mem cur
  let rf1 := symRun mem rf cur
  if p ≥ hi then return (mem1, rf1, [])
  let w := wordAt img p
  match decodeTerm p w with
  | Term.branch tgt =>
    if tgt ≤ pc then
      let s := s!"loop_{tgt}"
      return (s!"({s}_m {mem1})", (fun n => s!"({s}_r{n} {mem1})"), [s])
    else
      let (tk, tkr, s1) := reflectPath img regs hi (fuel-1) tgt mem1 rf1
      let (fl, flr, s2) := reflectPath img regs hi (fuel-1) (p+4) mem1 rf1
      let cond := branchCondSym rf1 w
      return (s!"(ite {cond} {tk} {fl})",
              (fun n => s!"(ite {cond} {tkr n} {flr n})"), (s1 ++ s2).eraseDups)
  | Term.jal rd tgt =>
    if rd != 1 && tgt ≤ pc then
      let s := s!"loop_{tgt}"
      return (s!"({s}_m {mem1})", (fun n => s!"({s}_r{n} {mem1})"), [s])
    else if rd == 1 then
      -- call: callee summary maps (mem,args) → mem'; a0 return = callee_ret; other
      -- caller-saved clobbered, callee-saved preserved.
      let s := s!"callee_{tgt}"
      let saved : List Nat := [2,3,4,8,9,18,19,20,21,22,23,24,25,26,27]
      let rf2 : Nat → String := fun n =>
        if n == 10 then s!"({s}_ret {mem1})" else if saved.contains n then rf1 n
        else s!"({s}_c{n} {mem1})"
      reflectPath img regs hi (fuel-1) (p+4) s!"({s}_m {mem1})" rf2
    else
      reflectPath img regs hi (fuel-1) tgt mem1 rf1     -- plain jump
  | Term.jalr _ _ => return (mem1, rf1, [])             -- ret
  | Term.sys    => return (mem1, rf1, [])

/-- Assemble the COMPLETE reflected `Steps` SMT for span `[lo,hi)`: register
decls, the entry memory, every callee summary's fold/unfold axiom (recursively
closed), the loop/branch summary declarations, and `mem_exit` = the composed
write-log.  A well-formed SMT-LIB2 preamble Z3 consumes; the residual's own
pre/post conjuncts are appended by the caller to form the validity query. -/
def reflectFullSmt (regs : List Nat) (lo hi : Nat) : IO String := do
  let img ← loadElf elfPath
  let (memExit, _, summaries) := reflectPath img regs hi 200 lo "mem" (fun n => regName n)
  let (axs, visited) := emitAxioms img regs summaries [] []
  let decls := String.intercalate "\n" (regs.map (fun r => s!"(declare-fun {regName r} () Int)"))
  -- ALL summary symbols declared first (any body may reference a later one);
  -- each loop_<t> also needs its exit-test predicate loopcond_<t>.
  let sumDecls := String.intercalate "\n" (visited.flatMap (fun s =>
    let f := s!"(declare-fun {s} ((Array Int (_ BitVec 8))) (Array Int (_ BitVec 8)))"
    if s.startsWith "loop_" then
      [f, s!"(declare-fun loopcond_{s.drop 5} ((Array Int (_ BitVec 8))) Bool)"]
    else [f]))
  let axBlock := String.intercalate "\n" axs
  -- load / bitwise / ABI-clobber helpers as uninterpreted functions (consistent
  -- reads; exact address arithmetic is in the terms themselves)
  let helpers := "(declare-fun loadw ((Array Int (_ BitVec 8)) Int) Int)\n(declare-fun loadb ((Array Int (_ BitVec 8)) Int) Int)\n(declare-fun bvor_i (Int Int) Int)\n(declare-fun bvand_i (Int Int) Int)\n(declare-fun bvxor_i (Int Int) Int)"
  return s!"(set-logic ALL)\n; === reflected Steps for span [{lo},{hi}) ===\n{decls}\n(declare-fun mem () (Array Int (_ BitVec 8)))\n{helpers}\n{sumDecls}\n{axBlock}\n(define-fun mem_exit () (Array Int (_ BitVec 8)) {memExit})\n"

-- ==========================================================================
-- EXACT state-threaded reflection.  Machine state = one datatype
--   MState = (mm : Array Int BV8, rr : Array Int Int).
-- Every register outcome comes from the callee's OWN reflection (no ABI
-- approximation); loads read the actual memory array (exact byte assembly).
-- ==========================================================================

/-- Store the low-`w` bytes of Int value `v` at Int address `a` into a mem term. -/
def storeBytes (mem a v : String) (w : Nat) : String := Id.run do
  let mut m := mem
  for j in List.range w do
    let hi := 8 * j + 7
    let lo := 8 * j
    m := s!"(store {m} (bvadd {a} {bvN j}) ((_ extract {hi} {lo}) {v}))"
  return m

/-- Signed U-type value (bits 31..12 << 12), from the full word. -/
def uimm (i : MInstr) : Int :=
  let u := (i.word &&& 0xfffff000).toNat
  if u ≥ 2147483648 then (u : Int) - 4294967296 else (u : Int)

/-- Shift amount = word bits 25..20 (6-bit for RV64 register-immediate shifts). -/
def shamt (i : MInstr) : Nat := ((i.word >>> 20) &&& 0x3f).toNat

/-- rd's new symbolic Int value for a register-producing instruction (over the
current reg map `rf` and mem term `mem`); `none` for stores/control.  EXACT for
every register-producing MKind (immediates from the full word; shifts via BV). -/
def regValExact (rf : Nat → String) (mem : String) (i : MInstr) : Option String :=
  let a := rf i.rs1
  let b := rf i.rs2
  let im := bv64 (imm12 i.imm)
  let sh := bvN (shamt i)
  let addr := s!"(bvadd {a} {im})"
  match i.kind with
  | .addi  => some s!"(bvadd {a} {im})"
  | .add   => some s!"(bvadd {a} {b})"
  | .sub   => some s!"(bvsub {a} {b})"
  -- the *W forms are 32-bit ops sign-extended back to 64; the Int encoding
  -- treated them as their 64-bit siblings, which is wrong on overflow
  | .addiw => some s!"(w32 (bvadd {a} {im}))"
  | .addw  => some s!"(w32 (bvadd {a} {b}))"
  | .subw  => some s!"(w32 (bvsub {a} {b}))"
  | .lui   => some (bv64 (uimm i))
  | .auipc => some (bv64 (Int.ofNat i.pc.toNat + uimm i))
  | .slti  => some s!"(ite (bvslt {a} {im}) {bvN 1} {bvN 0})"
  | .slt   => some s!"(ite (bvslt {a} {b}) {bvN 1} {bvN 0})"
  | .or    => some s!"(bvor {a} {b})"
  | .and   => some s!"(bvand {a} {b})"
  | .xor   => some s!"(bvxor {a} {b})"
  | .andi  => some s!"(bvand {a} {im})"
  | .ori   => some s!"(bvor {a} {im})"
  | .xori  => some s!"(bvxor {a} {im})"
  | .slli  => some s!"(bvshl {a} {sh})"
  | .srli  => some s!"(bvlshr {a} {sh})"
  | .srai  => some s!"(bvashr {a} {sh})"
  | .slliw => some s!"(w32 (bvshl {a} {sh}))"
  | .srliw => some s!"(w32 ((_ zero_extend 32) (bvlshr ((_ extract 31 0) {a}) ((_ extract 31 0) {sh}))))"
  | .sraiw => some s!"(w32 ((_ sign_extend 32) (bvashr ((_ extract 31 0) {a}) ((_ extract 31 0) {sh}))))"
  | .sll   => some s!"(bvshl {a} (bvand {b} {bvN 63}))"
  | .srl   => some s!"(bvlshr {a} (bvand {b} {bvN 63}))"
  | .sllw  => some s!"(w32 (bvshl {a} (bvand {b} {bvN 31})))"
  | .srlw  => some s!"(w32 ((_ zero_extend 32) (bvlshr ((_ extract 31 0) {a}) ((_ extract 31 0) (bvand {b} {bvN 31})))))"
  | .sraw  => some s!"(w32 ((_ sign_extend 32) (bvashr ((_ extract 31 0) {a}) ((_ extract 31 0) (bvand {b} {bvN 31})))))"
  | .ld    => some s!"(ld8 {mem} {addr})"
  | .lw    => some s!"(ld4s {mem} {addr})"
  | .lwu   => some s!"(ld4 {mem} {addr})"
  | .lh    => some s!"(ld2s {mem} {addr})"
  | .lhu   => some s!"(ld2 {mem} {addr})"
  | .lbu   => some s!"(ld1 {mem} {addr})"
  | _      => none

/-- Exact execution of a straight-line block over state term `S` → new state
term.  Stores update `mm`; register writes update `rr`; both exact. -/
def blockState (S : String) (instrs : List MInstr) : String := Id.run do
  let mut mem := s!"(mm {S})"
  let mut rf : Nat → String := fun n => stR S n
  let mut changed : List Nat := []
  for i in instrs do
    match i.kind with
    | .sd => mem := storeBytes mem s!"(bvadd {rf i.rs1} {bv64 (imm12 i.imm)})" (rf i.rs2) 8
    | .sw => mem := storeBytes mem s!"(bvadd {rf i.rs1} {bv64 (imm12 i.imm)})" (rf i.rs2) 4
    | .sh => mem := storeBytes mem s!"(bvadd {rf i.rs1} {bv64 (imm12 i.imm)})" (rf i.rs2) 2
    | .sb => mem := storeBytes mem s!"(bvadd {rf i.rs1} {bv64 (imm12 i.imm)})" (rf i.rs2) 1
    | _ =>
      match regValExact rf mem i with
      | some v => if i.rd != 0 then do
                    let old := rf; rf := (fun n => if n == i.rd then v else old n)
                    changed := i.rd :: changed
      | none => pure ()
  let regsArr := changed.eraseDups.foldl (fun ra n => s!"(store {ra} {bvN n} {rf n})") s!"(rr {S})"
  return s!"(mst {mem} {regsArr})"

/-- The block-start successors of the block at `pc` (control-flow only, no state).
Used for the reachability pass that turns a loop into a `loop_<header>` summary. -/
def blockSuccs (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat) (pc : Nat) : List Nat := Id.run do
  let mut p := pc
  while p < hi && !(stops.contains p) && !(isTerm (wordAt img p)) do p := p + 4
  if p ≥ hi || stops.contains p then return []
  let w := wordAt img p
  let inR := fun (q : Nat) => lo ≤ q && q < hi && !(stops.contains q)
  match decodeTerm p w with
  | Term.branch tgt => (if inR tgt then [tgt] else []) ++ (if inR (p+4) then [p+4] else [])
  | Term.jal rd tgt =>
    if rd == 1 then (if inR (p+4) then [p+4] else [])
    else if inR tgt then [tgt] else []
  | Term.jalr rd rs1 =>
    if rd == 1 then (if inR (p+4) then [p+4] else [])
    else if rs1 == 1 then []
    else match dispatchArms img p with
         | some arms => arms.filter inR
         | none => []
  | Term.sys => if inR (p+4) then [p+4] else []

/-- Every block start reachable from `src` (bounded by `fuel` blocks). -/
partial def reachFrom (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat)
    (work seen : List Nat) (fuel : Nat) : List Nat :=
  match fuel, work with
  | 0, _ => seen
  | _, [] => seen
  | f+1, q :: rest =>
    if seen.contains q then reachFrom img lo hi stops rest seen f
    else reachFrom img lo hi stops (blockSuccs img lo hi stops q ++ rest) (q :: seen) f

/-- Can control get from `src` back to `h`?  This is what distinguishes a loop's
BODY edges from its EXIT edges: after `loop_<h>` has run the loop to completion,
the exit continuation is exactly the successors that can no longer reach `h`. -/
def canReach (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat) (src h : Nat) : Bool :=
  (reachFrom img lo hi stops [src] [] 4000).contains h

/-- The natural loop of header `h`, in ONE backward pass.

The obvious definition — "every block reachable from `h` that can get back to
`h`" — invites a `canReach` call per node, which is a fresh forward exploration
each time and quadratic in the function; on `eval_expr` that alone stalled the
emitter.  Build the successor map over the forward-reachable set once, then walk
it BACKWARD from `h`. -/
def loopBody (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat) (h : Nat) :
    List Nat := Id.run do
  let fwd := reachFrom img lo hi stops [h] [] 4000
  let edges := fwd.map (fun b => (b, blockSuccs img lo hi stops b))
  let mut body : List Nat := [h]
  let mut work : List Nat := [h]
  let mut fuel := 4000
  while !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let q := work.head!
    work := work.tail!
    for (b, ss) in edges do
      if ss.contains q && !(body.contains b) then
        body := b :: body
        work := work ++ [b]
  return body

/-- Where a loop can go when it is done: every successor of a body block that is
not itself in the body (the loop's EXIT edges), plus a flag for "some body block
leaves the region outright" (a `ret` inside the loop). -/
def loopExits (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat) (h : Nat) :
    List Nat × Bool :=
  let body := loopBody img lo hi stops h
  let qs := (body.flatMap (blockSuccs img lo hi stops)).eraseDups.filter
    (fun q => !(body.contains q))
  let leaves := body.any (fun b => (blockSuccs img lo hi stops b).isEmpty)
  (qs, leaves)

/-- Per-INSTRUCTION `let`-bound block execution.  `blockState` builds one term
per block, which is quadratic in practice: every load in the block references the
whole accumulated memory term, and every register read inlines the expression
that produced it, so a ten-instruction block with a dependent chain is already
kilobytes and a forty-round frontier is tens of megabytes.  Binding each
instruction's state makes the block linear — every term references only the
previous instruction's variable. -/
def blockBinds (S : String) (instrs : List MInstr) (k : Nat) :
    String × Nat × List String × List (String × Nat) := Id.run do
  let mut cur := S
  let mut k := k
  let mut binds : List String := []
  let mut writes : List (String × Nat) := []
  for i in instrs do
    -- the store FOOTPRINT, recorded as address + width.  Frame, `StoreRepr`
    -- survival and code preservation are all "this address was not written", and
    -- with the footprint in hand that is BV ARITHMETIC over a few hundred
    -- addresses — not array theory over a chain of `store`s, which bit-blasts to
    -- millions of bit2core axioms and decides nothing.
    let w : Nat := match i.kind with
      | .sd => 8 | .sw => 4 | .sh => 2 | .sb => 1 | _ => 0
    if w != 0 then
      writes := writes ++ [(s!"(bvadd {stR cur i.rs1} {bv64 (imm12 i.imm)})", w)]
    let nxt := s!"i{k}"
    binds := binds ++ [s!"({nxt} {blockState cur [i]})"]
    cur := nxt
    k := k + 1
  return (cur, k, binds, writes)

/-- Branch condition over state `S` (exact register comparison). -/
def branchCondSt (S : String) (w : BitVec 32) : String :=
  let f3 := ((w >>> 12) &&& 7).toNat
  let a := stR S (((w >>> 15) &&& 0x1f).toNat)
  let b := stR S (((w >>> 20) &&& 0x1f).toNat)
  match f3 with
  | 0 => s!"(= {a} {b})"      | 1 => s!"(not (= {a} {b}))"   -- beq  / bne
  | 4 => s!"(bvslt {a} {b})"  | 5 => s!"(bvsge {a} {b})"     -- blt  / bge  (signed)
  | 6 => s!"(bvult {a} {b})"  | _ => s!"(bvuge {a} {b})"     -- bltu / bgeu (unsigned)

/-- EXACT path reflection threading the whole `MState`.  Branches → `ite` on the
exact condition; calls/loops → `State→State` summary (its axiom is the callee/
loop body's OWN reflection — no ABI); ret/hi end.  Returns `(exitStateTerm,
summaries)`. -/
partial def reflectExact (img : Nat → Option (BitVec 8)) (hi fuel : Nat)
    (pc : Nat) (S : String) : String × List String := Id.run do
  if fuel == 0 then return (S, [])
  let mut cur : List MInstr := []
  let mut p := pc
  while p < hi && !(isTerm (wordAt img p)) do
    cur := cur ++ [mkLine (BitVec.ofNat 64 p) (wordAt img p)]
    p := p + 4
  let S1 := blockState S cur
  if p ≥ hi then return (S1, [])
  let w := wordAt img p
  match decodeTerm p w with
  | Term.branch tgt =>
    if tgt ≤ pc then let s := s!"loop_{tgt}"; return (s!"({s} {S1})", [s])
    else
      let (tk, s1) := reflectExact img hi (fuel-1) tgt S1
      let (fl, s2) := reflectExact img hi (fuel-1) (p+4) S1
      return (s!"(ite {branchCondSt S1 w} {tk} {fl})", (s1 ++ s2).eraseDups)
  | Term.jal rd tgt =>
    -- rd = x1 is a CALL whatever the direction (a backward `jal ra` is a call to
    -- an earlier-defined function, NOT a loop back-edge); only `j` (rd = x0)
    -- closes a loop.
    if rd == 1 then
      let s := s!"callee_{tgt}"
      let (rest, s2) := reflectExact img hi (fuel-1) (p+4) s!"({s} {S1})"
      return (rest, (s :: s2).eraseDups)
    else if tgt ≤ pc then let s := s!"loop_{tgt}"; return (s!"({s} {S1})", [s])
    else reflectExact img hi (fuel-1) tgt S1
  | Term.jalr _ _ => return (S1, [])
  | Term.sys    => return (S1, [])

/-- DAG reflection: thread a state VARIABLE (not the full term) and accumulate
`let`-bindings, so shared states are emitted once — branch arms merge at the join
via `ite` over bound vars (no tail duplication), collapsing the exponential blowup
to linear size.  Returns `(exitVar, nextK, binds, summaries)`. -/
partial def reflectExactD (img : Nat → Option (BitVec 8)) (hi fuel : Nat) (pc : Nat)
    (sv : String) (k : Nat) (binds sums : List String) :
    String × Nat × List String × List String := Id.run do
  if fuel == 0 then return (sv, k, binds, sums)
  let mut cur : List MInstr := []
  let mut p := pc
  while p < hi && !(isTerm (wordAt img p)) do
    cur := cur ++ [mkLine (BitVec.ofNat 64 p) (wordAt img p)]
    p := p + 4
  let v := s!"s{k}"
  let binds := binds ++ [s!"({v} {blockState sv cur})"]
  let k := k + 1
  if p ≥ hi then return (v, k, binds, sums)
  let w := wordAt img p
  match decodeTerm p w with
  | Term.branch tgt =>
    if tgt ≤ pc then
      let lv := s!"s{k}"
      return (lv, k+1, binds ++ [s!"({lv} (loop_{tgt} {v}))"], (s!"loop_{tgt}" :: sums).eraseDups)
    else
      -- structured if: fallthrough [p+4,tgt) is the then-block; join at tgt
      let (thenV, k1, b1, s1) := reflectExactD img tgt (fuel-1) (p+4) v k binds sums
      let mv := s!"s{k1}"
      let b2 := b1 ++ [s!"({mv} (ite {branchCondSt v w} {v} {thenV}))"]
      reflectExactD img hi (fuel-1) tgt mv (k1+1) b2 s1
  | Term.jal rd tgt =>
    -- rd = x1 is a CALL whatever the direction (see `reflectExact`).
    if rd == 1 then
      let cv := s!"s{k}"
      reflectExactD img hi (fuel-1) (p+4) cv (k+1)
        (binds ++ [s!"({cv} (callee_{tgt} {v}))"]) ((s!"callee_{tgt}" :: sums).eraseDups)
    else if tgt ≤ pc then
      let lv := s!"s{k}"
      return (lv, k+1, binds ++ [s!"({lv} (loop_{tgt} {v}))"], (s!"loop_{tgt}" :: sums).eraseDups)
    else reflectExactD img hi (fuel-1) tgt v k binds sums
  | Term.jalr rd rs1 =>
    if rd == 1 then
      -- indirect CALL through a register (a native function pointer): the target
      -- is not statically known, so ONE named opaque summary per site.
      let cv := s!"s{k}"
      return (cv, k+1, binds ++ [s!"({cv} (icall_{p} {v}))"], (s!"icall_{p}" :: sums).eraseDups)
    else if rs1 == 1 then (v, k, binds, sums)                     -- ret
    else match dispatchArms img p with
    | some arms =>
      -- ground jump-table dispatch: reflect EVERY arm from the dispatch state and
      -- select on the computed target (which the pinned table forces to be one of
      -- them).  The arms' `let`-bindings are pure, so binding them all is free.
      let mut bs := binds; let mut kk := k; let mut ss := sums
      let mut exits : List (Nat × String) := []
      for a in arms do
        let (ev, k', b', s') := reflectExactD img hi (fuel-1) a v kk bs ss
        bs := b'; kk := k'; ss := s'; exits := exits ++ [(a, ev)]
      let mut acc := v
      for (a, ev) in exits.reverse do
        let nv := s!"s{kk}"
        bs := bs ++ [s!"({nv} (ite (= {stR v rs1} {a}) {ev} {acc}))"]
        acc := nv; kk := kk + 1
      return (acc, kk, bs, ss)
    | none =>
      -- an unlisted computed goto: named opaque summary, NOT a silent path end.
      let dv := s!"s{k}"
      return (dv, k+1, binds ++ [s!"({dv} (idisp_{p} {v}))"], (s!"idisp_{p}" :: sums).eraseDups)
  | Term.sys    => return (v, k, binds, sums)

-- ==========================================================================
-- PC-THREADED MACHINE REFLECTION — the ground truth.
--
-- The block-DAG reflector above is an optimisation that only reflects the
-- STRUCTURED cases exactly: it needs a forward branch to reconverge, a `jal ra`
-- to return, a backward edge to be a real loop back-edge, and it drops whatever
-- follows a loop.  Real compiled code breaks all four (a shared epilogue reached
-- by a backward `j`, a multi-exit loop, a computed goto).
--
-- `Steps` is just the reflexive-transitive closure of ONE step, so reflect ONE
-- step exactly and close it recursively.  The PC lives in `rr` at index 32 (not
-- a machine register), and `mstep` is a flat `ite` over every PC in the region —
-- so a computed goto, a backward `j`, a multi-exit loop and an irreducible
-- region all reflect with NO control-flow analysis at all: `mstep` dispatches on
-- whatever PC value the instruction produced.  Size is linear in the region.
--
-- An instruction whose `MKind` the value reflector does not model becomes a
-- NAMED per-site uninterpreted `unmodelled_<pc>` result rather than a silent
-- no-op — an over-approximation (sound for validity: proving the post against
-- every possible value proves it against the real one), and a reported one.
-- ==========================================================================

/-- The PC slot in `rr` (32 is past the 32 machine registers). -/
def pcIdx : Nat := 32

/-- The PC of state term `S`. -/
def stPC (S : String) : String := stR S pcIdx

/-- Sign-extended I-type immediate (bits 31..20) of a raw word. -/
def immI (w : BitVec 32) : Int :=
  let u := ((w >>> 20) &&& 0xfff).toNat
  if u ≥ 2048 then (u : Int) - 4096 else (u : Int)

/-- Register-producing encodings the proof's `decodeM` table does not carry.

Over this image that is exactly the UNSIGNED set-less-than pair — `sltiu`
(op `0x13`, funct3 `3`) and `sltu` (op `0x33`, funct3 `3`, funct7 `0`) — 30 sites,
2 of them inside `eval_expr` (`sltiu a1, a0, 1`, the `x == 0` test).  Modelling
them here rather than falling back to the opaque successor makes the whole
region's register effect EXACT.  Unsigned comparison goes through the bitvector
theory, like every other unsigned operation in this file. -/
def rawRegVal (S : String) (w : BitVec 32) : Option (Nat × String) :=
  let op := opcode w
  let f3 := ((w >>> 12) &&& 7).toNat
  let f7 := ((w >>> 25) &&& 0x7f).toNat
  let rd := ((w >>> 7) &&& 0x1f).toNat
  let rs1 := ((w >>> 15) &&& 0x1f).toNat
  let rs2 := ((w >>> 20) &&& 0x1f).toNat
  if op == 0x13 && f3 == 3 then
    some (rd, s!"(ite (bvult {stR S rs1} {bv64 (immI w)}) {bvN 1} {bvN 0})")
  else if op == 0x33 && f3 == 3 && f7 == 0 then
    some (rd, s!"(ite (bvult {stR S rs1} {stR S rs2}) {bvN 1} {bvN 0})")
  else none

/-- Is this word's effect modelled EXACTLY?

Two ways it can fail, and both must be caught: `decodeM` may not recognise the
word at all (`mkLine` then falls back to `addi x0, x0, 0` — a silent NOP, which
would be an unsound "the machine did nothing" claim), or the kind may decode but
have no `regValExact` value (`mul`/`div`/…).  Either way the site becomes the
shared opaque `unmodelled_step`, which is an over-approximation: proving the post
against EVERY possible successor state proves it against the real one. -/
def modelled (p : Nat) (w : BitVec 32) : Bool :=
  match decodeM w with
  | none => false
  | some _ =>
    let i := mkLine (BitVec.ofNat 64 p) w
    match i.kind with
    | .sd | .sw | .sh | .sb => true
    | _ => (regValExact (fun n => s!"r{n}") "m" i).isSome || i.rd == 0

/-- ONE instruction's EXACT effect on the whole state, PC included.  Returns the
new state term, the summary symbols it introduces, and whether it was modelled.
A `jal ra` leaving `[lo,hi)` applies that callee's summary and lands at `p+4`. -/
def stepArm (img : Nat → Option (BitVec 8)) (lo hi : Nat) (S : String) (p : Nat) :
    String × List String × Bool := Id.run do
  let w := wordAt img p
  let setPC (st : String) (v : String) : String :=
    s!"(mst (mm {st}) (store (rr {st}) {bvN pcIdx} {v}))"
  if !(isTerm w) then
    let base := blockState S [mkLine (BitVec.ofNat 64 p) w]
    if modelled p w then return (setPC base (bvN (p+4)), [], true)
    else match rawRegVal S w with
    | some (rd, v) =>
      let regs := if rd == 0 then s!"(rr {S})" else s!"(store (rr {S}) {bvN rd} {v})"
      return (s!"(mst (mm {S}) (store {regs} {bvN pcIdx} {bvN (p+4)}))", [], true)
    | none =>
      -- unmodelled: the SHARED opaque successor (the state carries the PC, so
      -- distinct sites can still behave distinctly).  Over-approximate, sound.
      return (s!"(unmodelled_step {S})", [], false)
  match decodeTerm p w with
  | Term.branch tgt =>
    return (setPC S s!"(ite {branchCondSt S w} {bvN tgt} {bvN (p+4)})", [], true)
  | Term.jal rd tgt =>
    if lo ≤ tgt && tgt < hi then
      let r1 := if rd == 0 then s!"(rr {S})" else s!"(store (rr {S}) {bvN rd} {bvN (p+4)})"
      return (s!"(mst (mm {S}) (store {r1} {bvN pcIdx} {bvN tgt}))", [], true)
    else
      -- out-of-region call: the callee's summary, then land after the call site
      let sym := s!"callee_{tgt}"
      let st := s!"({sym} {S})"
      let r1 := if rd == 0 then s!"(rr {st})" else s!"(store (rr {st}) {bvN rd} {bvN (p+4)})"
      return (s!"(mst (mm {st}) (store {r1} {bvN pcIdx} {bvN (p+4)}))", [sym], true)
  | Term.jalr rd rs1 =>
    -- EXACT: the target is the computed value with bit 0 cleared.  `ret`
    -- (rd=0, rs1=ra) and the AST-kind computed gotos are the SAME rule here.
    let v := s!"(bvadd {stR S rs1} {bv64 (immI w)})"
    let tgt := s!"(bvand {v} {bv64 (-2)})"
    let r1 := if rd == 0 then s!"(rr {S})" else s!"(store (rr {S}) {bvN rd} {bvN (p+4)})"
    return (s!"(mst (mm {S}) (store {r1} {bvN pcIdx} {tgt}))", [], true)
  | Term.sys => return (setPC S (bvN (p+4)), [], true)

/-- Dispatch on the PC by BALANCED BINARY SEARCH rather than a linear `ite`
chain: a region of `n` instructions gives depth `log2 n` instead of `n`, which
keeps the SMT parser off its recursion limit and gives Z3 a term it can resolve
in `log n` case splits once the PC is known. -/
partial def balancedDispatch (arms : List (Nat × String)) : String :=
  match arms with
  | [] => "S"
  | [(q, t)] => s!"(ite (= {stPC "S"} {bvN q}) {t} S)"
  | _ =>
    let n := arms.length / 2
    let lo := arms.take n
    let hi := arms.drop n
    match hi.head? with
    | none => "S"
    | some (mid, _) =>
      s!"(ite (bvult {stPC "S"} {bvN mid}) {balancedDispatch lo} {balancedDispatch hi})"

/-- The whole region as `mstep` (one exact machine step) + `mrun` (its closure).
Returns the SMT text, the summary symbols, and the unmodelled PCs. -/
def machineSmt (img : Nat → Option (BitVec 8)) (lo hi : Nat) :
    String × List String × List Nat := Id.run do
  let mut arms : List (Nat × String) := []
  let mut sums : List String := []
  let mut bad : List Nat := []
  let mut p := lo
  while p < hi do
    let (t, s, ok) := stepArm img lo hi "S" p
    arms := arms ++ [(p, t)]
    sums := (sums ++ s).eraseDups
    if !ok then bad := bad ++ [p]
    p := p + 4
  let body := balancedDispatch arms
  -- `mstep` is DECLARED with a defining `forall` axiom, not `define-fun`:
  -- SMT-LIB `define-fun` is a MACRO, so `(mstep (mstep … s0))` would inline the
  -- whole 10 MB body once per unrolling level before any simplification.  As an
  -- axiom it is instantiated lazily, and the balanced PC dispatch then collapses
  -- in `log n` splits per level because the PC at that level is concrete.
  let stepDef := s!"(declare-fun mstep (MState) MState)\n(assert (forall ((S MState)) (! (= (mstep S) {body}) :pattern ((mstep S)))))"
  -- `mrun` runs until control leaves the region OR reaches the query's own exit
  -- PC (`STOP`, a per-query constant), so ONE shared step/closure serves every
  -- residual, including the ones whose span ends mid-function.
  let inRegion := s!"(and (bvule {bvN lo} {stPC "S"}) (bvult {stPC "S"} {bvN hi}) (not (= {stPC "S"} STOP)))"
  let runDecl := "(declare-const STOP (_ BitVec 64))\n(declare-fun mrun (MState) MState)"
  let runAx := s!"(assert (forall ((S MState)) (= (mrun S) (ite {inRegion} (mrun (mstep S)) S))))"
  return (s!"{stepDef}\n{runDecl}\n{runAx}", sums, bad)

/-- The `mrun` one-step body under the induction hypothesis `mrun_ih` — the
Houdini obligation's `fbody`. -/
def machineRunBody (lo hi : Nat) (S : String) : String :=
  s!"(ite (and (bvule {bvN lo} {stPC S}) (bvult {stPC S} {bvN hi}) (not (= {stPC S} STOP))) (mrun_ih (mstep {S})) {S})"

-- ==========================================================================
-- BOUNDED SYMBOLIC EXECUTION WITH STATE MERGING (`reflectBmc`).
--
-- The straight-line DAG reflector needs a forward branch to reconverge, a
-- backward edge to be a real loop back-edge, and it drops whatever follows a
-- loop; real compiled code breaks all three (a shared epilogue reached by a
-- backward `j`, a multi-exit loop, a computed goto).  The PC-threaded `mstep`
-- machine below has none of those limits but hands Z3 a 25 000-arm dispatch it
-- cannot even take ONE step through.
--
-- This is the encoder that has neither problem: symbolic execution with the PC
-- CONCRETE (so every dispatch is resolved here, in Lean, for free), a guard term
-- per arrival, and a MERGE of all arrivals at the same PC in the same round.
-- Merging is what keeps it linear: the frontier can never exceed the number of
-- distinct PCs, so a diamond does not double and a loop does not branch — it
-- simply re-arrives at its header, which is one more round.
--
--   * loops           — unrolled `rounds` times, each iteration one round;
--   * computed gotos  — resolved against the ground jump tables;
--   * shared epilogue — just another PC that several arrivals merge at;
--   * calls           — `callee_<t>` summary, one round, no inlining;
--   * post-loop code  — nothing special: it is where the loop's exit arrives.
--
-- `complete = true` means the frontier emptied inside the bound, so the encoding
-- is EXACT for this span.  `complete = false` means arrivals were still live —
-- the result is then a BOUNDED one and is reported as such, never as validity.
-- ==========================================================================

/-- Every `jal ra` target in the image — the set of function entry points.  Used
to bound a span's REGION by its enclosing function, so bounded symbolic execution
follows backward jumps to a shared epilogue (still inside the function) but stops
at a `ret` or any transfer out of it. -/
def funcStarts (img : Nat → Option (BitVec 8)) (lo hi : Nat) : List Nat := Id.run do
  let mut out : List Nat := []
  let mut p := lo
  while p < hi do
    let w := wordAt img p
    if opcode w == 0x6f then
      match decodeTerm p w with
      | Term.jal rd tgt => if rd == 1 && !(out.contains tgt) then out := tgt :: out
      | _ => pure ()
    p := p + 4
  return out

/-- The enclosing function of `p`: the largest entry ≤ `p` and the smallest > `p`
(or the code bound). -/
def funcRange (starts : List Nat) (codeLo codeHi p : Nat) : Nat × Nat :=
  let below := starts.filter (fun q => q ≤ p)
  let above := starts.filter (fun q => q > p)
  let lo := below.foldl (fun a q => if q > a then q else a) codeLo
  let hi := above.foldl (fun a q => if q < a then q else a) codeHi
  (lo, hi)

/-- One live arrival: a concrete PC, the SMT Bool guard under which control is
here, and the SMT `MState` term at that point. -/
structure Arrival where
  pc : Nat
  guard : String
  state : String
  /-- The loop headers whose `loop_<h>` summary this arrival has already
  absorbed, so a header is summarised ONCE per path, not once per iteration. -/
  done : List Nat := []
  deriving Repr, Inhabited

/-- Merge arrivals at the same PC: guard = disjunction, state = `ite` chain
selected by the individual guards (exactly one holds on a real execution). -/
def mergeArrivals (as : List Arrival) : String × String :=
  match as with
  | [] => ("false", "S")
  | [a] => (a.guard, a.state)
  | _ :: _ =>
    let g := "(or " ++ String.intercalate " " (as.map (·.guard)) ++ ")"
    let st := (as.dropLast).foldr (fun x acc => s!"(ite {x.guard} {x.state} {acc})")
      (as.getLast!).state
    (g, st)

/-- Group a frontier by PC, preserving first-seen PC order. -/
def groupByPc (as : List Arrival) : List (Nat × List Arrival) := Id.run do
  let mut out : List (Nat × List Arrival) := []
  for a in as do
    if out.any (fun (q, _) => q == a.pc) then
      out := out.map (fun (q, l) => if q == a.pc then (q, l ++ [a]) else (q, l))
    else out := out ++ [(a.pc, [a])]
  return out

/-- The block starting at `pc`: its straight-line effect (the term to bind to
`bv`), then its successors and exits expressed OVER `bv`.

Taking the bound variable as a parameter is what keeps the encoding linear: a
branch condition, a computed-goto target and a call's argument all read the
block's exit state, and inlining that term into each of (say) thirteen dispatch
guards is what turns a 200-byte block into a megabyte. -/
def stepBlock (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat) (pc : Nat)
    (g sv bv : String) (k : Nat) :
    String × List (Nat × String) × List (String × String) × List String
      × List String × Nat × List (String × Nat) := Id.run do
  -- straight-line run to the terminator
  let mut cur : List MInstr := []
  let mut p := pc
  while p < hi && !(stops.contains p) && !(isTerm (wordAt img p)) do
    cur := cur ++ [mkLine (BitVec.ofNat 64 p) (wordAt img p)]
    p := p + 4
  let (st, k, ibinds, wr) := blockBinds sv cur k
  -- off the region, or arrived at the span's declared exit PC: EXIT
  if p ≥ hi || stops.contains p then return (st, [], [(g, bv)], [], ibinds, k, wr)
  let w := wordAt img p
  let inR := fun (q : Nat) => lo ≤ q && q < hi && !(stops.contains q)
  match decodeTerm p w with
  | Term.branch tgt =>
    let c := branchCondSt bv w
    let t := s!"(and {g} {c})"
    let f := s!"(and {g} (not {c}))"
    let succs := (if inR tgt then [(tgt, t)] else []) ++ (if inR (p+4) then [(p+4, f)] else [])
    let exits := (if inR tgt then [] else [(t, bv)]) ++ (if inR (p+4) then [] else [(f, bv)])
    return (st, succs, exits, [], ibinds, k, wr)
  | Term.jal rd tgt =>
    if rd == 1 then
      -- CALL (whatever the direction): the callee's summary, then the next PC.
      let sym := s!"callee_{tgt}"
      let st' := s!"({sym} {st})"
      if inR (p+4) then return (st', [(p+4, g)], [], [sym], ibinds, k, wr)
      else return (st', [], [(g, bv)], [sym], ibinds, k, wr)
    else if inR tgt then return (st, [(tgt, g)], [], [], ibinds, k, wr)
    else return (st, [], [(g, bv)], [], ibinds, k, wr)
  | Term.jalr rd rs1 =>
    if rd == 1 then
      -- indirect CALL through a register: one named opaque summary per site.
      let sym := s!"icall_{p}"
      let st' := s!"({sym} {st})"
      if inR (p+4) then return (st', [(p+4, g)], [], [sym], ibinds, k, wr)
      else return (st', [], [(g, bv)], [sym], ibinds, k, wr)
    else if rs1 == 1 then return (st, [], [(g, bv)], [], ibinds, k, wr)          -- ret: EXIT
    else match dispatchArms img p with
    | some arms =>
      -- ground jump table: one guarded successor per arm, over the BOUND state.
      let tgtE := stR bv rs1
      let mut succs : List (Nat × String) := []
      let mut exits : List (String × String) := []
      for a in arms do
        let ga := s!"(and {g} (= {tgtE} {bvN a}))"
        if inR a then succs := succs ++ [(a, ga)] else exits := exits ++ [(ga, bv)]
      return (st, succs, exits, [], ibinds, k, wr)
    | none =>
      -- an unlisted computed goto: an opaque per-site summary, then EXIT.
      let sym := s!"idisp_{p}"
      return (s!"({sym} {st})", [], [(g, bv)], [sym], ibinds, k, wr)
  | Term.sys =>
    if inR (p+4) then return (st, [(p+4, g)], [], [], ibinds, k, wr) else return (st, [], [(g, bv)], [], ibinds, k, wr)

/-- One BMC round: merge the frontier by PC, run each merged arrival's block, and
collect the new frontier + the exits.  Every merged state, every block outcome
and every guard is `let`-bound, so the term stays linear in
(rounds × distinct PCs). -/
def bmcRound (img : Nat → Option (BitVec 8)) (lo hi : Nat) (stops : List Nat) (front : List Arrival)
    (seen : List Nat) (k : Nat) (binds : List String) (sums : List String) :
    List Arrival × List (String × String) × Nat × List String × List String
      × List (String × String × Nat) := Id.run do
  let mut k := k
  let mut binds := binds
  let mut sums := sums
  let mut next : List Arrival := []
  let mut exits : List (String × String) := []
  let mut writes : List (String × String × Nat) := []
  for (pc, as) in groupByPc front do
    let (g0, st0) := mergeArrivals as
    let carried := (as.flatMap (·.done)).eraseDups
    -- RE-ARRIVAL at an already-processed PC = a loop back-edge closing on `pc`.
    -- Apply the `loop_<pc>` summary ONCE (it means "run the loop to completion"),
    -- then continue only along the successors that can no longer reach `pc` —
    -- exactly the loop's EXIT edges.  That is what lets a loop-bearing span
    -- COMPLETE: the post-loop code is reflected, not dropped.
    if seen.contains pc && !(carried.contains pc) then
      -- RE-ARRIVAL: a loop back-edge closing on `pc`.  `loop_<pc>` over-approximates
      -- the state at ANY of the loop's exit points, so control resumes at EVERY
      -- exit edge of the whole natural loop (not just this block's), and at the
      -- region exit when some body block `ret`s.  Nothing is dropped — the
      -- post-loop code is reflected, which is what a back-edge cut throws away.
      let lsum := s!"loop_{pc}"
      sums := (lsum :: sums).eraseDups
      let gv := s!"g{k}"; let sv := s!"m{k}"
      binds := binds ++ [s!"({gv} {g0})", s!"({sv} ({lsum} {st0}))"]
      k := k + 1
      let (qs, leaves) := loopExits img lo hi stops pc
      for q in qs do
        next := next ++ [{ pc := q, guard := gv, state := sv, done := pc :: carried }]
      if leaves then exits := exits ++ [(gv, sv)]
    else
    let gv := s!"g{k}"; let sv := s!"m{k}"; let bv := s!"b{k}"
    binds := binds ++ [s!"({gv} {g0})", s!"({sv} {st0})"]
    k := k + 1
    let (st1, succs, exs, ss, ibinds, k', wr) := stepBlock img lo hi stops pc gv sv bv k
    k := k'
    binds := binds ++ ibinds ++ [s!"({bv} {st1})"]
    sums := (sums ++ ss).eraseDups
    writes := writes ++ wr.map (fun (a, w) => (gv, a, w))
    for (q, gq) in succs do
      let gvq := s!"g{k}q"
      binds := binds ++ [s!"({gvq} {gq})"]
      k := k + 1
      next := next ++ [{ pc := q, guard := gvq, state := bv, done := carried }]
    for (gq, sq) in exs do
      let gvq := s!"g{k}x"
      binds := binds ++ [s!"({gvq} {gq})"]
      k := k + 1
      exits := exits ++ [(gvq, sq)]
  return (next, exits, k, binds, sums, writes)

/-- Per-round frontier PCs — the diagnostic for "why did this span not complete". -/
def bmcTrace (img : Nat → Option (BitVec 8)) (lo hi entry : Nat) (stops : List Nat) (rounds : Nat) : List (List Nat) := Id.run do
  let mut front : List Arrival := [{ pc := entry, guard := "true", state := "s0" }]
  let mut binds : List String := []
  let mut sums : List String := []
  let mut k := 0
  let mut out : List (List Nat) := []
  let mut seen : List Nat := []
  for _ in List.range rounds do
    if front.isEmpty then break
    let pcs := (front.map (·.pc)).eraseDups
    out := out ++ [pcs]
    let (f', _, k', b', s', _) := bmcRound img lo hi stops front seen k binds sums
    seen := (seen ++ pcs).eraseDups
    front := f'; k := k'; binds := b'; sums := s'
  return out

/-- Bounded symbolic execution of `[lo,hi)` from `lo`.  Returns the exit-state
term, the `let` bindings, the summary symbols, whether the frontier emptied
(`complete`), and the number of rounds used. -/
def reflectBmc (img : Nat → Option (BitVec 8)) (lo hi entry : Nat) (stops : List Nat) (rounds : Nat) (s0 : String) :
    String × List String × List String × Bool × Nat × List (String × String × Nat) := Id.run do
  let mut front : List Arrival := [{ pc := entry, guard := "true", state := s0 }]
  let mut exits : List (String × String) := []
  let mut binds : List String := []
  let mut sums : List String := []
  let mut k := 0
  let mut used := 0
  let mut seen : List Nat := []
  let mut writes : List (String × String × Nat) := []
  for r in List.range rounds do
    if front.isEmpty then break
    let pcs := (front.map (·.pc)).eraseDups
    let (f', e', k', b', s', w') := bmcRound img lo hi stops front seen k binds sums
    seen := (seen ++ pcs).eraseDups
    front := f'; exits := exits ++ e'; k := k'; binds := b'; sums := s'
    writes := writes ++ w'
    used := r + 1
  -- the exit state: the guarded merge of every exit arrival
  let exitTerm :=
    match exits with
    | [] => s0
    | _ => (exits.dropLast).foldr (fun (g, st) acc => s!"(ite {g} {st} {acc})")
             (exits.getLast!).2
  return (exitTerm, binds, sums, front.isEmpty, used, writes)

/-- Emit the binding chain as TOP-LEVEL `declare-const` + equational `assert`
instead of nested `let`s.

Two reasons, both decisive.  `let` hides every intermediate state inside the
term, so a summary's clause can only be stated as `∀S …` and Z3 has to guess the
instances — the profile showed it looping to the 10000-instantiation cap.  With
the states named at the top level, each clause is instantiated at exactly the
states the term applies the summary to, and the whole query becomes
QUANTIFIER-FREE: pure QF_ABV, which is decidable and bit-blastable.  And unlike
`define-fun`, `declare-const` + `assert (= v t)` is not a macro, so nothing is
expanded — sharing is structural.

A binding is `"(name term)"`; names starting with `g` are `Bool` guards, the rest
are `MState`. -/
def bindsToDecls (binds : List String) : String := Id.run do
  let mut out : List String := []
  for b in binds do
    let inner := (b.drop 1).dropRight 1
    let nm := (inner.takeWhile (· != ' '))
    let tm := (inner.drop (nm.length + 1))
    let sort := if nm.startsWith "g" then "Bool" else "MState"
    out := out ++ [s!"(declare-const {nm} {sort})", s!"(assert (= {nm} {tm}))"]
  return String.intercalate "\n" out

/-- Wrap a DAG's exit var + bindings into nested `let`s (a shared term). -/
def wrapLets (binds : List String) (body : String) : String :=
  binds.foldr (fun b acc => s!"(let ({b}) {acc})") body

/-- Exact axioms: `callee_t(S) = <callee body reflection>(S)`; loops via
define-fun-rec `loop_t(S) = ite(loopcond, S, loop_t(body))`.  All exact — the
body reflection defines every register + memory effect. -/
partial def emitExactAxioms (img : Nat → Option (BitVec 8))
    (worklist visited acc : List String) : List String × List String := Id.run do
  match worklist with
  | [] => (acc, visited)
  | s :: rest =>
    if visited.contains s then emitExactAxioms img rest visited acc
    else
      let visited := s :: visited
      if s.startsWith "callee_" then
        let t := (s.drop 7).toNat!
        let (ev, _, binds, subs) := reflectExactD img (findRet img t) 200 t "S" 0 [] []
        let ax := s!"(assert (forall ((S MState)) (= ({s} S) {wrapLets binds ev})))"
        emitExactAxioms img (subs ++ rest) visited (acc ++ [ax])
      else if s.startsWith "loop_" then
        let t := (s.drop 5).toNat!
        let (ev, _, binds, subs) := reflectExactD img (findBackEdge img t) 200 t "S" 0 [] []
        let ax := s!"(assert (forall ((S MState)) (= ({s} S) (ite (loopcond_{t} S) S ({s} {wrapLets binds ev})))))"
        emitExactAxioms img (subs ++ rest) visited (acc ++ [ax])
      else emitExactAxioms img rest visited acc

-- ==========================================================================
-- SUMMARY-LEMMA LAYER (assume-guarantee).  A `callee_`/`loop_` summary's full
-- definition is exact but undecidable for Z3 once the recursion is real.  The
-- decidable substitute is a per-summary CLAUSE SET (`sp` restored, memory below
-- the frame preserved, callee-saved registers restored, …) established ONCE per
-- summary by ONE-STEP unfolding under the induction hypothesis that every
-- summary — including a recursive occurrence of the summary itself, renamed
-- `<sym>_ih` — already satisfies the set.  A Houdini fixpoint over the clause
-- set (drop what fails, retry) is the "invariant mining" step; the surviving
-- set is then ASSERTED (instead of the definitions) in the per-residual
-- validity query.  Asserting lemmas is WEAKER than asserting definitions, so an
-- UNSAT under lemmas is an UNSAT under definitions — the mode is sound.
-- ==========================================================================

/-- The shared SMT preamble (state datatype + load/bitwise helpers). -/
def smtPreamble : String := "(set-logic ALL)
; ---------------------------------------------------------------------------
; Machine state, PURELY in the bitvector theory.  Registers and addresses are
; 64-bit two's complement (so arithmetic WRAPS, as RV64 does) and memory is a
; byte array indexed by a 64-bit address.  There is no `Int` anywhere: the
; earlier encoding modelled registers as mathematical integers and bridged to
; bitvectors with `int2bv`/`bv2int` at every load, store, shift and bitwise op,
; which (a) silently dropped 64-bit wraparound and (b) coupled the arithmetic
; solver to the bit-blaster — 19350 `bv-bit2core` axioms on a 34 KB obligation.
; Every span reflects to a FINITE term, so in pure QF_ABV the whole thing is
; bit-blastable.
; ---------------------------------------------------------------------------
(declare-datatypes () ((MState (mst (mm (Array (_ BitVec 64) (_ BitVec 8))) (rr (Array (_ BitVec 64) (_ BitVec 64)))))))
(define-fun ld1 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ zero_extend 56) (select m a)))
(define-fun ld2 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ zero_extend 48) (concat (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun ld4 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ zero_extend 32) (concat (select m (bvadd a #x0000000000000003)) (select m (bvadd a #x0000000000000002)) (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun ld8 ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) (concat (select m (bvadd a #x0000000000000007)) (select m (bvadd a #x0000000000000006)) (select m (bvadd a #x0000000000000005)) (select m (bvadd a #x0000000000000004)) (select m (bvadd a #x0000000000000003)) (select m (bvadd a #x0000000000000002)) (select m (bvadd a #x0000000000000001)) (select m a)))
(define-fun ld1s ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 56) (select m a)))
(define-fun ld2s ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 48) (concat (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun ld4s ((m (Array (_ BitVec 64) (_ BitVec 8))) (a (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 32) (concat (select m (bvadd a #x0000000000000003)) (select m (bvadd a #x0000000000000002)) (select m (bvadd a #x0000000000000001)) (select m a))))
(define-fun w32 ((v (_ BitVec 64))) (_ BitVec 64) ((_ sign_extend 32) ((_ extract 31 0) v)))"

/-- Declarations for a summary symbol (plus its `loopcond` when it is a loop). -/
def summaryDecls (syms : List String) : String :=
  String.intercalate "\n" (syms.flatMap (fun s =>
    let f := s!"(declare-fun {s} (MState) MState)"
    if s.startsWith "loop_" then [f, s!"(declare-fun loopcond_{s.drop 5} (MState) Bool)"] else [f]))

/-- The immediate summaries a summary's own body refers to (one unfold step). -/
def summaryDeps (img : Nat → Option (BitVec 8)) (sym : String) : List String :=
  if sym.startsWith "callee_" then
    let t := (sym.drop 7).toNat!
    let (_, _, _, subs) := reflectExactD img (findRet img t) 200 t "S" 0 [] []
    subs
  else if sym.startsWith "loop_" then
    let t := (sym.drop 5).toNat!
    let (_, _, _, subs) := reflectExactD img (findBackEdge img t) 200 t "S" 0 [] []
    sym :: subs
  else []   -- `icall_`/`idisp_`: opaque by construction, no body to unfold

/-- Transitive closure of the summary symbols reachable from a worklist. -/
partial def summaryClosure (img : Nat → Option (BitVec 8))
    (worklist visited : List String) : List String :=
  match worklist with
  | [] => visited
  | s :: rest =>
    if visited.contains s then summaryClosure img rest visited
    else summaryClosure img (summaryDeps img s ++ rest) (s :: visited)

/-- A summary's ONE-STEP body over state var `sv`, with self-references renamed
to `<sym>_ih` — the assume-guarantee induction hypothesis. -/
def summaryBody (img : Nat → Option (BitVec 8)) (sym sv : String) : String :=
  let rename (b : String) : String := b.replace s!"({sym} " s!"({sym}_ih "
  if sym.startsWith "callee_" then
    let t := (sym.drop 7).toNat!
    let (ev, _, binds, _) := reflectExactD img (findRet img t) 200 t sv 0 [] []
    rename (wrapLets binds ev)
  else if sym.startsWith "loop_" then
    let t := (sym.drop 5).toNat!
    let (ev, _, binds, _) := reflectExactD img (findBackEdge img t) 200 t sv 0 [] []
    s!"(ite (loopcond_{t} {sv}) {sv} ({sym}_ih {rename (wrapLets binds ev)}))"
  else sv

/-- The per-summary OBLIGATION file: preamble, every summary declared (plus the
`<sym>_ih` self-hypothesis symbol), and the one-step body as `fbody` over the
fresh entry state `S0`.  The Houdini driver appends the assumed clause set and
the negated goal, then runs Z3 (UNSAT ⇒ the clause is inductive for `sym`). -/
def summaryObligationSmt (img : Nat → Option (BitVec 8))
    (allSyms : List String) (sym : String) : String :=
  let decls := summaryDecls (allSyms ++ [s!"{sym}_ih"])
  let body := summaryBody img sym "S0"
  s!"{smtPreamble}\n{decls}\n(declare-const SL_lo Int)\n(declare-const SL_hi Int)\n(declare-const A_lo Int)\n(declare-const A_hi Int)\n(declare-const S0 MState)\n(define-fun fbody () MState {body})\n; clause set for every summary; `{sym}` itself is supplied as `{sym}_ih`\n; @@ASSUME@@\n; negated clause under test, over S0 / fbody\n; @@GOAL@@\n"

/-- The per-residual query in LEMMA MODE: the span's exit-state DAG, with the
summaries left UNINTERPRETED (their clause set is appended by the driver in
place of the defining axioms).  Sound: lemmas are weaker than definitions. -/
def lemmaModeSmt (lo hi : Nat) : IO (String × List String) := do
  let img ← loadElf elfPath
  let (ev, _, binds, summaries) := reflectExactD img hi 200 lo "s0" 0 [] []
  let exitS := wrapLets binds ev
  let syms := summaryClosure img summaries []
  let decls := summaryDecls syms
  let txt := s!"{smtPreamble}\n{decls}\n(declare-const SL_lo Int)\n(declare-const SL_hi Int)\n(declare-const A_lo Int)\n(declare-const A_hi Int)\n(declare-const s0 MState)\n; mined clause set for every summary\n; @@ASSUME@@\n(define-fun state_exit () MState {exitS})\n(define-fun mem_exit () (Array Int (_ BitVec 8)) (mm state_exit))\n; @@POST@@\n"
  return (txt, syms)

/-- Assemble the complete EXACT reflected Steps SMT for span `[lo,hi)`. -/
def reflectExactSmt (lo hi : Nat) : IO String := do
  let img ← loadElf elfPath
  let (ev, _, binds, summaries) := reflectExactD img hi 200 lo "s0" 0 [] []
  let exitS := wrapLets binds ev
  let (axs, visited) := emitExactAxioms img summaries [] []
  let sumDecls := String.intercalate "\n" (visited.flatMap (fun s =>
    let f := s!"(declare-fun {s} (MState) MState)"
    if s.startsWith "loop_" then [f, s!"(declare-fun loopcond_{s.drop 5} (MState) Bool)"] else [f]))
  let preamble := "(set-logic ALL)
(declare-datatypes () ((MState (mst (mm (Array Int (_ BitVec 8))) (rr (Array Int Int))))))
(define-fun ld1 ((m (Array Int (_ BitVec 8))) (a Int)) Int (bv2int (select m a)))
(define-fun ld4 ((m (Array Int (_ BitVec 8))) (a Int)) Int (+ (bv2int (select m a)) (* 256 (bv2int (select m (+ a 1)))) (* 65536 (bv2int (select m (+ a 2)))) (* 16777216 (bv2int (select m (+ a 3))))))
(define-fun ld2 ((m (Array Int (_ BitVec 8))) (a Int)) Int (+ (bv2int (select m a)) (* 256 (bv2int (select m (+ a 1))))))
(define-fun ld8 ((m (Array Int (_ BitVec 8))) (a Int)) Int (+ (ld4 m a) (* 4294967296 (ld4 m (+ a 4)))))
(define-fun shl_i ((a Int) (b Int)) Int (bv2int (bvshl ((_ int2bv 64) a) ((_ int2bv 64) b))))
(define-fun lshr_i ((a Int) (b Int)) Int (bv2int (bvlshr ((_ int2bv 64) a) ((_ int2bv 64) b))))
(define-fun ashr_i ((a Int) (b Int)) Int (bv2int (bvashr ((_ int2bv 64) a) ((_ int2bv 64) b))))
(define-fun bvor_i ((a Int) (b Int)) Int (bv2int (bvor ((_ int2bv 64) a) ((_ int2bv 64) b))))
(define-fun bvand_i ((a Int) (b Int)) Int (bv2int (bvand ((_ int2bv 64) a) ((_ int2bv 64) b))))
(define-fun bvxor_i ((a Int) (b Int)) Int (bv2int (bvxor ((_ int2bv 64) a) ((_ int2bv 64) b))))
(declare-const s0 MState)"
  let axBlock := String.intercalate "\n" axs
  return s!"{preamble}\n{sumDecls}\n{axBlock}\n(define-fun state_exit () MState {exitS})\n(define-fun mem_exit () (Array Int (_ BitVec 8)) (mm state_exit))\n"

end Vsa.ReflectSpan

open Vsa.ReflectSpan in
/-- `#reflect_full "<path>" <lo> <hi>` — write the complete reflected Steps SMT. -/
elab "#reflect_full " pathStx:str loStx:num hiStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let smt ← reflectFullSmt [2,1,8,9,18,19,15,16,14,13,11,12,10,5,6,7] loStx.getNat hiStx.getNat
    IO.FS.writeFile pathStx.getString smt
    Lean.logInfo m!"#reflect_full → {pathStx.getString} ({smt.length} bytes)"

open Vsa.ReflectSpan in
/-- `#reflect_exact "<path>" <lo> <hi>` — write the EXACT state-threaded Steps SMT. -/
elab "#reflect_exact " pathStx:str loStx:num hiStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let smt ← reflectExactSmt loStx.getNat hiStx.getNat
    IO.FS.writeFile pathStx.getString smt
    Lean.logInfo m!"#reflect_exact → {pathStx.getString} ({smt.length} bytes)"

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
