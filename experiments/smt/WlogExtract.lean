import Vsa.Sim.BlockMem

/-!
# `WlogExtract` — mechanically READ an arm's write-log off block-reflection

This is the plumbing WRITELOG-SMT.md named as "the next step, not a barrier":
instead of HAND-transcribing an exec-arm's store list into `scripts/writelog_smt.py`,
we EVALUATE the arm's `wlogM`/`runGM` fold (`Vsa/Sim/BlockMem.lean`) and print the
resulting `List WEntry` + register outcome in a machine-readable form that
`experiments/smt/bounded/gen_probe.py` (`wlog_stores`) consumes verbatim.

It PROVES NOTHING (no `sorry`/`axiom`/`native_decide`; not imported into
`Vsa.lean`; run only via `lake env lean`). It is a pure `#eval` EXPORT of an
existing Lean computation — the SAME fold the seg/`#derive_case` outcome computes
— so the emitted store list is provably identical to what block-reflection
produces (a wrong transcription cannot slip in: `wlogM` is the source of truth).

## Symbolic-offset trick

`wlogM` computes each store address as `(eaddrM a L).toNat = (srcVal rs1 L + sext
imm).toNat`, a `Nat`. With a SYMBOLIC entry `sp` this will not `#eval`-reduce.
So we run the fold at a CONCRETE probe base for each entry register (`baseOf`),
chosen far apart and page-aligned, then RECOVER the symbolic address of every
store as `(base_register, signed_offset)` by differencing against the probe
bases. gen_probe.py re-symbolises `base_register → sp` (etc.) so the SMT query is
over the symbolic `sp`, exactly as the hand probe was. The store WIDTH and the
program ORDER come straight from the fold; the DATA register (which entry reg was
spilled) is recovered the same way by differencing the data value.

Any arm that is a straight-line prefix (prologue spills, memcpy-style copies,
epilogue reloads) is expressible as a `List MInstr` + entry `GRegs`, so this
extractor covers the whole write-log SUPPLIER stratum, not just brk/cont.
-/

open Vsa.Sim LeanRV64DExecutable

namespace Vsa.WlogExtract

/-- Build one `MInstr` (byte pins irrelevant to the fold — set to 0). -/
def mkI (pc : BitVec 64) (k : MKind) (rd rs1 rs2 : Nat) (imm : BitVec 12) : MInstr :=
  { pc := pc, word := 0, b0 := 0, b1 := 0, b2 := 0, b3 := 0,
    kind := k, rd := rd, rs1 := rs1, rs2 := rs2, imm := imm }

/-- Concrete probe base for entry register `n`: distinct, page-aligned, far apart,
so store addresses and data values differencing back to a unique `(reg, off)`. -/
def baseOf (n : Nat) : BitVec 64 := BitVec.ofNat 64 (0x40000000 * (n + 1))

/-- The probe entry pin list over the registers a spec mentions. -/
def entryOf (regs : List Nat) : GRegs := regs.map (fun n => (n, baseOf n))

/-- For a store address `a : Nat`, find `(reg, signed offset)` s.t. `a =
baseOf reg + off`, searching the entry registers. Returns the FIRST match within
±4096 (a stack-frame window). Emits `-1` for the register when no base matches
(a genuinely absolute address — handed to gen_probe as a concrete literal). -/
def resolveAddr (regs : List Nat) (a : Nat) : Int × Int :=
  let rec go : List Nat → Int × Int
    | [] => (-1, (a : Int))
    | r :: rs =>
      let b := (baseOf r).toNat
      let d : Int := (a : Int) - (b : Int)
      if d.natAbs ≤ 8192 then ((r : Int), d) else go rs
  go regs

/-- For a store DATA value `d : Nat`, find which entry register it equals (the
spilled register). `-1` = a literal constant (emit `d`). -/
def resolveData (regs : List Nat) (d : Nat) : Int :=
  let rec go : List Nat → Int
    | [] => (-1 : Int)
    | r :: rs => if (baseOf r).toNat = d then (r : Int) else go rs
  go regs

/-- Emit the write-log of `is` (entry regs `regs`, load bytes `lds`) as a flat
list of `(dstReg, dstOff, width, dataReg, dataLit)` rows, machine-readable by
gen_probe.py. `dstReg = -1` ⇒ absolute `dstOff`; `dataReg = -1` ⇒ literal
`dataLit`. -/
def dumpWlog (is : List MInstr) (regs : List Nat) (lds : List (List (BitVec 8))) :
    List (Int × Int × Nat × Int × Nat) :=
  (wlogM is (entryOf regs) lds).map (fun (a, w, d) =>
    let (dr, doff) := resolveAddr regs a
    (dr, doff, w, resolveData regs d.toNat, d.toNat))

/-- Emit the register outcome `runGM` as `(reg, deltaReg, deltaOff, litVal)` rows
so gen_probe can thread symbolic reg outcomes if needed. -/
def dumpRegs (is : List MInstr) (regs : List Nat) (lds : List (List (BitVec 8))) :
    List (Nat × Int × Int × Nat) :=
  (runGM is (entryOf regs) lds).map (fun (n, v) =>
    let (dr, doff) := resolveAddr regs v.toNat
    (n, dr, doff, v.toNat))

/-! ## The brk/cont exec-leaf arm — the probe's known case.

`exec_stmt` prologue: `addi sp,sp,-176`; five `sd` spills of s0/s1/s2/s3/ra at
offsets 160/152/144/136/168 of the LOWERED sp. The arm body (`li a0,N`) and the
epilogue reloads write NO memory, so the whole entry→exit memory delta IS this
5-entry prologue write-log. Entry regs: sp=2, ra=1, s0=8, s1=9, s2=18, s3=19. -/

def brkContRegs : List Nat := [2, 1, 8, 9, 18, 19]

def brkContProlog : List MInstr :=
  [ mkI 0x80003fe0 .addi 2 2 0 (BitVec.ofNat 12 (0x1000 - 176))  -- addi sp,sp,-176
  , mkI 0x80003fe4 .sd 0 2 8  (0x0a0#12)   -- sd s0,160(sp)
  , mkI 0x80003fe8 .sd 0 2 9  (0x098#12)   -- sd s1,152(sp)
  , mkI 0x80003fec .sd 0 2 18 (0x090#12)   -- sd s2,144(sp)
  , mkI 0x80003ff0 .sd 0 2 19 (0x088#12)   -- sd s3,136(sp)
  , mkI 0x80003ff4 .sd 0 2 1  (0x0a8#12) ] -- sd ra,168(sp)

-- WLOG_BEGIN brkCont
#eval dumpWlog brkContProlog brkContRegs []
-- WLOG_END
-- REGS_BEGIN brkCont
#eval dumpRegs brkContProlog brkContRegs []
-- REGS_END

end Vsa.WlogExtract
