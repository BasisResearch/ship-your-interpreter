import Vsa.Compiler.Encode
import Vsa.Compiler.Exit
import Vsa.Sim.StepCount
import Vsa.Sim.HtifStepObs
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivWrap
import Vsa.Sim.DivSpec3

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Machine (MState Config Step Steps Halted Halts output)

abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

def codeBase : Nat := 0x80004800

def mulPC : Nat := 0x80004640
def divPC : Nat := 0x800046a4
def modPC : Nat := 0x80004728

def CodeAt (m : Mem) (code : List Ins) : Prop :=
  ∀ k i, code[k]? = some i → ∀ j < 4, m[codeBase + 4 * k + j]? = some (byte i.encode j)

structure LibLoaded (m : Mem) : Prop where
  mul : Code.__muldi3Loaded m
  div : Code.__divdi3Loaded m
  umod : Code.__umoddi3Loaded m
  udiv : Code.__hidden___udivdi3Loaded m
  mod : Code.__moddi3Loaded m

structure AM where
  pc : BitVec 64
  regs : GRegs
  mem : Mem
  out : Array String

inductive Out where
  | run (A : AM)
  | halt (e : Nat)

def fetch (code : List Ins) (pc : BitVec 64) : Option Ins :=
  if codeBase ≤ pc.toNat ∧ pc.toNat % 4 = 0 ∧ pc.toNat + 4 ≤ tohostAddr then
    code[(pc.toNat - codeBase) / 4]?
  else none

def rd8 (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a + 1]?).getD 0, (m[a + 2]?).getD 0, (m[a + 3]?).getD 0,
   (m[a + 4]?).getD 0, (m[a + 5]?).getD 0, (m[a + 6]?).getD 0, (m[a + 7]?).getD 0]

def putcWord (c : BitVec 8) : BitVec 64 := 0x0101000000000000#64 ||| BitVec.zeroExtend 64 c

def exitWord (e : BitVec 64) : BitVec 64 := (e <<< 1) ||| 1#64

def htifOut (v : BitVec 64) (A : AM) : Option Out :=
  if v = exitWord 0 then some (.halt 0)
  else if v = exitWord 70 then some (.halt 70)
  else if v = putcWord (v.setWidth 8) then
    some (.run { A with pc := BitVec.addInt A.pc 4,
                        out := A.out.push (toString (Char.ofNat (v.setWidth 8).toNat)) })
  else none

def clobbered : List Nat := [1, 5, 10, 11, 12, 13]

def eraseAll (ns : List Nat) (L : GRegs) : GRegs := ns.foldl (fun L n => eraseG n L) L

def libCall (tgt : Nat) (A : AM) : Option Out :=
  match lookupG 10 A.regs, lookupG 11 A.regs with
  | some x, some y =>
    if 12 ∈ keysG A.regs ∧ 13 ∈ keysG A.regs then
      let back (r : BitVec 64) : Option Out :=
        some (.run ⟨BitVec.addInt A.pc 4, (10, r) :: eraseAll clobbered A.regs, A.mem, A.out⟩)
      if tgt = mulPC then back (x * y)
      else if tgt = divPC ∧ y.toInt ≠ 0 then back (BitVec.ofInt 64 (x.toInt.tdiv y.toInt))
      else if tgt = modPC ∧ y.toInt ≠ 0 then back (BitVec.ofInt 64 (x.toInt.tmod y.toInt))
      else none
    else none
  | _, _ => none

def exec (i : Ins) (A : AM) : Option Out :=
  let L := A.regs
  let pc := A.pc
  match i with
  | .ld rd rs1 =>
    if KindOK (keysG L) .ld rd rs1 0 then
      let ea := (srcVal rs1 L).toNat
      if 0x80000000 ≤ ea ∧ ea + 8 ≤ 0x100000000 ∧ (ea + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea) then
        some (.run ⟨BitVec.addInt pc 4, stepGM (i.toM pc) L (rd8 A.mem ea), A.mem, A.out⟩)
      else none
    else none
  | .sd rs2 rs1 =>
    if SrcOK rs1 (keysG L) ∧ SrcOK rs2 (keysG L) then
      let ea := (srcVal rs1 L).toNat
      if ea = tohostAddr then htifOut (srcVal rs2 L) A
      else if 0x80000000 ≤ ea ∧ ea + 8 ≤ 0x100000000 ∧ tohostAddr + 16 ≤ ea ∧ ea % 8 = 0 then
        some (.run ⟨BitVec.addInt pc 4, L, applyW A.mem (ea, 8, srcVal rs2 L), A.out⟩)
      else none
    else none
  | .br op rs1 rs2 off =>
    let tgt := pc + sign_extend (m := 64) (evenB off)
    if SrcOK rs1 (keysG L) ∧ SrcOK rs2 (keysG L) ∧ tgt.toNat % 4 = 0 then
      some (.run { A with pc := if guardB op.bop (srcVal rs1 L) (srcVal rs2 L) then tgt
                                else BitVec.addInt pc 4 })
    else none
  | .jal rd off =>
    let tgt := pc + sign_extend (m := 64) (evenJ off)
    if tgt.toNat % 4 = 0 then
      if rd = 0 then some (.run { A with pc := tgt })
      else if rd = 1 then
        if tgt.toNat = mulPC ∨ tgt.toNat = divPC ∨ tgt.toNat = modPC then libCall tgt.toNat A
        else some (.run { A with pc := tgt, regs := (1, BitVec.addInt pc 4) :: eraseG 1 L })
      else none
    else none
  | .jalr rs1 =>
    let tgt := BitVec.update (srcVal rs1 L + sign_extend (m := 64) (0#12)) 0 0#1
    if SrcOK rs1 (keysG L) ∧ tgt.toNat % 4 = 0 then some (.run { A with pc := tgt }) else none
  | _ =>
    let a := i.toM pc
    if KindOK (keysG L) a.kind a.rd a.rs1 a.rs2 then
      some (.run ⟨BitVec.addInt pc 4, stepGM a L [], A.mem, A.out⟩)
    else none

def astep (code : List Ins) (A : AM) : Option Out :=
  match fetch code A.pc with
  | some i => exec i A
  | none => none

structure Corr (c : Config) (A : AM) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some A.pc
  regs : GHolds c.σ A.regs
  keys : KeysOK (keysG A.regs)
  mem : c.σ.mem = A.mem
  out : c.σ.sailOutput = A.out
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)

end Vsa.Compiler
