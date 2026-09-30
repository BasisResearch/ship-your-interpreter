import Vsa.Sim.Boot.Derive
import Lean

/-!
# `boot_witness`

In a namespace that defines the boot trace `script`, `log`, `gprs`, `entrySteps` and the
program `prog`, `boot_witness` runs the generator `Derive.data` natively and adds its results
as literal definitions (`runs`, `own`, `top`, `brkv`, `chunks`, `bins`, `stmts`, `count`),
the witness `W`, one kernel-checked theorem per `Witness.Ok` field (the log's stores in blocks
of 1024 entries), and the `Loaded` theorems `loadedEntry`, `loadedEntry_fill`, `loadedAt`,
`loaded`. The generator is untrusted: every derived value enters the proof only through the
`decide +kernel` checks.
-/

namespace Vsa.Sim.Boot.Derive

open Lean Elab Command Meta
open Vsa.Sim.DlHeap

instance : ToExpr Run where
  toExpr r := mkApp3 (mkConst ``Run.mk) (toExpr r.base) (toExpr r.len) (toExpr r.cells)
  toTypeExpr := mkConst ``Run

def runTreeExpr : RunTree → Expr
  | .leaf r => mkApp (mkConst ``RunTree.leaf) (toExpr r)
  | .node p l r => mkApp3 (mkConst ``RunTree.node) (toExpr p) (runTreeExpr l) (runTreeExpr r)

instance : ToExpr RunTree where
  toExpr := runTreeExpr
  toTypeExpr := mkConst ``RunTree

instance : ToExpr Chunk where
  toExpr c := mkApp3 (mkConst ``Chunk.mk) (toExpr c.addr) (toExpr c.size) (toExpr c.inuse)
  toTypeExpr := mkConst ``Chunk

instance : ToExpr BootOwn where
  toExpr o := mkAppN (mkConst ``BootOwn.mk)
    #[toExpr o.env, toExpr o.cap, toExpr o.pn, toExpr o.pv, toExpr o.key0, toExpr o.key1,
      toExpr o.key2, toExpr o.name0, toExpr o.name1, toExpr o.name2, toExpr o.ast]
  toTypeExpr := mkConst ``BootOwn

def rangeTreeExpr : RangeTree → Expr
  | .leaf lo n => mkApp2 (mkConst ``RangeTree.leaf) (toExpr lo) (toExpr n)
  | .node p l r => mkApp3 (mkConst ``RangeTree.node) (toExpr p) (rangeTreeExpr l) (rangeTreeExpr r)

instance : ToExpr RangeTree where
  toExpr := rangeTreeExpr
  toTypeExpr := mkConst ``RangeTree

def addLiteralDef {α : Type} [ToExpr α] (n : Name) (a : α) : CommandElabM Unit := liftCoreM do
  let value := toExpr a
  addDecl <| .defnDecl
    { name := n, levelParams := [], type := ToExpr.toTypeExpr α, value
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }

def evalData (ns : Name) : CommandElabM (Data × Nat) := liftTermElabM do
  let regs := mkConst (ns ++ `regs)
  let log := mkConst (ns ++ `log)
  let d ← unsafe evalExpr Data (mkConst ``Data)
    (mkApp3 (mkConst ``Derive.data) (mkConst (ns ++ `script)) log regs)
  let len ← unsafe evalExpr Nat (mkConst ``Nat) (mkApp (mkConst ``PackedLog.len) log)
  return (d, len)

syntax (name := bootWitness) "boot_witness" : command

set_option hygiene false in
@[command_elab bootWitness] def elabBootWitness : CommandElab := fun _ => do
  let ns ← getCurrNamespace
  elabCommand (← `(def regs (n : Nat) : BitVec 64 := (Vsa.Sim.lookupG n gprs).getD 0))
  let (d, len) ← evalData ns
  addLiteralDef (ns ++ `runs) d.runs
  addLiteralDef (ns ++ `own) d.own
  addLiteralDef (ns ++ `top) d.top
  addLiteralDef (ns ++ `brkv) d.brkv
  addLiteralDef (ns ++ `chunks) d.chunks
  addLiteralDef (ns ++ `bins) d.bins
  addLiteralDef (ns ++ `sharedT) d.sharedT
  addLiteralDef (ns ++ `stmts) d.stmts
  addLiteralDef (ns ++ `count) d.count
  elabCommand (← `(noncomputable def W : Witness where
    script := script
    log := log
    runs := runs
    regs := regs
    entrySteps := entrySteps
    own := own
    top := top
    brkv := brkv
    chunks := chunks
    bins := bins
    sharedT := sharedT
    stmts := stmts
    count := count
    prog := prog))
  -- the log's stores, one theorem per block of 16 pages (1024 entries)
  let blocks := (len + 1023) / 1024
  let mut parts ← `(trivial)
  for j in [0:blocks] do
    let nm := mkIdent (Name.mkSimple s!"stores{j}")
    let jl := Syntax.mkNumLit (toString j)
    elabCommand (← `(theorem $nm : pagesOk log runs (16 * $jl) 16 = true := by
      decide +kernel))
    parts ← `(⟨$parts, $nm⟩)
  let bl := Syntax.mkNumLit (toString blocks)
  elabCommand (← `(theorem runs_wf : runs.wfB 0 (2 ^ 40) = true := by decide +kernel))
  elabCommand (← `(theorem runs_ok : runs.runs.all (runOkF log) = true := by decide +kernel))
  elabCommand (← `(theorem logOk : LogOk log runs :=
    logOk_of_pages (n := $bl) $parts runs_wf (by decide) runs_ok))
  elabCommand (← `(theorem aboveOk : runs.above 0x8001acf0 = true := by decide +kernel))
  elabCommand (← `(theorem memRefOk : memRefCheck (bootView script runs) = true := by decide +kernel))
  elabCommand (← `(theorem globalsOk :
    readLEv (bootView script runs) Vsa.Sim.LayoutInstance.interpObject 8 = some own.env := by decide +kernel))
  elabCommand (← `(theorem ownFast : OwnFast own := by constructor <;> decide +kernel))
  elabCommand (← `(theorem ownOk : OwnOk own := ownFast.ownOk))
  elabCommand (← `(theorem frameOk : FrameOk (bootView script runs) own := by constructor <;> decide +kernel))
  elabCommand (← `(theorem bootRegs : BootRegs regs stmts count := by
    constructor <;> decide +kernel))
  elabCommand (← `(theorem storeOk : frameCheck (maskView prologueMask (bootView script runs)) bootNatives
    own.env initFrame = true := by decide +kernel))
  elabCommand (← `(theorem heapFactsOk : HeapFactsOk (bootView script runs) own top brkv chunks
    (own.env, 0x28) (own.pn, 0x48) (own.pv, 0xc8) := by constructor <;> decide +kernel))
  elabCommand (← `(theorem heapOk : heapCheck (bootView script runs) own.exts
    [(own.pn, 8 * own.cap), (own.pv, 24 * own.cap)] top brkv chunks bins =
      true := by decide +kernel))
  elabCommand (← `(theorem sharedOk :
    sharedT.ranges.all (fun r => own.sharedRanges.contains r) = true := by decide +kernel))
  elabCommand (← `(theorem progOk :
    decodesTo (bootView script runs) sharedT.mem 100000 stmts count prog = true := by decide +kernel))
  elabCommand (← `(theorem capacityOk : capOk 1000 prog top = true := by decide +kernel))
  elabCommand (← `(theorem fitsOk : Vsa.Sim.LayoutInstance.programStackFits prog = true := by
    decide +kernel))
  elabCommand (← `(theorem ok : W.Ok :=
    ⟨logOk, aboveOk, memRefOk, globalsOk, ownOk, frameOk, bootRegs, storeOk, heapFactsOk,
      heapOk, sharedOk, progOk, capacityOk, fitsOk⟩))
  elabCommand (← `(theorem view : ViewOf (bootMem script log) (bootView script runs) := ok.view))
  elabCommand (← `(theorem loadedEntry {σ : Vsa.Machine.MState} (E : EntryRegs σ regs)
    (hout : Vsa.Machine.output σ = "") (hv : PartialView σ.mem (bootView script runs))
    (hstack : ∀ k, Vsa.Sim.LayoutInstance.stackSL.lo ≤ k →
      k < Vsa.Sim.LayoutInstance.stackSL.hi → ∃ b : BitVec 8, σ.mem[k]? = some b)
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout prog ⟨σ, tick, steps⟩ :=
      ok.loadedEntry E hout hv hstack htick steps))
  elabCommand (← `(theorem loadedEntry_fill {σ : Vsa.Machine.MState} (E : EntryRegs σ regs)
    (hout : Vsa.Machine.output σ = "") (hv : PartialView σ.mem (bootView script runs))
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout prog
      (Vsa.Densify.fillZero ⟨σ, tick, steps⟩) :=
      ok.loadedEntry_fill E hout hv htick steps))
  elabCommand (← `(theorem loadedAt {m : Vsa.MemRepr.Mem}
    (hv : PartialView m (bootView script runs))
    (hstack : ∀ k, Vsa.Sim.LayoutInstance.stackSL.lo ≤ k →
      k < Vsa.Sim.LayoutInstance.stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :
    Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout prog
      (bootConfig m regs entrySteps) :=
      ok.loadedAt hv hstack))
  elabCommand (← `(theorem loaded : Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout prog
    (Vsa.Densify.fillZero (bootConfig (bootMem script log) regs entrySteps)) := ok.loaded))

end Vsa.Sim.Boot.Derive
