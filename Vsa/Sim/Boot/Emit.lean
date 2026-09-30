import Vsa.Sim.Boot.Derive
import Lean

/-! Literal emission for generated witness data: `ToExpr` for the witness types and
`addLiteralDef`, which adds a definition whose value is the literal term. -/

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

end Vsa.Sim.Boot.Derive
