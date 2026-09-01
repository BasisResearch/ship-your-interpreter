# Fleet batch B3-intcells — discharge these TermResidualsCore fields

Gating status: gated:arm-chains. If a field's suppliers are missing, log + skip per the contract — do not force it.

Template pointers (read these files FIRST): BinDispatchRow BinIntCellResid; rows/Eval{Add,Sub,Mul,Div,Mod,Lt,Le,Gt,Ge}Row; ONE template x9
Also read: Vsa/Sim/rows/AssemblySkeleton.lean (your targets: the SkelH* hole abbrevs), experiments/assembly_skeleton.tsv (the work-list; supplier notes per field), and experiments/field-census.tsv (baseline: no one-term discharges — you are writing the marshalling).

## Laws (CLAUDE.md governs; these WILL bite you)
- NEVER raise maxHeartbeats/timeouts. No sorry/axiom/native_decide/bv_decide.
- Verify ONLY with `lake env lean <your file>`. NEVER `lake build`, never LSP,
  NEVER `scripts/check_all.sh` (coordinator-only; it would crush the machine).
- Axioms of every theorem must be exactly ⊆ {propext, Classical.choice,
  Quot.sound} — end each file with `#print axioms <thm>` and CHECK it.
- Run `scripts/abs_inventory.sh` FIRST; reuse abstractions by name. Named-field
  structures only; never anonymous ∃/∧ towers; never .2.2.2 chains.
- A missing general fact → append to experiments/observations.md (format at its
  top) THE MOMENT you notice, then continue with the next field.

## Worker contract
- You are in a THROWAWAY CLONE of the repo. Work here only.
- ONE NEW FILE PER FIELD: `Vsa/Sim/rows/Field_<name>.lean`. It imports
  `Vsa.Sim.rows.AssemblySkeleton` and proves EXACTLY the skeleton hole:
  `theorem field_<name> (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelH<Name> L := ...`
  (the hole abbrev unfolds to the statement quoted below; the coordinator
  plugs your theorem into `termResidualsCore_of_skeleton`). Copy the opens
  from `AssemblySkeleton.lean`'s header.
- NEVER edit shared files (Vsa.lean, check_all.sh, existing rows, the record).
  The coordinator does all wiring later, from your new files only.
- Work the fields IN ORDER. After EACH field goes green: append a landing entry
  to `experiments/logs/fleet-<batch>.md` (this survives your death; your final
  message does not).
- STUCK on a field (missing supplier, unprovable as stated)? Write the
  machine-checked obstruction or the missing-supplier NAME into the log +
  observations.md, SKIP IT, move to the next field. Never work around it,
  never assert it, never touch the statement.
- First field of the batch is the TEMPLATE: spend the care there; the rest of
  the batch should consume your own template.
- Do NOT rm the clone or anything in it when done. Final message: per-field
  status table (green/skipped+why), nothing else.

## The fields (9), in order

### hIAdd
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .add Vsa.Sim.AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hISub
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .sub Vsa.Sim.SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hIMul
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .mul Vsa.Sim.MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hIDiv
```lean
∀ g N A SL φf φc st st' st'' el er a b, ¬(a = -2^63 ∧ b = -1) →
      ∀ sp r sret aExpr m0,
      BinIntCellResid .div Vsa.Sim.DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hIMod
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .mod Vsa.Sim.ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hILt
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .lt Vsa.Sim.LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hILe
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .le Vsa.Sim.LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hIGt
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .gt Vsa.Sim.GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```

### hIGe
```lean
∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .ge Vsa.Sim.GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
```
