# Fleet batch B4-eqstr — discharge these TermResidualsCore fields

Gating status: gated:bridges-lane. If a field's suppliers are missing, log + skip per the contract — do not force it.

Template pointers (read these files FIRST): value_equal_spec_full; rows/StrCmpBlockC strCmpCell_*_of; rows/EvalEqNeFront
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

## The fields (8), in order

### hEq
```lean
∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
      BinEqCellResid .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
        g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0
```

### hNe
```lean
∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
      BinEqCellResid .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
        g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0
```

### hStrLt
```lean
∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .lt el er) st'' (.bool (sl < sr))
```

### hStrLe
```lean
∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .le el er) st'' (.bool (sl < sr || sl == sr))
```

### hStrGt
```lean
∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .gt el er) st'' (.bool (sr < sl))
```

### hStrGe
```lean
∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .ge el er) st'' (.bool (sr < sl || sl == sr))
```

### hStrAddL
```lean
∀ st d env el er st'' (sl : String) (rv : Value),
      EvalIH st d env (.binary .add el er) st''
        (.str ((Value.str sl).catDisplay st''.store ++ rv.catDisplay st''.store))
```

### hStrAddR
```lean
∀ st d env el er st'' (lv : Value) (sr : String),
      EvalIH st d env (.binary .add el er) st''
        (.str (lv.catDisplay st''.store ++ (Value.str sr).catDisplay st''.store))
```
