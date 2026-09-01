# Fleet batch B5-execarms — discharge these TermResidualsCore fields

Gating status: ready. If a field's suppliers are missing, log + skip per the contract — do not force it.

Template pointers (read these files FIRST): Exec*Geom rows; ExecRecWiden; rows/ExecRouting; exec_varNull_row model
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

## The fields (14), in order

### hSExpr
```lean
∀ st st' d env e v, ExprResid st st' d env e v
```

### hSRet
```lean
∀ st st' d env e v, RetResid st st' d env e v
```

### hSRetNull
```lean
∀ st d env, RetNullResid st d env
```

### hSVarNull
```lean
∀ st d env x, VarNullResid st d env x
```

### hSBrk
```lean
∀ st, BrkResid st
```

### hSCont
```lean
∀ st, ContResid st
```

### hSVarInit
```lean
∀ st st' d env x e v, VarInitResid st st' d env x e v
```

### hSIfNone
```lean
∀ st st' d env c t v, IfNoneResid st st' d env c t v
```

### hSWhileFalse
```lean
∀ st st' d env c b v, WhileFalseResid st st' d env c b v
```

### hSIfTrue
```lean
∀ st st' st'' d env c t e v status, IfTrueResid st st' st'' d env c t e v status
```

### hSIfFalse
```lean
∀ st st' st'' d env c t e v status, IfFalseResid st st' st'' d env c t e v status
```

### hSBlock
```lean
∀ st st' d env ss status store' inner, BlockResid st st' d env ss status store' inner
```

### hSForStart
```lean
∀ st st' st'' d env init cnd step b status store' outer,
      ForStartResid st st' st'' d env init cnd step b status store' outer
```

### hSWhileBreak
```lean
∀ st st' d env c b status, WhileResid st st' d env c b status
```
