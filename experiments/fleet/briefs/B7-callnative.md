# Fleet batch B7-callnative — discharge these TermResidualsCore fields

Gating status: gated:io-lane+crux. If a field's suppliers are missing, log + skip per the contract — do not force it.

Template pointers (read these files FIRST): rows/CallRows; rows/CallClosureSplice; rows/NativeBodyPrint; FnSummary io splices
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

### hArgsNil
```lean
∀ st d env, ArgsNilResid st d env
```

### hArgsCons
```lean
∀ st d env, ArgsConsResid st d env
```

### hCallPrint
```lean
∀ st d vs, CallPrintResid st d vs
```

### hCallPrintln
```lean
∀ st d vs, CallPrintlnResid st d vs
```

### hCallAssertOk
```lean
∀ st d, CallAssertOkResid st d
```

### hCall
```lean
∀ st st' st'' st''' d env f args fval vs v,
      CallResid st st' st'' st''' d env f args fval vs v
```

### hFn
```lean
∀ st d env name params body store' a,
      FnResid st d env name params body store' a
```

### hCallClosure
```lean
∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store)
      (frame : Addr) (st' : SpecSt) (status : Status) (v : Value)
      (a_1 : st.store.closures[a]? = some cd) (a_2 : vs.length = cd.params.length)
      (a_3 : d < maxCallDepth) (a_4 : st.store.allocFrame (some cd.env) = (store', frame))
      (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status)
      (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v),
      mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 →
      mCall st d (Value.closure a) vs st' v (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6)
```
