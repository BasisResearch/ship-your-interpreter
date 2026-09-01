# Fleet batch B6-loopseq — discharge these TermResidualsCore fields

Gating status: partial. If a field's suppliers are missing, log + skip per the contract — do not force it.

Template pointers (read these files FIRST): rows/ScaffoldRows; execSeqNil/execSeqLoop; LoopScaffoldClose
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

## The fields (7), in order

### hFlCondFalse
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt)
      (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1)
```

### hFlBodyBreak
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk),
      mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 →
      mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1)
```

### hFlBodyRet
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' (Status.ret rv)),
      mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 →
      mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1)
```

### hFlLoop
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont)
      (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'),
      mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 →
      mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 →
      mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4)
```

### hSeqNil
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env)
```

### hSeqConsNormal
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt)
      (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status),
      mExecS st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 →
      mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1)
```

### hSeqConsAbrupt
```lean
∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt)
      (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal),
      mExecS st d env s st' status a →
      mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1)
```
