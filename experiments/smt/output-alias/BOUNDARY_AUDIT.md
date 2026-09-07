# Historical Loaded output-alias counterexample

The physical boundary before AST ownership admits this counterexample. The complete dense-state
certificate and closed refutations passed the resumed 1,403-module source build
and a separate type/axiom audit with the standard three axioms. See
`Vsa/Sim/OutputAliasRun.lean`, `Vsa/Sim/OutputAliasRefutation.lean`, and
`certification/verification/receipt.json`.

That evidence predates the approved ownership migration. The historical layout
is now `LayoutInstance.BeforeAstOwnership.interpRunLayout`. The new boundary
excludes this exact snapshot for every possible source program and entry witness;
see `Vsa/Sim/OutputAliasOwnedExclusion.lean`.

Source program:

```text
println();
if ("" == "\n") println();
```

Represent the empty string literal by a pointer to `consoleBuf = 0x8001bb97`, initially zero. The first `println()` writes newline to that byte. The byte immediately after it is stdout's line-buffer pointer low byte, pinned zero by `ExitRuntimeData.stdoutLine`. The formerly empty CString then represents newline. The pinned actual-ELF replay prints a second newline; the source comparison is false.

**Lean-verified:** `Vsa.While.LoadedOutputAlias.program_bigStep` derives source output `"\n"`. `Vsa.Sim.OutputAliasLoaded.snapshot_loaded` constructs the complete historical `Loaded` premise for a finite memory and explicit registers, with no hypotheses. Its stack bytes, `ProgramRepr`, initial store, store survival across the prologue footprint, fixed image, and all runtime fields are proved. Both theorem axiom sets are exactly `{propext, Classical.choice, Quot.sound}`.

**Execution checked:** `result.jsonl` records one newline for the control and two for the alias. Both reach `0x800045ec` with return value zero. All 55 runtime/static read checks, 31 `GoodState` register checks, and fixed text/rodata checks pass. That replay retains boot state and differs from the closed Lean snapshot. It deliberately sets stdout flags to `0x200a`; the separate natural-startup baseline has `0x000a` and fails that boundary check.

**Now verified privately:** `snapshot_halts_twoLF` proves a full HTIF halt from
the exact dense `snapshotConfig`. `snapshot_not_interpSim` refutes forward
simulation; `snapshot_not_remainingWork` has type
`RemainingWork BeforeAstOwnership.interpRunLayout → False`. The historical behavioral correspondence
is also refuted. These proofs use the dense snapshot directly.

## Exact memory recipe

The authoritative construction is `Vsa/Sim/OutputAliasSnapshot.lean`. `snapshotByte` uses the exact fixed `.text` and `.rodata` bytes from ELF SHA256 `b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0`. Outside those sections it applies 93 finite little-endian fields; every unlisted byte is zero.

`snapshotMem` populates the finite RAM interval `[0x80000000,0x88000000)`. `OutputAliasMemory.lean` proves interval lookup and little-endian read lemmas by induction. The proofs use those lemmas symbolically and never enumerate the 128 MiB map. Every stack byte is present. This is a finite `ExtHashMap`, not an infinite default-zero map.

### Global store

Choose `A = [0x81000000,0x81001000)`, `aLeft = 0`, `φf(n) = 0x81000000 + 32*n`, and `φc(n) = 0x81000400 + 16*n`. The closure map is unused initially. Use the fixed native addresses from the boundary.

| Address | Width | Value |
|---|---:|---:|
| `0x81000000` | 4 | 3, binding count |
| `0x81000004` | 4 | 8, capacity |
| `0x81000008` | 8 | `0x81000040`, names array |
| `0x81000010` | 8 | `0x81000080`, Value array |
| `0x81000018` | 8 | 0, null parent |
| `0x81000040` | 8 | `0x81000200` |
| `0x81000048` | 8 | `0x81000210` |
| `0x81000050` | 8 | `0x81000220` |

Place ASCII CStrings `"print\0"`, `"println\0"`, `"assert\0"` at `0x81000200`, `0x81000210`, `0x81000220` respectively. At Value slots `0x81000080 + 24*i`, set kind32=5, name64 at +8 to the corresponding name above, and function64 at +16 to `[0x80002ed4,0x80002f7c,0x80002df4][i]`.

This is exactly the one globals frame and three natives in `initSt.store` (`While/Semantics.lean:552`). `FrameRepr` permits capacity 8; its only requirement is capacity at least 3. Arrays have their full capacity present. All store reads, including names/native-name payloads, are outside the stack.

### Program AST

| Object | Contents |
|---|---|
| Statement array `0x82000000` | two u64 pointers: `0x82000020`, `0x82000040` |
| Expr statement `0x82000020` | tag32=0, expr64@+8=`0x82000080` |
| If statement `0x82000040` | tag32=3, cond64@+8=`0x820000c0`, then64@+16=`0x82000020`, else64@+24=0 |
| Call expression `0x82000080` | tag32=9, callee64@+8=`0x820000a0`, args64@+16=0, argc32@+24=0 |
| Variable expression `0x820000a0` | tag32=4, name64@+8=`0x81000210` (`println`) |
| Equality expression `0x820000c0` | tag32=6, op32@+8=19, left64@+16=`0x82000100`, right64@+24=`0x82000120` |
| Empty string expression `0x82000100` | tag32=1, string64@+8=`0x8001bb97` |
| Newline string expression `0x82000120` | tag32=1, string64@+8=`0x82000140` |
| Newline CString `0x82000140` | bytes `0x0a,0x00` |

All line/padding bytes remain zero. The then branch reuses the first expression statement. This is an acyclic shared AST; `StmtRepr` and `ProgramRepr` permit such sharing. There is no pointer-distinctness or parser-origin premise. The empty argument array needs no memory reads: `ExprArrayRepr.nil` accepts any base, and the stored signed count is zero.

The representation derivation is explicit: `StmtArrayRepr.cons` twice and `.nil`; the first statement uses `.expr`/`ExprRepr.call`/`.var`; the second uses `.ifNoElse`/`ExprRepr.binary`, with two `.str` children. The left string uses `CStr.nil` at `consoleBuf`; the right uses one `CStr.cons` followed by `.nil`. `binOpTok .eq = 19`, and `ProgramRepr`'s count is 2. None of these constructors requires string bytes to be read-only or disjoint from runtime data.

### Interpreter, main, console, and exit data

At `inp = 0x87fffe10`, store globals64=`0x81000000`, call_depth32@+8=0. Set main saved ra64 at `0x87fffff8` to `0x80000038`; saved s0 at `0x87fffff0` may be zero. All other stack bytes remain present.

Install every current `ConsoleStream` field exactly: `_impure_ptr=0x8001b538`, reent.stdout=`0x8001bb20`, reent.sinit=`0x80005d2c`, stdout cursor/base=`0x8001bb97`, counts=0, flags=`0x200a`, descriptor=1, size=1, line-count=0, cookie=self, writer=`0x8000efd4`, lock/mode=0. Set the buffer byte to zero. The byte pins for flags are the corresponding little-endian `0x0a,0x20`.

Install every `ExitRuntimeData` field exactly as in `Vsa/Sim/ExitRuntimeData.lean`: atexit=0; set the permitted lock argument to zero; stdio handler=`0x80005d18`; glue next=0/count=3/files=`0x8001ba68`; stdin/stderr flags/descriptors/counts/cookies/close pointers/null auxiliary buffers/locks/modes as specified; stdout close=`0x8000f0c0`, ungetc=0, line=0. In particular, `read64 mem 0x8001bb98 = some 0`, so the alias CString has a stable following terminator.

These overrides do not intersect `.text`/`.rodata` or the separate locale static pins. Direct ELF reads confirmed the mutable `ImageStaticsLoaded` fields already have their required values: `0x8001b880→0x80012268`, `0x8001b898→0x80019770`, `0x8001b8f8→1`, `0x8001b970→0x8001b538`. The last matches the console field. Initial BSS buffer and line-pointer bytes are all zero. No initial errno value matters; keeping its BSS zero is sufficient here.

## Exact configuration recipe

Set tick=0, steps=0, and `sailOutput=#[]`. Populate every GPR with a value, zero unless overridden:

| Register | Value |
|---|---:|
| PC | `0x800043ec` |
| x1 | `0x800045ec` |
| x2 | `0x87fffd00` |
| x3 | `0x8001b510` |
| x10 | `0x87fffe10` |
| x11 | `0x82000000` |
| x12 | 2 |
| x13 | 0 |

Populate the control registers with the typed values in `GoodState`: Machine privilege, `initMisa`, `initMstatus`, `mie=mseccfg=satp=mtvec=mideleg=medeleg=0`, active hart, `htif_done=false`, tohost base=`some 0x8001ad00`, `elp=0`, `initPmpcfg`, `initPmpaddr`, `initPmaRegions`, and zero menvcfg/mcountinhibit/mcyclecfg/minstretcfg. Supply typed present values for mip, external-interrupt signals, times/counters, nextPC, and minstret_increment; zero/false is allowed by those existential fields. Set `htif_tohost` to a present zero and `htif_payload_writes` to `0#4`. `OutputAliasPhysical.lean` assigns the remaining state components explicitly: unit choice/tag state, zero cycle count, and empty output.

For an actual-ELF experiment, boot to the first `interp_run` entry and retain its control registers/runtime image, then overlay the finite store/AST pages and modify globals/a1/a2/buffer as above. Verify the retained registers against `GoodState` and all fixed ABI pins. Merely reaching that PC is not itself a Lean proof of the approved boundary.

## Complete `InterpRunReadyFacts` premise audit

| Field group | Why the recipe supplies it |
|---|---|
| good/tick, PC/ABI, interp_local, main_ra, htif_payload, saved GPR presence | Direct register and memory assignments above. No conflicting register values. |
| text_image/rodata_image | Exact fixed ELF image, untouched by overlays. |
| statics | Exact ELF static bytes, checked against all four mutable locations; remaining static ranges are in fixed rodata. |
| console/exit_runtime | Exact named-field assignments above; the intentional alias is only the allowed buffer byte. |
| arena_protected | Arena `[0x81000000,0x81001000)` is above every protected fixed-image/runtime address and below the main saved pair. No protected interval intersects it. |
| out | Empty `sailOutput` gives `OutRepr initSt`. |
| globals/call_depth | Direct fields in the fixed Interp object. |
| interp_geom | `0x87fffe10` is 8-aligned, above HTIF, within RAM, and above live sp `0x87fffd00`; object end is `0x87ffff90`. |
| setjmp_geom | Base `0x87fffe20`, end `0x87fffe90`; aligned, in RAM, above HTIF and both jump helper code ranges. |
| stack_ok | Concrete 1264-byte headroom fits in the 8 MiB stack; sp is 16-aligned. |
| stack_bytes | Explicit finite zero-fill/retained-byte fill of the entire stack, followed by present-byte overlays. A sparse causal harness without this fill does not establish this field. |
| stmts_align/ram/win/stack | Base `0x82000000`, count 2, end `0x82000010`; 8-aligned, above HTIF, below stack, within RAM. |
| store | The exact globals frame construction above. Only frame 0 exists, so frame injectivity is trivial; closures and their bounds are vacuous. The 32-byte frame is aligned and in A. |
| native_addrs | Fixed three code addresses above. |
| store_survives | Every read needed by the initial `StoreRepr` lies in the store page, outside the entire stack. The setjmp interval lies inside the stack. For any memory agreeing off `interpRunWriteFootprint`, all frame/header/array/name/native-name reads are therefore equal. Rebuild the same `FrameRepr`/`StoreRepr` via existing read/CString transports; injectivity and arena facts are unchanged. This explains the universal field, rather than replacing it with a table of current reads. `StoreFacts.store_survives` proves this universal statement and is instantiated by `snapshot_readyFacts`. |
| arena_budget | `aLeft=0`, hence `A.lo+0≤A.hi`. No minimum budget is imposed at this boundary. |

The historical `Loaded` adds only the `ProgramRepr` witness already described. The AST/CString alias is not part of the initial store, so the initial store-survival field does not forbid it. This preceding boundary contains no hereditary AST read ownership.

## Machine mechanism

The C path uses no allocation: the calls are native with zero arguments; the conditional body is an expression statement, not a block. `call_value` immediately dispatches native values without allocating an environment or increasing closure depth (`c/src/interp.c:173`). `value_str` copies the pointer unchanged (`c/src/value.c:25`, assembly `0x8000281c..0x80002828`). Equality on strings invokes `strcmp` (`c/src/value.c:43–47`). No `fputs` of the aliased string is needed.

Existing component proofs establish the relevant leaf mechanism: the byte store at `0x8000f14c`, the flush's retained character, and unchanged stdoutLine pointer. After that write, the two relevant bytes are `0x0a,0x00`. `LoadedOutputAliasMutation.lean` compiles and proves that an intact string-node header then represents newline and cannot still represent `""`. Its hypotheses are explicit memory reads; its axiom set is the standard three.

Source output is one newline, Lean-proved in `Vsa/Sim/OutputAliasProgram.lean`. Observed machine output is two newlines for the alias and one for the control. The cases differ only in the empty literal's pointer; the ELF is identical. `check_run.py` accepts the pinned receipt and rejects the baseline's mismatched stdout flags.

The complete certificate now proves the incompatible machine behavior.
`RemainingWork` is a `Type`, so its impossibility is expressed by a function
from that type to `False`. Correcting recursive memory frames cannot supply a
value of this type under the historical boundary. The user subsequently approved
the ownership correction in `../AST_OWNERSHIP_PROPOSAL.md`.

## Concrete witness and execution checkpoint

`OutputAliasLoaded.snapshot_loaded` and the first 14 actual machine instructions
compiled in the earlier 1,380-module source build. The dense memory includes all
stack bytes; no representation, execution, or survival premise is supplied as
an oracle. `loaded-proof-receipt.json` records that checkpoint's source/build hashes.

`snapshot-replay/` starts a sparse memory from the same `snapshotByte` values and
explicit `physicalState` registers, with no boot. It returns from `interp_run`
after 1,409 instructions and halts through HTIF after 1,861, exit zero, with two
newlines. A complete instruction trace has been partitioned for certification.
The subsequent dense-state certificate covers the complete run and final halt.
All 285 remaining unit certificates and their composition passed repository
integration. See `TRACE_CERTIFICATION.md` for the proof route and evidence.
