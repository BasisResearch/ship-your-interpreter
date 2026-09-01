# Wave 44 — valueprint lane (start of the value_print machine contract)

Task: `value_print` (0x800028fc..0x800029ac, 51 instrs) — the callee that
`NativePrintInternal`'s loop invokes per argument. Build the dispatch head +
per-kind arm segs, parking each arm AT its IO callee entry with args pinned,
and name the 3 IO callee contracts (fprintf/fwrite/fputs) as typed premises.

## Ground truth (re-verified from disasm.txt + ELF rodata)

### Structure
- Entry (0x800028fc-0x80002904): `lw a4,0(a0)` (kind), `li a5,5`,
  `bltu a5,a4,0x800029ac` (kind>5 → early ret).
- Jump-table dispatch (0x80002908-0x80002924): `lwu a5,0(a0)`,
  `auipc/addi a4=0x80019f10`, `slli a5,a5,2`, `add a5,a5,a4`, `lw a5,0(a5)`,
  `add a5,a5,a4`, `jr a5`.
- Jump table @0x80019f10 (6 entries, ELF .rodata, base = 0x80019f10):
  kind0 null → 0x8000295c; kind1 bool → 0x80002974; kind2 int → 0x80002990;
  kind3 str → 0x800029a4; kind4 closure → 0x80002928; kind5 native → 0x80002948.
- kindTag (RuntimeRepr): null=0 bool=1 int=2 str=3 closure=4 native=5.

### Arms (every arm ENDS IN A `j` TAIL-CALL, not jal — value_print does not
### return itself; the IO fn returns to value_print's caller)
- null  @0x8000295c: mv a3,a1; li a2,4; li a1,1; auipc/addi a0=0x80019018;
  `j fwrite` (0x80005260). Prints "null".
- bool  @0x80002974: lw a5,8(a0); auipc/addi a0=0x80019010; beqz a5,0x8000298c;
  auipc/addi a0=0x80019008; `j fputs` (0x80006500). "true"/"false".
- int   @0x80002990: ld a2,8(a0); mv a0,a1; auipc/addi a1=0x800192c0 (%lld);
  `j fprintf` (0x800061c0).
- str   @0x800029a4: ld a0,8(a0); `j fputs` (0x80006500).
- closr @0x80002928: ld a5,8(a0); ld a5,0(a5); ld a2,8(a5); beqz a2,0x800029b0;
  mv a0,a1; auipc/addi a1=0x800192c8; `j fprintf` (0x800061c0).
- native@0x80002948: ld a2,8(a0); mv a0,a1; auipc/addi a1=0x800192d8;
  `j fprintf` (0x800061c0).

## Decode coverage: COMPLETE — zero gaps.
All 37 distinct instruction words of the span (incl. `jr a5`=00078067, the
jump-table auipc/add/lw) already have DecodeTable lemmas. No batch generation
needed. (Verified against scripts/decode_index.tsv.)

## Model files
- Dispatch head (jr): CmpDispatchSeg.lean precedent (`#derive_case` seg ending
  before jr) + ValueEqualSpec.lean's JumpTable/jt_target/jt_read (the .rodata
  jump-table modeling). value_print's jr is IN the seg as the `jr` TERMINATOR
  (TKind.jr; end PC = symbolic srcVal a5 = handlerAddr per kind).
- Arms (j): #derive_case seg + segToTriple (DeriveCaseRow), each ends in `j`
  (TKind.j, concrete target = callee entry).
- Callee contracts: named-field structures (model NativeBodyPrint's
  NativePrintEntry residual style).

## Landings

### `Vsa/Sim/rows/ValuePrintArms.lean` — GREEN, axiom-clean (all 7 rows ⊆
### {propext, Classical.choice, Quot.sound}), discipline OK
The six case arms as `#derive_case` segs + `segToTriple` rows, each parked AT its
IO callee's entry with the ABI args surviving in `GHolds c.σ out.regs` (the
`CmpDispatchSeg`/`MallocArgPost` GHolds-carrying shape — the concrete args
`decide`/`gholds_lookup` at the caller). SEVEN rows (bool splits on its inner
`beqz`):
- `vpIntArmRow`     (0x80002990 → j fprintf@0x800061c0; fmt 0x800192c0 %lld)
- `vpStrArmRow`     (0x800029a4 → j fputs@0x80006500)
- `vpNativeArmRow`  (0x80002948 → j fprintf@0x800061c0; fmt 0x800192d8)
- `vpNullArmRow`    (0x8000295c → j fwrite@0x80005260; "null" buf 0x80019018)
- `vpBoolTrueArmRow`/`vpBoolFalseArmRow` (0x80002974 → j fputs@0x80006500;
  inner `beqz a5` = beq a5,x0; true=NOT-taken "true"@0x80019008,
  false=TAKEN "false"@0x80019010)
- `vpClosureArmRow` (0x80002928 → j fprintf@0x800061c0; fmt 0x800192c8; inner
  `beqz a2` NON-NULL path; a2=0 exits span to 0x800029b0, own mini-arm NOT built)
KEY moves: each arm ends in `.j` TInstr (concrete target = callee entry, NOT
`jal` — value_print tail-jumps so `ra` = value_print's caller); posts carry
`GHolds` not concrete regs (forcing `lookupG` reduction over symbolic `lds`
stack-overflows — the cmpDispatch lesson); memFrame `by rw[hmem']; rfl`
(out.log=[]); bool-FALSE block2 = bare `j fputs` (empty body `[]`); NOTE
`#derive_case` rejects a `/-- -/` doc comment immediately above it (use `/- -/`).

### `Vsa/Sim/rows/ValuePrintContract.lean` — GREEN, axiom-clean, discipline OK
The frontier: three named-field callee-contract structures (model
`Vsa.Alloc.MallocContract`) + the dispatch residual + `vpHandler`.
- `vpHandler : Value → BitVec 64` — the per-kind arm-entry PC (the `jr a5`
  target; from the ELF .rodata table @0x80019f10).
- `FprintfContract`/`FwriteContract`/`FputsContract` (each `structure … where`
  with `privFoot` + `spec` = an output-append + ABI-return Triple parked at the
  callee entry). THE THREE CALLEE CONTRACTS — the genuine machine frontier
  (newlib fprintf/fwrite/fputs → HTIF putchar, no code image yet).
- `ValuePrintDispatch N φc` — the NAMED residual for the dispatch head
  (value_print entry 0x800028fc → parked at `vpHandler v` with arm-entry pins),
  BLOCKED on `MKind.lwu` (observation `lwu-missing-from-block-decoder`); post is
  exactly what the landed arm rows consume.
GOTCHA: under the file's opens, `StackLayout` must be written
`Vsa.Alloc.StackLayout` in the structure headers (else auto-bound implicit).

## Decode gaps
- ZERO DecodeTable gaps (all 37 span words have decode lemmas).
- ONE SegEval block-decoder gap: `MKind.lwu` missing (the dispatch-head
  `lwu a5,0(a0)` @0x80002908). Observation `lwu-missing-from-block-decoder`
  logged with the full `.lwu` add recipe. This blocks ONLY the dispatch head
  (all 6 arms are lwu-free and landed).

## The composition seam (NEXT serial item — deliberately NOT forced this wave)
`value_print` output-append = `ValuePrintDispatch` ≫ (per-kind) arm row ≫
callee contract, via `Triple.seq`. The seam that remains:
`segToTriple`'s `SegPre`/`Q` interface exposes only GoodState/mem/PC/minstret/
GHolds to the arm post — NOT `sailOutput`, `ra`/`sp`, or the ABI-frame clause
(all preserved by the seg, but hidden by this marshalling). Each callee
contract's PRE needs those (out0, ra, sp, AbiPreserved). So the composition
needs a FRAMED arm variant (`bblocks_sound_framed`/FrameMeta over the arm seg,
carrying the output + ABI frame) before `Triple.seq` closes. That framed-arm +
3-way splice is the next serial landing; the arms + contracts + dispatch
residual here are its inputs.

## Wiring (coordinator — NOT applied by me; Vsa.lean/check_all.sh not mine)
- Vsa.lean (after the last `import Vsa.Sim.rows.*` in the rows block, and after
  `import Vsa.Sim.NativeBodyPrint` is NOT required — ValuePrintContract imports
  only `Vsa.Sim.rows.ValuePrintArms` + `Vsa.Alloc`):
    import Vsa.Sim.rows.ValuePrintArms
    import Vsa.Sim.rows.ValuePrintContract
- scripts/check_all.sh axiom list additions (all ⊆ {propext, Classical.choice,
  Quot.sound}):
    Vsa.Sim.vpIntArmRow Vsa.Sim.vpStrArmRow Vsa.Sim.vpNativeArmRow
    Vsa.Sim.vpNullArmRow Vsa.Sim.vpBoolTrueArmRow Vsa.Sim.vpBoolFalseArmRow
    Vsa.Sim.vpClosureArmRow
  (`vpHandler`/the 3 contract structures/`ValuePrintDispatch` are defs/structures
  — no theorem axioms to list, but `#print axioms` clean.)
- discipline: both new files pass strict (no grandfathering).

## Coordinator requests
1. Add `MKind.lwu` (decodeM LOAD funct3=6; wvalM/astOfM/runGM zero-extend;
   ldsRunM pops one load; ChainFacts uses existing DecodeTable lemma) — mirrors
   the wave-38 `xori` add. UNBLOCKS `ValuePrintDispatch` → a clean `#derive_case`
   seg ending in the `jr` terminator (end PC = `vpHandler v` per kind; the
   ValueEqualSpec `JumpTable`/`jt_target`/`jt_read` .rodata modeling supplies the
   table-byte → handler resolution).
2. This unblocks the SAME `lwu a5,0(a0)` idiom in value_equal/value_kind_name
   (currently the ValueEqualSpec legacy hand-Steps dispatch).
