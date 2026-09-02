# hStr

- kind: field
- consumes/consumed-by: TermResidualsCore.hStr
- note: leaf arm; residual = EvalEntryStrAstRegion payload premise (wave 47g/h) | skeleton: `hStr`/`eval_str_row`.  Wave 47f: code/slot geometry DISCHARGED (`field_hStr_of_payload`, `rows/Field_hStr.lean`); wave 47g (Law-4 verdict): residual = EXACTLY ONE named premise `EvalEntryStrAstRegion` (`field_hStr_of_astRegion` machine-checks the discharge; the AST-region facts exist NOWHERE on main — ExprRepr/StoreRepr/ProgramRepr/Layout all region-free; needs the `ast_region` EvalEntry amendment wave). Wave 47h: the amendment INTERFACE is landed (`EvalGround`/`AstRegionPins`, `Vsa/Sim/EntryGround.lean`; `strAstRegionBody_of_ground` in `rows/EntryGroundRows.lean` is the exact ∃-body) — hStr becomes a record fill the moment `EvalEntry.ground` is inserted (fan-out map: `experiments/entry-needs-audit.md` §D).
- entry: 0x80003414 (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (3 blocks)

- Block(0x80003414..0x80003418 jal kind=jal succs=['0x8000341c'])
- Block(0x8000341c..0x8000341c j kind=j succs=['0x800033ec'])
- Block(0x800033ec..0x80003404 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `value_str` → LANDED (value_str_spec, value_str_spec_full)

## Register/memory outcome sketch

- regs written on slice: a1, ra, s0, s2, a0, s1, sp
- loads: 5, stores: 0

## Disasm slice

```
  -- block 0x80003414 [jal]
  80003414: ld a1,8(a2)
  80003418: jal 8000281c <value_str>
  -- block 0x8000341c [j]
  8000341c: j 800033ec <eval_expr+0x288>
  -- block 0x800033ec [ret] LOOP-HEAD
  800033ec: ld ra,1080(sp)
  800033f0: ld s0,1072(sp)
  800033f4: ld s2,1056(sp)
  800033f8: mv a0,s1
  800033fc: ld s1,1064(sp)
  80003400: addi sp,sp,1088
  80003404: ret 
```
