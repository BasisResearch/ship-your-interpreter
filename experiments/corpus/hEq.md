# hEq

- kind: field
- consumes/consumed-by: TermResidualsCore.hEq
- note: binary arm dispatch; eq cell, value_equal seam | skeleton: `hBinary` eq cell.  Supplier: `EqResid` via `value_equal_spec_full` (`TermCallees.valueEqual`, LANDED) + `EvalEqNeRow`.
- entry: 0x800034e8 (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (9 blocks)

- Block(0x800034e8..0x800034f8 jal kind=jal succs=['0x800034fc'])
- Block(0x800034fc..0x80003518 jal kind=jal succs=['0x8000351c'])
- Block(0x8000351c..0x80003534 bltu kind=br succs=['0x80003928', '0x80003538'])
- Block(0x80003928..0x80003950 jal kind=jal succs=['0x80003954'])
- Block(0x80003538..0x80003558 jr kind=ret succs=[])
- Block(0x80003954..0x8000395c fall kind=fallthrough succs=['0x80003960'])
- Block(0x80003960..0x80003964 jal kind=jal succs=['0x80003968'])
- Block(0x80003968..0x80003974 j kind=j succs=['0x800033ec'])
- Block(0x800033ec..0x80003404 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE
- `runtime_error` → LANDED (runtime_error_spec)
- `value_null` → LANDED (value_null_spec, value_null_spec_full)

## Register/memory outcome sketch

- regs written on slice: a2, a0, a3, a6, a1, s3, a4, s0, a5, a7, s5, s7, ra, s2, s1, sp
- loads: 19, stores: 8

## Disasm slice

```
  -- block 0x800034e8 [jal]
  800034e8: ld a2,16(a2)
  800034ec: addi a0,sp,120
  800034f0: sd s3,1048(sp)
  800034f4: sd a3,0(sp)
  800034f8: jal 80003164 <eval_expr>
  -- block 0x800034fc [jal]
  800034fc: ld a2,24(s0)
  80003500: ld a3,0(sp)
  80003504: lw a6,120(sp)
  80003508: addi a0,sp,144
  8000350c: mv a1,s2
  80003510: ld s3,128(sp)
  80003514: sd a6,0(sp)
  80003518: jal 80003164 <eval_expr>
  -- block 0x8000351c [br]
  8000351c: lw a2,8(s0)
  80003520: li a4,12
  80003524: lw s0,4(s0)
  80003528: addiw a5,a2,-11
  8000352c: lw a0,144(sp)
  80003530: ld a7,152(sp)
  80003534: bltu a4,a5,80003928 <eval_expr+0x7c4>
  -- block 0x80003928 [jal]
  80003928: mv a1,s0
  8000392c: mv a0,s2
  80003930: li a4,0
  80003934: li a3,0
  80003938: auipc a2,0x16
  8000393c: addi a2,a2,-1248
  80003940: sd s4,1040(sp)
  80003944: sd s5,1032(sp)
  80003948: sd s6,1024(sp)
  8000394c: sd s7,1016(sp)
  80003950: jal 80002da8 <runtime_error>
  -- block 0x80003538 [ret]
  80003538: slli a4,a5,0x20
  8000353c: srli a5,a4,0x1e
  80003540: auipc a4,0x17
  80003544: addi a4,a4,-1468
  80003548: add a5,a5,a4
  8000354c: lw a5,0(a5)
  80003550: ld a6,0(sp)
  80003554: add a5,a5,a4
  80003558: jr a5
  -- block 0x80003954 [fallthrough]
  80003954: lw a5,8(s2)
  80003958: addiw a5,a5,-1
  8000395c: sw a5,8(s2)
  -- block 0x80003960 [jal]
  80003960: mv a0,s1
  80003964: jal 800027ec <value_null>
  -- block 0x80003968 [j]
  80003968: ld s3,1048(sp)
  8000396c: ld s5,1032(sp)
  80003970: ld s7,1016(sp)
  80003974: j 800033ec <eval_expr+0x288>
  -- block 0x800033ec [ret] LOOP-HEAD
  800033ec: ld ra,1080(sp)
  800033f0: ld s0,1072(sp)
  800033f4: ld s2,1056(sp)
  800033f8: mv a0,s1
  800033fc: ld s1,1064(sp)
  80003400: addi sp,sp,1088
  80003404: ret 
```
