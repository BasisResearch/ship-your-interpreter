# hAssign

- kind: field
- consumes/consumed-by: TermResidualsCore.hAssign
- note: assign arm; child eval + env_define store-set | skeleton: `hAssign`/`eval_assign_row`.  Supplier: `AssignArmSpec` arm oracle (""row now, arm spec later"" precedent) — the composed `env_define` (`TermCallees.envDefine`, OPEN) store-set arm.  No `evalAssignSim` exists yet; whole ar
- entry: 0x8000347c (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (14 blocks)

- Block(0x8000347c..0x80003488 jal kind=jal succs=['0x8000348c'])
- Block(0x8000348c..0x800034b0 jal kind=jal succs=['0x800034b4'])
- Block(0x800034b4..0x800034b4 bnez kind=br succs=['0x80003448', '0x800034b8'])
- Block(0x80003448..0x80003478 ret kind=ret succs=[])
- Block(0x800034b8..0x800034e4 jal kind=jal succs=['0x800034e8'])
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
- `env_set` → NONE
- `runtime_error` → LANDED (runtime_error_spec)
- `value_null` → LANDED (value_null_spec, value_null_spec_full)

## Register/memory outcome sketch

- regs written on slice: a2, a0, a1, a6, a4, a5, a3, ra, s0, s2, s1, sp, s3, a7, s5, s7
- loads: 34, stores: 20

## Disasm slice

```
  -- block 0x8000347c [jal]
  8000347c: ld a2,16(a2)
  80003480: addi a0,sp,240
  80003484: sd a3,0(sp)
  80003488: jal 80003164 <eval_expr>
  -- block 0x8000348c [jal]
  8000348c: ld a1,8(s0)
  80003490: ld a6,240(sp)
  80003494: ld a4,248(sp)
  80003498: ld a5,256(sp)
  8000349c: ld a0,0(sp)
  800034a0: addi a2,sp,64
  800034a4: sd a6,64(sp)
  800034a8: sd a4,72(sp)
  800034ac: sd a5,80(sp)
  800034b0: jal 80002cdc <env_set>
  -- block 0x800034b4 [br]
  800034b4: bnez a0,80003448 <eval_expr+0x2e4>
  -- block 0x80003448 [ret] LOOP-HEAD
  80003448: ld a3,240(sp)
  8000344c: ld a4,248(sp)
  80003450: ld a5,256(sp)
  80003454: ld ra,1080(sp)
  80003458: ld s0,1072(sp)
  8000345c: sd a3,0(s1)
  80003460: sd a4,8(s1)
  80003464: sd a5,16(s1)
  80003468: ld s2,1056(sp)
  8000346c: mv a0,s1
  80003470: ld s1,1064(sp)
  80003474: addi sp,sp,1088
  80003478: ret 
  -- block 0x800034b8 [jal]
  800034b8: ld a3,8(s0)
  800034bc: lw a1,4(s0)
  800034c0: mv a0,s2
  800034c4: li a4,0
  800034c8: auipc a2,0x16
  800034cc: addi a2,a2,-296
  800034d0: sd s3,1048(sp)
  800034d4: sd s4,1040(sp)
  800034d8: sd s5,1032(sp)
  800034dc: sd s6,1024(sp)
  800034e0: sd s7,1016(sp)
  800034e4: jal 80002da8 <runtime_error>
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
  … (disasm capped at 90 lines)
```
