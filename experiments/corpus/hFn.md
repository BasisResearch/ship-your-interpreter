# hFn

- kind: field
- consumes/consumed-by: TermResidualsCore.hFn
- note: closure-alloc arm + native-store repr | skeleton: `hFn`/`eval_fn_row`.  Supplier: `FnResid` = closure-alloc arm + native-store repr.
- entry: 0x800033c4 (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (11 blocks)

- Block(0x800033c4..0x800033cc jal kind=jal succs=['0x800033d0'])
- Block(0x800033d0..0x800033d4 beqz kind=br succs=['0x80003e1c', '0x800033d8'])
- Block(0x80003e1c..0x80003e24 fall kind=fallthrough succs=['0x80003e28'])
- Block(0x800033d8..0x800033e8 fall kind=fallthrough succs=['0x800033ec'])
- Block(0x80003e28..0x80003e48 jal kind=jal succs=['0x80003e4c'])
- Block(0x800033ec..0x80003404 ret kind=ret succs=[])
- Block(0x80003e4c..0x80003e50 jal kind=jal succs=['0x80003e54'])
- Block(0x80003e54..0x80003e74 fall kind=fallthrough succs=['0x80003e78'])
- Block(0x80003e78..0x80003e7c jal kind=jal succs=['0x80003e80'])
- Block(0x80003e80..0x80003e98 jal kind=jal succs=['0x80003e9c'])
- Block(0x80003e9c..0x80003ec0 j kind=j succs=['0x80003e78'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `malloc` → LANDED (mallocArgRow, MallocContract, mallocCallSpec, concatMallocArgRow, mallocCallSpec_sat, strdupMallocArgRow)
- `fwrite` → LANDED (FwriteContract)
- `exit` → LANDED (foldExitL, exitToPrint_spec, exitToPrintNN_spec, FoldDefineExitReturn, callClosureBodyExitRetRow, foldDefineExitReturn_step)
- `value_kind_name` → NONE
- `runtime_error` → LANDED (runtime_error_spec)

## Register/memory outcome sketch

- regs written on slice: a0, a3, a5, a2, a1, ra, s0, s2, s1, sp, a4
- loads: 8, stores: 27

## Disasm slice

```
  -- block 0x800033c4 [jal]
  800033c4: li a0,16
  800033c8: sd a3,0(sp)
  800033cc: jal 80004790 <malloc>
  -- block 0x800033d0 [br]
  800033d0: ld a3,0(sp)
  800033d4: beqz a0,80003e1c <eval_expr+0xcb8>
  -- block 0x80003e1c [fallthrough]
  80003e1c: sd s3,1048(sp)
  80003e20: sd s4,1040(sp)
  80003e24: sd s5,1032(sp)
  -- block 0x800033d8 [fallthrough]
  800033d8: li a5,4
  800033dc: sd s0,0(a0)
  800033e0: sd a3,8(a0)
  800033e4: sd a0,8(s1)
  800033e8: sw a5,0(s1)
  -- block 0x80003e28 [jal]
  80003e28: ld a5,1120(gp)
  80003e2c: li a2,14
  80003e30: li a1,1
  80003e34: ld a3,24(a5)
  80003e38: auipc a0,0x15
  80003e3c: addi a0,a0,520
  80003e40: sd s6,1024(sp)
  80003e44: sd s7,1016(sp)
  80003e48: jal 80005260 <fwrite>
  -- block 0x800033ec [ret] LOOP-HEAD
  800033ec: ld ra,1080(sp)
  800033f0: ld s0,1072(sp)
  800033f4: ld s2,1056(sp)
  800033f8: mv a0,s1
  800033fc: ld s1,1064(sp)
  80003400: addi sp,sp,1088
  80003404: ret 
  -- block 0x80003e4c [jal]
  80003e4c: li a0,1
  80003e50: jal 80004764 <exit>
  -- block 0x80003e54 [fallthrough]
  80003e54: sd s4,1040(sp)
  80003e58: sd s5,1032(sp)
  80003e5c: sd s6,1024(sp)
  80003e60: sd s7,1016(sp)
  80003e64: sd a3,0(sp)
  80003e68: addi a0,sp,64
  80003e6c: sd a7,248(sp)
  80003e70: sd a4,64(sp)
  80003e74: sd a7,72(sp)
  -- block 0x80003e78 [jal] LOOP-HEAD
  80003e78: sd a5,80(sp)
  80003e7c: jal 800029c8 <value_kind_name>
  -- block 0x80003e80 [jal]
  80003e80: ld a3,0(sp)
  80003e84: mv a4,a0
  80003e88: mv a1,s0
  80003e8c: mv a0,s2
  80003e90: auipc a2,0x15
  80003e94: addi a2,a2,1376
  80003e98: jal 80002da8 <runtime_error>
  -- block 0x80003e9c [j]
  80003e9c: sd s4,1040(sp)
  80003ea0: sd s5,1032(sp)
  80003ea4: sd s6,1024(sp)
  80003ea8: sd s7,1016(sp)
  80003eac: sd a3,0(sp)
  80003eb0: addi a0,sp,64
  80003eb4: sd s3,248(sp)
  80003eb8: sd a4,64(sp)
  80003ebc: sd s3,72(sp)
  80003ec0: j 80003e78 <eval_expr+0xd14>
```
