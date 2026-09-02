# hSRet

- kind: field
- consumes/consumed-by: TermResidualsCore.hSRet
- note: exec return-with-value arm | skeleton: `hSRet`/`exec_ret_row`.  Supplier: `RetResid` = `ExecRetGeom`.
- entry: 0x80004120 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (6 blocks)

- Block(0x80004120..0x80004124 beqz kind=br succs=['0x800042f0', '0x80004128'])
- Block(0x800042f0..0x800042f4 jal kind=jal succs=['0x800042f8'])
- Block(0x80004128..0x80004134 jal kind=jal succs=['0x80004138'])
- Block(0x800042f8..0x800042f8 j kind=j succs=['0x80004138'])
- Block(0x80004138..0x8000414c fall kind=fallthrough succs=['0x80004150'])
- Block(0x80004150..0x8000416c ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `value_null` → LANDED (value_null_spec, value_null_spec_full)
- `eval_expr` → NONE

## Register/memory outcome sketch

- regs written on slice: a2, a0, a3, a1, a4, a5, ra, s0, s1, s2, s3, sp
- loads: 9, stores: 3

## Disasm slice

```
  -- block 0x80004120 [br]
  80004120: ld a2,8(s0)
  80004124: beqz a2,800042f0 <exec_stmt+0x310>
  -- block 0x800042f0 [jal]
  800042f0: addi a0,sp,16
  800042f4: jal 800027ec <value_null>
  -- block 0x80004128 [jal]
  80004128: mv a3,s3
  8000412c: mv a1,s1
  80004130: addi a0,sp,16
  80004134: jal 80003164 <eval_expr>
  -- block 0x800042f8 [j]
  800042f8: j 80004138 <exec_stmt+0x158>
  -- block 0x80004138 [fallthrough] LOOP-HEAD
  80004138: ld a3,16(sp)
  8000413c: ld a4,24(sp)
  80004140: ld a5,32(sp)
  80004144: sd a3,0(s2)
  80004148: sd a4,8(s2)
  8000414c: sd a5,16(s2)
  -- block 0x80004150 [ret] LOOP-HEAD
  80004150: ld ra,168(sp)
  80004154: ld s0,160(sp)
  80004158: ld s1,152(sp)
  8000415c: ld s2,144(sp)
  80004160: ld s3,136(sp)
  80004164: li a0,3
  80004168: addi sp,sp,176
  8000416c: ret 
```
