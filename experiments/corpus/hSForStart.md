# hSForStart

- kind: field
- consumes/consumed-by: TermResidualsCore.hSForStart
- note: exec for arm (allocFrame + init/for loop) | skeleton: `hSForStart`/`exec_forStart_row`.  Supplier: `ForStartResid` = `allocFrame` + init/for-loop exit-sim (`TermGuards.forMeasure`).
- entry: 0x80004234 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (18 blocks)

- Block(0x80004234..0x80004238 jal kind=jal succs=['0x8000423c'])
- Block(0x8000423c..0x80004244 beqz kind=br succs=['0x8000426c', '0x80004248'])
- Block(0x8000426c..0x80004270 beqz kind=br succs=['0x800042a8', '0x80004274'])
- Block(0x80004248..0x80004254 jal kind=jal succs=['0x80004258'])
- Block(0x800042a8..0x800042b8 jal kind=jal succs=['0x800042bc'])
- Block(0x80004274..0x80004280 jal kind=jal succs=['0x80004284'])
- Block(0x80004258..0x80004258 j kind=j succs=['0x8000426c'])
- Block(0x800042bc..0x800042c0 bne kind=br succs=['0x8000425c', '0x800042c4'])
- Block(0x80004284..0x800042a0 jal kind=jal succs=['0x800042a4'])
- Block(0x8000425c..0x80004260 beq kind=br succs=['0x80004150', '0x80004264'])
- Block(0x800042c4..0x800042c8 j kind=j succs=['0x8000409c'])
- Block(0x800042a4..0x800042a4 beqz kind=br succs=['0x80004090', '0x800042a8'])
- Block(0x80004150..0x8000416c ret kind=ret succs=[])
- Block(0x80004264..0x80004268 bnez kind=br succs=['0x800042dc', '0x8000426c'])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])
- Block(0x80004090..0x80004094 j kind=j succs=['0x8000409c'])
- Block(0x800042dc..0x800042e8 jal kind=jal succs=['0x800042ec'])
- Block(0x800042ec..0x800042ec j kind=j succs=['0x8000426c'])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `env_new` → LANDED (env_new_spec, callClosureEnvNewRetFoldRow, CallClosureEnvNewRetFoldPost, callClosureEnvNewRetBypassRow)
- `exec_stmt` → NONE
- `eval_expr` → NONE
- `value_truthy` → LANDED (value_truthy_spec)

## Register/memory outcome sketch

- regs written on slice: a0, a1, s3, a2, a3, a5, a4, ra, s0, s1, s2, sp
- loads: 17, stores: 3

## Disasm slice

```
  -- block 0x80004234 [jal]
  80004234: mv a0,s3
  80004238: jal 800029fc <env_new>
  -- block 0x8000423c [br]
  8000423c: ld a1,8(s0)
  80004240: mv s3,a0
  80004244: beqz a1,8000426c <exec_stmt+0x28c>
  -- block 0x8000426c [br] LOOP-HEAD
  8000426c: ld a2,16(s0)
  80004270: beqz a2,800042a8 <exec_stmt+0x2c8>
  -- block 0x80004248 [jal]
  80004248: mv a2,a0
  8000424c: mv a3,s2
  80004250: mv a0,s1
  80004254: jal 80003fe0 <exec_stmt>
  -- block 0x800042a8 [jal]
  800042a8: ld a1,32(s0)
  800042ac: mv a3,s2
  800042b0: mv a2,s3
  800042b4: mv a0,s1
  800042b8: jal 80003fe0 <exec_stmt>
  -- block 0x80004274 [jal]
  80004274: mv a3,s3
  80004278: addi a0,sp,104
  8000427c: mv a1,s1
  80004280: jal 80003164 <eval_expr>
  -- block 0x80004258 [j]
  80004258: j 8000426c <exec_stmt+0x28c>
  -- block 0x800042bc [br]
  800042bc: li a5,1
  800042c0: bne a0,a5,8000425c <exec_stmt+0x27c>
  -- block 0x80004284 [jal]
  80004284: ld a3,104(sp)
  80004288: ld a4,112(sp)
  8000428c: ld a5,120(sp)
  80004290: addi a0,sp,16
  80004294: sd a3,16(sp)
  80004298: sd a4,24(sp)
  8000429c: sd a5,32(sp)
  800042a0: jal 8000282c <value_truthy>
  -- block 0x8000425c [br] LOOP-HEAD
  8000425c: li a5,3
  80004260: beq a0,a5,80004150 <exec_stmt+0x170>
  -- block 0x800042c4 [j]
  800042c4: li a0,0
  800042c8: j 8000409c <exec_stmt+0xbc>
  -- block 0x800042a4 [br]
  800042a4: beqz a0,80004090 <exec_stmt+0xb0>
  -- block 0x80004150 [ret] LOOP-HEAD
  80004150: ld ra,168(sp)
  80004154: ld s0,160(sp)
  80004158: ld s1,152(sp)
  8000415c: ld s2,144(sp)
  80004160: ld s3,136(sp)
  80004164: li a0,3
  80004168: addi sp,sp,176
  8000416c: ret 
  -- block 0x80004264 [br]
  80004264: ld a2,24(s0)
  80004268: bnez a2,800042dc <exec_stmt+0x2fc>
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
  -- block 0x80004090 [j] LOOP-HEAD
  80004090: li a0,0
  80004094: j 8000409c <exec_stmt+0xbc>
  -- block 0x800042dc [jal]
  800042dc: mv a3,s3
  800042e0: mv a1,s1
  800042e4: addi a0,sp,16
  800042e8: jal 80003164 <eval_expr>
  -- block 0x800042ec [j]
  800042ec: j 8000426c <exec_stmt+0x28c>
```
