# hSWhileFalse

- kind: field
- consumes/consumed-by: TermResidualsCore.hSWhileFalse
- note: exec while, cond-false exit | skeleton: `hSWhileFalse`/`exec_whileFalse_row`.  Supplier: `WhileFalseResid`.
- entry: 0x8000403c (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (9 blocks)

- Block(0x8000403c..0x8000404c jal kind=jal succs=['0x80004050'])
- Block(0x80004050..0x8000406c jal kind=jal succs=['0x80004070'])
- Block(0x80004070..0x80004070 beqz kind=br succs=['0x80004090', '0x80004074'])
- Block(0x80004090..0x80004094 j kind=j succs=['0x8000409c'])
- Block(0x80004074..0x80004084 jal kind=jal succs=['0x80004088'])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])
- Block(0x80004088..0x8000408c bne kind=br succs=['0x80004034', '0x80004090'])
- Block(0x80004034..0x80004038 beq kind=br succs=['0x80004150', '0x8000403c'])
- Block(0x80004150..0x8000416c ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE
- `value_truthy` → LANDED (value_truthy_spec)
- `exec_stmt` → NONE

## Register/memory outcome sketch

- regs written on slice: a2, a3, a0, a1, a4, a5, ra, s0, s1, s2, s3, sp
- loads: 15, stores: 3

## Disasm slice

```
  -- block 0x8000403c [jal]
  8000403c: ld a2,8(s0)
  80004040: mv a3,s3
  80004044: addi a0,sp,80
  80004048: mv a1,s1
  8000404c: jal 80003164 <eval_expr>
  -- block 0x80004050 [jal]
  80004050: ld a3,80(sp)
  80004054: ld a4,88(sp)
  80004058: ld a5,96(sp)
  8000405c: addi a0,sp,16
  80004060: sd a3,16(sp)
  80004064: sd a4,24(sp)
  80004068: sd a5,32(sp)
  8000406c: jal 8000282c <value_truthy>
  -- block 0x80004070 [br]
  80004070: beqz a0,80004090 <exec_stmt+0xb0>
  -- block 0x80004090 [j] LOOP-HEAD
  80004090: li a0,0
  80004094: j 8000409c <exec_stmt+0xbc>
  -- block 0x80004074 [jal]
  80004074: ld a1,16(s0)
  80004078: mv a3,s2
  8000407c: mv a2,s3
  80004080: mv a0,s1
  80004084: jal 80003fe0 <exec_stmt>
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
  -- block 0x80004088 [br]
  80004088: li a5,1
  8000408c: bne a0,a5,80004034 <exec_stmt+0x54>
  -- block 0x80004034 [br] LOOP-HEAD
  80004034: li a5,3
  80004038: beq a0,a5,80004150 <exec_stmt+0x170>
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
