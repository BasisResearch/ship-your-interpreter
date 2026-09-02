# hSIfTrue

- kind: field
- consumes/consumed-by: TermResidualsCore.hSIfTrue
- note: exec if, then route | skeleton: `hSIfTrue`/`exec_ifTrue_row`.  Supplier: `IfTrueResid` (branch exit-sim).
- entry: 0x800041e8 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (10 blocks)

- Block(0x800041e8..0x800041f8 jal kind=jal succs=['0x800041fc'])
- Block(0x800041fc..0x80004218 jal kind=jal succs=['0x8000421c'])
- Block(0x8000421c..0x80004228 beqz kind=br succs=['0x800042cc', '0x8000422c'])
- Block(0x800042cc..0x800042d0 bnez kind=br succs=['0x80004014', '0x800042d4'])
- Block(0x8000422c..0x80004230 j kind=j succs=['0x80004014'])
- Block(0x80004014..0x80004018 bltu kind=br succs=['0x80004090', '0x8000401c'])
- Block(0x800042d4..0x800042d8 j kind=j succs=['0x8000409c'])
- Block(0x80004090..0x80004094 j kind=j succs=['0x8000409c'])
- Block(0x8000401c..0x80004030 jr kind=ret succs=[])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE
- `value_truthy` → LANDED (value_truthy_spec)

## Register/memory outcome sketch

- regs written on slice: a2, a3, a1, a0, a5, a6, a4, s0, ra, s1, s2, s3, sp
- loads: 14, stores: 3

## Disasm slice

```
  -- block 0x800041e8 [jal]
  800041e8: ld a2,8(s0)
  800041ec: mv a3,s3
  800041f0: mv a1,s1
  800041f4: addi a0,sp,56
  800041f8: jal 80003164 <eval_expr>
  -- block 0x800041fc [jal]
  800041fc: ld a2,56(sp)
  80004200: ld a3,64(sp)
  80004204: ld a5,72(sp)
  80004208: addi a0,sp,16
  8000420c: sd a2,16(sp)
  80004210: sd a3,24(sp)
  80004214: sd a5,32(sp)
  80004218: jal 8000282c <value_truthy>
  -- block 0x8000421c [br]
  8000421c: li a6,8
  80004220: auipc a4,0x16
  80004224: addi a4,a4,-616
  80004228: beqz a0,800042cc <exec_stmt+0x2ec>
  -- block 0x800042cc [br]
  800042cc: ld s0,24(s0)
  800042d0: bnez s0,80004014 <exec_stmt+0x34>
  -- block 0x8000422c [j]
  8000422c: ld s0,16(s0)
  80004230: j 80004014 <exec_stmt+0x34>
  -- block 0x80004014 [br] LOOP-HEAD
  80004014: lw a5,0(s0)
  80004018: bltu a6,a5,80004090 <exec_stmt+0xb0>
  -- block 0x800042d4 [j]
  800042d4: li a0,0
  800042d8: j 8000409c <exec_stmt+0xbc>
  -- block 0x80004090 [j] LOOP-HEAD
  80004090: li a0,0
  80004094: j 8000409c <exec_stmt+0xbc>
  -- block 0x8000401c [ret]
  8000401c: lwu a5,0(s0)
  80004020: slli a5,a5,0x2
  80004024: add a5,a5,a4
  80004028: lw a5,0(a5)
  8000402c: add a5,a5,a4
  80004030: jr a5
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
```
