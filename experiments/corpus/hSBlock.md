# hSBlock

- kind: field
- consumes/consumed-by: TermResidualsCore.hSBlock
- note: exec block arm (allocFrame + seq) | skeleton: `hSBlock`/`exec_block_row`.  Supplier: `BlockResid` = `allocFrame` + seq exit-sim.
- entry: 0x8000418c (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (8 blocks)

- Block(0x8000418c..0x80004190 jal kind=jal succs=['0x80004194'])
- Block(0x80004194..0x800041a0 blez kind=br succs=['0x80004090', '0x800041a4'])
- Block(0x80004090..0x80004094 j kind=j succs=['0x8000409c'])
- Block(0x800041a4..0x800041c4 jal kind=jal succs=['0x800041c8'])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])
- Block(0x800041c8..0x800041c8 bnez kind=br succs=['0x8000409c', '0x800041cc'])
- Block(0x800041cc..0x800041dc blt kind=br succs=['0x800041a4', '0x800041e0'])
- Block(0x800041e0..0x800041e4 j kind=j succs=['0x8000409c'])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `env_new` → LANDED (env_new_spec, callClosureEnvNewRetFoldRow, CallClosureEnvNewRetFoldPost, callClosureEnvNewRetBypassRow)
- `exec_stmt` → NONE

## Register/memory outcome sketch

- regs written on slice: a0, a5, s3, a6, a4, a3, a1, a2, ra, s0, s1, s2, sp
- loads: 10, stores: 1

## Disasm slice

```
  -- block 0x8000418c [jal]
  8000418c: mv a0,s3
  80004190: jal 800029fc <env_new>
  -- block 0x80004194 [br]
  80004194: lw a5,16(s0)
  80004198: mv s3,a0
  8000419c: li a6,0
  800041a0: blez a5,80004090 <exec_stmt+0xb0>
  -- block 0x80004090 [j] LOOP-HEAD
  80004090: li a0,0
  80004094: j 8000409c <exec_stmt+0xbc>
  -- block 0x800041a4 [jal] LOOP-HEAD
  800041a4: ld a5,8(s0)
  800041a8: slli a4,a6,0x3
  800041ac: mv a3,s2
  800041b0: add a5,a5,a4
  800041b4: ld a1,0(a5)
  800041b8: mv a2,s3
  800041bc: mv a0,s1
  800041c0: sd a6,8(sp)
  800041c4: jal 80003fe0 <exec_stmt>
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
  -- block 0x800041c8 [br]
  800041c8: bnez a0,8000409c <exec_stmt+0xbc>
  -- block 0x800041cc [br]
  800041cc: ld a6,8(sp)
  800041d0: lw a4,16(s0)
  800041d4: addi a6,a6,1
  800041d8: sext.w a5,a6
  800041dc: blt a5,a4,800041a4 <exec_stmt+0x1c4>
  -- block 0x800041e0 [j]
  800041e0: li a0,0
  800041e4: j 8000409c <exec_stmt+0xbc>
```
