# io_sflush_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: flush core
- entry: 0x8000eb70 (inside `__sflush_r` [0x8000eb70, 0x8000edcc))
- containing-fn CFG: 45 blocks, 25 branches, loop-template=no

## Case slice (28 blocks, truncated closure)

- Block(0x8000eb70..0x8000eb90 bnez kind=br succs=['0x8000ecb4', '0x8000eb94'])
- Block(0x8000ecb4..0x8000ecbc beqz kind=br succs=['0x8000ed50', '0x8000ecc0'])
- Block(0x8000eb94..0x8000eba8 blez kind=br succs=['0x8000ed40', '0x8000ebac'])
- Block(0x8000ed50..0x8000ed54 j kind=j succs=['0x8000ec9c'])
- Block(0x8000ecc0..0x8000ecd8 bnez kind=br succs=['0x8000ece0', '0x8000ecdc'])
- Block(0x8000ed40..0x8000ed44 bgtz kind=br succs=['0x8000ebac', '0x8000ed48'])
- Block(0x8000ebac..0x8000ebb0 beqz kind=br succs=['0x8000ec9c', '0x8000ebb4'])
- Block(0x8000ec9c..0x8000ecb0 ret kind=ret succs=[])
- Block(0x8000ece0..0x8000ece4 bgtz kind=br succs=['0x8000ecf4', '0x8000ece8'])
- Block(0x8000ecdc..0x8000ecdc fall kind=fallthrough succs=['0x8000ece0'])
- Block(0x8000ed48..0x8000ed48 j kind=j succs=['0x8000ec9c'])
- Block(0x8000ebb4..0x8000ebc4 bltz kind=br succs=['0x8000ed58', '0x8000ebc8'])
- Block(0x8000ecf4..0x8000ed08 jalr kind=jalrcall succs=['0x8000ed0c'])
- Block(0x8000ece8..0x8000ece8 j kind=j succs=['0x8000ed4c'])
- Block(0x8000ed58..0x8000ed5c j kind=j succs=['0x8000ebf0'])
- Block(0x8000ebc8..0x8000ebd8 jalr kind=jalrcall succs=['0x8000ebdc'])
- Block(0x8000ed0c..0x8000ed10 bgtz kind=br succs=['0x8000ecec', '0x8000ed14'])
- Block(0x8000ed4c..0x8000ed4c fall kind=fallthrough succs=['0x8000ed50'])
- Block(0x8000ebf0..0x8000ebf4 beqz kind=br succs=['0x8000ec10', '0x8000ebf8'])
- Block(0x8000ebdc..0x8000ebe4 beq kind=br succs=['0x8000ed9c', '0x8000ebe8'])
- Block(0x8000ecec..0x8000ecf0 blez kind=br succs=['0x8000ed4c', '0x8000ecf4'])
- Block(0x8000ed14..0x8000ed1c fall kind=fallthrough succs=['0x8000ed20'])
- Block(0x8000ec10..0x8000ec1c jalr kind=jalrcall succs=['0x8000ec20'])
- Block(0x8000ebf8..0x8000ec04 beqz kind=br succs=['0x8000ec10', '0x8000ec08'])
- Block(0x8000ed9c..0x8000eda0 beqz kind=br succs=['0x8000ebe8', '0x8000eda4'])
- Block(0x8000ebe8..0x8000ebec fall kind=fallthrough succs=['0x8000ebf0'])
- Block(0x8000ed20..0x8000ed3c ret kind=ret succs=[])
- Block(0x8000ec20..0x8000ec28 bne kind=br succs=['0x8000ed60', '0x8000ec2c'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jalrcall, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- (no call seams on slice)

## Register/memory outcome sketch

- regs written on slice: a4, sp, a5, s0, s3, s2, a3, s1, a6, ra, a0, a1, a2
- loads: 30, stores: 11

## Disasm slice

```
  -- block 0x8000eb70 [br]
  8000eb70: lh a4,16(a1)
  8000eb74: addi sp,sp,-48
  8000eb78: sd s0,32(sp)
  8000eb7c: sd s3,8(sp)
  8000eb80: sd ra,40(sp)
  8000eb84: andi a5,a4,8
  8000eb88: mv s0,a1
  8000eb8c: mv s3,a0
  8000eb90: bnez a5,8000ecb4 <__sflush_r+0x144>
  -- block 0x8000ecb4 [br]
  8000ecb4: sd s2,16(sp)
  8000ecb8: ld s2,24(a1)
  8000ecbc: beqz s2,8000ed50 <__sflush_r+0x1e0>
  -- block 0x8000eb94 [br]
  8000eb94: lui a5,0x1
  8000eb98: addi a5,a5,-2048
  8000eb9c: lw a3,8(a1)
  8000eba0: or a5,a4,a5
  8000eba4: sh a5,16(a1)
  8000eba8: blez a3,8000ed40 <__sflush_r+0x1d0>
  -- block 0x8000ed50 [j]
  8000ed50: ld s2,16(sp)
  8000ed54: j 8000ec9c <__sflush_r+0x12c>
  -- block 0x8000ecc0 [br]
  8000ecc0: sd s1,24(sp)
  8000ecc4: ld s1,0(a1)
  8000ecc8: andi a4,a4,3
  8000eccc: sd s2,0(a1)
  8000ecd0: subw s1,s1,s2
  8000ecd4: li a5,0
  8000ecd8: bnez a4,8000ece0 <__sflush_r+0x170>
  -- block 0x8000ed40 [br]
  8000ed40: lw a3,112(a1)
  8000ed44: bgtz a3,8000ebac <__sflush_r+0x3c>
  -- block 0x8000ebac [br] LOOP-HEAD
  8000ebac: ld a6,72(s0)
  8000ebb0: beqz a6,8000ec9c <__sflush_r+0x12c>
  -- block 0x8000ec9c [ret] LOOP-HEAD
  8000ec9c: ld ra,40(sp)
  8000eca0: ld s0,32(sp)
  8000eca4: ld s3,8(sp)
  8000eca8: li a0,0
  8000ecac: addi sp,sp,48
  8000ecb0: ret 
  -- block 0x8000ece0 [br]
  8000ece0: sw a5,12(s0)
  8000ece4: bgtz s1,8000ecf4 <__sflush_r+0x184>
  -- block 0x8000ecdc [fallthrough]
  8000ecdc: lw a5,32(a1)
  -- block 0x8000ed48 [j]
  8000ed48: j 8000ec9c <__sflush_r+0x12c>
  -- block 0x8000ebb4 [br]
  8000ebb4: sd s1,24(sp)
  8000ebb8: slli a3,a4,0x33
  8000ebbc: lw s1,0(s3)
  8000ebc0: sw zero,0(s3)
  8000ebc4: bltz a3,8000ed58 <__sflush_r+0x1e8>
  -- block 0x8000ecf4 [jalrcall]
  8000ecf4: ld a5,64(s0)
  8000ecf8: ld a1,48(s0)
  8000ecfc: mv a3,s1
  8000ed00: mv a2,s2
  8000ed04: mv a0,s3
  8000ed08: jalr a5
  -- block 0x8000ece8 [j]
  8000ece8: j 8000ed4c <__sflush_r+0x1dc>
  -- block 0x8000ed58 [j]
  8000ed58: ld a2,144(s0)
  8000ed5c: j 8000ebf0 <__sflush_r+0x80>
  -- block 0x8000ebc8 [jalrcall]
  8000ebc8: ld a1,48(s0)
  8000ebcc: li a2,0
  8000ebd0: li a3,1
  8000ebd4: mv a0,s3
  8000ebd8: jalr a6
  -- block 0x8000ed0c [br]
  8000ed0c: subw s1,s1,a0
  8000ed10: bgtz a0,8000ecec <__sflush_r+0x17c>
  -- block 0x8000ed4c [fallthrough]
  8000ed4c: ld s1,24(sp)
  -- block 0x8000ebf0 [br] LOOP-HEAD
  8000ebf0: andi a5,a5,4
  8000ebf4: beqz a5,8000ec10 <__sflush_r+0xa0>
  -- block 0x8000ebdc [br]
  8000ebdc: li a5,-1
  8000ebe0: mv a2,a0
  8000ebe4: beq a0,a5,8000ed9c <__sflush_r+0x22c>
  -- block 0x8000ecec [br] LOOP-HEAD
  8000ecec: add s2,s2,a0
  8000ecf0: blez s1,8000ed4c <__sflush_r+0x1dc>
  -- block 0x8000ed14 [fallthrough]
  8000ed14: lhu a5,16(s0)
  8000ed18: ld s2,16(sp)
  8000ed1c: ori a5,a5,64
  -- block 0x8000ec10 [jalrcall]
  8000ec10: ld a1,48(s0)
  8000ec14: li a3,0
  8000ec18: mv a0,s3
  8000ec1c: jalr a6
  -- block 0x8000ebf8 [br]
  8000ebf8: lw a4,8(s0)
  8000ebfc: ld a5,88(s0)
  8000ec00: sub a2,a2,a4
  8000ec04: beqz a5,8000ec10 <__sflush_r+0xa0>
  -- block 0x8000ed9c [br]
  8000ed9c: lw a5,0(s3)
  8000eda0: beqz a5,8000ebe8 <__sflush_r+0x78>
  -- block 0x8000ebe8 [fallthrough] LOOP-HEAD
  8000ebe8: lh a5,16(s0)
  8000ebec: ld a6,72(s0)
  -- block 0x8000ed20 [ret] LOOP-HEAD
  8000ed20: ld ra,40(sp)
  8000ed24: sh a5,16(s0)
  8000ed28: ld s0,32(sp)
  8000ed2c: ld s1,24(sp)
  8000ed30: ld s3,8(sp)
  … (disasm capped at 90 lines)
```
