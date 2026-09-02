# io_snprintf

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: ABI wrapper (landed snprintf_lld_spec; kept for cross-ref)
- entry: 0x80005c44 (inside `snprintf` [0x80005c44, 0x80005d18))
- containing-fn CFG: 10 blocks, 4 branches, loop-template=no

## Case slice (10 blocks)

- Block(0x80005c44..0x80005c70 bltu kind=br succs=['0x80005d08', '0x80005c74'])
- Block(0x80005d08..0x80005d14 j kind=j succs=['0x80005ccc'])
- Block(0x80005c74..0x80005cb8 jal kind=jal succs=['0x80005cbc'])
- Block(0x80005ccc..0x80005cd8 ret kind=ret succs=[])
- Block(0x80005cbc..0x80005cc0 blt kind=br succs=['0x80005cf8', '0x80005cc4'])
- Block(0x80005cf8..0x80005d00 beqz kind=br succs=['0x80005cc8', '0x80005d04'])
- Block(0x80005cc4..0x80005cc4 bnez kind=br succs=['0x80005cdc', '0x80005cc8'])
- Block(0x80005cc8..0x80005cc8 fall kind=fallthrough succs=['0x80005ccc'])
- Block(0x80005d04..0x80005d04 j kind=j succs=['0x80005cdc'])
- Block(0x80005cdc..0x80005cf4 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_svfprintf_r` → LANDED (iov2ToSvfprintfRet_spec)

## Register/memory outcome sketch

- regs written on slice: sp, t1, s1, a5, a0, a4, a6, a3, s0, a1, ra
- loads: 8, stores: 18

## Disasm slice

```
  -- block 0x80005c44 [br]
  80005c44: addi sp,sp,-272
  80005c48: lui t1,0x80000
  80005c4c: sd s1,200(sp)
  80005c50: sd ra,216(sp)
  80005c54: sd a3,232(sp)
  80005c58: sd a4,240(sp)
  80005c5c: sd a5,248(sp)
  80005c60: sd a6,256(sp)
  80005c64: sd a7,264(sp)
  80005c68: not t1,t1
  80005c6c: ld s1,1120(gp)
  80005c70: bltu t1,a1,80005d08 <snprintf+0xc4>
  -- block 0x80005d08 [j]
  80005d08: li a5,139
  80005d0c: sw a5,0(s1)
  80005d10: li a0,-1
  80005d14: j 80005ccc <snprintf+0x88>
  -- block 0x80005c74 [jal]
  80005c74: snez a4,a1
  80005c78: lui a6,0xffff0
  80005c7c: mv a5,a0
  80005c80: subw a4,a1,a4
  80005c84: sd s0,208(sp)
  80005c88: addi a3,sp,232
  80005c8c: addi a6,a6,520
  80005c90: mv s0,a1
  80005c94: mv a0,s1
  80005c98: addi a1,sp,8
  80005c9c: sd a5,8(sp)
  80005ca0: sd a5,32(sp)
  80005ca4: sw zero,184(sp)
  80005ca8: sw a4,20(sp)
  80005cac: sw a4,40(sp)
  80005cb0: sw a6,24(sp)
  80005cb4: sd a3,0(sp)
  80005cb8: jal 80007654 <_svfprintf_r>
  -- block 0x80005ccc [ret] LOOP-HEAD
  80005ccc: ld ra,216(sp)
  80005cd0: ld s1,200(sp)
  80005cd4: addi sp,sp,272
  80005cd8: ret 
  -- block 0x80005cbc [br]
  80005cbc: li a5,-1
  80005cc0: blt a0,a5,80005cf8 <snprintf+0xb4>
  -- block 0x80005cf8 [br]
  80005cf8: li a5,139
  80005cfc: sw a5,0(s1)
  80005d00: beqz s0,80005cc8 <snprintf+0x84>
  -- block 0x80005cc4 [br]
  80005cc4: bnez s0,80005cdc <snprintf+0x98>
  -- block 0x80005cc8 [fallthrough] LOOP-HEAD
  80005cc8: ld s0,208(sp)
  -- block 0x80005d04 [j]
  80005d04: j 80005cdc <snprintf+0x98>
  -- block 0x80005cdc [ret] LOOP-HEAD
  80005cdc: ld a5,8(sp)
  80005ce0: sb zero,0(a5)
  80005ce4: ld s0,208(sp)
  80005ce8: ld ra,216(sp)
  80005cec: ld s1,200(sp)
  80005cf0: addi sp,sp,272
  80005cf4: ret 
```
