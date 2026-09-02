# io_swbuf_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: buffer spill + flush trigger
- entry: 0x8000f0c8 (inside `__swbuf_r` [0x8000f0c8, 0x8000f21c))
- containing-fn CFG: 24 blocks, 14 branches, loop-template=no

## Case slice (24 blocks)

- Block(0x8000f0c8..0x8000f0e0 beqz kind=br succs=['0x8000f0ec', '0x8000f0e4'])
- Block(0x8000f0ec..0x8000f0fc beqz kind=br succs=['0x8000f188', '0x8000f100'])
- Block(0x8000f0e4..0x8000f0e8 beqz kind=br succs=['0x8000f20c', '0x8000f0ec'])
- Block(0x8000f188..0x8000f194 jal kind=jal succs=['0x8000f198'])
- Block(0x8000f100..0x8000f104 beqz kind=br succs=['0x8000f188', '0x8000f108'])
- Block(0x8000f20c..0x8000f210 jal kind=jal succs=['0x8000f214'])
- Block(0x8000f198..0x8000f198 bnez kind=br succs=['0x8000f1e0', '0x8000f19c'])
- Block(0x8000f108..0x8000f114 bgez kind=br succs=['0x8000f1b4', '0x8000f118'])
- Block(0x8000f214..0x8000f218 j kind=j succs=['0x8000f0ec'])
- Block(0x8000f1e0..0x8000f1e4 j kind=j succs=['0x8000f170'])
- Block(0x8000f19c..0x8000f1b0 bltz kind=br succs=['0x8000f118', '0x8000f1b4'])
- Block(0x8000f1b4..0x8000f1cc j kind=j succs=['0x8000f118'])
- Block(0x8000f118..0x8000f11c bltz kind=br succs=['0x8000f1e0', '0x8000f120'])
- Block(0x8000f170..0x8000f184 ret kind=ret succs=[])
- Block(0x8000f120..0x8000f130 bge kind=br succs=['0x8000f1e8', '0x8000f134'])
- Block(0x8000f1e8..0x8000f1f4 jal kind=jal succs=['0x8000f1f8'])
- Block(0x8000f134..0x8000f134 fall kind=fallthrough succs=['0x8000f138'])
- Block(0x8000f1f8..0x8000f1f8 bnez kind=br succs=['0x8000f1e0', '0x8000f1fc'])
- Block(0x8000f138..0x8000f158 beq kind=br succs=['0x8000f1d0', '0x8000f15c'])
- Block(0x8000f1fc..0x8000f208 j kind=j succs=['0x8000f138'])
- Block(0x8000f1d0..0x8000f1d8 jal kind=jal succs=['0x8000f1dc'])
- Block(0x8000f15c..0x8000f164 beqz kind=br succs=['0x8000f170', '0x8000f168'])
- Block(0x8000f1dc..0x8000f1dc beqz kind=br succs=['0x8000f170', '0x8000f1e0'])
- Block(0x8000f168..0x8000f16c beqz kind=br succs=['0x8000f1d0', '0x8000f170'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `__swsetup_r` → NONE
- `__sinit` → NONE
- `_fflush_r` → LANDED (svfprintf_flushReturn_spec, svfprintf_flushReturn1_spec)

## Register/memory outcome sketch

- regs written on slice: sp, s1, s0, a4, a5, a1, a0, a3, a2, ra
- loads: 20, stores: 12

## Disasm slice

```
  -- block 0x8000f0c8 [br]
  8000f0c8: addi sp,sp,-48
  8000f0cc: sd s0,32(sp)
  8000f0d0: sd s1,24(sp)
  8000f0d4: sd ra,40(sp)
  8000f0d8: mv s1,a0
  8000f0dc: mv s0,a1
  8000f0e0: beqz a0,8000f0ec <__swbuf_r+0x24>
  -- block 0x8000f0ec [br] LOOP-HEAD
  8000f0ec: lw a4,40(a2)
  8000f0f0: lh a5,16(a2)
  8000f0f4: sw a4,12(a2)
  8000f0f8: andi a4,a5,8
  8000f0fc: beqz a4,8000f188 <__swbuf_r+0xc0>
  -- block 0x8000f0e4 [br]
  8000f0e4: ld a5,72(a0)
  8000f0e8: beqz a5,8000f20c <__swbuf_r+0x144>
  -- block 0x8000f188 [jal]
  8000f188: mv a1,a2
  8000f18c: mv a0,s1
  8000f190: sd a2,8(sp)
  8000f194: jal 8000f230 <__swsetup_r>
  -- block 0x8000f100 [br]
  8000f100: ld a4,24(a2)
  8000f104: beqz a4,8000f188 <__swbuf_r+0xc0>
  -- block 0x8000f20c [jal]
  8000f20c: sd a2,8(sp)
  8000f210: jal 800060c0 <__sinit>
  -- block 0x8000f198 [br]
  8000f198: bnez a0,8000f1e0 <__swbuf_r+0x118>
  -- block 0x8000f108 [br]
  8000f108: slli a3,a5,0x32
  8000f10c: lw a4,176(a2)
  8000f110: lui a1,0x2
  8000f114: bgez a3,8000f1b4 <__swbuf_r+0xec>
  -- block 0x8000f214 [j]
  8000f214: ld a2,8(sp)
  8000f218: j 8000f0ec <__swbuf_r+0x24>
  -- block 0x8000f1e0 [j] LOOP-HEAD
  8000f1e0: li s0,-1
  8000f1e4: j 8000f170 <__swbuf_r+0xa8>
  -- block 0x8000f19c [br]
  8000f19c: ld a2,8(sp)
  8000f1a0: lui a1,0x2
  8000f1a4: lh a5,16(a2)
  8000f1a8: lw a4,176(a2)
  8000f1ac: slli a3,a5,0x32
  8000f1b0: bltz a3,8000f118 <__swbuf_r+0x50>
  -- block 0x8000f1b4 [j]
  8000f1b4: lui a3,0xffffe
  8000f1b8: addi a3,a3,-1
  8000f1bc: or a5,a5,a1
  8000f1c0: and a4,a4,a3
  8000f1c4: sh a5,16(a2)
  8000f1c8: sw a4,176(a2)
  8000f1cc: j 8000f118 <__swbuf_r+0x50>
  -- block 0x8000f118 [br] LOOP-HEAD
  8000f118: slli a5,a4,0x32
  8000f11c: bltz a5,8000f1e0 <__swbuf_r+0x118>
  -- block 0x8000f170 [ret] LOOP-HEAD
  8000f170: ld ra,40(sp)
  8000f174: mv a0,s0
  8000f178: ld s0,32(sp)
  8000f17c: ld s1,24(sp)
  8000f180: addi sp,sp,48
  8000f184: ret 
  -- block 0x8000f120 [br]
  8000f120: ld a4,0(a2)
  8000f124: ld a5,24(a2)
  8000f128: lw a3,32(a2)
  8000f12c: subw a5,a4,a5
  8000f130: bge a5,a3,8000f1e8 <__swbuf_r+0x120>
  -- block 0x8000f1e8 [jal]
  8000f1e8: mv a1,a2
  8000f1ec: mv a0,s1
  8000f1f0: sd a2,8(sp)
  8000f1f4: jal 8000edcc <_fflush_r>
  -- block 0x8000f134 [fallthrough]
  8000f134: addiw a5,a5,1
  -- block 0x8000f1f8 [br]
  8000f1f8: bnez a0,8000f1e0 <__swbuf_r+0x118>
  -- block 0x8000f138 [br] LOOP-HEAD
  8000f138: lw a3,12(a2)
  8000f13c: addi a1,a4,1
  8000f140: sd a1,0(a2)
  8000f144: addiw a3,a3,-1
  8000f148: sw a3,12(a2)
  8000f14c: sb s0,0(a4)
  8000f150: lw a4,32(a2)
  8000f154: zext.b s0,s0
  8000f158: beq a4,a5,8000f1d0 <__swbuf_r+0x108>
  -- block 0x8000f1fc [j]
  8000f1fc: ld a2,8(sp)
  8000f200: li a5,1
  8000f204: ld a4,0(a2)
  8000f208: j 8000f138 <__swbuf_r+0x70>
  -- block 0x8000f1d0 [jal]
  8000f1d0: mv a1,a2
  8000f1d4: mv a0,s1
  8000f1d8: jal 8000edcc <_fflush_r>
  -- block 0x8000f15c [br]
  8000f15c: lhu a5,16(a2)
  8000f160: andi a5,a5,1
  8000f164: beqz a5,8000f170 <__swbuf_r+0xa8>
  -- block 0x8000f1dc [br]
  8000f1dc: beqz a0,8000f170 <__swbuf_r+0xa8>
  -- block 0x8000f168 [br]
  8000f168: addi a5,s0,-10
  8000f16c: beqz a5,8000f1d0 <__swbuf_r+0x108>
```
