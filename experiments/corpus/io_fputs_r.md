# io_fputs_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: fputs over __sfvwrite_r
- entry: 0x800063b8 (inside `_fputs_r` [0x800063b8, 0x80006500))
- containing-fn CFG: 26 blocks, 12 branches, loop-template=no

## Case slice (26 blocks)

- Block(0x800063b8..0x800063d8 jal kind=jal succs=['0x800063dc'])
- Block(0x800063dc..0x800063f4 beqz kind=br succs=['0x80006400', '0x800063f8'])
- Block(0x80006400..0x8000640c beqz kind=br succs=['0x80006480', '0x80006410'])
- Block(0x800063f8..0x800063fc beqz kind=br succs=['0x800064ec', '0x80006400'])
- Block(0x80006480..0x80006484 beqz kind=br succs=['0x800064d0', '0x80006488'])
- Block(0x80006410..0x80006414 bltz kind=br succs=['0x800064a0', '0x80006418'])
- Block(0x800064ec..0x800064f0 jal kind=jal succs=['0x800064f4'])
- Block(0x800064d0..0x800064d4 jal kind=jal succs=['0x800064d8'])
- Block(0x80006488..0x8000648c bgez kind=br succs=['0x80006418', '0x80006490'])
- Block(0x800064a0..0x800064a4 bgez kind=br succs=['0x8000643c', '0x800064a8'])
- Block(0x80006418..0x80006430 fall kind=fallthrough succs=['0x80006434'])
- Block(0x800064f4..0x800064f4 j kind=j succs=['0x80006400'])
- Block(0x800064d8..0x800064e4 bltz kind=br succs=['0x80006434', '0x800064e8'])
- Block(0x80006490..0x80006494 bgez kind=br succs=['0x8000643c', '0x80006498'])
- Block(0x8000643c..0x80006448 jal kind=jal succs=['0x8000644c'])
- Block(0x800064a8..0x800064ac j kind=j succs=['0x80006468'])
- Block(0x80006434..0x80006438 bltz kind=br succs=['0x800064f8', '0x8000643c'])
- Block(0x800064e8..0x800064e8 j kind=j succs=['0x80006418'])
- Block(0x80006498..0x8000649c j kind=j succs=['0x8000645c'])
- Block(0x8000644c..0x80006450 fall kind=fallthrough succs=['0x80006454'])
- Block(0x80006468..0x8000647c ret kind=ret succs=[])
- Block(0x800064f8..0x800064fc j kind=j succs=['0x80006454'])
- Block(0x8000645c..0x80006464 beqz kind=br succs=['0x800064b0', '0x80006468'])
- Block(0x80006454..0x80006458 bnez kind=br succs=['0x80006468', '0x8000645c'])
- Block(0x800064b0..0x800064b4 jal kind=jal succs=['0x800064b8'])
- Block(0x800064b8..0x800064cc ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `strlen` → LANDED (strlen_spec, strlenArgRow, strlenCallSpec, strlen_full_spec, strdupStrlenArgRow, strlenCallSpec_sat)
- `__sinit` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__sfvwrite_r` → LANDED (sfvwrite_rXdee4Row, sfvwrite_rXdf10Row, sfvwrite_rXdf3cRow, sfvwrite_rXe0bcRow, sfvwrite_rXde8cFRow, sfvwrite_rXde94FRow)
- `__retarget_lock_release_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, s1, a0, s0, a4, a5, a3, a2, a1, ra
- loads: 15, stores: 10

## Disasm slice

```
  -- block 0x800063b8 [jal]
  800063b8: addi sp,sp,-80
  800063bc: sd s1,56(sp)
  800063c0: mv s1,a0
  800063c4: mv a0,a1
  800063c8: sd s0,64(sp)
  800063cc: sd ra,72(sp)
  800063d0: sd a1,8(sp)
  800063d4: mv s0,a2
  800063d8: jal 80006cf0 <strlen>
  -- block 0x800063dc [br]
  800063dc: addi a4,sp,8
  800063e0: li a5,1
  800063e4: sd a0,40(sp)
  800063e8: sd a0,16(sp)
  800063ec: sd a4,24(sp)
  800063f0: sw a5,32(sp)
  800063f4: beqz s1,80006400 <_fputs_r+0x48>
  -- block 0x80006400 [br] LOOP-HEAD
  80006400: lw a5,176(s0)
  80006404: lh a4,16(s0)
  80006408: andi a3,a5,1
  8000640c: beqz a3,80006480 <_fputs_r+0xc8>
  -- block 0x800063f8 [br]
  800063f8: ld a5,72(s1)
  800063fc: beqz a5,800064ec <_fputs_r+0x134>
  -- block 0x80006480 [br]
  80006480: andi a3,a4,512
  80006484: beqz a3,800064d0 <_fputs_r+0x118>
  -- block 0x80006410 [br]
  80006410: slli a3,a4,0x32
  80006414: bltz a3,800064a0 <_fputs_r+0xe8>
  -- block 0x800064ec [jal]
  800064ec: mv a0,s1
  800064f0: jal 800060c0 <__sinit>
  -- block 0x800064d0 [jal]
  800064d0: ld a0,160(s0)
  800064d4: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x80006488 [br]
  80006488: slli a3,a4,0x32
  8000648c: bgez a3,80006418 <_fputs_r+0x60>
  -- block 0x800064a0 [br]
  800064a0: slli a4,a5,0x32
  800064a4: bgez a4,8000643c <_fputs_r+0x84>
  -- block 0x80006418 [fallthrough] LOOP-HEAD
  80006418: lui a3,0xffffe
  8000641c: addi a3,a3,-1
  80006420: lui a2,0x2
  80006424: and a5,a5,a3
  80006428: or a4,a4,a2
  8000642c: sw a5,176(s0)
  80006430: sh a4,16(s0)
  -- block 0x800064f4 [j]
  800064f4: j 80006400 <_fputs_r+0x48>
  -- block 0x800064d8 [br]
  800064d8: lh a4,16(s0)
  800064dc: lw a5,176(s0)
  800064e0: slli a3,a4,0x32
  800064e4: bltz a3,80006434 <_fputs_r+0x7c>
  -- block 0x80006490 [br]
  80006490: slli a4,a5,0x32
  80006494: bgez a4,8000643c <_fputs_r+0x84>
  -- block 0x8000643c [jal] LOOP-HEAD
  8000643c: mv a0,s1
  80006440: addi a2,sp,24
  80006444: mv a1,s0
  80006448: jal 8000de8c <__sfvwrite_r>
  -- block 0x800064a8 [j]
  800064a8: li s1,-1
  800064ac: j 80006468 <_fputs_r+0xb0>
  -- block 0x80006434 [br] LOOP-HEAD
  80006434: slli a4,a5,0x32
  80006438: bltz a4,800064f8 <_fputs_r+0x140>
  -- block 0x800064e8 [j]
  800064e8: j 80006418 <_fputs_r+0x60>
  -- block 0x80006498 [j]
  80006498: li s1,-1
  8000649c: j 8000645c <_fputs_r+0xa4>
  -- block 0x8000644c [fallthrough]
  8000644c: lw a5,176(s0)
  80006450: mv s1,a0
  -- block 0x80006468 [ret] LOOP-HEAD
  80006468: ld ra,72(sp)
  8000646c: ld s0,64(sp)
  80006470: mv a0,s1
  80006474: ld s1,56(sp)
  80006478: addi sp,sp,80
  8000647c: ret 
  -- block 0x800064f8 [j]
  800064f8: li s1,-1
  800064fc: j 80006454 <_fputs_r+0x9c>
  -- block 0x8000645c [br] LOOP-HEAD
  8000645c: lhu a5,16(s0)
  80006460: andi a5,a5,512
  80006464: beqz a5,800064b0 <_fputs_r+0xf8>
  -- block 0x80006454 [br] LOOP-HEAD
  80006454: andi a5,a5,1
  80006458: bnez a5,80006468 <_fputs_r+0xb0>
  -- block 0x800064b0 [jal]
  800064b0: ld a0,160(s0)
  800064b4: jal 80006ff8 <__retarget_lock_release_recursive>
  -- block 0x800064b8 [ret]
  800064b8: ld ra,72(sp)
  800064bc: ld s0,64(sp)
  800064c0: mv a0,s1
  800064c4: ld s1,56(sp)
  800064c8: addi sp,sp,80
  800064cc: ret 
```
