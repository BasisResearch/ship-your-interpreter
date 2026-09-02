# io_putc_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: putc core: fast path + __swbuf_r spill
- entry: 0x8000e6a4 (inside `_putc_r` [0x8000e6a4, 0x8000e7b0))
- containing-fn CFG: 19 blocks, 9 branches, loop-template=no

## Case slice (19 blocks)

- Block(0x8000e6a4..0x8000e6b0 beqz kind=br succs=['0x8000e6bc', '0x8000e6b4'])
- Block(0x8000e6bc..0x8000e6c4 bnez kind=br succs=['0x8000e6d4', '0x8000e6c8'])
- Block(0x8000e6b4..0x8000e6b8 beqz kind=br succs=['0x8000e790', '0x8000e6bc'])
- Block(0x8000e6d4..0x8000e6e4 bgez kind=br succs=['0x8000e6f8', '0x8000e6e8'])
- Block(0x8000e6c8..0x8000e6d0 beqz kind=br succs=['0x8000e74c', '0x8000e6d4'])
- Block(0x8000e790..0x8000e79c jal kind=jal succs=['0x8000e7a0'])
- Block(0x8000e6f8..0x8000e708 fall kind=fallthrough succs=['0x8000e70c'])
- Block(0x8000e6e8..0x8000e6ec blt kind=br succs=['0x8000e734', '0x8000e6f0'])
- Block(0x8000e74c..0x8000e75c jal kind=jal succs=['0x8000e760'])
- Block(0x8000e7a0..0x8000e7ac j kind=j succs=['0x8000e6bc'])
- Block(0x8000e70c..0x8000e714 bnez kind=br succs=['0x8000e724', '0x8000e718'])
- Block(0x8000e734..0x8000e73c jal kind=jal succs=['0x8000e740'])
- Block(0x8000e6f0..0x8000e6f4 beqz kind=br succs=['0x8000e734', '0x8000e6f8'])
- Block(0x8000e760..0x8000e76c j kind=j succs=['0x8000e6d4'])
- Block(0x8000e724..0x8000e730 ret kind=ret succs=[])
- Block(0x8000e718..0x8000e720 beqz kind=br succs=['0x8000e770', '0x8000e724'])
- Block(0x8000e740..0x8000e748 j kind=j succs=['0x8000e70c'])
- Block(0x8000e770..0x8000e778 jal kind=jal succs=['0x8000e77c'])
- Block(0x8000e77c..0x8000e78c ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `__sinit` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__swbuf_r` → NONE
- `__retarget_lock_release_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, a4, a5, a3, a1, a0, a2, ra
- loads: 20, stores: 12

## Disasm slice

```
  -- block 0x8000e6a4 [br]
  8000e6a4: addi sp,sp,-48
  8000e6a8: sd ra,40(sp)
  8000e6ac: mv a4,a0
  8000e6b0: beqz a0,8000e6bc <_putc_r+0x18>
  -- block 0x8000e6bc [br] LOOP-HEAD
  8000e6bc: lw a5,176(a2)
  8000e6c0: andi a5,a5,1
  8000e6c4: bnez a5,8000e6d4 <_putc_r+0x30>
  -- block 0x8000e6b4 [br]
  8000e6b4: ld a5,72(a0)
  8000e6b8: beqz a5,8000e790 <_putc_r+0xec>
  -- block 0x8000e6d4 [br] LOOP-HEAD
  8000e6d4: lw a5,12(a2)
  8000e6d8: zext.b a3,a1
  8000e6dc: addiw a5,a5,-1
  8000e6e0: sw a5,12(a2)
  8000e6e4: bgez a5,8000e6f8 <_putc_r+0x54>
  -- block 0x8000e6c8 [br]
  8000e6c8: lhu a5,16(a2)
  8000e6cc: andi a5,a5,512
  8000e6d0: beqz a5,8000e74c <_putc_r+0xa8>
  -- block 0x8000e790 [jal]
  8000e790: sd a2,24(sp)
  8000e794: sd a1,16(sp)
  8000e798: sd a0,8(sp)
  8000e79c: jal 800060c0 <__sinit>
  -- block 0x8000e6f8 [fallthrough]
  8000e6f8: ld a5,0(a2)
  8000e6fc: zext.b a1,a1
  8000e700: addi a4,a5,1
  8000e704: sd a4,0(a2)
  8000e708: sb a3,0(a5)
  -- block 0x8000e6e8 [br]
  8000e6e8: lw a0,40(a2)
  8000e6ec: blt a5,a0,8000e734 <_putc_r+0x90>
  -- block 0x8000e74c [jal]
  8000e74c: ld a0,160(a2)
  8000e750: sd a1,24(sp)
  8000e754: sd a4,16(sp)
  8000e758: sd a2,8(sp)
  8000e75c: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x8000e7a0 [j]
  8000e7a0: ld a2,24(sp)
  8000e7a4: ld a1,16(sp)
  8000e7a8: ld a4,8(sp)
  8000e7ac: j 8000e6bc <_putc_r+0x18>
  -- block 0x8000e70c [br] LOOP-HEAD
  8000e70c: lw a5,176(a2)
  8000e710: andi a5,a5,1
  8000e714: bnez a5,8000e724 <_putc_r+0x80>
  -- block 0x8000e734 [jal]
  8000e734: mv a0,a4
  8000e738: sd a2,8(sp)
  8000e73c: jal 8000f0c8 <__swbuf_r>
  -- block 0x8000e6f0 [br]
  8000e6f0: addi a5,a3,-10
  8000e6f4: beqz a5,8000e734 <_putc_r+0x90>
  -- block 0x8000e760 [j]
  8000e760: ld a1,24(sp)
  8000e764: ld a4,16(sp)
  8000e768: ld a2,8(sp)
  8000e76c: j 8000e6d4 <_putc_r+0x30>
  -- block 0x8000e724 [ret]
  8000e724: ld ra,40(sp)
  8000e728: mv a0,a1
  8000e72c: addi sp,sp,48
  8000e730: ret 
  -- block 0x8000e718 [br]
  8000e718: lhu a5,16(a2)
  8000e71c: andi a5,a5,512
  8000e720: beqz a5,8000e770 <_putc_r+0xcc>
  -- block 0x8000e740 [j]
  8000e740: ld a2,8(sp)
  8000e744: mv a1,a0
  8000e748: j 8000e70c <_putc_r+0x68>
  -- block 0x8000e770 [jal]
  8000e770: ld a0,160(a2)
  8000e774: sd a1,8(sp)
  8000e778: jal 80006ff8 <__retarget_lock_release_recursive>
  -- block 0x8000e77c [ret]
  8000e77c: ld a1,8(sp)
  8000e780: ld ra,40(sp)
  8000e784: mv a0,a1
  8000e788: addi sp,sp,48
  8000e78c: ret 
```
