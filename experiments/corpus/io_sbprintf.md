# io_sbprintf

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: buffered-arm detour (57i; second copy at 0x8001688c)
- entry: 0x8000dda8 (inside `__sbprintf` [0x8000dda8, 0x8000de8c))
- containing-fn CFG: 10 blocks, 3 branches, loop-template=no

## Case slice (10 blocks)

- Block(0x8000dda8..0x8000de18 jal kind=jal succs=['0x8000de1c'])
- Block(0x8000de1c..0x8000de2c jal kind=jal succs=['0x8000de30'])
- Block(0x8000de30..0x8000de34 bgez kind=br succs=['0x8000de74', '0x8000de38'])
- Block(0x8000de74..0x8000de7c jal kind=jal succs=['0x8000de80'])
- Block(0x8000de38..0x8000de40 beqz kind=br succs=['0x8000de50', '0x8000de44'])
- Block(0x8000de80..0x8000de80 beqz kind=br succs=['0x8000de38', '0x8000de84'])
- Block(0x8000de50..0x8000de54 jal kind=jal succs=['0x8000de58'])
- Block(0x8000de44..0x8000de4c fall kind=fallthrough succs=['0x8000de50'])
- Block(0x8000de84..0x8000de88 j kind=j succs=['0x8000de38'])
- Block(0x8000de58..0x8000de70 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `__retarget_lock_init_recursive` → NONE
- `_vfprintf_r` → LANDED (iov2ToSvfprintfRet_spec)
- `_fflush_r` → LANDED (svfprintf_flushReturn_spec, svfprintf_flushReturn1_spec)
- `__retarget_lock_close_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: a5, t3, t1, a7, a6, sp, a4, s0, s2, a1, a0, s1, a3, a2, ra
- loads: 13, stores: 16

## Disasm slice

```
  -- block 0x8000dda8 [jal]
  8000dda8: lhu a5,16(a1)
  8000ddac: lw t3,176(a1)
  8000ddb0: lhu t1,18(a1)
  8000ddb4: ld a7,48(a1)
  8000ddb8: ld a6,64(a1)
  8000ddbc: addi sp,sp,-1264
  8000ddc0: li a4,1024
  8000ddc4: andi a5,a5,-3
  8000ddc8: sd s0,1248(sp)
  8000ddcc: sd s2,1232(sp)
  8000ddd0: mv s0,a1
  8000ddd4: mv s2,a0
  8000ddd8: addi a1,sp,208
  8000dddc: addi a0,sp,184
  8000dde0: sd ra,1256(sp)
  8000dde4: sd s1,1240(sp)
  8000dde8: sd a3,8(sp)
  8000ddec: mv s1,a2
  8000ddf0: sh a5,40(sp)
  8000ddf4: sw t3,200(sp)
  8000ddf8: sh t1,42(sp)
  8000ddfc: sd a7,72(sp)
  8000de00: sd a6,88(sp)
  8000de04: sd a1,24(sp)
  8000de08: sd a1,48(sp)
  8000de0c: sw a4,36(sp)
  8000de10: sw a4,56(sp)
  8000de14: sw zero,64(sp)
  8000de18: jal 80006fd0 <__retarget_lock_init_recursive>
  -- block 0x8000de1c [jal]
  8000de1c: ld a3,8(sp)
  8000de20: mv a2,s1
  8000de24: addi a1,sp,24
  8000de28: mv a0,s2
  8000de2c: jal 8000a884 <_vfprintf_r>
  -- block 0x8000de30 [br]
  8000de30: mv s1,a0
  8000de34: bgez a0,8000de74 <__sbprintf+0xcc>
  -- block 0x8000de74 [jal]
  8000de74: addi a1,sp,24
  8000de78: mv a0,s2
  8000de7c: jal 8000edcc <_fflush_r>
  -- block 0x8000de38 [br] LOOP-HEAD
  8000de38: lhu a5,40(sp)
  8000de3c: andi a5,a5,64
  8000de40: beqz a5,8000de50 <__sbprintf+0xa8>
  -- block 0x8000de80 [br]
  8000de80: beqz a0,8000de38 <__sbprintf+0x90>
  -- block 0x8000de50 [jal]
  8000de50: ld a0,184(sp)
  8000de54: jal 80006fd8 <__retarget_lock_close_recursive>
  -- block 0x8000de44 [fallthrough]
  8000de44: lhu a5,16(s0)
  8000de48: ori a5,a5,64
  8000de4c: sh a5,16(s0)
  -- block 0x8000de84 [j]
  8000de84: li s1,-1
  8000de88: j 8000de38 <__sbprintf+0x90>
  -- block 0x8000de58 [ret]
  8000de58: ld ra,1256(sp)
  8000de5c: ld s0,1248(sp)
  8000de60: ld s2,1232(sp)
  8000de64: mv a0,s1
  8000de68: ld s1,1240(sp)
  8000de6c: addi sp,sp,1264
  8000de70: ret 
```
