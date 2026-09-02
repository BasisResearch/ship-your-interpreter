# io_fflush_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: flush shim
- entry: 0x8000edcc (inside `_fflush_r` [0x8000edcc, 0x8000ee94))
- containing-fn CFG: 15 blocks, 7 branches, loop-template=no

## Case slice (15 blocks)

- Block(0x8000edcc..0x8000edd8 beqz kind=br succs=['0x8000ede4', '0x8000eddc'])
- Block(0x8000ede4..0x8000edec beqz kind=br succs=['0x8000ee30', '0x8000edf0'])
- Block(0x8000eddc..0x8000ede0 beqz kind=br succs=['0x8000ee7c', '0x8000ede4'])
- Block(0x8000ee30..0x8000ee3c ret kind=ret succs=[])
- Block(0x8000edf0..0x8000edf8 bnez kind=br succs=['0x8000ee04', '0x8000edfc'])
- Block(0x8000ee7c..0x8000ee84 jal kind=jal succs=['0x8000ee88'])
- Block(0x8000ee04..0x8000ee0c jal kind=jal succs=['0x8000ee10'])
- Block(0x8000edfc..0x8000ee00 beqz kind=br succs=['0x8000ee40', '0x8000ee04'])
- Block(0x8000ee88..0x8000ee90 j kind=j succs=['0x8000ede4'])
- Block(0x8000ee10..0x8000ee20 bnez kind=br succs=['0x8000ee30', '0x8000ee24'])
- Block(0x8000ee40..0x8000ee4c jal kind=jal succs=['0x8000ee50'])
- Block(0x8000ee24..0x8000ee2c beqz kind=br succs=['0x8000ee5c', '0x8000ee30'])
- Block(0x8000ee50..0x8000ee58 j kind=j succs=['0x8000ee04'])
- Block(0x8000ee5c..0x8000ee64 jal kind=jal succs=['0x8000ee68'])
- Block(0x8000ee68..0x8000ee78 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `__sinit` → NONE
- `__sflush_r` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__retarget_lock_release_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, a4, a3, a5, ra, a0, a1
- loads: 15, stores: 7

## Disasm slice

```
  -- block 0x8000edcc [br]
  8000edcc: addi sp,sp,-32
  8000edd0: sd ra,24(sp)
  8000edd4: mv a4,a0
  8000edd8: beqz a0,8000ede4 <_fflush_r+0x18>
  -- block 0x8000ede4 [br] LOOP-HEAD
  8000ede4: lh a3,16(a1)
  8000ede8: li a5,0
  8000edec: beqz a3,8000ee30 <_fflush_r+0x64>
  -- block 0x8000eddc [br]
  8000eddc: ld a5,72(a0)
  8000ede0: beqz a5,8000ee7c <_fflush_r+0xb0>
  -- block 0x8000ee30 [ret]
  8000ee30: ld ra,24(sp)
  8000ee34: mv a0,a5
  8000ee38: addi sp,sp,32
  8000ee3c: ret 
  -- block 0x8000edf0 [br]
  8000edf0: lw a5,176(a1)
  8000edf4: andi a5,a5,1
  8000edf8: bnez a5,8000ee04 <_fflush_r+0x38>
  -- block 0x8000ee7c [jal]
  8000ee7c: sd a1,8(sp)
  8000ee80: sd a0,0(sp)
  8000ee84: jal 800060c0 <__sinit>
  -- block 0x8000ee04 [jal] LOOP-HEAD
  8000ee04: mv a0,a4
  8000ee08: sd a1,0(sp)
  8000ee0c: jal 8000eb70 <__sflush_r>
  -- block 0x8000edfc [br]
  8000edfc: andi a3,a3,512
  8000ee00: beqz a3,8000ee40 <_fflush_r+0x74>
  -- block 0x8000ee88 [j]
  8000ee88: ld a1,8(sp)
  8000ee8c: ld a4,0(sp)
  8000ee90: j 8000ede4 <_fflush_r+0x18>
  -- block 0x8000ee10 [br]
  8000ee10: ld a1,0(sp)
  8000ee14: mv a5,a0
  8000ee18: lw a4,176(a1)
  8000ee1c: andi a4,a4,1
  8000ee20: bnez a4,8000ee30 <_fflush_r+0x64>
  -- block 0x8000ee40 [jal]
  8000ee40: ld a0,160(a1)
  8000ee44: sd a4,8(sp)
  8000ee48: sd a1,0(sp)
  8000ee4c: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x8000ee24 [br]
  8000ee24: lhu a4,16(a1)
  8000ee28: andi a4,a4,512
  8000ee2c: beqz a4,8000ee5c <_fflush_r+0x90>
  -- block 0x8000ee50 [j]
  8000ee50: ld a4,8(sp)
  8000ee54: ld a1,0(sp)
  8000ee58: j 8000ee04 <_fflush_r+0x38>
  -- block 0x8000ee5c [jal]
  8000ee5c: sd a0,0(sp)
  8000ee60: ld a0,160(a1)
  8000ee64: jal 80006ff8 <__retarget_lock_release_recursive>
  -- block 0x8000ee68 [ret]
  8000ee68: ld a5,0(sp)
  8000ee6c: ld ra,24(sp)
  8000ee70: mv a0,a5
  8000ee74: addi sp,sp,32
  8000ee78: ret 
```
