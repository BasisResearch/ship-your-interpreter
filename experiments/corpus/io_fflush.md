# io_fflush

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: top flush entry
- entry: 0x8000ee94 (inside `fflush` [0x8000ee94, 0x8000ef70))
- containing-fn CFG: 17 blocks, 8 branches, loop-template=no

## Case slice (17 blocks)

- Block(0x8000ee94..0x8000ee94 beqz kind=br succs=['0x8000ef5c', '0x8000ee98'])
- Block(0x8000ef5c..0x8000ef6c j kind=tailj succs=[])
- Block(0x8000ee98..0x8000eea8 beqz kind=br succs=['0x8000eeb4', '0x8000eeac'])
- Block(0x8000eeb4..0x8000eebc beqz kind=br succs=['0x8000ef00', '0x8000eec0'])
- Block(0x8000eeac..0x8000eeb0 beqz kind=br succs=['0x8000ef10', '0x8000eeb4'])
- Block(0x8000ef00..0x8000ef0c ret kind=ret succs=[])
- Block(0x8000eec0..0x8000eec8 bnez kind=br succs=['0x8000eed4', '0x8000eecc'])
- Block(0x8000ef10..0x8000ef1c jal kind=jal succs=['0x8000ef20'])
- Block(0x8000eed4..0x8000eedc jal kind=jal succs=['0x8000eee0'])
- Block(0x8000eecc..0x8000eed0 beqz kind=br succs=['0x8000ef2c', '0x8000eed4'])
- Block(0x8000ef20..0x8000ef28 j kind=j succs=['0x8000eeb4'])
- Block(0x8000eee0..0x8000eef0 bnez kind=br succs=['0x8000ef00', '0x8000eef4'])
- Block(0x8000ef2c..0x8000ef38 jal kind=jal succs=['0x8000ef3c'])
- Block(0x8000eef4..0x8000eefc beqz kind=br succs=['0x8000ef48', '0x8000ef00'])
- Block(0x8000ef3c..0x8000ef44 j kind=j succs=['0x8000eed4'])
- Block(0x8000ef48..0x8000ef50 jal kind=jal succs=['0x8000ef54'])
- Block(0x8000ef54..0x8000ef58 j kind=j succs=['0x8000ef00'])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret, tailj
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_fwalk_sglue` → NONE
- `__sinit` → NONE
- `__sflush_r` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__retarget_lock_release_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: a2, a1, a0, a4, sp, a3, a5, ra
- loads: 15, stores: 7

## Disasm slice

```
  -- block 0x8000ee94 [br]
  8000ee94: beqz a0,8000ef5c <fflush+0xc8>
  -- block 0x8000ef5c [tailj]
  8000ef5c: addi a2,gp,16
  8000ef60: auipc a1,0x0
  8000ef64: addi a1,a1,-404
  8000ef68: addi a0,gp,40
  8000ef6c: j 8000e368 <_fwalk_sglue>
  -- block 0x8000ee98 [br]
  8000ee98: ld a4,1120(gp)
  8000ee9c: addi sp,sp,-32
  8000eea0: sd ra,24(sp)
  8000eea4: mv a1,a0
  8000eea8: beqz a4,8000eeb4 <fflush+0x20>
  -- block 0x8000eeb4 [br] LOOP-HEAD
  8000eeb4: lh a3,16(a1)
  8000eeb8: li a5,0
  8000eebc: beqz a3,8000ef00 <fflush+0x6c>
  -- block 0x8000eeac [br]
  8000eeac: ld a5,72(a4)
  8000eeb0: beqz a5,8000ef10 <fflush+0x7c>
  -- block 0x8000ef00 [ret] LOOP-HEAD
  8000ef00: ld ra,24(sp)
  8000ef04: mv a0,a5
  8000ef08: addi sp,sp,32
  8000ef0c: ret 
  -- block 0x8000eec0 [br]
  8000eec0: lw a5,176(a1)
  8000eec4: andi a5,a5,1
  8000eec8: bnez a5,8000eed4 <fflush+0x40>
  -- block 0x8000ef10 [jal]
  8000ef10: sd a0,8(sp)
  8000ef14: mv a0,a4
  8000ef18: sd a4,0(sp)
  8000ef1c: jal 800060c0 <__sinit>
  -- block 0x8000eed4 [jal] LOOP-HEAD
  8000eed4: mv a0,a4
  8000eed8: sd a1,0(sp)
  8000eedc: jal 8000eb70 <__sflush_r>
  -- block 0x8000eecc [br]
  8000eecc: andi a3,a3,512
  8000eed0: beqz a3,8000ef2c <fflush+0x98>
  -- block 0x8000ef20 [j]
  8000ef20: ld a1,8(sp)
  8000ef24: ld a4,0(sp)
  8000ef28: j 8000eeb4 <fflush+0x20>
  -- block 0x8000eee0 [br]
  8000eee0: ld a1,0(sp)
  8000eee4: mv a5,a0
  8000eee8: lw a4,176(a1)
  8000eeec: andi a4,a4,1
  8000eef0: bnez a4,8000ef00 <fflush+0x6c>
  -- block 0x8000ef2c [jal]
  8000ef2c: ld a0,160(a1)
  8000ef30: sd a4,8(sp)
  8000ef34: sd a1,0(sp)
  8000ef38: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x8000eef4 [br]
  8000eef4: lhu a4,16(a1)
  8000eef8: andi a4,a4,512
  8000eefc: beqz a4,8000ef48 <fflush+0xb4>
  -- block 0x8000ef3c [j]
  8000ef3c: ld a4,8(sp)
  8000ef40: ld a1,0(sp)
  8000ef44: j 8000eed4 <fflush+0x40>
  -- block 0x8000ef48 [jal]
  8000ef48: sd a0,0(sp)
  8000ef4c: ld a0,160(a1)
  8000ef50: jal 80006ff8 <__retarget_lock_release_recursive>
  -- block 0x8000ef54 [j]
  8000ef54: ld a5,0(sp)
  8000ef58: j 8000ef00 <fflush+0x6c>
```
