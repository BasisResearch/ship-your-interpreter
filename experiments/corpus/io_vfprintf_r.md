# io_vfprintf_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: SEPARATE compilation: pinned fmt paths %lld + %s×2; sbprintf detour at +0x39c; digit loop re-instantiates at vfprintf-local PCs
- entry: 0x8000a884 (inside `_vfprintf_r` [0x8000a884, 0x8000dd90))
- containing-fn CFG: 873 blocks, 392 branches, loop-template=no

## Case slice (28 blocks, truncated closure)

- Block(0x8000a884..0x8000a8a8 jal kind=jal succs=['0x8000a8ac'])
- Block(0x8000a8ac..0x8000a8b8 jal kind=jal succs=['0x8000a8bc'])
- Block(0x8000a8bc..0x8000a8cc jal kind=jal succs=['0x8000a8d0'])
- Block(0x8000a8d0..0x8000a8d0 beqz kind=br succs=['0x8000a8e0', '0x8000a8d4'])
- Block(0x8000a8e0..0x8000a8ec beqz kind=br succs=['0x8000ace8', '0x8000a8f0'])
- Block(0x8000a8d4..0x8000a8d8 bnez kind=br succs=['0x8000a8e0', '0x8000a8dc'])
- Block(0x8000ace8..0x8000acec beqz kind=br succs=['0x8000af44', '0x8000acf0'])
- Block(0x8000a8f0..0x8000a8f4 bgez kind=br succs=['0x8000a8fc', '0x8000a8f8'])
- Block(0x8000a8dc..0x8000a8dc j kind=j succs=['0x8000c838'])
- Block(0x8000af44..0x8000af48 jal kind=jal succs=['0x8000af4c'])
- Block(0x8000acf0..0x8000acf4 bgez kind=br succs=['0x8000a8fc', '0x8000acf8'])
- Block(0x8000a8fc..0x8000a914 fall kind=fallthrough succs=['0x8000a918'])
- Block(0x8000a8f8..0x8000a8f8 j kind=j succs=['0x8000c008'])
- Block(0x8000c838..0x8000c83c jal kind=jal succs=['0x8000c840'])
- Block(0x8000af4c..0x8000af58 bltz kind=br succs=['0x8000a918', '0x8000af5c'])
- Block(0x8000acf8..0x8000acfc bgez kind=br succs=['0x8000a928', '0x8000ad00'])
- Block(0x8000a918..0x8000a91c bgez kind=br succs=['0x8000a924', '0x8000a920'])
- Block(0x8000c008..0x8000c00c bltz kind=br succs=['0x8000c014', '0x8000c010'])
- Block(0x8000c840..0x8000c840 j kind=j succs=['0x8000a8e0'])
- Block(0x8000af5c..0x8000af5c j kind=j succs=['0x8000a8fc'])
- Block(0x8000a928..0x8000a92c beqz kind=br succs=['0x8000abcc', '0x8000a930'])
- Block(0x8000ad00..0x8000ad08 beqz kind=br succs=['0x8000ad10', '0x8000ad0c'])
- Block(0x8000a924..0x8000a924 fall kind=fallthrough succs=['0x8000a928'])
- Block(0x8000a920..0x8000a920 j kind=j succs=['0x8000dafc'])
- Block(0x8000c014..0x8000c014 j kind=j succs=['0x8000d818'])
- Block(0x8000c010..0x8000c010 j kind=j succs=['0x8000a928'])
- Block(0x8000abcc..0x8000abd4 jal kind=jal succs=['0x8000abd8'])
- Block(0x8000a930..0x8000a934 beqz kind=br succs=['0x8000abcc', '0x8000a938'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_localeconv_r` → NONE
- `strlen` → LANDED (strlen_spec, strlenArgRow, strlenCallSpec, strlen_full_spec, strdupStrlenArgRow, strlenCallSpec_sat)
- `memset` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__sinit` → NONE
- `__swsetup_r` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, s4, s6, s0, a5, a0, a2, a1, a4, a3
- loads: 10, stores: 9

## Disasm slice

```
  -- block 0x8000a884 [jal]
  8000a884: addi sp,sp,-592
  8000a888: sd ra,584(sp)
  8000a88c: sd s0,576(sp)
  8000a890: sd s4,544(sp)
  8000a894: sd s6,528(sp)
  8000a898: mv s4,a1
  8000a89c: mv s6,a2
  8000a8a0: sd a3,24(sp)
  8000a8a4: mv s0,a0
  8000a8a8: jal 80010258 <_localeconv_r>
  -- block 0x8000a8ac [jal]
  8000a8ac: ld a5,0(a0)
  8000a8b0: mv a0,a5
  8000a8b4: sd a5,64(sp)
  8000a8b8: jal 80006cf0 <strlen>
  -- block 0x8000a8bc [jal]
  8000a8bc: sd a0,56(sp)
  8000a8c0: li a2,8
  8000a8c4: addi a0,sp,200
  8000a8c8: li a1,0
  8000a8cc: jal 80006aec <memset>
  -- block 0x8000a8d0 [br]
  8000a8d0: beqz s0,8000a8e0 <_vfprintf_r+0x5c>
  -- block 0x8000a8e0 [br] LOOP-HEAD
  8000a8e0: lw a4,176(s4)
  8000a8e4: lh a5,16(s4)
  8000a8e8: andi a3,a4,1
  8000a8ec: beqz a3,8000ace8 <_vfprintf_r+0x464>
  -- block 0x8000a8d4 [br]
  8000a8d4: ld a5,72(s0)
  8000a8d8: bnez a5,8000a8e0 <_vfprintf_r+0x5c>
  -- block 0x8000ace8 [br]
  8000ace8: andi a3,a5,512
  8000acec: beqz a3,8000af44 <_vfprintf_r+0x6c0>
  -- block 0x8000a8f0 [br]
  8000a8f0: slli a3,a5,0x32
  8000a8f4: bgez a3,8000a8fc <_vfprintf_r+0x78>
  -- block 0x8000a8dc [j]
  8000a8dc: j 8000c838 <_vfprintf_r+0x1fb4>
  -- block 0x8000af44 [jal]
  8000af44: ld a0,160(s4)
  8000af48: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x8000acf0 [br]
  8000acf0: slli a3,a5,0x32
  8000acf4: bgez a3,8000a8fc <_vfprintf_r+0x78>
  -- block 0x8000a8fc [fallthrough] LOOP-HEAD
  8000a8fc: lui a3,0xffffe
  8000a900: addi a3,a3,-1
  8000a904: lui a2,0x2
  8000a908: and a4,a4,a3
  8000a90c: or a5,a5,a2
  8000a910: sw a4,176(s4)
  8000a914: sh a5,16(s4)
  -- block 0x8000a8f8 [j]
  8000a8f8: j 8000c008 <_vfprintf_r+0x1784>
  -- block 0x8000c838 [jal]
  8000c838: mv a0,s0
  8000c83c: jal 800060c0 <__sinit>
  -- block 0x8000af4c [br]
  8000af4c: lh a5,16(s4)
  8000af50: lw a4,176(s4)
  8000af54: slli a3,a5,0x32
  8000af58: bltz a3,8000a918 <_vfprintf_r+0x94>
  -- block 0x8000acf8 [br]
  8000acf8: slli a3,a4,0x32
  8000acfc: bgez a3,8000a928 <_vfprintf_r+0xa4>
  -- block 0x8000a918 [br] LOOP-HEAD
  8000a918: slli a5,a4,0x32
  8000a91c: bgez a5,8000a924 <_vfprintf_r+0xa0>
  -- block 0x8000c008 [br]
  8000c008: slli a3,a4,0x32
  8000c00c: bltz a3,8000c014 <_vfprintf_r+0x1790>
  -- block 0x8000c840 [j]
  8000c840: j 8000a8e0 <_vfprintf_r+0x5c>
  -- block 0x8000af5c [j]
  8000af5c: j 8000a8fc <_vfprintf_r+0x78>
  -- block 0x8000a928 [br] LOOP-HEAD
  8000a928: andi a4,a5,8
  8000a92c: beqz a4,8000abcc <_vfprintf_r+0x348>
  -- block 0x8000ad00 [br] LOOP-HEAD
  8000ad00: lhu a5,16(s4)
  8000ad04: andi a5,a5,512
  8000ad08: beqz a5,8000ad10 <_vfprintf_r+0x48c>
  -- block 0x8000a924 [fallthrough]
  8000a924: lh a5,16(s4)
  -- block 0x8000a920 [j]
  8000a920: j 8000dafc <_vfprintf_r+0x3278>
  -- block 0x8000c014 [j]
  8000c014: j 8000d818 <_vfprintf_r+0x2f94>
  -- block 0x8000c010 [j]
  8000c010: j 8000a928 <_vfprintf_r+0xa4>
  -- block 0x8000abcc [jal]
  8000abcc: mv a1,s4
  8000abd0: mv a0,s0
  8000abd4: jal 8000f230 <__swsetup_r>
  -- block 0x8000a930 [br]
  8000a930: ld a4,24(s4)
  8000a934: beqz a4,8000abcc <_vfprintf_r+0x348>
```
