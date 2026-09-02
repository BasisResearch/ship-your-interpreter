# io_fwrite_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: fwrite over __sfvwrite_r
- entry: 0x80005078 (inside `_fwrite_r` [0x80005078, 0x80005260))
- containing-fn CFG: 36 blocks, 17 branches, loop-template=no

## Case slice (28 blocks, truncated closure)

- Block(0x80005078..0x800050ac jal kind=jal succs=['0x800050b0'])
- Block(0x800050b0..0x800050cc beqz kind=br succs=['0x800050d8', '0x800050d0'])
- Block(0x800050d8..0x800050e4 beqz kind=br succs=['0x80005148', '0x800050e8'])
- Block(0x800050d0..0x800050d4 beqz kind=br succs=['0x8000523c', '0x800050d8'])
- Block(0x80005148..0x8000514c beqz kind=br succs=['0x800051dc', '0x80005150'])
- Block(0x800050e8..0x800050ec bltz kind=br succs=['0x800051d0', '0x800050f0'])
- Block(0x8000523c..0x80005244 jal kind=jal succs=['0x80005248'])
- Block(0x800051dc..0x800051e4 jal kind=jal succs=['0x800051e8'])
- Block(0x80005150..0x80005154 bgez kind=br succs=['0x800050f0', '0x80005158'])
- Block(0x800051d0..0x800051d4 bltz kind=br succs=['0x80005128', '0x800051d8'])
- Block(0x800050f0..0x80005108 fall kind=fallthrough succs=['0x8000510c'])
- Block(0x80005248..0x8000524c j kind=j succs=['0x800050d8'])
- Block(0x800051e8..0x800051f8 bltz kind=br succs=['0x8000510c', '0x800051fc'])
- Block(0x80005158..0x8000515c bltz kind=br succs=['0x8000511c', '0x80005160'])
- Block(0x80005128..0x80005144 ret kind=ret succs=[])
- Block(0x800051d8..0x800051d8 j kind=j succs=['0x80005160'])
- Block(0x8000510c..0x80005110 bgez kind=br succs=['0x80005160', '0x80005114'])
- Block(0x800051fc..0x800051fc j kind=j succs=['0x800050f0'])
- Block(0x8000511c..0x80005124 beqz kind=br succs=['0x80005200', '0x80005128'])
- Block(0x80005160..0x80005170 jal kind=jal succs=['0x80005174'])
- Block(0x80005114..0x80005118 bnez kind=br succs=['0x80005128', '0x8000511c'])
- Block(0x80005200..0x80005204 jal kind=jal succs=['0x80005208'])
- Block(0x80005174..0x80005180 beqz kind=br succs=['0x8000520c', '0x80005184'])
- Block(0x80005208..0x80005208 j kind=j succs=['0x80005128'])
- Block(0x8000520c..0x8000520c bnez kind=br succs=['0x8000521c', '0x80005210'])
- Block(0x80005184..0x80005184 bnez kind=br succs=['0x800051a4', '0x80005188'])
- Block(0x8000521c..0x8000521c fall kind=fallthrough succs=['0x80005220'])
- Block(0x80005210..0x80005218 beqz kind=br succs=['0x80005250', '0x8000521c'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `__muldi3` → LANDED (muldi3_spec)
- `__sinit` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__sfvwrite_r` → LANDED (sfvwrite_rXdee4Row, sfvwrite_rXdf10Row, sfvwrite_rXdf3cRow, sfvwrite_rXe0bcRow, sfvwrite_rXde8cFRow, sfvwrite_rXde94FRow)
- `__retarget_lock_release_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, s1, a1, a0, s0, s3, s2, a4, a5, a3, a2, ra
- loads: 18, stores: 15

## Disasm slice

```
  -- block 0x80005078 [jal]
  80005078: addi sp,sp,-112
  8000507c: sd s1,88(sp)
  80005080: sd a1,24(sp)
  80005084: mv s1,a0
  80005088: mv a1,a2
  8000508c: mv a0,a3
  80005090: sd s0,96(sp)
  80005094: sd s2,80(sp)
  80005098: sd s3,72(sp)
  8000509c: mv s0,a4
  800050a0: mv s3,a3
  800050a4: sd ra,104(sp)
  800050a8: mv s2,a2
  800050ac: jal 80004640 <__muldi3>
  -- block 0x800050b0 [br]
  800050b0: addi a4,sp,24
  800050b4: li a5,1
  800050b8: sd a0,32(sp)
  800050bc: sd a0,56(sp)
  800050c0: sd a4,40(sp)
  800050c4: sw a5,48(sp)
  800050c8: mv a3,a0
  800050cc: beqz s1,800050d8 <_fwrite_r+0x60>
  -- block 0x800050d8 [br] LOOP-HEAD
  800050d8: lw a5,176(s0)
  800050dc: lh a4,16(s0)
  800050e0: andi a2,a5,1
  800050e4: beqz a2,80005148 <_fwrite_r+0xd0>
  -- block 0x800050d0 [br]
  800050d0: ld a5,72(s1)
  800050d4: beqz a5,8000523c <_fwrite_r+0x1c4>
  -- block 0x80005148 [br]
  80005148: andi a2,a4,512
  8000514c: beqz a2,800051dc <_fwrite_r+0x164>
  -- block 0x800050e8 [br]
  800050e8: slli a2,a4,0x32
  800050ec: bltz a2,800051d0 <_fwrite_r+0x158>
  -- block 0x8000523c [jal]
  8000523c: sd a0,8(sp)
  80005240: mv a0,s1
  80005244: jal 800060c0 <__sinit>
  -- block 0x800051dc [jal]
  800051dc: ld a0,160(s0)
  800051e0: sd a3,8(sp)
  800051e4: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x80005150 [br]
  80005150: slli a2,a4,0x32
  80005154: bgez a2,800050f0 <_fwrite_r+0x78>
  -- block 0x800051d0 [br]
  800051d0: slli a4,a5,0x32
  800051d4: bltz a4,80005128 <_fwrite_r+0xb0>
  -- block 0x800050f0 [fallthrough] LOOP-HEAD
  800050f0: lui a2,0xffffe
  800050f4: addi a2,a2,-1
  800050f8: lui a1,0x2
  800050fc: and a5,a5,a2
  80005100: or a4,a4,a1
  80005104: sw a5,176(s0)
  80005108: sh a4,16(s0)
  -- block 0x80005248 [j]
  80005248: ld a3,8(sp)
  8000524c: j 800050d8 <_fwrite_r+0x60>
  -- block 0x800051e8 [br]
  800051e8: lh a4,16(s0)
  800051ec: lw a5,176(s0)
  800051f0: ld a3,8(sp)
  800051f4: slli a2,a4,0x32
  800051f8: bltz a2,8000510c <_fwrite_r+0x94>
  -- block 0x80005158 [br]
  80005158: slli a4,a5,0x32
  8000515c: bltz a4,8000511c <_fwrite_r+0xa4>
  -- block 0x80005128 [ret] LOOP-HEAD
  80005128: ld ra,104(sp)
  8000512c: ld s0,96(sp)
  80005130: ld s1,88(sp)
  80005134: ld s2,80(sp)
  80005138: ld s3,72(sp)
  8000513c: li a0,0
  80005140: addi sp,sp,112
  80005144: ret 
  -- block 0x800051d8 [j]
  800051d8: j 80005160 <_fwrite_r+0xe8>
  -- block 0x8000510c [br] LOOP-HEAD
  8000510c: slli a4,a5,0x32
  80005110: bgez a4,80005160 <_fwrite_r+0xe8>
  -- block 0x800051fc [j]
  800051fc: j 800050f0 <_fwrite_r+0x78>
  -- block 0x8000511c [br] LOOP-HEAD
  8000511c: lhu a5,16(s0)
  80005120: andi a5,a5,512
  80005124: beqz a5,80005200 <_fwrite_r+0x188>
  -- block 0x80005160 [jal] LOOP-HEAD
  80005160: mv a0,s1
  80005164: addi a2,sp,40
  80005168: mv a1,s0
  8000516c: sd a3,8(sp)
  80005170: jal 8000de8c <__sfvwrite_r>
  -- block 0x80005114 [br]
  80005114: andi a5,a5,1
  80005118: bnez a5,80005128 <_fwrite_r+0xb0>
  -- block 0x80005200 [jal]
  80005200: ld a0,160(s0)
  80005204: jal 80006ff8 <__retarget_lock_release_recursive>
  -- block 0x80005174 [br]
  80005174: lw a5,176(s0)
  80005178: ld a3,8(sp)
  8000517c: andi a5,a5,1
  80005180: beqz a0,8000520c <_fwrite_r+0x194>
  -- block 0x80005208 [j]
  80005208: j 80005128 <_fwrite_r+0xb0>
  -- block 0x8000520c [br]
  8000520c: bnez a5,8000521c <_fwrite_r+0x1a4>
  -- block 0x80005184 [br]
  80005184: bnez a5,800051a4 <_fwrite_r+0x12c>
  -- block 0x8000521c [fallthrough]
  8000521c: mv a0,s3
  -- block 0x80005210 [br]
  … (disasm capped at 90 lines)
```
