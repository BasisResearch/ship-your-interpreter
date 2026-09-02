# io_svfprintf_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: snprintf-family fmt core (landed %lld specs live HERE)
- entry: 0x80007654 (inside `_svfprintf_r` [0x80007654, 0x8000a884))
- containing-fn CFG: 810 blocks, 372 branches, loop-template=no

## Case slice (28 blocks, truncated closure)

- Block(0x80007654..0x8000767c jal kind=jal succs=['0x80007680'])
- Block(0x80007680..0x8000768c jal kind=jal succs=['0x80007690'])
- Block(0x80007690..0x800076a0 jal kind=jal succs=['0x800076a4'])
- Block(0x800076a4..0x800076ac beqz kind=br succs=['0x800076bc', '0x800076b0'])
- Block(0x800076bc..0x800076dc fall kind=fallthrough succs=['0x800076e0'])
- Block(0x800076b0..0x800076b4 bnez kind=br succs=['0x800076bc', '0x800076b8'])
- Block(0x800076e0..0x8000771c fall kind=fallthrough succs=['0x80007720'])
- Block(0x800076b8..0x800076b8 j kind=j succs=['0x8000908c'])
- Block(0x80007720..0x80007720 fall kind=fallthrough succs=['0x80007724'])
- Block(0x8000908c..0x80009094 jal kind=jal succs=['0x80009098'])
- Block(0x80007724..0x80007728 jal kind=jal succs=['0x8000772c'])
- Block(0x80009098..0x800090a4 bnez kind=br succs=['0x800090ac', '0x800090a8'])
- Block(0x8000772c..0x80007740 jalr kind=jalrcall succs=['0x80007744'])
- Block(0x800090ac..0x800090dc j kind=j succs=['0x800076e0'])
- Block(0x800090a8..0x800090a8 j kind=j succs=['0x8000a824'])
- Block(0x80007744..0x80007744 beqz kind=br succs=['0x80007960', '0x80007748'])
- Block(0x8000a824..0x8000a82c j kind=j succs=['0x8000a75c'])
- Block(0x80007960..0x8000796c beqz kind=br succs=['0x800079b0', '0x80007970'])
- Block(0x80007748..0x80007748 bltz kind=br succs=['0x80007944', '0x8000774c'])
- Block(0x8000a75c..0x8000a764 j kind=j succs=['0x800079f4'])
- Block(0x800079b0..0x800079b4 beqz kind=br succs=['0x800079bc', '0x800079b8'])
- Block(0x80007970..0x8000799c blt kind=br succs=['0x80007a10', '0x800079a0'])
- Block(0x80007944..0x80007950 jal kind=jal succs=['0x80007954'])
- Block(0x8000774c..0x80007750 beq kind=br succs=['0x8000775c', '0x80007754'])
- Block(0x800079f4..0x80007a0c ret kind=ret succs=[])
- Block(0x800079bc..0x800079c4 fall kind=fallthrough succs=['0x800079c8'])
- Block(0x800079b8..0x800079b8 j kind=j succs=['0x80009e40'])
- Block(0x80007a10..0x80007a1c jal kind=jal succs=['0x80007a20'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, jalrcall, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_localeconv_r` → NONE
- `strlen` → LANDED (strlen_spec, strlenArgRow, strlenCallSpec, strlen_full_spec, strdupStrlenArgRow, strlenCallSpec_sat)
- `memset` → NONE
- `_malloc_r` → NONE
- `__locale_mb_cur_max` → NONE
- `__ssprint_r` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, s1, s6, s0, a4, a0, a2, a1, a5, s5, s7, s3, s2, s4, a3, s8, ra
- loads: 21, stores: 46

## Disasm slice

```
  -- block 0x80007654 [jal]
  80007654: addi sp,sp,-592
  80007658: sd ra,584(sp)
  8000765c: sd a3,24(sp)
  80007660: sd a1,8(sp)
  80007664: sd s0,576(sp)
  80007668: sd s1,568(sp)
  8000766c: sd s6,528(sp)
  80007670: mv s1,a1
  80007674: mv s6,a2
  80007678: mv s0,a0
  8000767c: jal 80010258 <_localeconv_r>
  -- block 0x80007680 [jal]
  80007680: ld a4,0(a0)
  80007684: mv a0,a4
  80007688: sd a4,80(sp)
  8000768c: jal 80006cf0 <strlen>
  -- block 0x80007690 [jal]
  80007690: sd a0,72(sp)
  80007694: li a2,8
  80007698: addi a0,sp,200
  8000769c: li a1,0
  800076a0: jal 80006aec <memset>
  -- block 0x800076a4 [br]
  800076a4: lhu a5,16(s1)
  800076a8: andi a5,a5,128
  800076ac: beqz a5,800076bc <_svfprintf_r+0x68>
  -- block 0x800076bc [fallthrough]
  800076bc: sd s2,560(sp)
  800076c0: sd s3,552(sp)
  800076c4: sd s4,544(sp)
  800076c8: sd s5,536(sp)
  800076cc: sd s7,520(sp)
  800076d0: sd s8,512(sp)
  800076d4: sd s9,504(sp)
  800076d8: sd s10,496(sp)
  800076dc: sd s11,488(sp)
  -- block 0x800076b0 [br]
  800076b0: ld a5,24(s1)
  800076b4: bnez a5,800076bc <_svfprintf_r+0x68>
  -- block 0x800076e0 [fallthrough] LOOP-HEAD
  800076e0: addi s5,sp,352
  800076e4: sd zero,240(sp)
  800076e8: sw zero,232(sp)
  800076ec: sd s5,224(sp)
  800076f0: mv s7,s5
  800076f4: sd zero,40(sp)
  800076f8: sd zero,64(sp)
  800076fc: sd zero,88(sp)
  80007700: sd zero,104(sp)
  80007704: sd zero,128(sp)
  80007708: sd zero,96(sp)
  8000770c: sd zero,16(sp)
  80007710: addi s1,gp,648
  80007714: li s3,37
  80007718: li s2,16
  8000771c: sd s6,0(sp)
  -- block 0x800076b8 [j]
  800076b8: j 8000908c <_svfprintf_r+0x1a38>
  -- block 0x80007720 [fallthrough] LOOP-HEAD
  80007720: ld s6,0(sp)
  -- block 0x8000908c [jal]
  8000908c: li a1,64
  80009090: mv a0,s0
  80009094: jal 800047a8 <_malloc_r>
  -- block 0x80007724 [jal] LOOP-HEAD
  80007724: ld s4,232(s1)
  80007728: jal 80010234 <__locale_mb_cur_max>
  -- block 0x80009098 [br]
  80009098: ld a5,8(sp)
  8000909c: sd a0,0(a5)
  800090a0: sd a0,24(a5)
  800090a4: bnez a0,800090ac <_svfprintf_r+0x1a58>
  -- block 0x8000772c [jalrcall]
  8000772c: mv a3,a0
  80007730: addi a4,sp,200
  80007734: mv a2,s6
  80007738: addi a1,sp,180
  8000773c: mv a0,s0
  80007740: jalr s4
  -- block 0x800090ac [j]
  800090ac: ld a4,8(sp)
  800090b0: sd s2,560(sp)
  800090b4: sd s3,552(sp)
  800090b8: sd s4,544(sp)
  800090bc: sd s5,536(sp)
  800090c0: sd s7,520(sp)
  800090c4: sd s8,512(sp)
  800090c8: sd s9,504(sp)
  800090cc: sd s10,496(sp)
  800090d0: sd s11,488(sp)
  800090d4: li a5,64
  800090d8: sw a5,32(a4)
  800090dc: j 800076e0 <_svfprintf_r+0x8c>
  -- block 0x800090a8 [j]
  800090a8: j 8000a824 <_svfprintf_r+0x31d0>
  -- block 0x80007744 [br]
  80007744: beqz a0,80007960 <_svfprintf_r+0x30c>
  -- block 0x8000a824 [j]
  8000a824: li a5,12
  8000a828: sw a5,0(s0)
  8000a82c: j 8000a75c <_svfprintf_r+0x3108>
  -- block 0x80007960 [br]
  80007960: ld a5,0(sp)
  80007964: mv s4,a0
  80007968: subw s8,s6,a5
  8000796c: beqz s8,800079b0 <_svfprintf_r+0x35c>
  -- block 0x80007748 [br]
  80007748: bltz a0,80007944 <_svfprintf_r+0x2f0>
  -- block 0x8000a75c [j] LOOP-HEAD
  … (disasm capped at 90 lines)
```
