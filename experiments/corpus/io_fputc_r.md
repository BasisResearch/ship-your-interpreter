# io_fputc_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: fputc shim over _putc_r
- entry: 0x80006210 (inside `_fputc_r` [0x80006210, 0x800062e0))
- containing-fn CFG: 14 blocks, 6 branches, loop-template=no

## Case slice (14 blocks)

- Block(0x80006210..0x8000621c beqz kind=br succs=['0x80006228', '0x80006220'])
- Block(0x80006228..0x80006230 bnez kind=br succs=['0x80006240', '0x80006234'])
- Block(0x80006220..0x80006224 beqz kind=br succs=['0x800062c0', '0x80006228'])
- Block(0x80006240..0x80006248 jal kind=jal succs=['0x8000624c'])
- Block(0x80006234..0x8000623c beqz kind=br succs=['0x8000629c', '0x80006240'])
- Block(0x800062c0..0x800062cc jal kind=jal succs=['0x800062d0'])
- Block(0x8000624c..0x8000625c bnez kind=br succs=['0x8000626c', '0x80006260'])
- Block(0x8000629c..0x800062ac jal kind=jal succs=['0x800062b0'])
- Block(0x800062d0..0x800062dc j kind=j succs=['0x80006228'])
- Block(0x8000626c..0x80006278 ret kind=ret succs=[])
- Block(0x80006260..0x80006268 beqz kind=br succs=['0x8000627c', '0x8000626c'])
- Block(0x800062b0..0x800062bc j kind=j succs=['0x80006240'])
- Block(0x8000627c..0x80006284 jal kind=jal succs=['0x80006288'])
- Block(0x80006288..0x80006298 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_putc_r` → NONE
- `__sinit` → NONE
- `__retarget_lock_acquire_recursive` → NONE
- `__retarget_lock_release_recursive` → NONE

## Register/memory outcome sketch

- regs written on slice: sp, a4, a5, a0, a2, a1, ra
- loads: 17, stores: 9

## Disasm slice

```
  -- block 0x80006210 [br]
  80006210: addi sp,sp,-48
  80006214: sd ra,40(sp)
  80006218: mv a4,a0
  8000621c: beqz a0,80006228 <_fputc_r+0x18>
  -- block 0x80006228 [br] LOOP-HEAD
  80006228: lw a5,176(a2)
  8000622c: andi a5,a5,1
  80006230: bnez a5,80006240 <_fputc_r+0x30>
  -- block 0x80006220 [br]
  80006220: ld a5,72(a0)
  80006224: beqz a5,800062c0 <_fputc_r+0xb0>
  -- block 0x80006240 [jal] LOOP-HEAD
  80006240: mv a0,a4
  80006244: sd a2,8(sp)
  80006248: jal 8000e6a4 <_putc_r>
  -- block 0x80006234 [br]
  80006234: lhu a5,16(a2)
  80006238: andi a5,a5,512
  8000623c: beqz a5,8000629c <_fputc_r+0x8c>
  -- block 0x800062c0 [jal]
  800062c0: sd a2,24(sp)
  800062c4: sd a1,16(sp)
  800062c8: sd a0,8(sp)
  800062cc: jal 800060c0 <__sinit>
  -- block 0x8000624c [br]
  8000624c: ld a2,8(sp)
  80006250: mv a4,a0
  80006254: lw a5,176(a2)
  80006258: andi a5,a5,1
  8000625c: bnez a5,8000626c <_fputc_r+0x5c>
  -- block 0x8000629c [jal]
  8000629c: ld a0,160(a2)
  800062a0: sd a1,24(sp)
  800062a4: sd a4,16(sp)
  800062a8: sd a2,8(sp)
  800062ac: jal 80006fe0 <__retarget_lock_acquire_recursive>
  -- block 0x800062d0 [j]
  800062d0: ld a2,24(sp)
  800062d4: ld a1,16(sp)
  800062d8: ld a4,8(sp)
  800062dc: j 80006228 <_fputc_r+0x18>
  -- block 0x8000626c [ret]
  8000626c: ld ra,40(sp)
  80006270: mv a0,a4
  80006274: addi sp,sp,48
  80006278: ret 
  -- block 0x80006260 [br]
  80006260: lhu a5,16(a2)
  80006264: andi a5,a5,512
  80006268: beqz a5,8000627c <_fputc_r+0x6c>
  -- block 0x800062b0 [j]
  800062b0: ld a1,24(sp)
  800062b4: ld a4,16(sp)
  800062b8: ld a2,8(sp)
  800062bc: j 80006240 <_fputc_r+0x30>
  -- block 0x8000627c [jal]
  8000627c: sd a0,8(sp)
  80006280: ld a0,160(a2)
  80006284: jal 80006ff8 <__retarget_lock_release_recursive>
  -- block 0x80006288 [ret]
  80006288: ld a4,8(sp)
  8000628c: ld ra,40(sp)
  80006290: mv a0,a4
  80006294: addi sp,sp,48
  80006298: ret 
```
