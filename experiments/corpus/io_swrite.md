# io_swrite

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: FILE-op shim over _write_r
- entry: 0x8000efd4 (inside `__swrite` [0x8000efd4, 0x8000f05c))
- containing-fn CFG: 4 blocks, 1 branches, loop-template=no

## Case slice (4 blocks)

- Block(0x8000efd4..0x8000eff4 bnez kind=br succs=['0x8000f024', '0x8000eff8'])
- Block(0x8000f024..0x8000f040 jal kind=jal succs=['0x8000f044'])
- Block(0x8000eff8..0x8000f020 j kind=tailj succs=[])
- Block(0x8000f044..0x8000f058 j kind=j succs=['0x8000eff8'])

## Terminator/loop classification

- terminators on slice: br, j, jal, tailj
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_lseek_r` → NONE
- `_write_r` → LANDED (write_rX04fcRow, write_r_summary, write_rX0524FRow, write_rX0524TRow, write_rX053cFRow, write_rX053cTRow)

## Register/memory outcome sketch

- regs written on slice: a5, sp, t1, a3, a4, a7, a6, a1, a2, ra, a0
- loads: 9, stores: 6

## Disasm slice

```
  -- block 0x8000efd4 [br]
  8000efd4: lh a5,16(a1)
  8000efd8: addi sp,sp,-48
  8000efdc: mv t1,a3
  8000efe0: sd ra,40(sp)
  8000efe4: andi a3,a5,256
  8000efe8: mv a4,a1
  8000efec: mv a7,a2
  8000eff0: mv a6,a0
  8000eff4: bnez a3,8000f024 <__swrite+0x50>
  -- block 0x8000f024 [jal]
  8000f024: lh a1,18(a1)
  8000f028: sd a2,16(sp)
  8000f02c: li a3,2
  8000f030: li a2,0
  8000f034: sd t1,24(sp)
  8000f038: sd a4,0(sp)
  8000f03c: sd a0,8(sp)
  8000f040: jal 80010444 <_lseek_r>
  -- block 0x8000eff8 [tailj] LOOP-HEAD
  8000eff8: lui a3,0xfffff
  8000effc: addi a3,a3,-1
  8000f000: ld ra,40(sp)
  8000f004: and a5,a5,a3
  8000f008: lh a1,18(a4)
  8000f00c: sh a5,16(a4)
  8000f010: mv a3,t1
  8000f014: mv a2,a7
  8000f018: mv a0,a6
  8000f01c: addi sp,sp,48
  8000f020: j 800104fc <_write_r>
  -- block 0x8000f044 [j]
  8000f044: ld a4,0(sp)
  8000f048: ld t1,24(sp)
  8000f04c: ld a7,16(sp)
  8000f050: lh a5,16(a4)
  8000f054: ld a6,8(sp)
  8000f058: j 8000eff8 <__swrite+0x24>
```
