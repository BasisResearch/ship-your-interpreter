# io_write_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: reent shim over _write
- entry: 0x800104fc (inside `_write_r` [0x800104fc, 0x80010558))
- containing-fn CFG: 5 blocks, 2 branches, loop-template=no

## Case slice (5 blocks)

- Block(0x800104fc..0x80010520 jal kind=jal succs=['0x80010524'])
- Block(0x80010524..0x80010528 beq kind=br succs=['0x8001053c', '0x8001052c'])
- Block(0x8001053c..0x80010540 beqz kind=br succs=['0x8001052c', '0x80010544'])
- Block(0x8001052c..0x80010538 ret kind=ret succs=[])
- Block(0x80010544..0x80010554 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `_write` → LANDED (writeX0040Row, writeX004cRow, write_summary, FwriteContract, swriteXeff8Row, swriteXf024Row)

## Register/memory outcome sketch

- regs written on slice: a5, sp, a1, s0, a2, a0, ra
- loads: 5, stores: 4

## Disasm slice

```
  -- block 0x800104fc [jal]
  800104fc: mv a5,a1
  80010500: addi sp,sp,-16
  80010504: sd s0,0(sp)
  80010508: mv a1,a2
  8001050c: mv s0,a0
  80010510: mv a2,a3
  80010514: mv a0,a5
  80010518: sd ra,8(sp)
  8001051c: sw zero,1272(gp)
  80010520: jal 8000003c <_write>
  -- block 0x80010524 [br]
  80010524: li a5,-1
  80010528: beq a0,a5,8001053c <_write_r+0x40>
  -- block 0x8001053c [br]
  8001053c: lw a5,1272(gp)
  80010540: beqz a5,8001052c <_write_r+0x30>
  -- block 0x8001052c [ret] LOOP-HEAD
  8001052c: ld ra,8(sp)
  80010530: ld s0,0(sp)
  80010534: addi sp,sp,16
  80010538: ret 
  -- block 0x80010544 [ret]
  80010544: ld ra,8(sp)
  80010548: sw a5,0(s0)
  8001054c: ld s0,0(sp)
  80010550: addi sp,sp,16
  80010554: ret 
```
