# io_value_print

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: value dispatch via vp jump table 0x80019f10
- entry: 0x800028fc (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (3 blocks)

- Block(0x800028fc..0x80002904 bltu kind=br succs=['0x800029ac', '0x80002908'])
- Block(0x800029ac..0x800029ac ret kind=ret succs=[])
- Block(0x80002908..0x80002924 jr kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, ret
- back-edge/loop on slice: no

## Calls (landed-summary status)

- (no call seams on slice)

## Register/memory outcome sketch

- regs written on slice: a4, a5
- loads: 3, stores: 0

## Disasm slice

```
  -- block 0x800028fc [br]
  800028fc: lw a4,0(a0)
  80002900: li a5,5
  80002904: bltu a5,a4,800029ac <value_print+0xb0>
  -- block 0x800029ac [ret]
  800029ac: ret 
  -- block 0x80002908 [ret]
  80002908: lwu a5,0(a0)
  8000290c: auipc a4,0x17
  80002910: addi a4,a4,1540
  80002914: slli a5,a5,0x2
  80002918: add a5,a5,a4
  8000291c: lw a5,0(a5)
  80002920: add a5,a5,a4
  80002924: jr a5
```
