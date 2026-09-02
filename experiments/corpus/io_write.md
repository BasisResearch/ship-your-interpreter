# io_write

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: tohost byte loop (counted-loop template)
- entry: 0x8000003c (inside `_write` [0x8000003c, 0x8000006c))
- containing-fn CFG: 5 blocks, 2 branches, loop-template=yes (a1)

## Case slice (5 blocks)

- Block(0x8000003c..0x8000003c beqz kind=br succs=['0x80000064', '0x80000040'])
- Block(0x80000064..0x80000068 ret kind=ret succs=[])
- Block(0x80000040..0x80000048 fall kind=fallthrough succs=['0x8000004c'])
- Block(0x8000004c..0x8000005c sd kind=tohost succs=['0x80000060'])
- Block(0x80000060..0x80000060 bne kind=br succs=['0x8000004c', '0x80000064'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, ret, tohost
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- (no call seams on slice)

## Register/memory outcome sketch

- regs written on slice: a0, a4, a3, a5, a1, a6
- loads: 1, stores: 1

## Disasm slice

```
  -- block 0x8000003c [br]
  8000003c: beqz a2,80000064 <_write+0x28>
  -- block 0x80000064 [ret]
  80000064: mv a0,a2
  80000068: ret 
  -- block 0x80000040 [fallthrough]
  80000040: li a4,257
  80000044: add a3,a1,a2
  80000048: slli a4,a4,0x30
  -- block 0x8000004c [tohost] LOOP-HEAD
  8000004c: lbu a5,0(a1)
  80000050: addi a1,a1,1
  80000054: or a5,a5,a4
  80000058: auipc a6,0x1b
  8000005c: sd a5,-856(a6)
  -- block 0x80000060 [br]
  80000060: bne a1,a3,8000004c <_write+0x10>
```
