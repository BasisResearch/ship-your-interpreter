# vparm_VP_BOOL

- kind: field
- consumes/consumed-by: hCallPrint/hCallPrintln via rows/ValuePrintContract
- note: value_print arm VP_BOOL (vp table 0x80019f10)
- entry: 0x80002974 (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (3 blocks)

- Block(0x80002974..0x80002980 beqz kind=br succs=['0x8000298c', '0x80002984'])
- Block(0x8000298c..0x8000298c j kind=tailj succs=[])
- Block(0x80002984..0x80002988 fall kind=fallthrough succs=['0x8000298c'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, tailj
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `fputs` → LANDED (FputsContract)

## Register/memory outcome sketch

- regs written on slice: a5, a0
- loads: 1, stores: 0

## Disasm slice

```
  -- block 0x80002974 [br]
  80002974: lw a5,8(a0)
  80002978: auipc a0,0x16
  8000297c: addi a0,a0,1688
  80002980: beqz a5,8000298c <value_print+0x90>
  -- block 0x8000298c [tailj]
  8000298c: j 80006500 <fputs>
  -- block 0x80002984 [fallthrough]
  80002984: auipc a0,0x16
  80002988: addi a0,a0,1668
```
