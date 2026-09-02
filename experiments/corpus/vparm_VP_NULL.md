# vparm_VP_NULL

- kind: field
- consumes/consumed-by: hCallPrint/hCallPrintln via rows/ValuePrintContract
- note: value_print arm VP_NULL (vp table 0x80019f10)
- entry: 0x8000295c (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (1 blocks)

- Block(0x8000295c..0x80002970 j kind=tailj succs=[])

## Terminator/loop classification

- terminators on slice: tailj
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `fwrite` → LANDED (FwriteContract)

## Register/memory outcome sketch

- regs written on slice: a3, a2, a1, a0
- loads: 0, stores: 0

## Disasm slice

```
  -- block 0x8000295c [tailj]
  8000295c: mv a3,a1
  80002960: li a2,4
  80002964: li a1,1
  80002968: auipc a0,0x16
  8000296c: addi a0,a0,1712
  80002970: j 80005260 <fwrite>
```
