# vparm_VP_STR

- kind: field
- consumes/consumed-by: hCallPrint/hCallPrintln via rows/ValuePrintContract
- note: value_print arm VP_STR (vp table 0x80019f10)
- entry: 0x800029a4 (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (1 blocks)

- Block(0x800029a4..0x800029a8 j kind=tailj succs=[])

## Terminator/loop classification

- terminators on slice: tailj
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `fputs` → LANDED (FputsContract)

## Register/memory outcome sketch

- regs written on slice: a0
- loads: 1, stores: 0

## Disasm slice

```
  -- block 0x800029a4 [tailj]
  800029a4: ld a0,8(a0)
  800029a8: j 80006500 <fputs>
```
