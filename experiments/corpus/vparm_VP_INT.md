# vparm_VP_INT

- kind: field
- consumes/consumed-by: hCallPrint/hCallPrintln via rows/ValuePrintContract
- note: value_print arm VP_INT (vp table 0x80019f10)
- entry: 0x80002990 (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (1 blocks)

- Block(0x80002990..0x800029a0 j kind=tailj succs=[])

## Terminator/loop classification

- terminators on slice: tailj
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `fprintf` → LANDED (FprintfContract, svfprintf_lld_spec, svfprintf_lld_spec', svfprintf_lld_nn_spec, iov2ToSvfprintfRet_spec, svfprintf_flushReturn_spec)

## Register/memory outcome sketch

- regs written on slice: a2, a0, a1
- loads: 1, stores: 0

## Disasm slice

```
  -- block 0x80002990 [tailj]
  80002990: ld a2,8(a0)
  80002994: mv a0,a1
  80002998: auipc a1,0x17
  8000299c: addi a1,a1,-1752
  800029a0: j 800061c0 <fprintf>
```
