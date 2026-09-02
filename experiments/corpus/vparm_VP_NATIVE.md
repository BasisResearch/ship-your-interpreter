# vparm_VP_NATIVE

- kind: field
- consumes/consumed-by: hCallPrint/hCallPrintln via rows/ValuePrintContract
- note: value_print arm VP_NATIVE (vp table 0x80019f10)
- entry: 0x80002948 (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (1 blocks)

- Block(0x80002948..0x80002958 j kind=tailj succs=[])

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
  -- block 0x80002948 [tailj]
  80002948: ld a2,8(a0)
  8000294c: mv a0,a1
  80002950: auipc a1,0x17
  80002954: addi a1,a1,-1656
  80002958: j 800061c0 <fprintf>
```
