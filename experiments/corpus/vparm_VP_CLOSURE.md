# vparm_VP_CLOSURE

- kind: field
- consumes/consumed-by: hCallPrint/hCallPrintln via rows/ValuePrintContract
- note: value_print arm VP_CLOSURE (vp table 0x80019f10)
- entry: 0x80002928 (inside `value_print` [0x800028fc, 0x800029c8))
- containing-fn CFG: 13 blocks, 3 branches, loop-template=no

## Case slice (3 blocks)

- Block(0x80002928..0x80002934 beqz kind=br succs=['0x800029b0', '0x80002938'])
- Block(0x800029b0..0x800029c4 j kind=tailj succs=[])
- Block(0x80002938..0x80002944 j kind=tailj succs=[])

## Terminator/loop classification

- terminators on slice: br, tailj
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `fwrite` → LANDED (FwriteContract)
- `fprintf` → LANDED (FprintfContract, svfprintf_lld_spec, svfprintf_lld_spec', svfprintf_lld_nn_spec, iov2ToSvfprintfRet_spec, svfprintf_flushReturn_spec)

## Register/memory outcome sketch

- regs written on slice: a5, a2, a3, a1, a0
- loads: 3, stores: 0

## Disasm slice

```
  -- block 0x80002928 [br]
  80002928: ld a5,8(a0)
  8000292c: ld a5,0(a5)
  80002930: ld a2,8(a5)
  80002934: beqz a2,800029b0 <value_print+0xb4>
  -- block 0x800029b0 [tailj]
  800029b0: mv a3,a1
  800029b4: li a2,4
  800029b8: li a1,1
  800029bc: auipc a0,0x17
  800029c0: addi a0,a0,-1772
  800029c4: j 80005260 <fwrite>
  -- block 0x80002938 [tailj]
  80002938: mv a0,a1
  8000293c: auipc a1,0x17
  80002940: addi a1,a1,-1652
  80002944: j 800061c0 <fprintf>
```
