# err_80002ebc

- kind: errsite
- consumes/consumed-by: ErrWork/hErrFam premises: hArity, hBody, hAssertFail
- note: jal runtime_error site; errSite_80002ebc Triple rows landed (rows/ErrSitesBatch*); residual = hsite caller linkage
- entry: 0x80002ebc (inside `native_assert` [0x80002df4, 0x80002ed4))
- containing-fn CFG: 10 blocks, 4 branches, loop-template=no
- arm entry 0x80002ebc is a computed-jump target inside block 0x80002ea4 (suffix view)

## Case slice (4 blocks)

- Block(0x80002ebc..0x80002ebc jal kind=jal succs=['0x80002ec0'])
- Block(0x80002ec0..0x80002ec8 bne kind=br succs=['0x80002ea4', '0x80002ecc'])
- Block(0x80002ea4..0x80002ebc jal kind=jal succs=['0x80002ec0'])
- Block(0x80002ecc..0x80002ed0 j kind=j succs=['0x80002ea4'])

## Terminator/loop classification

- terminators on slice: br, j, jal
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `runtime_error` → LANDED (runtime_error_spec)

## Register/memory outcome sketch

- regs written on slice: a2, a4, a3, a1, a0, a5
- loads: 2, stores: 0

## Disasm slice

```
  -- block 0x80002ebc [jal]
  80002ebc: jal 80002da8 <runtime_error>
  -- block 0x80002ec0 [br]
  80002ec0: lw a2,24(a3)
  80002ec4: li a4,3
  80002ec8: bne a2,a4,80002ea4 <native_assert+0xb0>
  -- block 0x80002ea4 [jal] LOOP-HEAD
  80002ea4: mv a3,a5
  80002ea8: mv a1,s2
  80002eac: mv a0,s1
  80002eb0: li a4,0
  80002eb4: auipc a2,0x16
  80002eb8: addi a2,a2,388
  80002ebc: jal 80002da8 <runtime_error>
  -- block 0x80002ecc [j]
  80002ecc: ld a5,32(a3)
  80002ed0: j 80002ea4 <native_assert+0xb0>
```
