# err_80003fdc

- kind: errsite
- consumes/consumed-by: ErrWork/hErrFam premises: hArgsTail, hSeqHead
- note: jal runtime_error site; errSite_80003fdc Triple rows landed (rows/ErrSitesBatch*); residual = hsite caller linkage
- entry: 0x80003fdc (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no
- arm entry 0x80003fdc is a computed-jump target inside block 0x80003fb0 (suffix view)

## Case slice (1 blocks)

- Block(0x80003fdc..0x80003fdc jal kind=jal succs=['0x80003fe0'])

## Terminator/loop classification

- terminators on slice: jal
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `runtime_error` → LANDED (runtime_error_spec)

## Register/memory outcome sketch

- regs written on slice: (none)
- loads: 0, stores: 0

## Disasm slice

```
  -- block 0x80003fdc [jal]
  80003fdc: jal 80002da8 <runtime_error>
```
