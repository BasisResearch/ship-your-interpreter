# err_80003fac

- kind: errsite
- consumes/consumed-by: ErrWork/hErrFam premises: hArgsHead, hFlLoop
- note: jal runtime_error site; errSite_80003fac Triple rows landed (rows/ErrSitesBatch*); residual = hsite caller linkage
- entry: 0x80003fac (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no
- arm entry 0x80003fac is a computed-jump target inside block 0x80003f80 (suffix view)

## Case slice (2 blocks)

- Block(0x80003fac..0x80003fac jal kind=jal succs=['0x80003fb0'])
- Block(0x80003fb0..0x80003fdc jal kind=jal succs=['0x80003fe0'])

## Terminator/loop classification

- terminators on slice: jal
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `runtime_error` → LANDED (runtime_error_spec)

## Register/memory outcome sketch

- regs written on slice: a1, a0, a4, a3, a2
- loads: 1, stores: 5

## Disasm slice

```
  -- block 0x80003fac [jal]
  80003fac: jal 80002da8 <runtime_error>
  -- block 0x80003fb0 [jal]
  80003fb0: lw a1,4(s0)
  80003fb4: mv a0,s2
  80003fb8: li a4,0
  80003fbc: li a3,0
  80003fc0: auipc a2,0x15
  80003fc4: addi a2,a2,1200
  80003fc8: sd s3,1048(sp)
  80003fcc: sd s4,1040(sp)
  80003fd0: sd s5,1032(sp)
  80003fd4: sd s6,1024(sp)
  80003fd8: sd s7,1016(sp)
  80003fdc: jal 80002da8 <runtime_error>
```
