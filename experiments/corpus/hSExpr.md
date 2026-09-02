# hSExpr

- kind: field
- consumes/consumed-by: TermResidualsCore.hSExpr
- note: exec expr arm | skeleton: `hSExpr`/`exec_expr_row`.  Supplier: `ExprResid` = `execExprSimD` geometry.
- entry: 0x80004170 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (3 blocks)

- Block(0x80004170..0x80004180 jal kind=jal succs=['0x80004184'])
- Block(0x80004184..0x80004188 j kind=j succs=['0x8000409c'])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE

## Register/memory outcome sketch

- regs written on slice: a2, a0, a3, a1, ra, s0, s1, s2, s3, sp
- loads: 6, stores: 0

## Disasm slice

```
  -- block 0x80004170 [jal]
  80004170: ld a2,8(s0)
  80004174: addi a0,sp,16
  80004178: mv a3,s3
  8000417c: mv a1,s1
  80004180: jal 80003164 <eval_expr>
  -- block 0x80004184 [j]
  80004184: li a0,0
  80004188: j 8000409c <exec_stmt+0xbc>
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
```
