# hSBrk

- kind: field
- consumes/consumed-by: TermResidualsCore.hSBrk
- note: exec break arm | skeleton: `hSBrk`/`exec_brk_row`.  Supplier: `BrkResid` = `ExecCaseGeom` brk arm.
- entry: 0x80004098 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (2 blocks)

- Block(0x80004098..0x80004098 fall kind=fallthrough succs=['0x8000409c'])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: fallthrough, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- (no call seams on slice)

## Register/memory outcome sketch

- regs written on slice: a0, ra, s0, s1, s2, s3, sp
- loads: 5, stores: 0

## Disasm slice

```
  -- block 0x80004098 [fallthrough]
  80004098: li a0,1
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
```
