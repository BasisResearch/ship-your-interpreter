# hSCont

- kind: field
- consumes/consumed-by: TermResidualsCore.hSCont
- note: exec continue arm | skeleton: `hSCont`/`exec_cont_row`.  Supplier: `ContResid` = `ExecCaseGeom` cont arm.
- entry: 0x800040b8 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (1 blocks)

- Block(0x800040b8..0x800040d4 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: ret
- back-edge/loop on slice: no

## Calls (landed-summary status)

- (no call seams on slice)

## Register/memory outcome sketch

- regs written on slice: ra, s0, s1, s2, s3, a0, sp
- loads: 5, stores: 0

## Disasm slice

```
  -- block 0x800040b8 [ret]
  800040b8: ld ra,168(sp)
  800040bc: ld s0,160(sp)
  800040c0: ld s1,152(sp)
  800040c4: ld s2,144(sp)
  800040c8: ld s3,136(sp)
  800040cc: li a0,2
  800040d0: addi sp,sp,176
  800040d4: ret 
```
