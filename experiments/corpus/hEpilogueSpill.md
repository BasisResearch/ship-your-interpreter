# hEpilogueSpill

- kind: field
- consumes/consumed-by: TermResidualsCore.hEpilogueSpill
- note: interpNormalExitPC epilogue restore block (s5=0 latch) | skeleton: **ENTRY (epilogue)** — `hEntryHalts` exit-0 spill seam.  Supplier: the epilogue restore-block byte-level spill/frame/image/tail facts (`Vsa.Sim.EpilogueSpill`, the `s5=0` latch + restore `ChainFacts`).
- entry: 0x80004514 (inside `interp_run` [0x800043ec, 0x80004588))
- containing-fn CFG: 23 blocks, 9 branches, loop-template=no

## Case slice (1 blocks)

- Block(0x80004514..0x8000453c ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- (no call seams on slice)

## Register/memory outcome sketch

- regs written on slice: ra, s0, s1, s2, s3, s4, s6, a0, s5, sp
- loads: 8, stores: 0

## Disasm slice

```
  -- block 0x80004514 [ret] LOOP-HEAD
  80004514: ld ra,168(sp)
  80004518: ld s0,160(sp)
  8000451c: ld s1,152(sp)
  80004520: ld s2,144(sp)
  80004524: ld s3,136(sp)
  80004528: ld s4,128(sp)
  8000452c: ld s6,112(sp)
  80004530: mv a0,s5
  80004534: ld s5,120(sp)
  80004538: addi sp,sp,176
  8000453c: ret 
```
