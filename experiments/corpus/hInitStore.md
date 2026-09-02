# hInitStore

- kind: field
- consumes/consumed-by: TermResidualsCore.hInitStore
- note: interp_init store build + interp_run loop setup [0x8000442c,0x8000448c) (EntrySeams doc) | skeleton: **ENTRY (prologue)** — `hEntryHalts` store-init locus.  Supplier: the off-path `interp_init` store representation at the `interp_run` loop head (`Vsa.Sim.InterpInitStoreRepr`, decoded PC span in its doc).
- entry: 0x80004308 (inside `interp_init` [0x80004308, 0x800043ec))
- containing-fn CFG: 5 blocks, 0 branches, loop-template=no

## Case slice (5 blocks)

- Block(0x80004308..0x80004324 jal kind=jal succs=['0x80004328'])
- Block(0x80004328..0x80004364 jal kind=jal succs=['0x80004368'])
- Block(0x80004368..0x8000439c jal kind=jal succs=['0x800043a0'])
- Block(0x800043a0..0x800043d4 jal kind=jal succs=['0x800043d8'])
- Block(0x800043d8..0x800043e8 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: jal, ret
- back-edge/loop on slice: no

## Calls (landed-summary status)

- `env_new` → LANDED (env_new_spec, callClosureEnvNewRetFoldRow, CallClosureEnvNewRetFoldPost, callClosureEnvNewRetBypassRow)
- `env_define` → LANDED (env_define_append_spec)

## Register/memory outcome sketch

- regs written on slice: sp, s0, s1, a0, a5, a1, a2, a4, ra
- loads: 8, stores: 24

## Disasm slice

```
  -- block 0x80004308 [jal]
  80004308: addi sp,sp,-96
  8000430c: sd s0,80(sp)
  80004310: sd s1,72(sp)
  80004314: mv s0,a0
  80004318: li s1,5
  8000431c: li a0,0
  80004320: sd ra,88(sp)
  80004324: jal 800029fc <env_new>
  -- block 0x80004328 [jal]
  80004328: sw s1,40(sp)
  8000432c: ld a5,40(sp)
  80004330: sd a0,0(s0)
  80004334: auipc a1,0x15
  80004338: addi a1,a1,516
  8000433c: sd a5,0(sp)
  80004340: sw zero,8(s0)
  80004344: sb zero,224(s0)
  80004348: auipc a5,0xfffff
  8000434c: addi a5,a5,-1140
  80004350: mv a2,sp
  80004354: sd a1,48(sp)
  80004358: sd a1,8(sp)
  8000435c: sd a5,56(sp)
  80004360: sd a5,16(sp)
  80004364: jal 80002a5c <env_define>
  -- block 0x80004368 [jal]
  80004368: sw s1,40(sp)
  8000436c: ld a5,40(sp)
  80004370: ld a0,0(s0)
  80004374: auipc a1,0x15
  80004378: addi a1,a1,460
  8000437c: sd a5,0(sp)
  80004380: mv a2,sp
  80004384: auipc a5,0xfffff
  80004388: addi a5,a5,-1032
  8000438c: sd a1,48(sp)
  80004390: sd a1,8(sp)
  80004394: sd a5,56(sp)
  80004398: sd a5,16(sp)
  8000439c: jal 80002a5c <env_define>
  -- block 0x800043a0 [jal]
  800043a0: sw s1,40(sp)
  800043a4: ld a0,0(s0)
  800043a8: ld a4,40(sp)
  800043ac: auipc a1,0x15
  800043b0: addi a1,a1,412
  800043b4: auipc a5,0xfffff
  800043b8: addi a5,a5,-1472
  800043bc: mv a2,sp
  800043c0: sd a4,0(sp)
  800043c4: sd a1,48(sp)
  800043c8: sd a1,8(sp)
  800043cc: sd a5,56(sp)
  800043d0: sd a5,16(sp)
  800043d4: jal 80002a5c <env_define>
  -- block 0x800043d8 [ret]
  800043d8: ld ra,88(sp)
  800043dc: ld s0,80(sp)
  800043e0: ld s1,72(sp)
  800043e4: addi sp,sp,96
  800043e8: ret 
```
