# hAndTrue

- kind: field
- consumes/consumed-by: TermResidualsCore.hAndTrue
- note: logical fall-through, and/true route (two children) | skeleton: `hAndTrue`/`eval_andTrue_row`.  Supplier: logical fall-through geometry.
- entry: 0x8000355c (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (18 blocks)

- Block(0x8000355c..0x80003568 jal kind=jal succs=['0x8000356c'])
- Block(0x8000356c..0x80003578 beq kind=br succs=['0x80003978', '0x8000357c'])
- Block(0x80003978..0x80003990 jal kind=jal succs=['0x80003994'])
- Block(0x8000357c..0x80003594 jal kind=jal succs=['0x80003598'])
- Block(0x80003994..0x80003998 beqz kind=br succs=['0x80003a00', '0x8000399c'])
- Block(0x80003598..0x8000359c beqz kind=br succs=['0x800036d4', '0x800035a0'])
- Block(0x80003a00..0x80003a0c jal kind=jal succs=['0x80003a10'])
- Block(0x8000399c..0x800039a4 jal kind=jal succs=['0x800039a8'])
- Block(0x800036d4..0x800036dc jal kind=jal succs=['0x800036e0'])
- Block(0x800035a0..0x800035ac jal kind=jal succs=['0x800035b0'])
- Block(0x80003a10..0x80003a1c j kind=j succs=['0x800035bc'])
- Block(0x800039a8..0x800039a8 j kind=j succs=['0x800033ec'])
- Block(0x800036e0..0x800036e0 j kind=j succs=['0x800033ec'])
- Block(0x800035b0..0x800035b8 fall kind=fallthrough succs=['0x800035bc'])
- Block(0x800035bc..0x800035cc jal kind=jal succs=['0x800035d0'])
- Block(0x800033ec..0x80003404 ret kind=ret succs=[])
- Block(0x800035d0..0x800035d8 jal kind=jal succs=['0x800035dc'])
- Block(0x800035dc..0x800035dc j kind=j succs=['0x800033ec'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE
- `value_truthy` → LANDED (value_truthy_spec)
- `value_bool` → LANDED (value_bool_spec, value_bool_spec_full)

## Register/memory outcome sketch

- regs written on slice: a2, a0, a4, a5, a3, a1, ra, s0, s2, s1, sp
- loads: 21, stores: 10

## Disasm slice

```
  -- block 0x8000355c [jal]
  8000355c: ld a2,16(a2)
  80003560: addi a0,sp,120
  80003564: sd a3,0(sp)
  80003568: jal 80003164 <eval_expr>
  -- block 0x8000356c [br]
  8000356c: lw a4,8(s0)
  80003570: li a5,25
  80003574: ld a2,120(sp)
  80003578: beq a4,a5,80003978 <eval_expr+0x814>
  -- block 0x80003978 [jal]
  80003978: ld a4,128(sp)
  8000397c: ld a5,136(sp)
  80003980: addi a0,sp,64
  80003984: sd a2,64(sp)
  80003988: sd a4,72(sp)
  8000398c: sd a5,80(sp)
  80003990: jal 8000282c <value_truthy>
  -- block 0x8000357c [jal]
  8000357c: ld a4,128(sp)
  80003580: ld a5,136(sp)
  80003584: addi a0,sp,64
  80003588: sd a2,64(sp)
  8000358c: sd a4,72(sp)
  80003590: sd a5,80(sp)
  80003594: jal 8000282c <value_truthy>
  -- block 0x80003994 [br]
  80003994: ld a3,0(sp)
  80003998: beqz a0,80003a00 <eval_expr+0x89c>
  -- block 0x80003598 [br]
  80003598: ld a3,0(sp)
  8000359c: beqz a0,800036d4 <eval_expr+0x570>
  -- block 0x80003a00 [jal]
  80003a00: ld a2,24(s0)
  80003a04: mv a1,s2
  80003a08: addi a0,sp,144
  80003a0c: jal 80003164 <eval_expr>
  -- block 0x8000399c [jal]
  8000399c: li a1,1
  800039a0: mv a0,s1
  800039a4: jal 800027f8 <value_bool>
  -- block 0x800036d4 [jal]
  800036d4: li a1,0
  800036d8: mv a0,s1
  800036dc: jal 800027f8 <value_bool>
  -- block 0x800035a0 [jal]
  800035a0: ld a2,24(s0)
  800035a4: mv a1,s2
  800035a8: addi a0,sp,240
  800035ac: jal 80003164 <eval_expr>
  -- block 0x80003a10 [j]
  80003a10: ld a3,144(sp)
  80003a14: ld a4,152(sp)
  80003a18: ld a5,160(sp)
  80003a1c: j 800035bc <eval_expr+0x458>
  -- block 0x800039a8 [j]
  800039a8: j 800033ec <eval_expr+0x288>
  -- block 0x800036e0 [j]
  800036e0: j 800033ec <eval_expr+0x288>
  -- block 0x800035b0 [fallthrough]
  800035b0: ld a3,240(sp)
  800035b4: ld a4,248(sp)
  800035b8: ld a5,256(sp)
  -- block 0x800035bc [jal] LOOP-HEAD
  800035bc: addi a0,sp,64
  800035c0: sd a3,64(sp)
  800035c4: sd a4,72(sp)
  800035c8: sd a5,80(sp)
  800035cc: jal 8000282c <value_truthy>
  -- block 0x800033ec [ret] LOOP-HEAD
  800033ec: ld ra,1080(sp)
  800033f0: ld s0,1072(sp)
  800033f4: ld s2,1056(sp)
  800033f8: mv a0,s1
  800033fc: ld s1,1064(sp)
  80003400: addi sp,sp,1088
  80003404: ret 
  -- block 0x800035d0 [jal]
  800035d0: mv a1,a0
  800035d4: mv a0,s1
  800035d8: jal 800027f8 <value_bool>
  -- block 0x800035dc [j]
  800035dc: j 800033ec <eval_expr+0x288>
```
