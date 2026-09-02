# hNot

- kind: field
- consumes/consumed-by: TermResidualsCore.hNot
- note: unary arm, not route | skeleton: `hNot`/`eval_not_row`.  Supplier: not-arm geometry.
- entry: 0x800035e0 (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (17 blocks)

- Block(0x800035e0..0x800035e8 jal kind=jal succs=['0x800035ec'])
- Block(0x800035ec..0x800035f8 beq kind=br succs=['0x800039ac', '0x800035fc'])
- Block(0x800039ac..0x800039cc bne kind=br succs=['0x80003b58', '0x800039d0'])
- Block(0x800035fc..0x80003614 jal kind=jal succs=['0x80003618'])
- Block(0x80003b58..0x80003b78 fall kind=fallthrough succs=['0x80003b7c'])
- Block(0x800039d0..0x800039d8 jal kind=jal succs=['0x800039dc'])
- Block(0x80003618..0x80003620 jal kind=jal succs=['0x80003624'])
- Block(0x80003b7c..0x80003b7c jal kind=jal succs=['0x80003b80'])
- Block(0x800039dc..0x800039dc j kind=j succs=['0x800033ec'])
- Block(0x80003624..0x80003624 j kind=j succs=['0x800033ec'])
- Block(0x80003b80..0x80003b9c jal kind=jal succs=['0x80003ba0'])
- Block(0x800033ec..0x80003404 ret kind=ret succs=[])
- Block(0x80003ba0..0x80003bc8 jal kind=jal succs=['0x80003bcc'])
- Block(0x80003bcc..0x80003be8 fall kind=fallthrough succs=['0x80003bec'])
- Block(0x80003bec..0x80003bf0 jal kind=jal succs=['0x80003bf4'])
- Block(0x80003bf4..0x80003c10 jal kind=jal succs=['0x80003c14'])
- Block(0x80003c14..0x80003c34 j kind=j succs=['0x80003bec'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE
- `value_truthy` → LANDED (value_truthy_spec)
- `value_int` → LANDED (value_int_spec)
- `value_bool` → LANDED (value_bool_spec, value_bool_spec_full)
- `value_kind_name` → NONE
- `runtime_error` → LANDED (runtime_error_spec)

## Register/memory outcome sketch

- regs written on slice: a2, a0, a4, a5, a3, a1, s0, ra, s2, s1, sp
- loads: 13, stores: 33

## Disasm slice

```
  -- block 0x800035e0 [jal]
  800035e0: ld a2,16(a2)
  800035e4: addi a0,sp,144
  800035e8: jal 80003164 <eval_expr>
  -- block 0x800035ec [br]
  800035ec: lw a4,8(s0)
  800035f0: li a5,12
  800035f4: ld a3,144(sp)
  800035f8: beq a4,a5,800039ac <eval_expr+0x848>
  -- block 0x800039ac [br]
  800039ac: ld a1,152(sp)
  800039b0: ld a4,160(sp)
  800039b4: lw a0,144(sp)
  800039b8: sd a3,240(sp)
  800039bc: sd a1,248(sp)
  800039c0: sd a4,256(sp)
  800039c4: li a2,2
  800039c8: lw s0,4(s0)
  800039cc: bne a0,a2,80003b58 <eval_expr+0x9f4>
  -- block 0x800035fc [jal]
  800035fc: ld a4,152(sp)
  80003600: ld a5,160(sp)
  80003604: addi a0,sp,64
  80003608: sd a3,64(sp)
  8000360c: sd a4,72(sp)
  80003610: sd a5,80(sp)
  80003614: jal 8000282c <value_truthy>
  -- block 0x80003b58 [fallthrough]
  80003b58: sd s3,1048(sp)
  80003b5c: sd s4,1040(sp)
  80003b60: sd s5,1032(sp)
  80003b64: sd s6,1024(sp)
  80003b68: sd s7,1016(sp)
  80003b6c: addi a0,sp,64
  80003b70: sd a3,64(sp)
  80003b74: sd a1,72(sp)
  80003b78: sd a4,80(sp)
  -- block 0x800039d0 [jal]
  800039d0: neg a1,a1
  800039d4: mv a0,s1
  800039d8: jal 8000280c <value_int>
  -- block 0x80003618 [jal]
  80003618: seqz a1,a0
  8000361c: mv a0,s1
  80003620: jal 800027f8 <value_bool>
  -- block 0x80003b7c [jal] LOOP-HEAD
  80003b7c: jal 800029c8 <value_kind_name>
  -- block 0x800039dc [j]
  800039dc: j 800033ec <eval_expr+0x288>
  -- block 0x80003624 [j]
  80003624: j 800033ec <eval_expr+0x288>
  -- block 0x80003b80 [jal]
  80003b80: mv a4,a0
  80003b84: mv a1,s0
  80003b88: mv a0,s2
  80003b8c: auipc a3,0x16
  80003b90: addi a3,a3,-1188
  80003b94: auipc a2,0x16
  80003b98: addi a2,a2,-1956
  80003b9c: jal 80002da8 <runtime_error>
  -- block 0x800033ec [ret] LOOP-HEAD
  800033ec: ld ra,1080(sp)
  800033f0: ld s0,1072(sp)
  800033f4: ld s2,1056(sp)
  800033f8: mv a0,s1
  800033fc: ld s1,1064(sp)
  80003400: addi sp,sp,1088
  80003404: ret 
  -- block 0x80003ba0 [jal]
  80003ba0: mv a1,s0
  80003ba4: mv a0,s2
  80003ba8: li a4,0
  80003bac: li a3,0
  80003bb0: auipc a2,0x16
  80003bb4: addi a2,a2,-1896
  80003bb8: sd s4,1040(sp)
  80003bbc: sd s5,1032(sp)
  80003bc0: sd s6,1024(sp)
  80003bc4: sd s7,1016(sp)
  80003bc8: jal 80002da8 <runtime_error>
  -- block 0x80003bcc [fallthrough]
  80003bcc: sd s4,1040(sp)
  80003bd0: sd s5,1032(sp)
  80003bd4: sd s6,1024(sp)
  80003bd8: sd s7,1016(sp)
  80003bdc: addi a0,sp,64
  80003be0: sd a7,248(sp)
  80003be4: sd a4,64(sp)
  80003be8: sd a7,72(sp)
  -- block 0x80003bec [jal] LOOP-HEAD
  80003bec: sd a5,80(sp)
  80003bf0: jal 800029c8 <value_kind_name>
  -- block 0x80003bf4 [jal]
  80003bf4: mv a4,a0
  80003bf8: mv a1,s0
  80003bfc: mv a0,s2
  80003c00: auipc a3,0x16
  80003c04: addi a3,a3,-1984
  80003c08: auipc a2,0x15
  80003c0c: addi a2,a2,2024
  80003c10: jal 80002da8 <runtime_error>
  -- block 0x80003c14 [j]
  80003c14: sd s4,1040(sp)
  80003c18: sd s5,1032(sp)
  80003c1c: sd s6,1024(sp)
  80003c20: sd s7,1016(sp)
  80003c24: addi a0,sp,64
  … (disasm capped at 90 lines)
```
